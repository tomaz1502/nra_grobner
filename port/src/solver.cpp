#include "solver.h"

#include <algorithm>
#include <iostream>
#include <sstream>

#include "CoCoA/BigRatOps.H"
#include "CoCoA/CanonicalHom.H"
#include "CoCoA/FractionField.H"
#include "CoCoA/PPMonoid.H"
#include "CoCoA/PPOrdering.H"
#include "CoCoA/PolyRing.H"
#include "CoCoA/RingHom.H"
#include "CoCoA/RingQQ.H"
#include "CoCoA/SparsePolyIter.H"
#include "CoCoA/SparsePolyOps-RingElem.H"
#include "CoCoA/SparsePolyOps-ideal.H"
#include "CoCoA/factor.H"
#include "CoCoA/ideal.H"
#include "CoCoA/symbol.H"

using CoCoA::BigRat;
using CoCoA::RingElem;

namespace tiwari {

TiwariSolver::TiwariSolver(const CoCoA::SparsePolyRing & ring,
                           std::vector<RingElem> polys,
                           std::set<long> v_pos,
                           std::set<long> v_nonneg,
                           bool verbose)
    : ring_(ring),
      polys_(std::move(polys)),
      v_pos_(std::move(v_pos)),
      v_nonneg_(std::move(v_nonneg)),
      alpha_poly_ring_(CoCoA::RingQQ()),  // placeholder until alpha is live
      verbose_(verbose)
{
}

void TiwariSolver::log(const std::string & msg) const
{
  if (verbose_)
  {
    std::cerr << msg << std::endl;
  }
}

// -- ring management ---------------------------------------------------------

long TiwariSolver::add_main_var(const CoCoA::symbol & s)
{
  std::vector<CoCoA::symbol> syms = CoCoA::symbols(CoCoA::PPM(ring_));
  syms.push_back(s);
  CoCoA::SparsePolyRing bigger =
      CoCoA::NewPolyRing(CoCoA::CoeffRing(ring_), syms, CoCoA::lex);
  std::vector<RingElem> images;
  const long n = CoCoA::NumIndets(ring_);
  images.reserve(n);
  for (long i = 0; i < n; ++i)
  {
    images.push_back(CoCoA::indet(bigger, i));
  }
  CoCoA::RingHom phi = CoCoA::PolyAlgebraHom(ring_, bigger, images);
  for (auto & p : polys_)
  {
    p = phi(p);
  }
  for (auto & d : def_exprs_)
  {
    d = phi(d);
  }
  ring_ = bigger;
  return n;  // index of the new indeterminate
}

long TiwariSolver::enter_alpha_ring(const CoCoA::symbol & alpha_sym,
                                    const CoCoA::symbol & evar_sym)
{
  alpha_poly_ring_ = CoCoA::NewPolyRing(
      CoCoA::RingQQ(), std::vector<CoCoA::symbol>{ alpha_sym });
  CoCoA::FractionField K = CoCoA::NewFractionField(alpha_poly_ring_);

  std::vector<CoCoA::symbol> syms = CoCoA::symbols(CoCoA::PPM(ring_));
  syms.push_back(evar_sym);
  CoCoA::SparsePolyRing bigger = CoCoA::NewPolyRing(K, syms, CoCoA::lex);

  std::vector<RingElem> images;
  const long n = CoCoA::NumIndets(ring_);
  images.reserve(n);
  for (long i = 0; i < n; ++i)
  {
    images.push_back(CoCoA::indet(bigger, i));
  }
  // coefficients: QQ -> QQ(alpha)[vars]
  CoCoA::RingHom coeffhom = CoCoA::CanonicalHom(CoCoA::RingQQ(), bigger);
  CoCoA::RingHom phi = CoCoA::PolyRingHom(ring_, bigger, coeffhom, images);
  for (auto & p : polys_)
  {
    p = phi(p);
  }
  for (auto & d : def_exprs_)
  {
    d = phi(d);
  }
  ring_ = bigger;
  alpha_live_ = true;
  return n;
}

void TiwariSolver::leave_alpha_ring(const BigRat & value)
{
  std::vector<CoCoA::symbol> syms = CoCoA::symbols(CoCoA::PPM(ring_));
  CoCoA::SparsePolyRing smaller =
      CoCoA::NewPolyRing(CoCoA::RingQQ(), syms, CoCoA::lex);

  // QQ[alpha] -> QQ[vars], alpha |-> value
  CoCoA::SparsePolyRing Pa(alpha_poly_ring_);
  CoCoA::RingHom evalA = CoCoA::PolyRingHom(
      Pa,
      smaller,
      CoCoA::CanonicalHom(CoCoA::RingQQ(), smaller),
      std::vector<RingElem>{ RingElem(smaller, value) });
  // QQ(alpha) -> QQ[vars]; total on our polys: denominators are cleared
  CoCoA::FractionField K(CoCoA::CoeffRing(ring_));
  CoCoA::RingHom coeffhom = CoCoA::InducedHom(K, evalA);

  std::vector<RingElem> images;
  const long n = CoCoA::NumIndets(ring_);
  images.reserve(n);
  for (long i = 0; i < n; ++i)
  {
    images.push_back(CoCoA::indet(smaller, i));
  }
  CoCoA::RingHom phi = CoCoA::PolyRingHom(ring_, smaller, coeffhom, images);
  for (auto & p : polys_)
  {
    p = phi(p);
  }
  for (auto & d : def_exprs_)
  {
    d = phi(d);
  }
  ring_ = smaller;
  alpha_live_ = false;
}

RingElem TiwariSolver::clear_denominators(const RingElem & f) const
{
  if (!alpha_live_ || CoCoA::IsZero(f))
  {
    return f;
  }
  RingElem d = CoCoA::one(alpha_poly_ring_);
  for (CoCoA::SparsePolyIter it = CoCoA::BeginIter(f); !CoCoA::IsEnded(it);
       ++it)
  {
    d = CoCoA::lcm(d, CoCoA::den(coeff(it)));
  }
  if (CoCoA::IsOne(d))
  {
    return f;
  }
  CoCoA::FractionField K(CoCoA::CoeffRing(ring_));
  return f * CoCoA::CoeffEmbeddingHom(ring_)(CoCoA::EmbeddingHom(K)(d));
}

RingElem TiwariSolver::alpha_in_ring() const
{
  CoCoA::FractionField K(CoCoA::CoeffRing(ring_));
  RingElem alpha_in_K =
      CoCoA::EmbeddingHom(K)(CoCoA::indet(alpha_poly_ring_, 0));
  return CoCoA::CoeffEmbeddingHom(ring_)(alpha_in_K);
}

// -- helpers ------------------------------------------------------------------

bool TiwariSolver::has_alpha(const RingElem & f) const
{
  if (!alpha_live_)
  {
    return false;
  }
  for (CoCoA::SparsePolyIter it = CoCoA::BeginIter(f); !CoCoA::IsEnded(it);
       ++it)
  {
    BigRat q;
    if (!CoCoA::IsRational(q, coeff(it)))
    {
      return true;
    }
  }
  return false;
}

bool TiwariSolver::is_nonneg_pp(const CoCoA::ConstRefPPMonoidElem pp) const
{
  const long n = CoCoA::NumIndets(ring_);
  for (long i = 0; i < n; ++i)
  {
    long e = CoCoA::exponent(pp, i);
    if (e > 0 && v_nonneg_.count(i) == 0 && e % 2 != 0)
    {
      return false;
    }
  }
  return true;
}

bool TiwariSolver::is_strictly_pos_pp(
    const CoCoA::ConstRefPPMonoidElem pp) const
{
  const long n = CoCoA::NumIndets(ring_);
  for (long i = 0; i < n; ++i)
  {
    if (CoCoA::exponent(pp, i) > 0 && v_pos_.count(i) == 0)
    {
      return false;
    }
  }
  return true;
}

bool TiwariSolver::is_known_def(const RingElem & expr) const
{
  for (const auto & d : def_exprs_)
  {
    if (d == expr)
    {
      return true;
    }
  }
  return false;
}

// -- inference rules -----------------------------------------------------------

bool TiwariSolver::check_witness(const RingElem & f) const
{
  // single nonzero term whose variables are all strictly positive and whose
  // coefficient does not depend on a live alpha (sign unknown)
  return !CoCoA::IsZero(f) && CoCoA::NumTerms(f) == 1 && !has_alpha(f)
         && is_strictly_pos_pp(CoCoA::LPP(f));
}

bool TiwariSolver::try_detect(const std::vector<RingElem> & gb, bool & unsat)
{
  // candidate split: every monomial manifestly nonneg, coefficients all of
  // one sign => each term must vanish individually.  Polys with
  // alpha-dependent coefficients are skipped (signs unknown).
  std::vector<std::pair<size_t, std::vector<RingElem>>> candidates;
  for (size_t i = 0; i < gb.size(); ++i)
  {
    const RingElem & f = gb[i];
    if (CoCoA::NumTerms(f) <= 1 || has_alpha(f))
    {
      continue;
    }
    bool ok = true;
    int sign = 0;
    std::vector<RingElem> terms;
    for (CoCoA::SparsePolyIter it = CoCoA::BeginIter(f); !CoCoA::IsEnded(it);
         ++it)
    {
      if (!is_nonneg_pp(PP(it)))
      {
        ok = false;
        break;
      }
      BigRat c;
      CoCoA::IsRational(c, coeff(it));
      int s = CoCoA::sign(c);
      if (sign == 0)
      {
        sign = s;
      }
      else if (s != sign)
      {
        ok = false;
        break;
      }
      terms.push_back(CoCoA::monomial(ring_, coeff(it), PP(it)));
    }
    if (ok)
    {
      candidates.emplace_back(i, std::move(terms));
    }
  }
  if (candidates.empty())
  {
    return false;
  }

  for (auto cand = candidates.rbegin(); cand != candidates.rend(); ++cand)
  {
    std::ostringstream os;
    os << "  Detect: " << gb[cand->first] << " -> " << cand->second.size()
       << " terms";
    log(os.str());
    polys_.erase(polys_.begin() + static_cast<long>(cand->first));
    polys_.insert(polys_.end(), cand->second.begin(), cand->second.end());
  }
  for (const auto & cand : candidates)
  {
    for (const RingElem & t : cand.second)
    {
      if (check_witness(t))
      {
        std::ostringstream os;
        os << "  UNSAT (Witness after Detect): " << t;
        log(os.str());
        unsat = true;
        return true;
      }
    }
  }
  return true;
}

bool TiwariSolver::try_extend1(const std::vector<RingElem> & gb)
{
  for (const RingElem & f : gb)
  {
    if (CoCoA::NumTerms(f) <= 1)
    {
      continue;
    }
    CoCoA::ConstRefPPMonoidElem lpp = CoCoA::LPP(f);
    if (!is_nonneg_pp(lpp) || CoCoA::StdDeg(lpp) <= 1)
    {
      continue;
    }
    RingElem lm = CoCoA::monomial(ring_, 1, lpp);
    if (is_known_def(lm))
    {
      continue;
    }
    std::vector<long> expv = CoCoA::exponents(lpp);
    long e = add_main_var(CoCoA::symbol("e", ++ext_count_));
    v_nonneg_.insert(e);
    expv.push_back(0);
    RingElem def = CoCoA::monomial(ring_, 1, expv);
    def_exprs_.push_back(def);
    polys_.push_back(def - CoCoA::indet(ring_, e));
    std::ostringstream os;
    os << "  Extend1: " << CoCoA::indet(ring_, e) << " := " << def;
    log(os.str());
    return true;
  }
  return false;
}

bool TiwariSolver::try_extend3(const std::vector<RingElem> & gb)
{
  for (const RingElem & f : gb)
  {
    if (CoCoA::NumTerms(f) <= 1)
    {
      continue;
    }
    std::vector<long> expv = CoCoA::exponents(CoCoA::LPP(f));
    long total = 0;
    for (size_t i = 0; i < expv.size(); ++i)
    {
      long m = expv[i];
      expv[i] = (v_nonneg_.count(static_cast<long>(i)) != 0) ? m / 2
                                                             : (m + 1) / 2;
      total += expv[i];
    }
    if (total <= 1)
    {
      continue;
    }
    RingElem nu = CoCoA::monomial(ring_, 1, expv);
    if (is_known_def(nu))
    {
      continue;
    }
    long e = add_main_var(CoCoA::symbol("e", ++ext_count_));
    expv.push_back(0);
    RingElem def = CoCoA::monomial(ring_, 1, expv);
    def_exprs_.push_back(def);
    polys_.push_back(def - CoCoA::indet(ring_, e));
    std::ostringstream os;
    os << "  Extend3: " << CoCoA::indet(ring_, e) << " := " << def;
    log(os.str());
    return true;
  }
  return false;
}

bool TiwariSolver::try_extend2(const std::vector<RingElem> & gb)
{
  if (alpha_live_)
  {
    return false;
  }
  const long n = CoCoA::NumIndets(ring_);

  std::set<std::vector<long>> monoms;
  for (const RingElem & f : gb)
  {
    for (CoCoA::SparsePolyIter it = CoCoA::BeginIter(f); !CoCoA::IsEnded(it);
         ++it)
    {
      monoms.insert(CoCoA::exponents(PP(it)));
    }
  }

  auto unit = [n](long i, long ei, long j, long ej) {
    std::vector<long> v(static_cast<size_t>(n), 0);
    v[static_cast<size_t>(i)] = ei;
    if (j >= 0)
    {
      v[static_cast<size_t>(j)] = ej;
    }
    return v;
  };

  for (long i = 0; i < n; ++i)
  {
    if (monoms.count(unit(i, 2, -1, 0)) == 0)
    {
      continue;
    }
    for (long j = i + 1; j < n; ++j)
    {
      if (monoms.count(unit(j, 2, -1, 0)) == 0
          || monoms.count(unit(i, 1, j, 1)) == 0)
      {
        continue;
      }
      long e = enter_alpha_ring(CoCoA::symbol("alpha", ++alpha_count_),
                                CoCoA::symbol("e", ++ext_count_));
      RingElem nu = CoCoA::indet(ring_, i)
                    + alpha_in_ring() * CoCoA::indet(ring_, j);
      def_exprs_.push_back(nu);
      polys_.push_back(nu - CoCoA::indet(ring_, e));
      std::ostringstream os;
      os << "  Extend2: " << CoCoA::indet(ring_, e) << " := " << nu;
      log(os.str());
      return true;
    }
  }
  return false;
}

bool TiwariSolver::try_instantiate(const std::vector<RingElem> & gb)
{
  if (!alpha_live_)
  {
    return false;
  }
  CoCoA::SparsePolyRing Pa(alpha_poly_ring_);
  const long a = 0;  // alpha is the only indet of Pa

  for (const RingElem & f : gb)
  {
    if (CoCoA::IsZero(f))
    {
      continue;
    }
    // coefficients are in QQ[alpha] (denominators are cleared after GB)
    for (CoCoA::SparsePolyIter it = CoCoA::BeginIter(f); !CoCoA::IsEnded(it);
         ++it)
    {
      RingElem cp = CoCoA::num(coeff(it));
      if (CoCoA::IsConstant(cp))
      {
        continue;
      }
      // rational roots = roots of the linear factors over QQ
      std::vector<BigRat> roots;
      CoCoA::factorization<RingElem> facs = CoCoA::factor(cp);
      for (const RingElem & lin : facs.myFactors())
      {
        if (CoCoA::deg(lin) != 1)
        {
          continue;
        }
        BigRat c1, c0;  // lin = c1*alpha + c0
        for (CoCoA::SparsePolyIter lt = CoCoA::BeginIter(lin);
             !CoCoA::IsEnded(lt);
             ++lt)
        {
          BigRat c;
          CoCoA::IsRational(c, coeff(lt));
          if (CoCoA::exponent(PP(lt), a) == 1)
          {
            c1 = c;
          }
          else
          {
            c0 = c;
          }
        }
        BigRat r = -c0 / c1;
        if (!CoCoA::IsZero(r))
        {
          roots.push_back(r);
        }
      }
      if (roots.empty())
      {
        continue;
      }
      // smallest magnitude first; ties go to the negative root (-1 over
      // +1), matching the paper's preference for (x - y)^2 witnesses.
      // (Deliberate deviation: the Python sort key (abs(r), -r) prefers
      // the positive root, contradicting its own comment.)
      BigRat best = roots[0];
      for (const BigRat & r : roots)
      {
        if (abs(r) < abs(best) || (abs(r) == abs(best) && r < best))
        {
          best = r;
        }
      }
      std::ostringstream os;
      os << "  Instantiate: alpha := " << best;
      log(os.str());
      leave_alpha_ring(best);
      return true;
    }
  }
  return false;
}

// -- main loop -------------------------------------------------------------------

SolveResult TiwariSolver::solve(long max_rounds)
{
  for (long rnd = 0; rnd < max_rounds; ++rnd)
  {
    polys_.erase(std::remove_if(polys_.begin(), polys_.end(),
                                [](const RingElem & p)
                                { return CoCoA::IsZero(p); }),
                 polys_.end());
    if (polys_.empty())
    {
      log("  No equalities left.");
      return SolveResult::UNKNOWN;
    }

    CoCoA::ideal I(ring_, polys_);
    polys_ = CoCoA::GBasis(I);
    for (auto & p : polys_)
    {
      p = clear_denominators(p);
    }
    std::vector<RingElem> gb = polys_;
    {
      std::ostringstream os;
      os << "--- Round " << rnd << " ---  |GB|=" << gb.size()
         << " |vars|=" << CoCoA::NumIndets(ring_);
      log(os.str());
    }

    if (alpha_live_ && try_instantiate(gb))
    {
      continue;
    }

    // nonzero constant in the basis => trivially UNSAT
    for (const RingElem & f : gb)
    {
      if (CoCoA::IsConstant(f) && !CoCoA::IsZero(f) && !has_alpha(f))
      {
        log("  UNSAT: nonzero constant in GB");
        return SolveResult::UNSAT;
      }
    }

    bool found_witness = false;
    for (const RingElem & f : gb)
    {
      if (check_witness(f))
      {
        std::ostringstream os;
        os << "  UNSAT (Witness): " << f;
        log(os.str());
        found_witness = true;
        break;
      }
    }
    if (found_witness)
    {
      return SolveResult::UNSAT;
    }

    bool unsat = false;
    if (try_detect(gb, unsat))
    {
      if (unsat)
      {
        return SolveResult::UNSAT;
      }
      continue;
    }
    if (try_extend2(gb))
    {
      continue;
    }
    if (try_extend1(gb))
    {
      continue;
    }
    if (try_extend3(gb))
    {
      continue;
    }

    log("  No rules applicable.");
    return SolveResult::UNKNOWN;
  }
  log("  Reached max rounds.");
  return SolveResult::UNKNOWN;
}

}  // namespace tiwari
