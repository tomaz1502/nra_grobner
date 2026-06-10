/**
 * Tiwari's algebraic unsatisfiability procedure (CSL 2005) over CoCoALib.
 * C++ port of tiwari.py.
 *
 * Alpha handling mirrors the Python implementation: after Extend2 the
 * coefficient domain becomes QQ(alpha) (sympy's QQ[alpha] lifted to its
 * fraction field, which is what sympy's groebner uses internally), so the
 * polynomial ring switches from QQ[vars] to QQ(alpha)[vars].  Basis
 * elements are denominator-cleared after every GB computation, keeping all
 * coefficients in QQ[alpha]; instantiation evaluates alpha at a rational
 * root and drops back to QQ[vars].  At most one alpha is live at a time.
 *
 * Variable order (lex, largest first): original variables in declaration
 * order, then slack variables, then extension variables in creation order.
 * The ring is rebuilt (and all polynomials mapped over) whenever a
 * variable is added or the coefficient domain changes.
 */

#pragma once

#include <set>
#include <string>
#include <vector>

#include "CoCoA/BigRat.H"
#include "CoCoA/SparsePolyRing.H"
#include "CoCoA/ring.H"

namespace tiwari {

enum class SolveResult
{
  UNSAT,
  UNKNOWN,
};

class TiwariSolver
{
 public:
  /** @param ring   lex polynomial ring over QQ containing the original and
   *                slack variables (extension variables are added on demand)
   *  @param polys  the equality side: every constraint as poly = 0, with
   *                slack variables already substituted for inequalities
   *  @param v_pos  indices of strictly positive variables (gt slacks)
   *  @param v_nonneg indices of nonnegative variables (superset of v_pos)
   */
  TiwariSolver(const CoCoA::SparsePolyRing & ring,
               std::vector<CoCoA::RingElem> polys,
               std::set<long> v_pos,
               std::set<long> v_nonneg,
               bool verbose = false);

  SolveResult solve(long max_rounds = 200);

 private:
  // -- ring management --
  /** Append a variable to the current ring (same coefficient ring);
   *  remaps all state.  Returns the new indeterminate's index. */
  long add_main_var(const CoCoA::symbol & s);
  /** Switch QQ[vars] -> QQ(alpha)[vars, evar] for Extend2.
   *  Returns the index of evar. */
  long enter_alpha_ring(const CoCoA::symbol & alpha_sym,
                        const CoCoA::symbol & evar_sym);
  /** Evaluate the live alpha at value; back to QQ[vars]. */
  void leave_alpha_ring(const CoCoA::BigRat & value);
  /** Multiply f by the lcm of its coefficients' denominators, so that all
   *  coefficients lie in QQ[alpha].  Identity when no alpha is live. */
  CoCoA::RingElem clear_denominators(const CoCoA::RingElem & f) const;
  /** The live alpha as an element of the current ring's coefficient field,
   *  embedded into the ring. */
  CoCoA::RingElem alpha_in_ring() const;

  // -- helpers --
  /** True if some coefficient of f genuinely involves the live alpha. */
  bool has_alpha(const CoCoA::RingElem & f) const;
  bool is_nonneg_pp(const CoCoA::ConstRefPPMonoidElem pp) const;
  bool is_strictly_pos_pp(const CoCoA::ConstRefPPMonoidElem pp) const;
  bool is_known_def(const CoCoA::RingElem & expr) const;

  // -- inference rules (operating on the current basis) --
  bool check_witness(const CoCoA::RingElem & f) const;
  bool try_detect(const std::vector<CoCoA::RingElem> & gb, bool & unsat);
  bool try_extend1(const std::vector<CoCoA::RingElem> & gb);
  bool try_extend2(const std::vector<CoCoA::RingElem> & gb);
  bool try_extend3(const std::vector<CoCoA::RingElem> & gb);
  bool try_instantiate(const std::vector<CoCoA::RingElem> & gb);

  void log(const std::string & msg) const;

  CoCoA::SparsePolyRing ring_;
  std::vector<CoCoA::RingElem> polys_;
  std::set<long> v_pos_;
  std::set<long> v_nonneg_;
  std::vector<CoCoA::RingElem> def_exprs_;  ///< defining exprs of ext vars
  bool alpha_live_ = false;
  CoCoA::ring alpha_poly_ring_;  ///< QQ[alpha] while alpha is live
  long ext_count_ = 0;
  long alpha_count_ = 0;
  bool verbose_;
};

}  // namespace tiwari
