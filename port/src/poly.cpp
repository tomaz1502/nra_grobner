#include "poly.h"

#include <sstream>

#include "CoCoA/BigInt.H"
#include "CoCoA/BigIntOps.H"
#include "CoCoA/BigRatOps.H"
#include "CoCoA/PPOrdering.H"
#include "CoCoA/RingQQ.H"
#include "CoCoA/error.H"
#include "CoCoA/symbol.H"

namespace tiwari {

namespace {

smt::PrimOp prim_op(const smt::Term & t)
{
  smt::Op op = t->get_op();
  return op.is_null() ? smt::NUM_OPS_AND_NULL : op.prim_op;
}

smt::TermVec children(const smt::Term & t)
{
  return smt::TermVec(t->begin(), t->end());
}

/** Recursive-descent parse over whitespace tokens with '(' / ')' stripped. */
CoCoA::BigRat parse_tokens(const std::vector<std::string> & toks, size_t & i)
{
  if (i >= toks.size())
  {
    throw UnsupportedInput("Malformed rational constant");
  }
  const std::string & tok = toks[i++];
  if (tok == "/")
  {
    CoCoA::BigRat num = parse_tokens(toks, i);
    CoCoA::BigRat den = parse_tokens(toks, i);
    return num / den;
  }
  if (tok == "-")
  {
    return -parse_tokens(toks, i);
  }
  // literal: integer, fraction "p/q", or decimal "d.d"
  std::string::size_type dot = tok.find('.');
  if (dot == std::string::npos)
  {
    return CoCoA::BigRatFromString(tok);
  }
  std::string digits = tok.substr(0, dot) + tok.substr(dot + 1);
  CoCoA::BigInt num = CoCoA::BigIntFromString(digits);
  CoCoA::BigInt den =
      CoCoA::power(10, static_cast<long>(tok.size() - dot - 1));
  return CoCoA::BigRat(num, den);
}

}  // namespace

CoCoA::BigRat parse_rational(const std::string & s)
{
  std::string cleaned;
  cleaned.reserve(s.size());
  for (char c : s)
  {
    cleaned += (c == '(' || c == ')') ? ' ' : c;
  }
  std::vector<std::string> toks;
  std::istringstream iss(cleaned);
  std::string tok;
  while (iss >> tok)
  {
    toks.push_back(tok);
  }
  size_t i = 0;
  CoCoA::BigRat q = parse_tokens(toks, i);
  if (i != toks.size())
  {
    throw UnsupportedInput("Malformed rational constant: " + s);
  }
  return q;
}

PolyConverter::PolyConverter(const std::vector<smt::Term> & vars,
                             const CoCoA::SparsePolyRing & ring)
    : ring_(ring)
{
  for (size_t i = 0; i < vars.size(); ++i)
  {
    index_[vars[i]->to_string()] = static_cast<long>(i);
  }
}

SolverInput build_solver_input(const std::vector<smt::Term> & vars,
                               const std::vector<Constraint> & constraints)
{
  std::vector<CoCoA::symbol> syms;
  syms.reserve(vars.size());
  for (size_t i = 0; i < vars.size(); ++i)
  {
    std::string name = vars[i]->to_string();
    try
    {
      syms.push_back(CoCoA::symbol(name));
    }
    catch (const CoCoA::ErrorInfo &)
    {
      // name not a valid CoCoA symbol; fall back to x[i]
      syms.push_back(CoCoA::symbol("x", static_cast<long>(i)));
    }
  }
  long vc = 0;
  long wc = 0;
  for (const Constraint & c : constraints)
  {
    if (c.rel == Rel::GT)
    {
      syms.push_back(CoCoA::symbol("v", ++vc));
    }
    else if (c.rel == Rel::GE)
    {
      syms.push_back(CoCoA::symbol("w", ++wc));
    }
  }

  CoCoA::SparsePolyRing ring =
      CoCoA::NewPolyRing(CoCoA::RingQQ(), syms, CoCoA::lex);
  PolyConverter conv(vars, ring);

  SolverInput in{ ring, {}, {}, {} };
  long slack = static_cast<long>(vars.size());
  for (const Constraint & c : constraints)
  {
    CoCoA::RingElem p = conv.convert(c.poly);
    switch (c.rel)
    {
      case Rel::EQ:
        in.polys.push_back(p);
        break;
      case Rel::GT:
        in.v_pos.insert(slack);
        in.v_nonneg.insert(slack);
        in.polys.push_back(p - CoCoA::indet(ring, slack));
        ++slack;
        break;
      case Rel::GE:
        in.v_nonneg.insert(slack);
        in.polys.push_back(p - CoCoA::indet(ring, slack));
        ++slack;
        break;
    }
  }
  return in;
}

CoCoA::BigRat PolyConverter::value_of(const smt::Term & t) const
{
  if (!t->is_value())
  {
    throw UnsupportedInput("Expected a rational constant: " + t->to_string());
  }
  return parse_rational(t->to_string());
}

CoCoA::RingElem PolyConverter::convert(const smt::Term & t) const
{
  smt::PrimOp op = prim_op(t);

  if (op == smt::NUM_OPS_AND_NULL)
  {
    if (t->is_value())
    {
      return CoCoA::RingElem(ring_, parse_rational(t->to_string()));
    }
    auto it = index_.find(t->to_string());
    if (it != index_.end())
    {
      return CoCoA::indet(ring_, it->second);
    }
    throw UnsupportedInput("Unknown symbol: " + t->to_string());
  }

  smt::TermVec args = children(t);

  switch (op)
  {
    case smt::Plus:
    {
      CoCoA::RingElem sum(ring_);
      for (const auto & a : args)
      {
        sum += convert(a);
      }
      return sum;
    }
    case smt::Minus:
    {
      CoCoA::RingElem res = convert(args.at(0));
      for (size_t i = 1; i < args.size(); ++i)
      {
        res -= convert(args[i]);
      }
      return res;
    }
    case smt::Negate:
      return -convert(args.at(0));
    case smt::Mult:
    {
      CoCoA::RingElem prod = CoCoA::one(ring_);
      for (const auto & a : args)
      {
        prod *= convert(a);
      }
      return prod;
    }
    case smt::Pow:
    {
      CoCoA::BigRat e = value_of(args.at(1));
      if (!CoCoA::IsOneDen(e) || e < 0)
      {
        throw UnsupportedInput("Non-natural exponent: " + t->to_string());
      }
      return CoCoA::power(convert(args.at(0)), CoCoA::num(e));
    }
    case smt::Div:
    {
      // only division by nonzero constants keeps us polynomial
      CoCoA::RingElem res = convert(args.at(0));
      for (size_t i = 1; i < args.size(); ++i)
      {
        CoCoA::BigRat den = value_of(args[i]);
        if (CoCoA::IsZero(den))
        {
          throw UnsupportedInput("Division by zero: " + t->to_string());
        }
        res *= CoCoA::RingElem(ring_, 1 / den);
      }
      return res;
    }
    default:
      throw UnsupportedInput("Non-polynomial term: " + t->to_string());
  }
}

}  // namespace tiwari
