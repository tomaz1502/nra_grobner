/**
 * Conversion of normalized smt-switch terms into CoCoALib polynomials, and
 * assembly of the Tiwari solver input (slack-variable encoding).
 *
 * The solver ring is QQ[x_0, ..., x_{n-1}, s_1, ..., s_m] with one
 * indeterminate per declared Real variable (declaration order) followed by
 * one slack per inequality (constraint order: v[k] for >, w[k] for >=),
 * lex ordered.  SMT variable names are reused as CoCoA symbols when CoCoA
 * accepts them; otherwise the variable becomes the subscripted symbol x[i].
 */

#pragma once

#include <set>
#include <string>
#include <unordered_map>
#include <vector>

#include "CoCoA/BigRat.H"
#include "CoCoA/SparsePolyRing.H"
#include "CoCoA/ring.H"

#include "parser.h"

namespace tiwari {

class PolyConverter
{
 public:
  /** @param vars declared Real variables; vars[i] maps to indet i of ring
   *  @param ring a polynomial ring whose first vars.size() indets
   *              correspond to vars (it may have more, e.g. slacks) */
  PolyConverter(const std::vector<smt::Term> & vars,
                const CoCoA::SparsePolyRing & ring);

  /** Converts a normalized polynomial term (Plus/Minus/Negate/Mult/Pow/Div
   *  over symbols and rational constants) into a ring element.
   *  Throws UnsupportedInput on anything non-polynomial. */
  CoCoA::RingElem convert(const smt::Term & t) const;

  const CoCoA::SparsePolyRing & ring() const { return ring_; }

 private:
  CoCoA::BigRat value_of(const smt::Term & t) const;

  std::unordered_map<std::string, long> index_;  ///< SMT name -> indet index
  CoCoA::SparsePolyRing ring_;
};

/** Everything TiwariSolver needs, built from the parsed problem. */
struct SolverInput
{
  CoCoA::SparsePolyRing ring;
  std::vector<CoCoA::RingElem> polys;  ///< constraints as poly = 0
  std::set<long> v_pos;                ///< strictly positive slack indices
  std::set<long> v_nonneg;             ///< nonnegative slack indices
};

SolverInput build_solver_input(const std::vector<smt::Term> & vars,
                               const std::vector<Constraint> & constraints);

/** Parses a cvc5 rational value string: "5", "5.25", "1/2",
 *  "(/ 1 2)", "(- 5.0)" and nestings thereof. */
CoCoA::BigRat parse_rational(const std::string & s);

}  // namespace tiwari
