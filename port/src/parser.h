/**
 * SMT-LIB (QF_NRA fragment) front end for the Tiwari procedure.
 *
 * Parses a file with smt-switch's SmtLibReader and normalizes the asserted
 * conjunction of relational atoms into constraints of the form
 *   poly = 0, poly >= 0, poly > 0,
 * mirroring main.py: conjunctions are flattened, <, <=, >, >= and the
 * negations of < and <= are rewritten; disjunctions and disequalities are
 * rejected as unsupported.
 */

#pragma once

#include <stdexcept>
#include <string>
#include <vector>

#include "smt-switch/smt.h"
#include "smt-switch/smtlib_reader.h"

namespace tiwari {

/** Raised on input outside the supported fragment. */
class UnsupportedInput : public std::runtime_error
{
 public:
  explicit UnsupportedInput(const std::string & msg) : std::runtime_error(msg)
  {
  }
};

/** A cvc5 solver for pure-Real problems.
 *
 *  The smt-switch SMT-LIB grammar always gives integer numerals the Int
 *  sort, which breaks mixed terms like (= 0 (* x x)) over Reals.  This
 *  solver creates Int-sorted numerals as Real instead, which is the
 *  SMT-LIB-correct reading in QF_NRA (Ints do not exist in that logic).
 */
smt::SmtSolver make_qfnra_solver();

enum class Rel
{
  EQ,  ///< poly = 0
  GE,  ///< poly >= 0
  GT,  ///< poly > 0
};

struct Constraint
{
  smt::Term poly;  ///< polynomial term, constrained against 0
  Rel rel;
};

class TiwariReader : public smt::SmtLibReader
{
 public:
  explicit TiwariReader(smt::SmtSolver & solver);

  /** Records the assertion as normalized constraints (does not assert
   *  anything into the underlying solver). */
  void assert_formula(const smt::Term & assertion) override;

  /** (check-sat) is recorded but never dispatched to the solver. */
  smt::Result check_sat() override;

  /** Records declared Real constants, in declaration order. */
  void new_symbol(const std::string & name, const smt::Sort & sort) override;

  const std::vector<smt::Term> & vars() const { return vars_; }
  const std::vector<Constraint> & constraints() const { return constraints_; }
  bool saw_check_sat() const { return saw_check_sat_; }

 private:
  void add_atom(const smt::Term & atom);
  smt::Term diff(const smt::Term & lhs, const smt::Term & rhs);

  std::vector<smt::Term> vars_;
  std::vector<Constraint> constraints_;
  bool saw_check_sat_ = false;
};

}  // namespace tiwari
