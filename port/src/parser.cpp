#include "parser.h"

#include "smt-switch/cvc5_solver.h"

namespace tiwari {

namespace {

class QfnraCvc5Solver : public smt::Cvc5Solver
{
 public:
  using smt::Cvc5Solver::make_term;

  smt::Term make_term(const std::string val,
                      const smt::Sort & sort,
                      std::uint64_t base = 10) const override
  {
    return smt::Cvc5Solver::make_term(val, realify(sort), base);
  }

  smt::Term make_term(std::int64_t i, const smt::Sort & sort) const override
  {
    return smt::Cvc5Solver::make_term(i, realify(sort));
  }

 private:
  smt::Sort realify(const smt::Sort & sort) const
  {
    return sort->get_sort_kind() == smt::INT ? make_sort(smt::REAL) : sort;
  }
};

smt::TermVec children(const smt::Term & t)
{
  return smt::TermVec(t->begin(), t->end());
}

smt::PrimOp prim_op(const smt::Term & t)
{
  smt::Op op = t->get_op();
  return op.is_null() ? smt::NUM_OPS_AND_NULL : op.prim_op;
}

}  // namespace

smt::SmtSolver make_qfnra_solver()
{
  return std::make_shared<QfnraCvc5Solver>();
}

TiwariReader::TiwariReader(smt::SmtSolver & solver) : smt::SmtLibReader(solver)
{
}

void TiwariReader::new_symbol(const std::string & name, const smt::Sort & sort)
{
  smt::SmtLibReader::new_symbol(name, sort);
  if (sort->get_sort_kind() == smt::REAL)
  {
    vars_.push_back(lookup_symbol(name));
  }
}

smt::Result TiwariReader::check_sat()
{
  saw_check_sat_ = true;
  return smt::Result(smt::UNKNOWN, "tiwari front end only parses");
}

void TiwariReader::assert_formula(const smt::Term & assertion)
{
  // Flatten a top-level conjunction into atoms (collect_atoms in main.py).
  smt::TermVec todo{ assertion };
  while (!todo.empty())
  {
    smt::Term t = todo.back();
    todo.pop_back();
    if (prim_op(t) == smt::And)
    {
      smt::TermVec args = children(t);
      // preserve source order of the atoms
      todo.insert(todo.end(), args.rbegin(), args.rend());
    }
    else
    {
      add_atom(t);
    }
  }
}

smt::Term TiwariReader::diff(const smt::Term & lhs, const smt::Term & rhs)
{
  return solver_->make_term(smt::Minus, lhs, rhs);
}

void TiwariReader::add_atom(const smt::Term & atom)
{
  smt::PrimOp op = prim_op(atom);
  smt::TermVec args = children(atom);

  if (op == smt::Or)
  {
    throw UnsupportedInput("Disjunctions not supported: " + atom->to_string());
  }

  if (op == smt::Not)
  {
    const smt::Term & inner = args.at(0);
    smt::PrimOp inner_op = prim_op(inner);
    if (inner_op == smt::Equal)
    {
      // not (a = b)  <=>  a > b OR a < b  -- needs disjunction.
      throw UnsupportedInput("Disequalities not supported: "
                             + atom->to_string());
    }
    smt::TermVec inner_args = children(inner);
    if (inner_args.size() != 2)
    {
      throw UnsupportedInput("Unsupported negation: " + atom->to_string());
    }
    const smt::Term & lhs = inner_args[0];
    const smt::Term & rhs = inner_args[1];
    switch (inner_op)
    {
      case smt::Lt:  // not (lhs < rhs)  <=>  lhs - rhs >= 0
        constraints_.push_back({ diff(lhs, rhs), Rel::GE });
        return;
      case smt::Le:  // not (lhs <= rhs)  <=>  lhs - rhs > 0
        constraints_.push_back({ diff(lhs, rhs), Rel::GT });
        return;
      case smt::Gt:  // not (lhs > rhs)  <=>  rhs - lhs >= 0
        constraints_.push_back({ diff(rhs, lhs), Rel::GE });
        return;
      case smt::Ge:  // not (lhs >= rhs)  <=>  rhs - lhs > 0
        constraints_.push_back({ diff(rhs, lhs), Rel::GT });
        return;
      default:
        throw UnsupportedInput("Unsupported negation: " + atom->to_string());
    }
  }

  if (args.size() != 2)
  {
    throw UnsupportedInput("Unsupported atom: " + atom->to_string());
  }

  const smt::Term & lhs = args[0];
  const smt::Term & rhs = args[1];

  switch (op)
  {
    case smt::Equal:
      if (lhs->get_sort()->get_sort_kind() == smt::BOOL)
      {
        throw UnsupportedInput("Boolean equality not supported: "
                               + atom->to_string());
      }
      constraints_.push_back({ diff(lhs, rhs), Rel::EQ });
      return;
    case smt::Lt:  // lhs < rhs  <=>  rhs - lhs > 0
      constraints_.push_back({ diff(rhs, lhs), Rel::GT });
      return;
    case smt::Le:  // lhs <= rhs  <=>  rhs - lhs >= 0
      constraints_.push_back({ diff(rhs, lhs), Rel::GE });
      return;
    case smt::Gt:  // lhs > rhs  <=>  lhs - rhs > 0
      constraints_.push_back({ diff(lhs, rhs), Rel::GT });
      return;
    case smt::Ge:  // lhs >= rhs  <=>  lhs - rhs >= 0
      constraints_.push_back({ diff(lhs, rhs), Rel::GE });
      return;
    default:
      throw UnsupportedInput("Unsupported relation: " + atom->to_string());
  }
}

}  // namespace tiwari
