#include <iostream>
#include <string>

#include "CoCoA/GlobalManager.H"
#include "CoCoA/PolyRing.H"
#include "CoCoA/error.H"

#include "parser.h"
#include "poly.h"
#include "solver.h"

namespace {

const char * rel_str(tiwari::Rel rel)
{
  switch (rel)
  {
    case tiwari::Rel::EQ: return "= 0";
    case tiwari::Rel::GE: return ">= 0";
    case tiwari::Rel::GT: return "> 0";
  }
  return "?";
}

}  // namespace

int main(int argc, char ** argv)
{
  bool verbose = false;
  std::string path;
  for (int i = 1; i < argc; ++i)
  {
    std::string arg = argv[i];
    if (arg == "-v" || arg == "--verbose")
    {
      verbose = true;
    }
    else
    {
      path = arg;
    }
  }
  if (path.empty())
  {
    std::cerr << "usage: " << argv[0] << " [-v] <file.smt2>" << std::endl;
    return 2;
  }

  smt::SmtSolver solver = tiwari::make_qfnra_solver();
  tiwari::TiwariReader reader(solver);

  try
  {
    reader.parse(path);
  }
  catch (tiwari::UnsupportedInput & e)
  {
    std::cerr << "unsupported: " << e.what() << std::endl;
    return 1;
  }
  catch (SmtException & e)
  {
    std::cerr << "parse error: " << e.what() << std::endl;
    return 1;
  }

  CoCoA::GlobalManager cocoa_foundations;

  try
  {
    tiwari::SolverInput in =
        tiwari::build_solver_input(reader.vars(), reader.constraints());

    if (verbose)
    {
      std::cerr << "vars: ";
      for (long i = 0; i < CoCoA::NumIndets(in.ring); ++i)
      {
        std::cerr << CoCoA::indet(in.ring, i)
                  << (in.v_pos.count(i)      ? " (>0)"
                      : in.v_nonneg.count(i) ? " (>=0)"
                                             : "")
                  << " ";
      }
      std::cerr << std::endl << "constraints:" << std::endl;
      for (size_t i = 0; i < in.polys.size(); ++i)
      {
        std::cerr << "  " << in.polys[i] << " = 0   [from "
                  << rel_str(reader.constraints()[i].rel) << "]" << std::endl;
      }
    }

    tiwari::TiwariSolver tiwari_solver(in.ring,
                                       std::move(in.polys),
                                       std::move(in.v_pos),
                                       std::move(in.v_nonneg),
                                       verbose);
    tiwari::SolveResult result = tiwari_solver.solve();
    std::cout << "  => "
              << (result == tiwari::SolveResult::UNSAT ? "UNSAT" : "UNKNOWN")
              << std::endl;
  }
  catch (tiwari::UnsupportedInput & e)
  {
    std::cerr << "unsupported: " << e.what() << std::endl;
    return 1;
  }
  catch (CoCoA::ErrorInfo & e)
  {
    std::cerr << "cocoa error: " << e << std::endl;
    return 1;
  }

  return 0;
}
