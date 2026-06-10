cmake_minimum_required(VERSION 3.16)
project(tiwari-port CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

# smt-switch (built from deps/smt-switch, installed system-wide)
find_path(SMT_SWITCH_INCLUDE_DIR smt-switch/smt.h REQUIRED)
find_library(SMT_SWITCH_LIB smt-switch REQUIRED)
find_library(SMT_SWITCH_CVC5_LIB smt-switch-cvc5 REQUIRED)

# CoCoALib (built in-tree: cd deps/CoCoALib && ./configure --only-cocoalib && make library)
set(COCOALIB_DIR ${CMAKE_CURRENT_SOURCE_DIR}/deps/CoCoALib)
find_library(GMP_LIB gmp REQUIRED)

add_executable(tiwari
  src/main.cpp
  src/parser.cpp
  src/poly.cpp
  src/solver.cpp
)
target_include_directories(tiwari PRIVATE
  ${SMT_SWITCH_INCLUDE_DIR}
  ${COCOALIB_DIR}/include
)
target_link_libraries(tiwari PRIVATE
  ${SMT_SWITCH_CVC5_LIB}
  ${SMT_SWITCH_LIB}
  ${COCOALIB_DIR}/lib/libcocoa.a
  ${GMP_LIB}
)
