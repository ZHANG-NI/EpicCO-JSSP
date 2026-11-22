#!/bin/bash
# Build recipe of this solver, as used for every build of the paper's runs.
# Run it from this directory:  bash build.sh <output directory>   ->  <output directory>/solver
set -e
g++ -O3 -DNDEBUG -std=gnu++17 -w *.cpp -o "$1/solver"
