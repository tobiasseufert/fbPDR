# fbPDR

Forward / backward PDR/IC3 implementation. From our paper "fbPDR: In-depth combination of forward and backward analysis in Property Directed Reachability" (DATE, 2019)

# Build instructions

Download z lib.
Download the latest aiger release (e.g., https://github.com/arminbiere/aiger)
into folder aiger (do not make).

    cd minisat
    mkdir build
    cd build
    cmake -DCMAKE_BUILD_TYPE=Release ..  
    make
    cd ../..
    mkdir build
    cd build
    cmake -DCMAKE_BUILD_TYPE=Release ..  
    make

# Configuration

You can configure the tool with different heuristics from the paper.
E.g., uncommenting #define FBPDR_USE_LEMMA_SHARING in Config.h might be interesting.

# Run 

    ./IC3 [-v] [-s] [-r] [-b] [-x] [propertyIndex] < [AIGER file]
      -v: verbose output
      -s: print statistics
      -r: randomize the run
      -b: use basic generalization
      propertyIndex: index of the property to check
      If no propertyIndex is given, the first property is used.
      If no properties are given, the program will exit.

