# fbPDR

Forward / backward PDR/IC3 implementation. From our paper "Combining PDR and Reverse PDR for Hardware Model Checking" (DATE, 2018) and "fbPDR: In-depth combination of forward and backward analysis in Property Directed Reachability" (DATE, 2019).
Based on IC3ref (https://github.com/arbrad/IC3ref).

The tool will output a certifaiger (https://github.com/Froleyks/certifaiger)  certificate or an aigsim witness.

*Limitations*: no preprocessing of the AIGER, only AIGER standard < 1.9

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

