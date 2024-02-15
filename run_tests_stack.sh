#!/bin/bash
export RUNHASKELL="stack exec runhaskell --"
export EXECUTABLE="stack exec tyinf --"
./run_tests_cabal.sh $1 $2 $3 $4 $5
