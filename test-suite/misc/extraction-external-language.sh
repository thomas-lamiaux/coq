#!/usr/bin/env bash

set -ex

export COQBIN=$BIN
export PATH=$COQBIN:$PATH

cd misc/extraction-external-language/

rocq makefile -f _CoqProject -o Makefile

make clean

make src/toy_extraction_plugin.cmxs

# -test-mode prints the messages of Fail
rocq c -q -test-mode -I src -Q theories ToyExtraction theories/test.v > log 2>&1
cat log
grep -q 'Unknown extraction language Toy' log
# the quote in red' is turned into an underscore, type names are capitalized
grep -q 'red_' log
grep -q 'Color' log
grep -q 'Modular extraction is not supported for Toy' log
