#!/bin/bash

# rebuild compiler
make clean
make

# empty output folder
rm -R output
mkdir output

# start test
./main.native llprograms/add.ll

code output/add.s

