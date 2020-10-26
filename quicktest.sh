#!/bin/bash

# rebuild compiler
make clean
make

# empty output folder
cd output
pwd
cd ..

# start test
./main.native llprograms/add.ll

