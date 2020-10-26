#!/bin/bash

# rebuild compiler
make clean
make

# empty output folder
rm -R output
mkdir output

s=${1##*/}
echo "gitter" $1
echo "gatter"

# compile source
./main.native $1

# open compiled program
FILE_PATH="output/"
s=${s##*/}
FILE="${s%.ll}"
EXTENSION=".s"
code $FILE_PATH$FILE$EXTENSION

