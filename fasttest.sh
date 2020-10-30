#!/bin/bash

rm a.out

clang  $1
echo "It should be: "
./a.out
echo $?

rm a.out

echo "It is: "
./main.native $1
./a.out
echo $?