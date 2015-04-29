#!/bin/sh

dir=$(dirname $1)
krun -v --parser="agda -i$dir" $1 | tee out
