#!/bin/sh

krun -v --parser='agda -itests' $1 | tee out
