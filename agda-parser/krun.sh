#!/bin/sh

dir=$(dirname $1)
#K_OPTS="-Xms100m -Xmx10000m -Xss50m"
krun -v --parser="agda -i$dir" $1 | tee out
