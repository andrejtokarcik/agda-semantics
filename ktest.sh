#!/bin/sh

# run with --update-out from CLI if desired
ktest tests/config.xml -v --skip=pdf $1
