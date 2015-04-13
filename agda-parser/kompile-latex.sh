#!/bin/sh
set -e

kompile --backend latex -d latex agda.k -v
cp latex/agda.tex latex/agda.tex.orig
./latex/postprocess.py latex/agda.tex
