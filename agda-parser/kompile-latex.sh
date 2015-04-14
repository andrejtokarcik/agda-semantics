#!/bin/sh
set -e

LATEX_DIR=~/ltx/k/

kompile --backend latex -d $LATEX_DIR agda.k -v
cp $LATEX_DIR/agda.tex $LATEX_DIR/agda.tex.orig
echo Postprocessing...
$LATEX_DIR/postprocess.py $LATEX_DIR/agda.tex.orig >$LATEX_DIR/agda.tex
