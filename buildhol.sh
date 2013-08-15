#!/bin/sh
outdir=$HOME/Desktop/SMLproject/HOLtoTFF/beagletacresult
testsrcdir=$HOME/Desktop/HOLtest/HOL/src/HOLtoTFF/src
srcdir=$HOME/Desktop/SMLproject/HOLtoTFF/src
#erasing files
find $outdir -mindepth 1 -maxdepth 1 -delete
find $testsrcdir -mindepth 1 -maxdepth 1 -delete
#copying files
smlfile=$(find $srcdir -iname "*.sml")
cp -f $smlfile $testsrcdir 
sigfile=$(find $srcdir -iname "*.sig")
cp -f $sigfile $testsrcdir 
#calling buildhol
$HOME/Desktop/HOLtest/HOL/bin/build
#
