#!/bin/sh
echo "Calling beagle..." 
filepath=$(head -1 filepath.txt) 
timeout 15s \
  java -jar beagle.jar "-genvars" "-proofstatus" "$filepath"
#
