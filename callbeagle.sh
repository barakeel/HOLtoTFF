#!/bin/sh
echo "Hello, World!" 
filepath=$(head -1 $HOME/Desktop/SMLproject/HOLtoTFF/filepath.txt) 
BEAGLE=$HOME/Desktop/Scalaproject/beagleproject
# Assume scala 2.10.1 is in the search path
exec $HOME/scala-2.10.1/bin/scala -Dfile.encoding=UTF-8 \
    -J-Xss200m \
    -classpath $BEAGLE/lib/'*':$BEAGLE/bin:$BEAGLE \
    -howtorun:object "calculus.main" "$filepath"
#
