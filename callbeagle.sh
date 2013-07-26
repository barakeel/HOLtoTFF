#!/bin/sh
echo "Calling beagle..." 
filepath=$(head -1 filepath.txt) 
#assume beagle is located here
BEAGLE=$HOME/Desktop/Scalaproject/beagleproject

exec	timeout --foreground 30s \ 
	$HOME/scala-2.10.1/bin/scala -Dfile.encoding=UTF-8 \
    -J-Xss200m \
    -classpath $BEAGLE/lib/'*':$BEAGLE/bin:$BEAGLE \
    -howtorun:object "calculus.main" "-d" "$filepath"
#
