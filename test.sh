#!/bin/sh
echo "Calling beagle..." 
filepath=/home/thibault/Desktop/SMLproject/HOLtoTFF/test
#assume beagle is located here
BEAGLE=$HOME/Desktop/Scalaproject/beagleproject

timeout 15s \
  $HOME/scala-2.10.1/bin/scala -Dfile.encoding=UTF-8 \
    -J-Xss200m \
    -classpath $BEAGLE/lib/'*':$BEAGLE/bin:$BEAGLE \
    -howtorun:object "beagle.main" "-proof" "$filepath"
#
