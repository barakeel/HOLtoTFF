#!/bin/sh
echo "Calling beagle..." 
timeout 15s \java -jar beagle.jar "-q" "$1" > "$1_status"
#
