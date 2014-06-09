#!/bin/sh
echo "Calling beagle..." 
beagle "-t" "15" "-q" "$1" > "$1_status"
#
