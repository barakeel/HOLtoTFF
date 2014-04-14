#!/bin/sh
echo "Calling beagle..." 
timeout 15s \java -jar beagle.jar "-proof" "$1"
#
