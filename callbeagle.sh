#!/bin/sh
echo "Calling beagle..." 
timeout 5s \java -jar beagle.jar "-proof" "$1"
#
