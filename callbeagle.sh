#!/bin/sh
echo "Calling beagle..." 
timeout 20s \java -jar beagle.jar "-proof" "$1"
#
