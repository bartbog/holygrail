#!/bin/sh
cat /dev/stdin | sed '/unique solution/d' | sed '/The final result is/,$d' | sed 's/.*assumptions.*/ "assumptions": [/' | jq --slurp "."
