#!/bin/bash

for x in `ls | grep "\.c\.out\.log"`; do
    echo "================================== result for "$x
    tail $x
    echo "=================================================="
  done
