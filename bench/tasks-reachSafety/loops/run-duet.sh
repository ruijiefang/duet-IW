#!/bin/bash
set -x
DUET=/home/rjf/fast/duet/

srcs=`ls | grep "\.c" | grep -v yml | grep -v "\.i"`

for x in $srcs;do
  echo "=================================================== running file "$x" ============================="
  time ((time (timeout 60 $DUET/duet.exe -mcl-concolic $x || echo "execution timeout")) &> $x".out.log")
  echo "=================================================== done running "$x" ============================="
done
