#!/bin/bash
set -x
DUET=/home/rjf/fast/duet-private/

srcs=`ls | grep "\.c" | grep -v yml | grep -v "\.i"`

for x in $srcs;do
  echo "=================================================== running file "$x" ============================="
  time ((time timeout 60 $DUET/duet.exe -mcl-plain $x) &> $x".out.log")
  echo "=================================================== done running "$x" ============================="
done
