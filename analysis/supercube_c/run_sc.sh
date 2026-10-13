#!/bin/bash
# usage: run_sc.sh BOUND  -> two halves (first move R / R') in parallel
B=$1
cd /home/claude/clump/sc
for F in 3 5; do
  ( s=$(date +%s); ./proto_sc $B $F /home/claude/clump/sc/sc${B}_f${F}.txt > sc${B}_f${F}.log 2>&1; e=$(date +%s); echo "bound $B first $F elapsed $((e-s)) s" >> sc${B}_f${F}.log ) &
done
wait
echo "=== bound $B done $(date -u +%H:%M:%S)" >> runs.log
