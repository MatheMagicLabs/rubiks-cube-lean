#!/bin/bash
# bound B, first move R only (mirror symmetry), second face in {U, F, L} (x2 symmetry)
B=$1
cd /home/claude/clump/sc
for S in 1 4 16; do
  ( s=$(date +%s); SECOND=$S ./proto_sc3 $B 3 /home/claude/clump/sc/sc${B}_R_s${S}.txt > sc${B}_R_s${S}.log 2>&1; e=$(date +%s); echo "bound $B second $S elapsed $((e-s)) s" >> sc${B}_R_s${S}.log ) &
done
wait
echo "=== bound $B (R; U,F,L) done $(date -u +%H:%M:%S)" >> runs.log
