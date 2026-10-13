#!/bin/bash
cd ~/sf
for args in "18 2 1" "19 2 1" "20 2 1" "19 2 0"; do
  s=$(date +%s); ./proto2 $args; e=$(date +%s); echo "args=$args elapsed $((e-s)) s"
done
