#!/bin/bash
# Clean lake rebuild after the reboot, one heavy certificate at a time (memory limit 6.27 GB).
export PATH=/root/lean/lean-4.23.0-linux/bin:$PATH
cd /root/cubelean
L=demo/rebuild.log
for t in CubeP.Low2ThmB CubeS.ScThm CubeS.ScCtrl CubeP.ScFinal CubeP.Final; do
  s=$(date +%s); echo "start $t $(date -u)" >> $L
  lake build $t > demo/rebuild_$t.log 2>&1; rc=$?
  echo "done $t rc=$rc $(( $(date +%s)-s )) s $(date -u)" >> $L
  [ $rc -ne 0 ] && break
done
grep -h "depends on axioms" -A6 demo/rebuild_CubeP.ScFinal.log >> $L 2>/dev/null
