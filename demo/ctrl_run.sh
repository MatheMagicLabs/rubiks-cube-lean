#!/bin/bash
export PATH=/root/lean/lean-4.23.0-linux/bin:$PATH
cd /root/cubelean
s=$(date +%s)
echo "=== ScCtrl (bound 20 only) start $(date -u)" >> demo/sc_progress.log
LEAN_PATH=/root/cubelean/.lake/build/lib/lean lean -DmaxRecDepth=100000 CubeS/ScCtrl.lean -o /tmp/claude-0/ScCtrl.olean --setup demo/ScCtrl.setup.json > demo/ScCtrl_out.log 2>&1
echo "ScCtrl rc=$? elapsed $(( $(date +%s)-s )) s $(date -u)" >> demo/sc_chain.log
