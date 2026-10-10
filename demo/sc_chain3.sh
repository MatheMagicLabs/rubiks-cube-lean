#!/bin/bash
# Chain v3: freeze the bound-22 C jobs (tables are file-backed mmaps, anon ~80 MB), run the Lean supercube certificate
# (~6 GB), recheck ScProof, positive control, then resume the C jobs and analyze bound 22 when they finish.
export PATH=/root/lean/lean-4.23.0-linux/bin:$PATH
cd /root/cubelean
L=demo/sc_chain.log
ts() { while IFS= read -r l; do echo "$(date -u +%H:%M:%S) $l"; done; }
echo "v3 start $(date -u)" >> $L
kill -STOP 3732 3734; echo "C jobs stopped $(date -u)" >> $L
run() {  # name
  local n=$1 s=$(date +%s)
  LEAN_PATH=/root/cubelean/.lake/build/lib/lean lean -DmaxRecDepth=100000 CubeS/$n.lean \
    -o /tmp/claude-0/$n.olean --setup demo/$n.setup.json > demo/${n}_out.log 2> >(ts > demo/${n}_progress.log) &
  local pid=$!
  while kill -0 $pid 2>/dev/null; do echo "$(date -u +%H:%M:%S) rss_kb $(ps -o rss= -p $pid)" >> demo/${n}_mem.log; sleep 300; done
  wait $pid; local rc=$?
  echo "$n rc=$rc elapsed $(( $(date +%s)-s )) s $(date -u)" >> $L
  return $rc
}
if run ScThm; then
  rm -f /tmp/claude-0/olean/CubeS/ScThm.olean
  cp /tmp/claude-0/ScThm.olean /tmp/claude-0/olean/CubeS/ScThm.olean
  LEAN_PATH=/tmp/claude-0/olean:/root/cubelean/.lake/build/lib/lean lean -DmaxRecDepth=100000 \
    -o /tmp/claude-0/olean/CubeP/ScProof.olean CubeP/ScProof.lean > demo/supercube_axioms.log 2>&1
  echo "ScProof rc=$? $(date -u)" >> $L
fi
run ScCtrl
kill -CONT 3732 3734; echo "C jobs resumed $(date -u)" >> $L
while kill -0 3727 2>/dev/null; do sleep 60; done
echo "bound 22 finished $(date -u)" >> $L
(cd /home/claude/clump && python3 sc_analyze.py sc/sc22_s1_t63.txt sc/sc22_s4_t63.txt sc/sc22_s16_t1.txt sc/sc22_s16_t4.txt sc/sc20_f3.txt sc/sc20_f5.txt > sc/analysis22.txt 2>&1)
echo "analysis22 done $(date -u)" >> $L
