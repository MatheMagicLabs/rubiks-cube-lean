import CubeG.Solver
#eval show IO Unit from do
  let s ← IO.FS.readFile "demo/scr50.txt"
  let ls := (s.splitOn "\n").filter (· ≠ "")
  let out := solveAllF ls
  IO.FS.writeFile "demo/sol50.tsv" ("\n".intercalate out ++ "\n")
  IO.println s!"{out.length} solved"
