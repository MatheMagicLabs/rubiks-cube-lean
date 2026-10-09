import Cube.Parity

def bubble (target : List Nat) : List Nat := Id.run do
  let mut cur := (List.range target.length)
  let mut ks : Array Nat := #[]
  for i in [0:target.length] do
    let v := target[i]!
    let mut j := cur.idxOf v
    while j > i do
      cur := swapAt (j-1) cur
      ks := ks.push (j-1)
      j := j - 1
  return ks.toList

#eval (List.range 18).map (fun m => bubble (moves[m]!).cp.toList)
#eval (List.range 18).map (fun m => bubble (moves[m]!).ep.toList)
