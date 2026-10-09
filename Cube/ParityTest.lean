import Cube.Parity
-- find adjacent-swap sequences realising each basic move's position map (bubble sort of the index map)
def bubble (target : List Nat) : List Nat := Id.run do
  -- produce ks with swaps ks (List.range n) = target
  let mut cur := (List.range target.length)
  let mut ks : Array Nat := #[]
  for i in [0:target.length] do
    -- bring target[i] to position i
    let v := target[i]!
    let mut j := cur.idxOf v
    while j > i do
      cur := swapAt (j-1) cur
      ks := ks.push (j-1)
      j := j - 1
  return ks.toList
#eval (List.range 6).map (fun f => bubble (basic[f]!).cp.toList)
#eval (List.range 6).map (fun f => bubble (basic[f]!).ep.toList)
#eval (List.range 6).map (fun f => (swaps (bubble (basic[f]!).ep.toList) (List.range 12)) == (basic[f]!).ep.toList)
