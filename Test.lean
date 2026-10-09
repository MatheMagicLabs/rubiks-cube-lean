import Cube.Model
def order (w : List Nat) : Nat := Id.run do
  let mut s := eval w; let mut k := 1
  while s != St.id && k < 2000 do
    s := applyList s w; k := k + 1
  return k
#eval order (parseAlg "R")
#eval order (parseAlg "R U R' U'")
#eval order (parseAlg "R U")
#eval order (parseAlg "R2 U2")
#eval order (parseAlg "F")
-- superflip: known 20-move solution
#eval (eval (parseAlg "U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2"))
#eval (eval (parseAlg "R U R' U'")) == (eval (parseAlg "R U R' U' R U R' U' R U R' U' R U R' U' R U R' U' R U R' U' R U R' U'"))
