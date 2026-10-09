import CubeG.Lower
import Cube.Phase34
open Std


/-! Lower bounds for Thistlethwaite's phases 1–3: the solving tables are 1-Lipschitz along the phase's moves. -/

def dOf {K : Type} [BEq K] [Hashable K] (t : HashMap K (Option (List Nat))) (k : K) : Nat :=
  match t[k]? with
  | some (some w) => w.length
  | _ => 0

def wit2 : List Nat := parseAlg "F2 U2 R2 D2 R2 B2 L2 F2 R2 D2 D' B2 R2 U F2 U2 R2 U' L2 U R' F2 D F2 U' L2 U L' D' U'"
def wit3 : List Nat := parseAlg "B2 D2 L2 U2 L2 F2 L2 F2 R2 U2 F2 D' B2 R2 U2 L2 U' R2 U2 F2 U' R2"

def p1LowOk : Bool :=
  eoTable.toList.all (fun p => allMoves.all (fun m => decide (dOf eoTable p.1 ≤ dOf eoTable (eoAct p.1 m) + 1))) &&
  dOf eoTable eoZero == 0 && dOf eoTable (eval superflip).eo == 7 && superflip.all (fun m => decide (m < 18))

def p2LowW (t : HashMap K2 (Option (List Nat))) : Bool :=
  t.toList.all (fun p => g1Moves.all (fun m => decide (dOf t p.1 ≤ dOf t (k2Act p.1 m) + 1))) &&
  dOf t k2Start == 0 && dOf t ((eval wit2).co, maskOf (eval wit2).ep) == 10 && wit2.all (fun m => decide (m < 18)) &&
  (eval wit2).eo == eoZero
def p2LowF (_ : Unit) : Bool := p2LowW (k2TableF ())

def p3LowW (t : HashMap K3 (Option (List Nat))) : Bool :=
  cpSet.toList.all (fun p => ms70.all (fun k => g2Moves.all (fun m =>
    decide (dOf t (p.1, k) ≤ dOf t (k3Act (p.1, k) m) + 1)))) &&
  hList.all (fun c => dOf t (c, idMS) == 0) &&
  dOf t ((eval wit3).cp, maskMSof (eval wit3).ep) == 13 && wit3.all (fun m => decide (m < 18)) &&
  (eval wit3).eo == eoZero && (eval wit3).co == St.id.co && maskOf (eval wit3).ep == idE
def p3LowF (_ : Unit) : Bool := p3LowW (k3TableF ())
