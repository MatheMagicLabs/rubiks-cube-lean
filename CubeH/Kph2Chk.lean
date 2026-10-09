import CubeH.Kph2
open Std
set_option compiler.extract_closed false

/-! Finite certificate facts for the phase-2 proof (all checked by `native_decide`). -/

def idxOkC (_ : Unit) : Bool := cpG.toList.all (fun p => match cpGI[p.1]? with
  | some r => decide (r < NCP) && cpGL[r]! == p.1
  | none => false)
def idxOkE (_ : Unit) : Bool := epG.toList.all (fun p => match epGI[p.1]? with
  | some r => decide (r < NE) && epGL[r]! == p.1
  | none => false)
def listInC (_ : Unit) : Bool := (List.range NCP).all (fun r => cpG.contains cpGL[r]!)
def listInE (_ : Unit) : Bool := (List.range NE).all (fun e => epG.contains epGL[e]!)
def closedC (_ : Unit) : Bool := cpG.toList.all (fun p => g2Moves.all (fun m => cpG.contains (cpAct p.1 m)) &&
  (List.range 16).all (fun s => cpG.contains (conjC s p.1)))
def closedE (_ : Unit) : Bool := epG.toList.all (fun p => g2Moves.all (fun m => epG.contains (epAct p.1 m)) &&
  (List.range 16).all (fun s => epG.contains (conjE s p.1)))
def symOk (_ : Unit) : Bool := (List.range NCP).all (fun r => decide (clsT[r]! < NC) && decide (syT[r]! < 16) &&
  conjC syT[r]! cpGL[r]! == cpGL[repsT[clsT[r]!]!]!) && (List.range NC).all (fun c => decide (repsT[c]! < NCP))
def mvOkC (_ : Unit) : Bool := (List.range NCP).all (fun r => (List.range 10).all (fun j =>
  cpMv[r * 10 + j]! == cpGI[cpAct cpGL[r]! g2A[j]!]!))
def mvOkE (_ : Unit) : Bool := (List.range NE).all (fun e => (List.range 10).all (fun j =>
  epMv[e * 10 + j]! == epGI[epAct epGL[e]! g2A[j]!]!) &&
  (List.range 16).all (fun s => epCj[e * 16 + s]! == epGI[conjE s epGL[e]!]!))
def compatC (_ : Unit) : Bool := cpG.toList.all (fun p => (List.range 16).all (fun s => g2Moves.all (fun m =>
  conjC s (cpAct p.1 m) == cpAct (conjC s p.1) (mu s m) && g2Moves.contains (mu s m))))
def compatE (_ : Unit) : Bool := epG.toList.all (fun p => (List.range 16).all (fun s => g2Moves.all (fun m =>
  conjE s (epAct p.1 m) == epAct (conjE s p.1) (mu s m))))
def invOk (_ : Unit) : Bool := (List.range 16).all (fun s => decide (invS[s]! < 16)) &&
  cpG.toList.all (fun p => (List.range 16).all (fun s => conjC invS[s]! (conjC s p.1) == p.1)) &&
  epG.toList.all (fun p => (List.range 16).all (fun s => conjE invS[s]! (conjE s p.1) == p.1))
def idOk (_ : Unit) : Bool := (List.range 16).all (fun s => conjC s St.id.cp == St.id.cp && conjE s St.id.ep == St.id.ep) &&
  stateOf idCell == idP
def parOk (_ : Unit) : Bool :=
  cpG.toList.all (fun p => (List.range 16).all (fun s => inv (conjC s p.1).toList % 2 == inv p.1.toList % 2)) &&
  epG.toList.all (fun p => (List.range 16).all (fun s => inv (conjE s p.1).toList % 2 == inv p.1.toList % 2)) &&
  (List.range NC).all (fun c => pcT[c]! == inv cpGL[repsT[c]!]!.toList % 2) &&
  (List.range NE).all (fun e => peT[e]! == inv epGL[e]!.toList % 2)
def sliceSets2 : List (List Nat) :=
  [[0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7],
   [0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7],
   [8,9,10,11],[8,9,10,11],[8,9,10,11],[8,9,10,11]]
def startOk (_ : Unit) : Bool := cpSet.toList.all (fun p => cpG.contains p.1) &&
  allSel sliceSets2 [] (fun l => epG.contains l.toArray) &&
  (List.range 12).all (fun i => (List.range 12).all (fun e => !(cls e == idE[i]!) || (sliceSets2[i]!).contains e))

def stabOk (_ : Unit) : Bool := (List.range NC).all (fun c => (stabT[c]!).all (fun t =>
  decide (t < 16) && conjC t cpGL[repsT[c]!]! == cpGL[repsT[c]!]!))
def canonOk (_ : Unit) : Bool := (List.range NC).all (fun c => (stabT[c]!).isEmpty ||
  (List.range NE).all (fun e => canon c (canon c e) == canon c e))
def idSymOk (_ : Unit) : Bool := cpG.toList.all (fun p => conjC 0 p.1 == p.1) && epG.toList.all (fun p => conjE 0 p.1 == p.1)

def factsOk (_ : Unit) : Bool := idxOkC () && idxOkE () && listInC () && listInE () && closedC () && closedE () && symOk () && mvOkC () && mvOkE () &&
  compatC () && compatE () && invOk () && idOk () && parOk () && startOk () && stabOk () && canonOk () && idSymOk ()
