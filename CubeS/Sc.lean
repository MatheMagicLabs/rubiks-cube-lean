import CubeO.Sf
open Std
set_option compiler.extract_closed false

/-! Supercube certificate. A word solves the superflip on the supercube with centre pattern `tgt` iff it solves the
superflip on the cube and turns face `f` by `tgt_f` quarter turns modulo 4. The search is the superflip search of
`CubeO.Sf` with bound `B`, commuting moves on opposite faces in increasing face order inside `s1` and inside `s2`,
the centre signature carried along, and the leaves enumerating `s2` exactly (phase-2 distances as pruning). -/

/-- quarter turns per face, modulo 4 -/
structure Sig where
  s0 : Nat
  s1 : Nat
  s2 : Nat
  s3 : Nat
  s4 : Nat
  s5 : Nat
deriving Inhabited, BEq, DecidableEq, Repr

def sig0 : Sig := ⟨0, 0, 0, 0, 0, 0⟩

def sigStep (s : Sig) (m : Nat) : Sig :=
  let a := m % 3 + 1
  match m / 3 with
  | 0 => { s with s0 := (s.s0 + a) % 4 }
  | 1 => { s with s1 := (s.s1 + a) % 4 }
  | 2 => { s with s2 := (s.s2 + a) % 4 }
  | 3 => { s with s3 := (s.s3 + a) % 4 }
  | 4 => { s with s4 := (s.s4 + a) % 4 }
  | _ => { s with s5 := (s.s5 + a) % 4 }

def sigOf (w : List Nat) : Sig := w.foldl sigStep sig0

/-- may a move `m` follow a move on face `lf`? Not the same face, and opposite faces only in increasing order. -/
def okNext (lf m : Nat) : Bool := m / 3 != lf && !(lf < 6 && (m / 3) % 3 == lf % 3 && m / 3 < lf)

/-- leaf: every word of ⟨U,D,R2,L2,F2,B2⟩ with length in [need, need + rem] ... precisely: every such word `s2` with
`need ≤ |s2| ≤ rem` from `p` that reaches the identity ends with a signature different from `tgt`. Inside `s2` the
order rule applies; the first move only avoids the face `lf`. -/
def leafS (d2 : ByteArray) (tgt : Sig) : Nat → Nat → P → Nat → Bool → Sig → Bool
  | rem, need, p, lf, first, s =>
    (!(need == 0 && p == idP && decide (s = tgt))) &&
    (match rem with
     | 0 => true
     | r + 1 => allLt (fun t =>
         let m := g2A[t]!
         (m / 3 == lf) || (!first && (m / 3) % 3 == lf % 3 && m / 3 < lf) || decide (r + 1 < need) ||
         (let q := pAct p m
          decide (r < (d2.get! (cellOf q)).toNat) || leafS d2 tgt r (need - 1) q (m / 3) false (sigStep s m))) 10)

/-- progress output on stderr for long certificate runs; logically just `x ()` -/
def traceIf (b : Bool) (msg : Unit → String) (x : Unit → Bool) : Bool :=
  if b then dbgTrace (msg ()) x else x ()

theorem traceIf_eq (b : Bool) (msg : Unit → String) (x : Unit → Bool) : traceIf b msg x = x () := by
  unfold traceIf dbgTrace; split <;> rfl

def scSearch (d1 d2 : ByteArray) (B : Nat) (tgt : Sig) :
    Nat → Nat → Nat → Nat → P → Nat → Nat → RunSt → Bool → Sig → Bool
  | fuel, r0, r1, r2, p, g, lastf, rs, lnh, s =>
    (!(lnh && (d1.get! r0).toNat == 0) || leafS d2 tgt (B - g) rs.mx p lastf true s) &&
    (match fuel with
     | 0 => true
     | f + 1 => allLt (fun m =>
         !(okNext lastf m) || (g == 0 && !(m == 3 || m == 5)) ||
         (let s0 := next r0 m
          let s1 := next r1 (muS m)
          let s2 := next r2 (muS (muS m))
          let rs' := runStep rs m
          decide (B < g + 1 + (d1.get! s0).toNat + rs'.mx) || decide (B < g + 1 + (d1.get! s1).toNat) ||
            decide (B < g + 1 + (d1.get! s2).toNat) ||
            traceIf (g < 3) (fun _ => s!"sc g={g} m={m}")
              (fun _ => scSearch d1 d2 B tgt f s0 s1 s2 (pAct p m) (g + 1) (m / 3) rs' (!isHUD m) (sigStep s m)))) 18)

/-- the certificate: true iff no normal-form word of length ≤ B solves the superflip with centre signature `tgt` -/
def scF (B : Nat) (tgt : Sig) (_ : Unit) : Bool :=
  let d1 := distF ()
  let d2 := dist2F ()
  let r := rank sfSt
  scSearch d1 d2 B tgt B r r r idP 0 6 run0 false sig0
