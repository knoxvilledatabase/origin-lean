/-
Extracted from Tactic/Linarith/Oracle/FourierMotzkin.lean
Genuine: 25 of 28 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core
import Mathlib.Std.Data.HashMap
import Batteries.Lean.HashMap
import Mathlib.Tactic.Linarith.Datatypes

/-!
# The Fourier-Motzkin elimination procedure

The Fourier-Motzkin procedure is a variable elimination method for linear inequalities.
<https://en.wikipedia.org/wiki/Fourier%E2%80%93Motzkin_elimination>

Given a set of linear inequalities `comps = {tᵢ Rᵢ 0}`,
we aim to eliminate a single variable `a` from the set.
We partition `comps` into `comps_pos`, `comps_neg`, and `comps_zero`,
where `comps_pos` contains the comparisons `tᵢ Rᵢ 0` in which
the coefficient of `a` in `tᵢ` is positive, and similar.

For each pair of comparisons `tᵢ Rᵢ 0 ∈ comps_pos`, `tⱼ Rⱼ 0 ∈ comps_neg`,
we compute coefficients `vᵢ, vⱼ ∈ ℕ` such that `vᵢ*tᵢ + vⱼ*tⱼ` cancels out `a`.
We collect these sums `vᵢ*tᵢ + vⱼ*tⱼ R' 0` in a set `S` and set `comps' = S ∪ comps_zero`,
a new set of comparisons in which `a` has been eliminated.

Theorem: `comps` and `comps'` are equisatisfiable.

We recursively eliminate all variables from the system. If we derive an empty clause `0 < 0`,
we conclude that the original system was unsatisfiable.
-/

open Batteries

open Std (format ToFormat)

namespace Linarith

/-!
### Datatypes

The `CompSource` and `PComp` datatypes are specific to the FM elimination routine;
they are not shared with other components of `linarith`.
-/

inductive CompSource : Type
  | assump : Nat → CompSource
  | add : CompSource → CompSource → CompSource
  | scale : Nat → CompSource → CompSource

deriving Inhabited

def CompSource.flatten : CompSource → Std.HashMap Nat Nat
  | (CompSource.assump n) => Std.HashMap.empty.insert n 1
  | (CompSource.add c1 c2) =>
      (CompSource.flatten c1).mergeWith (fun _ b b' => b + b') (CompSource.flatten c2)
  | (CompSource.scale n c) => (CompSource.flatten c).mapVal (fun _ v => v * n)

def CompSource.toString : CompSource → String
  | (CompSource.assump e) => ToString.toString e
  | (CompSource.add c1 c2) => CompSource.toString c1 ++ " + " ++ CompSource.toString c2
  | (CompSource.scale n c) => ToString.toString n ++ " * " ++ CompSource.toString c

instance : ToFormat CompSource :=
  ⟨fun a => CompSource.toString a⟩

structure PComp : Type where
  /-- The comparison `Σ cᵢ*xᵢ R 0`. -/
  c : Comp
  /-- We track how the comparison was constructed by adding and scaling previous comparisons,
  back to the original assumptions. -/
  src : CompSource
  /-- The set of original assumptions which have been used in constructing this comparison. -/
  history : RBSet ℕ Ord.compare
  /-- The variables which have been *effectively eliminated*,
  i.e. by running the elimination algorithm on that variable. -/
  effective : RBSet ℕ Ord.compare
  /-- The variables which have been *implicitly eliminated*.
  These are variables that appear in the historical set,
  do not appear in `c` itself, and are not in `effective. -/
  implicit : RBSet ℕ Ord.compare
  /-- The union of all variables appearing in those original assumptions
  which appear in the `history` set. -/
  vars : RBSet ℕ Ord.compare

def PComp.maybeMinimal (c : PComp) (elimedGE : ℕ) : Bool :=
  c.history.size ≤ 1 + ((c.implicit.filter (· ≥ elimedGE)).union c.effective).size

def PComp.cmp (p1 p2 : PComp) : Ordering := p1.c.cmp p2.c

def PComp.scale (c : PComp) (n : ℕ) : PComp :=
  { c with c := c.c.scale n, src := c.src.scale n }

def PComp.add (c1 c2 : PComp) (elimVar : ℕ) : PComp :=
  let c := c1.c.add c2.c
  let src := c1.src.add c2.src
  let history := c1.history.union c2.history
  let vars := c1.vars.union c2.vars
  let effective := (c1.effective.union c2.effective).insert elimVar
  let implicit := (vars.sdiff (.ofList c.vars _)).sdiff effective
  ⟨c, src, history, effective, implicit, vars⟩

def PComp.assump (c : Comp) (n : ℕ) : PComp where
  c := c
  src := CompSource.assump n
  history := RBSet.empty.insert n
  effective := .empty
  implicit := .empty
  vars := .ofList c.vars _

instance : ToFormat PComp :=
  ⟨fun p => format p.c.coeffs ++ toString p.c.str ++ "0"⟩

instance : ToString PComp :=
  ⟨fun p => toString p.c.coeffs ++ toString p.c.str ++ "0"⟩

abbrev PCompSet := RBSet PComp PComp.cmp

/-! ### Elimination procedure -/

def elimVar (c1 c2 : Comp) (a : ℕ) : Option (ℕ × ℕ) :=
  let v1 := c1.coeffOf a
  let v2 := c2.coeffOf a
  if v1 * v2 < 0 then
    let vlcm := Nat.lcm v1.natAbs v2.natAbs
    some ⟨vlcm / v1.natAbs, vlcm / v2.natAbs⟩
  else none

def pelimVar (p1 p2 : PComp) (a : ℕ) : Option PComp := do
  let (n1, n2) ← elimVar p1.c p2.c a
  return (p1.scale n1).add (p2.scale n2) a

def PComp.isContr (p : PComp) : Bool := p.c.isContr

def elimWithSet (a : ℕ) (p : PComp) (comps : PCompSet) : PCompSet :=
  comps.foldl (fun s pc =>
  match pelimVar p pc a with
  | some pc => if pc.maybeMinimal a then s.insert pc else s
  | none => s) RBSet.empty

structure LinarithData : Type where
  /-- The largest variable index that has not been (officially) eliminated. -/
  maxVar : ℕ
  /-- The set of comparisons. -/
  comps : PCompSet

abbrev LinarithM : Type → Type :=
  StateT LinarithData (ExceptT PComp Lean.Core.CoreM)

def getMaxVar : LinarithM ℕ :=
  LinarithData.maxVar <$> get

def getPCompSet : LinarithM PCompSet :=
  LinarithData.comps <$> get

def validate : LinarithM Unit := do
  match (← getPCompSet).toList.find? (fun p : PComp => p.isContr) with
  | none => return ()
  | some c => throwThe _ c

def update (maxVar : ℕ) (comps : PCompSet) : LinarithM Unit := do
  StateT.set ⟨maxVar, comps⟩
  validate

def splitSetByVarSign (a : ℕ) (comps : PCompSet) : PCompSet × PCompSet × PCompSet :=
  comps.foldl (fun ⟨pos, neg, notPresent⟩ pc =>
    let n := pc.c.coeffOf a
    if n > 0 then ⟨pos.insert pc, neg, notPresent⟩
    else if n < 0 then ⟨pos, neg.insert pc, notPresent⟩
    else ⟨pos, neg, notPresent.insert pc⟩)
    ⟨RBSet.empty, RBSet.empty, RBSet.empty⟩

def elimVarM (a : ℕ) : LinarithM Unit := do
  let vs ← getMaxVar
  if (a ≤ vs) then
    Lean.Core.checkSystem decl_name%.toString
    let ⟨pos, neg, notPresent⟩ := splitSetByVarSign a (← getPCompSet)
    update (vs - 1) (← pos.foldlM (fun s p => do
      Lean.Core.checkSystem decl_name%.toString
      pure (s.union (elimWithSet a p neg))) notPresent)
  else
    pure ()

def elimAllVarsM : LinarithM Unit := do
  for i in (List.range ((← getMaxVar) + 1)).reverse do
    elimVarM i

def mkLinarithData (hyps : List Comp) (maxVar : ℕ) : LinarithData :=
  ⟨maxVar, .ofList (hyps.enum.map fun ⟨n, cmp⟩ => PComp.assump cmp n) _⟩

def CertificateOracle.fourierMotzkin : CertificateOracle where
  produceCertificate hyps maxVar :=  do
    let linarithData := mkLinarithData hyps maxVar
    let result ←
      (ExceptT.run (StateT.run (do validate; elimAllVarsM : LinarithM Unit) linarithData) : _)
    match result with
    | (Except.ok _) => failure
    | (Except.error contr) => return contr.src.flatten

end Linarith
