/-
Extracted from Tactic/Linarith/Parsing.lean
Genuine: 21 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Tactic.Linarith.Datatypes

noncomputable section

/-!
# Parsing input expressions into linear form

`linarith` computes the linear form of its input expressions,
assuming (without justification) that the type of these expressions
is a commutative semiring.
It identifies atoms up to ring-equivalence: that is, `(y*3)*x` will be identified `3*(x*y)`,
where the monomial `x*y` is the linear atom.

* Variables are represented by natural numbers.
* Monomials are represented by `Monom := RBMap ℕ ℕ`.
  The monomial `1` is represented by the empty map.
* Linear combinations of monomials are represented by `Sum := RBMap Monom ℤ`.

All input expressions are converted to `Sum`s, preserving the map from expressions to variables.
We then discard the monomial information, mapping each distinct monomial to a natural number.
The resulting `RBMap ℕ ℤ` represents the ring-normalized linear form of the expression.
This is ultimately converted into a `Linexp` in the obvious way.

`linearFormsAndMaxVar` is the main entry point into this file. Everything else is contained.
-/

open Mathlib.Ineq Batteries

section

open Lean Elab Tactic Meta

def List.findDefeq {v : Type} (red : TransparencyMode) (m : List (Expr × v)) (e : Expr) :
    MetaM v := do
  if let some (_, n) ← m.findM? fun ⟨e', _⟩ => withTransparency red (isDefEq e e') then
    return n
  else
    failure

end

local instance {α β : Type*} {c : α → α → Ordering} [Add β] [Zero β] [DecidableEq β] :
    Add (RBMap α β c) where
  add := fun f g => (f.mergeWith (fun _ b b' => b + b') g).filter (fun _ b => b ≠ 0)

namespace Linarith

abbrev Map (α β) [Ord α] := RBMap α β Ord.compare

/-! ### Parsing datatypes -/

abbrev Monom : Type := Map ℕ ℕ

def Monom.one : Monom := RBMap.empty

def Monom.lt : Monom → Monom → Bool :=
  fun a b =>
    ((a.keys : List ℕ) < b.keys) ||
      (((a.keys : List ℕ) = b.keys) && ((a.values : List ℕ) < b.values))

instance : Ord Monom where
  compare x y := if x.lt y then .lt else if x == y then .eq else .gt

abbrev Sum : Type := Map Monom ℤ

def Sum.one : Sum := RBMap.empty.insert Monom.one 1

def Sum.scaleByMonom (s : Sum) (m : Monom) : Sum :=
  s.foldr (fun m' coeff sm => sm.insert (m + m') coeff) RBMap.empty

def Sum.mul (s1 s2 : Sum) : Sum :=
  s1.foldr (fun mn coeff sm => sm + ((s2.scaleByMonom mn).mapVal (fun _ v => v * coeff)))
    RBMap.empty

partial def Sum.pow (s : Sum) : ℕ → Sum
  | 0 => Sum.one
  | 1 => s
  | n =>
    let m := n >>> 1
    let a := s.pow m
    if n &&& 1 = 0 then
      a.mul a
    else
      a.mul a |>.mul s

def SumOfMonom (m : Monom) : Sum :=
  RBMap.empty.insert m 1

def one : Monom := RBMap.empty

def scalar (z : ℤ) : Sum :=
  RBMap.empty.insert one z

def var (n : ℕ) : Sum :=
  RBMap.empty.insert (RBMap.empty.insert n 1) 1

/-! ### Parsing algorithms -/

open Lean Elab Tactic Meta

abbrev ExprMap := List (Expr × ℕ)

def linearFormOfAtom (red : TransparencyMode) (m : ExprMap) (e : Expr) : MetaM (ExprMap × Sum) := do
  try
    let k ← m.findDefeq red e
    return (m, var k)
  catch _ =>
    let n := m.length + 1
    return ((e, n)::m, var n)

partial def linearFormOfExpr (red : TransparencyMode) (m : ExprMap) (e : Expr) :
    MetaM (ExprMap × Sum) :=
  match e.numeral? with
  | some 0 => return ⟨m, RBMap.empty⟩
  | some (n+1) => return ⟨m, scalar (n+1)⟩
  | none =>
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, e1, e2]) => do
    let (m1, comp1) ← linearFormOfExpr red m e1
    let (m2, comp2) ← linearFormOfExpr red m1 e2
    return (m2, comp1.mul comp2)
  | (``HAdd.hAdd, #[_, _, _, _, e1, e2]) => do
    let (m1, comp1) ← linearFormOfExpr red m e1
    let (m2, comp2) ← linearFormOfExpr red m1 e2
    return (m2, comp1 + comp2)
  | (``HSub.hSub, #[_, _, _, _, e1, e2]) => do
    let (m1, comp1) ← linearFormOfExpr red m e1
    let (m2, comp2) ← linearFormOfExpr red m1 e2
    return (m2, comp1 + comp2.mapVal (fun _ v => -v))
  | (``Neg.neg, #[_, _, e]) => do
    let (m1, comp) ← linearFormOfExpr red m e
    return (m1, comp.mapVal (fun _ v => -v))
  | (``HPow.hPow, #[_, _, _, _, a, n]) => do
    match n.numeral? with
    | some n => do
      let (m1, comp) ← linearFormOfExpr red m a
      return (m1, comp.pow n)
    | none => linearFormOfAtom red m e
  | _ => linearFormOfAtom red m e

def elimMonom (s : Sum) (m : Map Monom ℕ) : Map Monom ℕ × Map ℕ ℤ :=
  s.foldr (fun mn coeff ⟨map, out⟩ ↦
    match map.find? mn with
    | some n => ⟨map, out.insert n coeff⟩
    | none =>
      let n := map.size
      ⟨map.insert mn n, out.insert n coeff⟩)
    (m, RBMap.empty)

def toComp (red : TransparencyMode) (e : Expr) (e_map : ExprMap) (monom_map : Map Monom ℕ) :
    MetaM (Comp × ExprMap × Map Monom ℕ) := do
  let (iq, e) ← parseCompAndExpr e
  let (m', comp') ← linearFormOfExpr red e_map e
  let ⟨nm, mm'⟩ := elimMonom comp' monom_map
  -- Note: we use `.reverse` as `Linexp.get` assumes the monomial are in descending order
  return ⟨⟨iq, mm'.toList.reverse⟩, m', nm⟩

def toCompFold (red : TransparencyMode) : ExprMap → List Expr → Map Monom ℕ →
    MetaM (List Comp × ExprMap × Map Monom ℕ)
| m, [],     mm => return ([], m, mm)
| m, (h::t), mm => do
    let (c, m', mm') ← toComp red h m mm
    let (l, mp, mm') ← toCompFold red m' t mm'
    return (c::l, mp, mm')

def linearFormsAndMaxVar (red : TransparencyMode) (pfs : List Expr) :
    MetaM (List Comp × ℕ) := do
  let pftps ← (pfs.mapM inferType)
  let (l, _, map) ← toCompFold red [] pftps RBMap.empty
  trace[linarith.detail] "monomial map: {map.toList.map fun ⟨k,v⟩ => (k.toList, v)}"
  return (l, map.size - 1)

end Linarith
