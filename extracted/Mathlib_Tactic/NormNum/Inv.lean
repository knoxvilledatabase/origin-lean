/-
Extracted from Tactic/NormNum/Inv.lean
Genuine: 18 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Algebra.Field.Basic

noncomputable section

/-!
# `norm_num` plugins for `Rat.cast` and `⁻¹`.
-/

variable {u : Lean.Level}

set_option linter.unusedVariables false

namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

def inferCharZeroOfRing {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM Q(CharZero $α) :=
  return ← synthInstanceQ (q(CharZero $α) : Q(Prop)) <|>
    throwError "not a characteristic zero ring"

def inferCharZeroOfRing? {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

def inferCharZeroOfAddMonoidWithOne {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
  return ← synthInstanceQ (q(CharZero $α) : Q(Prop)) <|>
    throwError "not a characteristic zero AddMonoidWithOne"

def inferCharZeroOfAddMonoidWithOne? {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) :
      MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

def inferCharZeroOfDivisionRing {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
  return ← synthInstanceQ (q(CharZero $α) : Q(Prop)) <|>
    throwError "not a characteristic zero division ring"

def inferCharZeroOfDivisionRing? {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

theorem isRat_mkRat : {a na n : ℤ} → {b nb d : ℕ} → IsInt a na → IsNat b nb →
    IsRat (na / nb : ℚ) n d → IsRat (mkRat a b) n d
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, ⟨_, h⟩ => by rw [Rat.mkRat_eq_div]; exact ⟨_, h⟩

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `mkRat a b`,

such that `norm_num` successfully recognises both `a` and `b`, and returns `a / b`. -/

@[norm_num mkRat _ _]
def evalMkRat : NormNumExt where eval {u α} (e : Q(ℚ)) : MetaM (Result e) := do
  let .app (.app (.const ``mkRat _) (a : Q(ℤ))) (b : Q(ℕ)) ← whnfR e | failure
  haveI' : $e =Q mkRat $a $b := ⟨⟩
  let ra ← derive a
  let some ⟨_, na, pa⟩ := ra.toInt (q(Int.instRing) : Q(Ring Int)) | failure
  let ⟨nb, pb⟩ ← deriveNat q($b) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let rab ← derive q($na / $nb : Rat)
  let ⟨q, n, d, p⟩ ← rab.toRat' q(Rat.instDivisionRing)
  return .isRat' _ q n d q(isRat_mkRat $pa $pb $p)

theorem isNat_ratCast {R : Type*} [DivisionRing R] : {q : ℚ} → {n : ℕ} →
    IsNat q n → IsNat (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem isInt_ratCast {R : Type*} [DivisionRing R] : {q : ℚ} → {n : ℤ} →
    IsInt q n → IsInt (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem isRat_ratCast {R : Type*} [DivisionRing R] [CharZero R] : {q : ℚ} → {n : ℤ} → {d : ℕ} →
    IsRat q n d → IsRat (q : R) n d
  | _, _, _, ⟨⟨qi,_,_⟩, rfl⟩ => ⟨⟨qi, by norm_cast, by norm_cast⟩, by simp only []; norm_cast⟩

@[norm_num Rat.cast _, RatCast.ratCast _] def evalRatCast : NormNumExt where eval {u α} e := do
  let dα ← inferDivisionRing α
  let .app r (a : Q(ℚ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq r q(Rat.cast (K := $α))
  let r ← derive q($a)
  haveI' : $e =Q Rat.cast $a := ⟨⟩
  match r with
  | .isNat _ na pa =>
    assumeInstancesCommute
    return .isNat _ na q(isNat_ratCast $pa)
  | .isNegNat _ na pa =>
    assumeInstancesCommute
    return .isNegNat _ na q(isInt_ratCast $pa)
  | .isRat _ qa na da pa =>
    assumeInstancesCommute
    let i ← inferCharZeroOfDivisionRing dα
    return .isRat dα qa na da q(isRat_ratCast $pa)
  | _ => failure

theorem isRat_inv_pos {α} [DivisionRing α] [CharZero α] {a : α} {n d : ℕ} :
    IsRat a (.ofNat (Nat.succ n)) d → IsRat a⁻¹ (.ofNat d) (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  exact ⟨this, by simp⟩

theorem isRat_inv_one {α} [DivisionRing α] : {a : α} →
    IsNat a (nat_lit 1) → IsNat a⁻¹ (nat_lit 1)
  | _, ⟨rfl⟩ => ⟨by simp⟩

theorem isRat_inv_zero {α} [DivisionRing α] : {a : α} →
    IsNat a (nat_lit 0) → IsNat a⁻¹ (nat_lit 0)
  | _, ⟨rfl⟩ => ⟨by simp⟩

theorem isRat_inv_neg_one {α} [DivisionRing α] : {a : α} →
    IsInt a (.negOfNat (nat_lit 1)) → IsInt a⁻¹ (.negOfNat (nat_lit 1))
  | _, ⟨rfl⟩ => ⟨by simp [inv_neg_one]⟩

theorem isRat_inv_neg {α} [DivisionRing α] [CharZero α] {a : α} {n d : ℕ} :
    IsRat a (.negOfNat (Nat.succ n)) d → IsRat a⁻¹ (.negOfNat d) (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  simp only [Int.negOfNat_eq]
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  generalize Nat.succ n = n at *
  use this; simp only [Int.ofNat_eq_coe, Int.cast_neg,
    Int.cast_natCast, invOf_eq_inv, inv_neg, neg_mul, mul_inv_rev, inv_inv]

open Lean

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `a⁻¹`,

such that `norm_num` successfully recognises `a`. -/

@[norm_num _⁻¹] def evalInv : NormNumExt where eval {u α} e := do
  let .app f (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let dα ← inferDivisionRing α
  let i ← inferCharZeroOfDivisionRing? dα
  guard <|← withNewMCtxDepth <| isDefEq f q(Inv.inv (α := $α))
  haveI' : $e =Q $a⁻¹ := ⟨⟩
  assumeInstancesCommute
  let rec
  /-- Main part of `evalInv`. -/
  core : Option (Result e) := do
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα
    let qb := qa⁻¹
    if qa > 0 then
      if let some i := i then
        have lit : Q(ℕ) := na.appArg!
        haveI : $na =Q Int.ofNat $lit := ⟨⟩
        have lit2 : Q(ℕ) := mkRawNatLit (lit.natLit! - 1)
        haveI : $lit =Q ($lit2).succ := ⟨⟩
        return .isRat' dα qb q(.ofNat $da) lit q(isRat_inv_pos $pa)
      else
        guard (qa = 1)
        let .isNat inst n pa := ra | failure
        haveI' : $n =Q nat_lit 1 := ⟨⟩
        assumeInstancesCommute
        return .isNat inst n q(isRat_inv_one $pa)
    else if qa < 0 then
      if let some i := i then
        have lit : Q(ℕ) := na.appArg!
        haveI : $na =Q Int.negOfNat $lit := ⟨⟩
        have lit2 : Q(ℕ) := mkRawNatLit (lit.natLit! - 1)
        haveI : $lit =Q ($lit2).succ := ⟨⟩
        return .isRat' dα qb q(.negOfNat $da) lit q(isRat_inv_neg $pa)
      else
        guard (qa = -1)
        let .isNegNat inst n pa := ra | failure
        haveI' : $n =Q nat_lit 1 := ⟨⟩
        assumeInstancesCommute
        return .isNegNat inst n q(isRat_inv_neg_one $pa)
    else
      let .isNat inst n pa := ra | failure
      haveI' : $n =Q nat_lit 0 := ⟨⟩
      assumeInstancesCommute
      return .isNat inst n q(isRat_inv_zero $pa)
  core

end Mathlib.Meta.NormNum
