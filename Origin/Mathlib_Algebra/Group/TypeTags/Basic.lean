/-
Extracted from Algebra/Group/TypeTags/Basic.lean
Genuine: 10 | Conflates: 0 | Dissolved: 0 | Infrastructure: 96
-/
import Origin.Core
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Set
import Mathlib.Util.AssertExists
import Mathlib.Logic.Nontrivial.Basic

noncomputable section

/-!
# Type tags that turn additive structures into multiplicative, and vice versa

We define two type tags:

* `Additive α`: turns any multiplicative structure on `α` into the corresponding
  additive structure on `Additive α`;
* `Multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `Multiplicative α`.

We also define instances `Additive.*` and `Multiplicative.*` that actually transfer the structures.

## See also

This file is similar to `Order.Synonym`.

-/

universe u v

variable {α : Type u} {β : Type v}

def Additive (α : Type*) := α

def Multiplicative (α : Type*) := α

namespace Additive

def ofMul : α ≃ Additive α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

def toMul : Additive α ≃ α := ofMul.symm

@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec {motive : Additive α → Sort*} (ofMul : ∀ a, motive (ofMul a)) : ∀ a, motive a :=
  fun a => ofMul (a.toMul)

end Additive

namespace Multiplicative

def ofAdd : α ≃ Multiplicative α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

def toAdd : Multiplicative α ≃ α := ofAdd.symm

@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec {motive : Multiplicative α → Sort*} (ofAdd : ∀ a, motive (ofAdd a)) : ∀ a, motive a :=
  fun a => ofAdd (a.toAdd)

end Multiplicative

open Additive (ofMul toMul)

open Multiplicative (ofAdd toAdd)

instance [Subsingleton α] : Subsingleton (Additive α) := toMul.injective.subsingleton

instance [Subsingleton α] : Subsingleton (Multiplicative α) := toAdd.injective.subsingleton

instance [Inhabited α] : Inhabited (Additive α) :=
  ⟨ofMul default⟩

instance [Inhabited α] : Inhabited (Multiplicative α) :=
  ⟨ofAdd default⟩

instance [Unique α] : Unique (Additive α) := toMul.unique

instance [Unique α] : Unique (Multiplicative α) := toAdd.unique

instance [h : DecidableEq α] : DecidableEq (Multiplicative α) := h

instance [h : DecidableEq α] : DecidableEq (Additive α) := h

instance Additive.instNontrivial [Nontrivial α] : Nontrivial (Additive α) :=
  ofMul.injective.nontrivial

instance Multiplicative.instNontrivial [Nontrivial α] : Nontrivial (Multiplicative α) :=
  ofAdd.injective.nontrivial

instance Additive.add [Mul α] : Add (Additive α) where
  add x y := ofMul (x.toMul * y.toMul)

instance Multiplicative.mul [Add α] : Mul (Multiplicative α) where
  mul x y := ofAdd (x.toAdd + y.toAdd)

instance Additive.addSemigroup [Semigroup α] : AddSemigroup (Additive α) :=
  { Additive.add with add_assoc := @mul_assoc α _ }

instance Multiplicative.semigroup [AddSemigroup α] : Semigroup (Multiplicative α) :=
  { Multiplicative.mul with mul_assoc := @add_assoc α _ }

instance Additive.addCommSemigroup [CommSemigroup α] : AddCommSemigroup (Additive α) :=
  { Additive.addSemigroup with add_comm := @mul_comm α _ }

instance Multiplicative.commSemigroup [AddCommSemigroup α] : CommSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup with mul_comm := @add_comm α _ }

instance Additive.isLeftCancelAdd [Mul α] [IsLeftCancelMul α] : IsLeftCancelAdd (Additive α) :=
  ⟨@mul_left_cancel α _ _⟩

instance Multiplicative.isLeftCancelMul [Add α] [IsLeftCancelAdd α] :
    IsLeftCancelMul (Multiplicative α) :=
  ⟨@add_left_cancel α _ _⟩

instance Additive.isRightCancelAdd [Mul α] [IsRightCancelMul α] : IsRightCancelAdd (Additive α) :=
  ⟨@mul_right_cancel α _ _⟩

instance Multiplicative.isRightCancelMul [Add α] [IsRightCancelAdd α] :
    IsRightCancelMul (Multiplicative α) :=
  ⟨@add_right_cancel α _ _⟩

instance Additive.isCancelAdd [Mul α] [IsCancelMul α] : IsCancelAdd (Additive α) :=
  ⟨⟩

instance Multiplicative.isCancelMul [Add α] [IsCancelAdd α] : IsCancelMul (Multiplicative α) :=
  ⟨⟩

instance Additive.addLeftCancelSemigroup [LeftCancelSemigroup α] :
    AddLeftCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.isLeftCancelAdd with }

instance Multiplicative.leftCancelSemigroup [AddLeftCancelSemigroup α] :
    LeftCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.isLeftCancelMul with }

instance Additive.addRightCancelSemigroup [RightCancelSemigroup α] :
    AddRightCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.isRightCancelAdd with }

instance Multiplicative.rightCancelSemigroup [AddRightCancelSemigroup α] :
    RightCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.isRightCancelMul with }

instance [One α] : Zero (Additive α) :=
  ⟨Additive.ofMul 1⟩

@[simp]
theorem ofMul_one [One α] : @Additive.ofMul α 1 = 0 := rfl

instance [Zero α] : One (Multiplicative α) :=
  ⟨Multiplicative.ofAdd 0⟩

@[simp]
theorem ofAdd_zero [Zero α] : @Multiplicative.ofAdd α 0 = 1 :=
  rfl

instance Additive.addZeroClass [MulOneClass α] : AddZeroClass (Additive α) where
  zero := 0
  add := (· + ·)
  zero_add := @one_mul α _
  add_zero := @mul_one α _

instance Multiplicative.mulOneClass [AddZeroClass α] : MulOneClass (Multiplicative α) where
  one := 1
  mul := (· * ·)
  one_mul := @zero_add α _
  mul_one := @add_zero α _

instance Additive.addMonoid [h : Monoid α] : AddMonoid (Additive α) :=
  { Additive.addZeroClass, Additive.addSemigroup with
    nsmul := @Monoid.npow α h
    nsmul_zero := @Monoid.npow_zero α h
    nsmul_succ := @Monoid.npow_succ α h }

instance Multiplicative.monoid [h : AddMonoid α] : Monoid (Multiplicative α) :=
  { Multiplicative.mulOneClass, Multiplicative.semigroup with
    npow := @AddMonoid.nsmul α h
    npow_zero := @AddMonoid.nsmul_zero α h
    npow_succ := @AddMonoid.nsmul_succ α h }

instance Additive.addLeftCancelMonoid [LeftCancelMonoid α] : AddLeftCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addLeftCancelSemigroup with }

instance Multiplicative.leftCancelMonoid [AddLeftCancelMonoid α] :
    LeftCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.leftCancelSemigroup with }

instance Additive.addRightCancelMonoid [RightCancelMonoid α] : AddRightCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addRightCancelSemigroup with }

instance Multiplicative.rightCancelMonoid [AddRightCancelMonoid α] :
    RightCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.rightCancelSemigroup with }

instance Additive.addCommMonoid [CommMonoid α] : AddCommMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addCommSemigroup with }

instance Multiplicative.commMonoid [AddCommMonoid α] : CommMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.commSemigroup with }

instance Additive.neg [Inv α] : Neg (Additive α) :=
  ⟨fun x => ofAdd x.toMul⁻¹⟩

instance Multiplicative.inv [Neg α] : Inv (Multiplicative α) :=
  ⟨fun x => ofMul (-x.toAdd)⟩

instance Additive.sub [Div α] : Sub (Additive α) where
  sub x y := ofMul (x.toMul / y.toMul)

instance Multiplicative.div [Sub α] : Div (Multiplicative α) where
  div x y := ofAdd (x.toAdd - y.toAdd)

instance Additive.involutiveNeg [InvolutiveInv α] : InvolutiveNeg (Additive α) :=
  { Additive.neg with neg_neg := @inv_inv α _ }

instance Multiplicative.involutiveInv [InvolutiveNeg α] : InvolutiveInv (Multiplicative α) :=
  { Multiplicative.inv with inv_inv := @neg_neg α _ }

instance Additive.subNegMonoid [DivInvMonoid α] : SubNegMonoid (Additive α) :=
  { Additive.neg, Additive.sub, Additive.addMonoid with
    sub_eq_add_neg := @div_eq_mul_inv α _
    zsmul := @DivInvMonoid.zpow α _
    zsmul_zero' := @DivInvMonoid.zpow_zero' α _
    zsmul_succ' := @DivInvMonoid.zpow_succ' α _
    zsmul_neg' := @DivInvMonoid.zpow_neg' α _ }

instance Multiplicative.divInvMonoid [SubNegMonoid α] : DivInvMonoid (Multiplicative α) :=
  { Multiplicative.inv, Multiplicative.div, Multiplicative.monoid with
    div_eq_mul_inv := @sub_eq_add_neg α _
    zpow := @SubNegMonoid.zsmul α _
    zpow_zero' := @SubNegMonoid.zsmul_zero' α _
    zpow_succ' := @SubNegMonoid.zsmul_succ' α _
    zpow_neg' := @SubNegMonoid.zsmul_neg' α _ }

instance Additive.subtractionMonoid [DivisionMonoid α] : SubtractionMonoid (Additive α) :=
  { Additive.subNegMonoid, Additive.involutiveNeg with
    neg_add_rev := @mul_inv_rev α _
    neg_eq_of_add := @inv_eq_of_mul_eq_one_right α _ }

instance Multiplicative.divisionMonoid [SubtractionMonoid α] : DivisionMonoid (Multiplicative α) :=
  { Multiplicative.divInvMonoid, Multiplicative.involutiveInv with
    mul_inv_rev := @neg_add_rev α _
    inv_eq_of_mul := @neg_eq_of_add_eq_zero_right α _ }

instance Additive.subtractionCommMonoid [DivisionCommMonoid α] :
    SubtractionCommMonoid (Additive α) :=
  { Additive.subtractionMonoid, Additive.addCommSemigroup with }

instance Multiplicative.divisionCommMonoid [SubtractionCommMonoid α] :
    DivisionCommMonoid (Multiplicative α) :=
  { Multiplicative.divisionMonoid, Multiplicative.commSemigroup with }

instance Additive.addGroup [Group α] : AddGroup (Additive α) :=
  { Additive.subNegMonoid with neg_add_cancel := @inv_mul_cancel α _ }

instance Multiplicative.group [AddGroup α] : Group (Multiplicative α) :=
  { Multiplicative.divInvMonoid with inv_mul_cancel := @neg_add_cancel α _ }

instance Additive.addCommGroup [CommGroup α] : AddCommGroup (Additive α) :=
  { Additive.addGroup, Additive.addCommMonoid with }

instance Multiplicative.commGroup [AddCommGroup α] : CommGroup (Multiplicative α) :=
  { Multiplicative.group, Multiplicative.commMonoid with }

instance Additive.coeToFun {α : Type*} {β : α → Sort*} [CoeFun α β] :
    CoeFun (Additive α) fun a => β a.toMul :=
  ⟨fun a => CoeFun.coe a.toMul⟩

instance Multiplicative.coeToFun {α : Type*} {β : α → Sort*} [CoeFun α β] :
    CoeFun (Multiplicative α) fun a => β a.toAdd :=
  ⟨fun a => CoeFun.coe a.toAdd⟩

lemma Pi.mulSingle_multiplicativeOfAdd_eq {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [(i : ι) → AddMonoid (M i)] (i : ι) (a : M i) (j : ι) :
    Pi.mulSingle (f := fun i ↦ Multiplicative (M i)) i (Multiplicative.ofAdd a) j =
      Multiplicative.ofAdd ((Pi.single i a) j) := by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [mulSingle, ne_eq, h, not_false_eq_true, Function.update_noteq, one_apply, single,
      zero_apply, ofAdd_zero]

lemma Pi.single_additiveOfMul_eq {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [(i : ι) → Monoid (M i)] (i : ι) (a : M i) (j : ι) :
    Pi.single (f := fun i ↦ Additive (M i)) i (Additive.ofMul a) j =
      Additive.ofMul ((Pi.mulSingle i a) j) := by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [single, ne_eq, h, not_false_eq_true, Function.update_noteq, zero_apply, mulSingle,
      one_apply, ofMul_one]
