/-
Extracted from Algebra/Ring/Hom/Defs.lean
Genuine: 48 of 107 | Dissolved: 6 | Infrastructure: 53
-/
import Origin.Core
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Basic

/-!
# Homomorphisms of semirings and rings

This file defines bundled homomorphisms of (non-unital) semirings and rings. As with monoid and
groups, we use the same structure `RingHom a β`, a.k.a. `α →+* β`, for both types of homomorphisms.

## Main definitions

* `NonUnitalRingHom`: Non-unital (semi)ring homomorphisms. Additive monoid homomorphism which
  preserve multiplication.
* `RingHom`: (Semi)ring homomorphisms. Monoid homomorphisms which are also additive monoid
  homomorphism.

## Notations

* `→ₙ+*`: Non-unital (semi)ring homs
* `→+*`: (Semi)ring homs

## Implementation notes

* There's a coercion from bundled homs to fun, and the canonical notation is to
  use the bundled hom as a function via this coercion.

* There is no `SemiringHom` -- the idea is that `RingHom` is used.
  The constructor for a `RingHom` between semirings needs a proof of `map_zero`,
  `map_one` and `map_add` as well as `map_mul`; a separate constructor
  `RingHom.mk'` will construct ring homs between rings from monoid homs given
  only a proof that addition is preserved.

## Tags

`RingHom`, `SemiringHom`
-/

open Function

variable {F α β γ : Type*}

structure NonUnitalRingHom (α β : Type*) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] extends α →ₙ* β, α →+ β

infixr:25 " →ₙ+* " => NonUnitalRingHom

section NonUnitalRingHomClass

class NonUnitalRingHomClass (F : Type*) (α β : outParam Type*) [NonUnitalNonAssocSemiring α]
  [NonUnitalNonAssocSemiring β] [FunLike F α β]
  extends MulHomClass F α β, AddMonoidHomClass F α β : Prop

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [FunLike F α β]

variable [NonUnitalRingHomClass F α β]

@[coe]
def NonUnitalRingHomClass.toNonUnitalRingHom (f : F) : α →ₙ+* β :=
  { (f : α →ₙ* β), (f : α →+ β) with }

instance : CoeTC F (α →ₙ+* β) :=
  ⟨NonUnitalRingHomClass.toNonUnitalRingHom⟩

end NonUnitalRingHomClass

namespace NonUnitalRingHom

section coe

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

instance : FunLike (α →ₙ+* β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance : NonUnitalRingHomClass (α →ₙ+* β) α β where
  map_add := NonUnitalRingHom.map_add'
  map_zero := NonUnitalRingHom.map_zero'
  map_mul f := f.map_mul'

initialize_simps_projections NonUnitalRingHom (toFun → apply)

@[simp]
theorem coe_toMulHom (f : α →ₙ+* β) : ⇑f.toMulHom = f :=
  rfl

@[simp]
theorem coe_mulHom_mk (f : α → β) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁⟩, h₂, h₃⟩ : α →ₙ+* β) : α →ₙ* β) = ⟨f, h₁⟩ :=
  rfl

theorem coe_toAddMonoidHom (f : α →ₙ+* β) : ⇑f.toAddMonoidHom = f := rfl

@[simp]
theorem coe_addMonoidHom_mk (f : α → β) (h₁ h₂ h₃) :
    ((⟨⟨f, h₁⟩, h₂, h₃⟩ : α →ₙ+* β) : α →+ β) = ⟨⟨f, h₂⟩, h₃⟩ :=
  rfl

protected def copy (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : α →ₙ+* β :=
  { f.toMulHom.copy f' h, f.toAddMonoidHom.copy f' h with }

@[simp]
theorem coe_copy (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

end coe

section

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

@[ext]
theorem ext ⦃f g : α →ₙ+* β⦄ : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

@[simp]
theorem mk_coe (f : α →ₙ+* β) (h₁ h₂ h₃) : NonUnitalRingHom.mk (MulHom.mk f h₁) h₂ h₃ = f :=
  ext fun _ => rfl

theorem coe_addMonoidHom_injective : Injective fun f : α →ₙ+* β => (f : α →+ β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

theorem coe_mulHom_injective : Injective fun f : α →ₙ+* β => (f : α →ₙ* β) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

end

variable [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β]

protected def id (α : Type*) [NonUnitalNonAssocSemiring α] : α →ₙ+* α where
  toFun := id
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

instance : Zero (α →ₙ+* β) :=
  ⟨{ toFun := 0, map_mul' := fun _ _ => (mul_zero (0 : β)).symm, map_zero' := rfl,
      map_add' := fun _ _ => (add_zero (0 : β)).symm }⟩

instance : Inhabited (α →ₙ+* β) :=
  ⟨0⟩

@[simp]
theorem coe_zero : ⇑(0 : α →ₙ+* β) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : α) : (0 : α →ₙ+* β) x = 0 :=
  rfl

@[simp]
theorem id_apply (x : α) : NonUnitalRingHom.id α x = x :=
  rfl

@[simp]
theorem coe_addMonoidHom_id : (NonUnitalRingHom.id α : α →+ α) = AddMonoidHom.id α :=
  rfl

@[simp]
theorem coe_mulHom_id : (NonUnitalRingHom.id α : α →ₙ* α) = MulHom.id α :=
  rfl

variable [NonUnitalNonAssocSemiring γ]

def comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : α →ₙ+* γ :=
  { g.toMulHom.comp f.toMulHom, g.toAddMonoidHom.comp f.toAddMonoidHom with }

theorem comp_assoc {δ} {_ : NonUnitalNonAssocSemiring δ} (f : α →ₙ+* β) (g : β →ₙ+* γ)
    (h : γ →ₙ+* δ) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem coe_comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
theorem comp_apply (g : β →ₙ+* γ) (f : α →ₙ+* β) (x : α) : g.comp f x = g (f x) :=
  rfl

@[simp]
theorem coe_comp_addMonoidHom (g : β →ₙ+* γ) (f : α →ₙ+* β) :
    AddMonoidHom.mk ⟨g ∘ f, (g.comp f).map_zero'⟩ (g.comp f).map_add' = (g : β →+ γ).comp f :=
  rfl

@[simp]
theorem coe_comp_mulHom (g : β →ₙ+* γ) (f : α →ₙ+* β) :
    MulHom.mk (g ∘ f) (g.comp f).map_mul' = (g : β →ₙ* γ).comp f :=
  rfl

@[simp]
theorem comp_zero (g : β →ₙ+* γ) : g.comp (0 : α →ₙ+* β) = 0 := by
  ext
  simp

@[simp]
theorem zero_comp (f : α →ₙ+* β) : (0 : β →ₙ+* γ).comp f = 0 := by
  ext
  rfl

@[simp]
theorem comp_id (f : α →ₙ+* β) : f.comp (NonUnitalRingHom.id α) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : α →ₙ+* β) : (NonUnitalRingHom.id β).comp f = f :=
  ext fun _ => rfl

instance : MonoidWithZero (α →ₙ+* α) where
  one := NonUnitalRingHom.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
  zero := 0
  mul_zero := comp_zero
  zero_mul := zero_comp

theorem one_def : (1 : α →ₙ+* α) = NonUnitalRingHom.id α :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : α →ₙ+* α) = id :=
  rfl

theorem mul_def (f g : α →ₙ+* α) : f * g = f.comp g :=
  rfl

@[simp]
theorem coe_mul (f g : α →ₙ+* α) : ⇑(f * g) = f ∘ g :=
  rfl

@[simp]
theorem cancel_right {g₁ g₂ : β →ₙ+* γ} {f : α →ₙ+* β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 (NonUnitalRingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
theorem cancel_left {g : β →ₙ+* γ} {f₁ f₂ : α →ₙ+* β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

end NonUnitalRingHom

structure RingHom (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β] extends
  α →* β, α →+ β, α →ₙ+* β, α →*₀ β

infixr:25 " →+* " => RingHom

section RingHomClass

class RingHomClass (F : Type*) (α β : outParam Type*)
    [NonAssocSemiring α] [NonAssocSemiring β] [FunLike F α β]
  extends MonoidHomClass F α β, AddMonoidHomClass F α β, MonoidWithZeroHomClass F α β : Prop

variable [FunLike F α β]

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} [RingHomClass F α β]

@[coe]
def RingHomClass.toRingHom (f : F) : α →+* β :=
  { (f : α →* β), (f : α →+ β) with }

instance : CoeTC F (α →+* β) :=
  ⟨RingHomClass.toRingHom⟩

instance (priority := 100) RingHomClass.toNonUnitalRingHomClass : NonUnitalRingHomClass F α β :=
  { ‹RingHomClass F α β› with }

end RingHomClass

namespace RingHom

section coe

/-!
Throughout this section, some `Semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

instance instFunLike : FunLike (α →+* β) α β where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective'
    exact h

instance instRingHomClass : RingHomClass (α →+* β) α β where
  map_add := RingHom.map_add'
  map_zero := RingHom.map_zero'
  map_mul f := f.map_mul'
  map_one f := f.map_one'

initialize_simps_projections RingHom (toFun → apply)

theorem toFun_eq_coe (f : α →+* β) : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f : α →* β) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : α →+* β) : α → β) = f :=
  rfl

@[simp]
theorem coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β] (f : F) :
    ((f : α →+* β) : α → β) = f :=
  rfl

attribute [coe] RingHom.toMonoidHom

instance coeToMonoidHom : Coe (α →+* β) (α →* β) :=
  ⟨RingHom.toMonoidHom⟩

@[simp]
theorem toMonoidHom_eq_coe (f : α →+* β) : f.toMonoidHom = f :=
  rfl

-- DISSOLVED: toMonoidWithZeroHom_eq_coe

@[simp]
theorem coe_monoidHom_mk (f : α →* β) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : α →+* β) : α →* β) = f :=
  rfl

@[simp]
theorem toAddMonoidHom_eq_coe (f : α →+* β) : f.toAddMonoidHom = f :=
  rfl

@[simp]
theorem coe_addMonoidHom_mk (f : α → β) (h₁ h₂ h₃ h₄) :
    ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃, h₄⟩ : α →+* β) : α →+ β) = ⟨⟨f, h₃⟩, h₄⟩ :=
  rfl

def copy (f : α →+* β) (f' : α → β) (h : f' = f) : α →+* β :=
  { f.toMonoidWithZeroHom.copy f' h, f.toAddMonoidHom.copy f' h with }

@[simp]
theorem coe_copy (f : α →+* β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : α →+* β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

end coe

section

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β} (f : α →+* β)

protected theorem congr_fun {f g : α →+* β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x

protected theorem congr_arg (f : α →+* β) {x y : α} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

theorem coe_inj ⦃f g : α →+* β⦄ (h : (f : α → β) = g) : f = g :=
  DFunLike.coe_injective h

@[ext]
theorem ext ⦃f g : α →+* β⦄ : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

@[simp]
theorem mk_coe (f : α →+* β) (h₁ h₂ h₃ h₄) : RingHom.mk ⟨⟨f, h₁⟩, h₂⟩ h₃ h₄ = f :=
  ext fun _ => rfl

theorem coe_addMonoidHom_injective : Injective (fun f : α →+* β => (f : α →+ β)) := fun _ _ h =>
  ext <| DFunLike.congr_fun (F := α →+ β) h

theorem coe_monoidHom_injective : Injective (fun f : α →+* β => (f : α →* β)) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

protected theorem map_zero (f : α →+* β) : f 0 = 0 :=
  map_zero f

protected theorem map_one (f : α →+* β) : f 1 = 1 :=
  map_one f

protected theorem map_add (f : α →+* β) : ∀ a b, f (a + b) = f a + f b :=
  map_add f

protected theorem map_mul (f : α →+* β) : ∀ a b, f (a * b) = f a * f b :=
  map_mul f

@[simp]
theorem map_ite_zero_one {F : Type*} [FunLike F α β] [RingHomClass F α β] (f : F)
    (p : Prop) [Decidable p] :
    f (ite p 0 1) = ite p 0 1 := by
  split_ifs with h <;> simp [h]

-- DISSOLVED: map_ite_one_zero

theorem codomain_trivial_iff_map_one_eq_zero : (0 : β) = 1 ↔ f 1 = 0 := by rw [map_one, eq_comm]

theorem codomain_trivial_iff_range_trivial : (0 : β) = 1 ↔ ∀ x, f x = 0 :=
  f.codomain_trivial_iff_map_one_eq_zero.trans
    ⟨fun h x => by rw [← mul_one x, map_mul, h, mul_zero], fun h => h 1⟩

-- DISSOLVED: map_one_ne_zero

include f in

theorem domain_nontrivial [Nontrivial β] : Nontrivial α :=
  ⟨⟨1, 0, mt (fun h => show f 1 = 0 by rw [h, map_zero]) f.map_one_ne_zero⟩⟩

theorem codomain_trivial (f : α →+* β) [h : Subsingleton α] : Subsingleton β :=
  (subsingleton_or_nontrivial β).resolve_right fun _ =>
    not_nontrivial_iff_subsingleton.mpr h f.domain_nontrivial

end

protected theorem map_neg [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x : α) : f (-x) = -f x :=
  map_neg f x

protected theorem map_sub [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x y : α) :
    f (x - y) = f x - f y :=
  map_sub f x y

def mk' [NonAssocSemiring α] [NonAssocRing β] (f : α →* β)
    (map_add : ∀ a b, f (a + b) = f a + f b) : α →+* β :=
  { AddMonoidHom.mk' f map_add, f with }

variable {_ : NonAssocSemiring α} {_ : NonAssocSemiring β}

def id (α : Type*) [NonAssocSemiring α] : α →+* α where
  toFun := _root_.id
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

instance : Inhabited (α →+* α) :=
  ⟨id α⟩

@[simp]
theorem id_apply (x : α) : RingHom.id α x = x :=
  rfl

@[simp]
theorem coe_addMonoidHom_id : (id α : α →+ α) = AddMonoidHom.id α :=
  rfl

@[simp]
theorem coe_monoidHom_id : (id α : α →* α) = MonoidHom.id α :=
  rfl

variable {_ : NonAssocSemiring γ}

def comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=
  { g.toNonUnitalRingHom.comp f.toNonUnitalRingHom with toFun := g ∘ f, map_one' := by simp }

theorem comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α →+* β) (g : β →+* γ) (h : γ →+* δ) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem coe_comp (hnp : β →+* γ) (hmn : α →+* β) : (hnp.comp hmn : α → γ) = hnp ∘ hmn :=
  rfl

theorem comp_apply (hnp : β →+* γ) (hmn : α →+* β) (x : α) :
    (hnp.comp hmn : α → γ) x = hnp (hmn x) :=
  rfl

@[simp]
theorem comp_id (f : α →+* β) : f.comp (id α) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : α →+* β) : (id β).comp f = f :=
  ext fun _ => rfl

instance instOne : One (α →+* α) where one := id _

instance instMul : Mul (α →+* α) where mul := comp

lemma one_def : (1 : α →+* α) = id α := rfl

lemma mul_def (f g : α →+* α) : f * g = f.comp g := rfl

@[simp, norm_cast] lemma coe_one : ⇑(1 : α →+* α) = _root_.id := rfl

@[simp, norm_cast] lemma coe_mul (f g : α →+* α) : ⇑(f * g) = f ∘ g := rfl

instance instMonoid : Monoid (α →+* α) where
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
  npow n f := (npowRec n f).copy f^[n] <| by induction n <;> simp [npowRec, *]
  npow_succ _ _ := DFunLike.coe_injective <| Function.iterate_succ _ _

@[simp, norm_cast] lemma coe_pow (f : α →+* α) (n : ℕ) : ⇑(f ^ n) = f^[n] := rfl

@[simp]
theorem cancel_right {g₁ g₂ : β →+* γ} {f : α →+* β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => RingHom.ext <| hf.forall.2 (RingHom.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
theorem cancel_left {g : β →+* γ} {f₁ f₂ : α →+* β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => RingHom.ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

end RingHom

section Semiring

variable [Semiring α] [Semiring β]

protected lemma RingHom.map_pow (f : α →+* β) (a) : ∀ n : ℕ, f (a ^ n) = f a ^ n := map_pow f a

end Semiring

namespace AddMonoidHom

variable [CommRing α] [IsDomain α] [CommRing β] (f : β →+ α)

-- DISSOLVED: mkRingHomOfMulSelfOfTwoNeZero

-- DISSOLVED: coe_fn_mkRingHomOfMulSelfOfTwoNeZero

-- DISSOLVED: coe_addMonoidHom_mkRingHomOfMulSelfOfTwoNeZero

end AddMonoidHom
