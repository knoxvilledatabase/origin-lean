/-
Extracted from Algebra/Star/StarRingHom.lean
Genuine: 30 | Conflates: 0 | Dissolved: 0 | Infrastructure: 40
-/
import Origin.Core
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Star.Basic

noncomputable section

/-!
# Morphisms of star rings

This file defines a new type of morphism between (non-unital) rings `A` and `B` where both
`A` and `B` are equipped with a `star` operation. This morphism, namely `NonUnitalStarRingHom`, is
a direct extension of its non-`star`red counterpart with a field `map_star` which guarantees it
preserves the star operation.

As with `NonUnitalRingHom`, the multiplications are not assumed to be associative or unital.

## Main definitions

  * `NonUnitalStarRingHom`

## Implementation

This file is heavily inspired by `Mathlib.Algebra.Star.StarAlgHom`.

## Tags

non-unital, ring, morphism, star
-/

open EquivLike

/-! ### Non-unital star ring homomorphisms -/

structure NonUnitalStarRingHom (A B : Type*) [NonUnitalNonAssocSemiring A]
    [Star A] [NonUnitalNonAssocSemiring B] [Star B] extends A →ₙ+* B where
  /-- By definition, a non-unital ⋆-ring homomorphism preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

infixr:25 " →⋆ₙ+* " => NonUnitalStarRingHom

class NonUnitalStarRingHomClass (F : Type*) (A B : outParam Type*)
    [NonUnitalNonAssocSemiring A] [Star A] [NonUnitalNonAssocSemiring B] [Star B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] extends StarHomClass F A B : Prop

namespace NonUnitalStarRingHomClass

variable {F A B : Type*}

variable [NonUnitalNonAssocSemiring A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Star B]

variable [FunLike F A B] [NonUnitalRingHomClass F A B]

@[coe]
def toNonUnitalStarRingHom [NonUnitalStarRingHomClass F A B] (f : F) : A →⋆ₙ+* B :=
  { (f : A →ₙ+* B) with
    map_star' := map_star f }

instance [NonUnitalStarRingHomClass F A B] : CoeHead F (A →⋆ₙ+* B) :=
  ⟨toNonUnitalStarRingHom⟩

end NonUnitalStarRingHomClass

namespace NonUnitalStarRingHom

section Basic

variable {A B C D : Type*}

variable [NonUnitalNonAssocSemiring A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Star B]

variable [NonUnitalNonAssocSemiring C] [Star C]

variable [NonUnitalNonAssocSemiring D] [Star D]

instance : FunLike (A →⋆ₙ+* B) A B where
  coe f := f.toFun
  coe_injective' := by rintro ⟨⟨⟨f, _⟩,  _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h; congr

instance : NonUnitalRingHomClass (A →⋆ₙ+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'
  map_zero f := f.map_zero'

instance : NonUnitalStarRingHomClass (A →⋆ₙ+* B) A B where
  map_star f := f.map_star'

def Simps.apply (f : A →⋆ₙ+* B) : A → B := f

initialize_simps_projections NonUnitalStarRingHom (toFun → apply)

@[ext]
theorem ext {f g : A →⋆ₙ+* B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

protected def copy (f : A →⋆ₙ+* B) (f' : A → B) (h : f' = f) : A →⋆ₙ+* B where
  toFun := f'
  map_zero' := h.symm ▸ map_zero f
  map_add' := h.symm ▸ map_add f
  map_mul' := h.symm ▸ map_mul f
  map_star' := h.symm ▸ map_star f

theorem copy_eq (f : A →⋆ₙ+* B) (f' : A → B) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
theorem mk_coe (f : A →⋆ₙ+* B) (h₁ h₂ h₃ h₄) :
    (⟨⟨⟨f, h₁⟩, h₂, h₃⟩, h₄⟩ : A →⋆ₙ+* B) = f := by
  ext
  rfl

section

variable (A)

protected def id : A →⋆ₙ+* A :=
  { (1 : A →ₙ+* A) with map_star' := fun _ => rfl }

end

def comp (f : B →⋆ₙ+* C) (g : A →⋆ₙ+* B) : A →⋆ₙ+* C :=
  { f.toNonUnitalRingHom.comp g.toNonUnitalRingHom with
    map_star' := fun a => by simp [Function.comp_def, map_star, map_star] }

@[simp]
theorem comp_assoc (f : C →⋆ₙ+* D) (g : B →⋆ₙ+* C) (h : A →⋆ₙ+* B) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem id_comp (f : A →⋆ₙ+* B) : (NonUnitalStarRingHom.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : A →⋆ₙ+* B) : f.comp (NonUnitalStarRingHom.id _) = f :=
  ext fun _ => rfl

instance : Monoid (A →⋆ₙ+* A) where
  mul := comp
  mul_assoc := comp_assoc
  one := NonUnitalStarRingHom.id A
  one_mul := id_comp
  mul_one := comp_id

end Basic

section Zero

variable {A B C : Type*}

variable [NonUnitalNonAssocSemiring A] [StarAddMonoid A]

variable [NonUnitalNonAssocSemiring B] [StarAddMonoid B]

instance : Zero (A →⋆ₙ+* B) :=
  ⟨{ (0 : NonUnitalRingHom A B) with map_star' := by simp }⟩

instance : Inhabited (A →⋆ₙ+* B) :=
  ⟨0⟩

instance : MonoidWithZero (A →⋆ₙ+* A) where
  zero_mul := fun _ => ext fun _ => rfl
  mul_zero := fun f => ext fun _ => map_zero f

end Zero

end NonUnitalStarRingHom

/-! ### Star ring equivalences -/

structure StarRingEquiv (A B : Type*) [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B]
    extends A ≃+* B where
  /-- By definition, a ⋆-ring equivalence preserves the `star` operation. -/
  map_star' : ∀ a : A, toFun (star a) = star (toFun a)

@[inherit_doc] notation:25 A " ≃⋆+* " B => StarRingEquiv A B

class StarRingEquivClass (F : Type*) (A B : outParam Type*)
    [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B] [EquivLike F A B]
    extends RingEquivClass F A B : Prop where
  /-- By definition, a ⋆-ring equivalence preserves the `star` operation. -/
  map_star : ∀ (f : F) (a : A), f (star a) = star (f a)

namespace StarRingEquivClass

instance (priority := 50) {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [hF : StarRingEquivClass F A B] :
    StarHomClass F A B :=
  { hF with }

instance (priority := 100) {F A B : Type*} [NonUnitalNonAssocSemiring A] [Star A]
    [NonUnitalNonAssocSemiring B] [Star B] [EquivLike F A B] [RingEquivClass F A B]
    [StarRingEquivClass F A B] : NonUnitalStarRingHomClass F A B :=
  { }

@[coe]
def toStarRingEquiv {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [RingEquivClass F A B] [StarRingEquivClass F A B] (f : F) : A ≃⋆+* B :=
  { (f : A ≃+* B) with
    map_star' := map_star f}

instance instCoeHead {F A B : Type*} [Add A] [Mul A] [Star A] [Add B] [Mul B] [Star B]
    [EquivLike F A B] [RingEquivClass F A B] [StarRingEquivClass F A B] : CoeHead F (A ≃⋆+* B) :=
  ⟨toStarRingEquiv⟩

end StarRingEquivClass

namespace StarRingEquiv

section Basic

variable {A B C : Type*} [Add A] [Add B] [Mul A] [Mul B] [Star A] [Star B] [Add C] [Mul C] [Star C]

instance : EquivLike (A ≃⋆+* B) A B where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    rcases f with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    rcases g with ⟨⟨⟨_, _, _⟩, _⟩, _⟩
    congr

instance : RingEquivClass (A ≃⋆+* B) A B where
  map_mul f := f.map_mul'
  map_add f := f.map_add'

instance : StarRingEquivClass (A ≃⋆+* B) A B where
  map_star := map_star'

instance : FunLike (A ≃⋆+* B) A B where
  coe f := f.toFun
  coe_injective' := DFunLike.coe_injective

@[ext]
theorem ext {f g : A ≃⋆+* B} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

@[refl]
def refl : A ≃⋆+* A :=
  { RingEquiv.refl A with
    map_star' := fun _ => rfl }

instance : Inhabited (A ≃⋆+* A) :=
  ⟨refl⟩

@[symm]
nonrec def symm (e : A ≃⋆+* B) : B ≃⋆+* A :=
  { e.symm with
    map_star' := fun b => by
      simpa only [apply_inv_apply, inv_apply_apply] using
        congr_arg (inv e) (map_star e (inv e b)).symm }

def Simps.apply (e : A ≃⋆+* B) : A → B := e

def Simps.symm_apply (e : A ≃⋆+* B) : B → A :=
  e.symm

initialize_simps_projections StarRingEquiv (toFun → apply, invFun → symm_apply)

@[simp]
theorem symm_symm (e : A ≃⋆+* B) : e.symm.symm = e := rfl

theorem symm_bijective : Function.Bijective (symm : (A ≃⋆+* B) → B ≃⋆+* A) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem mk_coe (e : A ≃⋆+* B) (e' h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨e, e', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : A ≃⋆+* B) = e := ext fun _ => rfl

protected def symm_mk.aux (f f') (h₁ h₂ h₃ h₄ h₅) :=
  (⟨⟨⟨f, f', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : A ≃⋆+* B).symm

@[simp]
theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
    (⟨⟨⟨f, f', h₁, h₂⟩, h₃, h₄⟩, h₅⟩ : A ≃⋆+* B).symm =
      { symm_mk.aux f f' h₁ h₂ h₃ h₄ h₅ with
        toFun := f'
        invFun := f } :=
  rfl

@[trans]
def trans (e₁ : A≃⋆+* B) (e₂ : B ≃⋆+* C) : A ≃⋆+* C :=
  { e₁.toRingEquiv.trans e₂.toRingEquiv with
    map_star' := fun a =>
      show e₂.toFun (e₁.toFun (star a)) = star (e₂.toFun (e₁.toFun a)) by
        rw [e₁.map_star', e₂.map_star'] }

@[simp]
theorem apply_symm_apply (e : A ≃⋆+* B) : ∀ x, e (e.symm x) = x :=
  e.toRingEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A ≃⋆+* B) : ∀ x, e.symm (e x) = x :=
  e.toRingEquiv.symm_apply_apply

theorem leftInverse_symm (e : A ≃⋆+* B) : Function.LeftInverse e.symm e :=
  e.left_inv

theorem rightInverse_symm (e : A ≃⋆+* B) : Function.RightInverse e.symm e :=
  e.right_inv

end Basic

section Bijective

variable {F G A B : Type*}

variable [NonUnitalNonAssocSemiring A] [Star A]

variable [NonUnitalNonAssocSemiring B] [Star B]

variable [FunLike F A B] [NonUnitalRingHomClass F A B] [NonUnitalStarRingHomClass F A B]

variable [FunLike G B A]

@[simps]
def ofStarRingHom (f : F) (g : G) (h₁ : ∀ x, g (f x) = x) (h₂ : ∀ x, f (g x) = x) : A ≃⋆+* B where
  toFun := f
  invFun := g
  left_inv := h₁
  right_inv := h₂
  map_add' := map_add f
  map_mul' := map_mul f
  map_star' := map_star f

noncomputable def ofBijective (f : F) (hf : Function.Bijective f) : A ≃⋆+* B :=
  { RingEquiv.ofBijective f (hf : Function.Bijective (f : A → B)) with
    toFun := f
    map_star' := map_star f }

end Bijective

end StarRingEquiv
