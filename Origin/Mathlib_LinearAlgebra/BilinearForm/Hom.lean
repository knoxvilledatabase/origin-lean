/-
Extracted from LinearAlgebra/BilinearForm/Hom.lean
Genuine: 28 | Conflates: 0 | Dissolved: 0 | Infrastructure: 25
-/
import Origin.Core
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Basis.Defs

noncomputable section

/-!
# Bilinear form and linear maps

This file describes the relation between bilinear forms and linear maps.

## TODO

A lot of this file is now redundant following the replacement of the dedicated `_root_.BilinForm`
structure with `LinearMap.BilinForm`, which is just an alias for `M →ₗ[R] M →ₗ[R] R`. For example
`LinearMap.BilinForm.toLinHom` is now just the identity map. This redundant code should be removed.

## Notations

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, ie. `B x y = B.bilin x y`.

In this file we use the following type variables:
 - `M`, `M'`, ... are modules over the commutative semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the commutative ring `R₁`,
 - `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

open LinearMap (BilinForm)

open LinearMap (BilinMap)

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]

variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

section ToLin'

def toLinHomAux₁ (A : BilinForm R M) (x : M) : M →ₗ[R] R := A x

def toLinHomAux₂ (A : BilinForm R M) : M →ₗ[R] M →ₗ[R] R := A

def toLinHom : BilinForm R M →ₗ[R] M →ₗ[R] M →ₗ[R] R := LinearMap.id

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-04-26")]

variable (B)

theorem sum_left {α} (t : Finset α) (g : α → M) (w : M) :
    B (∑ i ∈ t, g i) w = ∑ i ∈ t, B (g i) w :=
  B.map_sum₂ t g w

variable (w : M)

theorem sum_right {α} (t : Finset α) (w : M) (g : α → M) :
    B w (∑ i ∈ t, g i) = ∑ i ∈ t, B w (g i) := map_sum _ _ _

theorem sum_apply {α} (t : Finset α) (B : α → BilinForm R M) (v w : M) :
    (∑ i ∈ t, B i) v w = ∑ i ∈ t, B i v w := by
  simp only [coeFn_sum, Finset.sum_apply]

variable {B}

def toLinHomFlip : BilinForm R M →ₗ[R] M →ₗ[R] M →ₗ[R] R :=
  flipHom.toLinearMap

end ToLin'

end BilinForm

end LinearMap

section EquivLin

def LinearMap.toBilinAux (f : M →ₗ[R] M →ₗ[R] R) : BilinForm R M := f

set_option linter.deprecated false in
/-- Bilinear forms are linearly equivalent to maps with two arguments that are linear in both. -/

def LinearMap.BilinForm.toLin : BilinForm R M ≃ₗ[R] M →ₗ[R] M →ₗ[R] R :=
  { BilinForm.toLinHom with
    invFun := LinearMap.toBilinAux
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

set_option linter.deprecated false in
/-- A map with two arguments that is linear in both is linearly equivalent to bilinear form. -/

def LinearMap.toBilin : (M →ₗ[R] M →ₗ[R] R) ≃ₗ[R] BilinForm R M :=
  BilinForm.toLin.symm

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-04-26")]

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-04-26")]

theorem BilinForm.toLin_symm :
    (BilinForm.toLin.symm : _ ≃ₗ[R] BilinForm R M) = LinearMap.toBilin :=
  LinearMap.toBilin.symm_symm

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-04-26")]

set_option linter.deprecated false in
@[deprecated "No deprecation message was provided." (since := "2024-04-26")]

end EquivLin

namespace LinearMap

variable {R' : Type*} [CommSemiring R'] [Algebra R' R] [Module R' M] [IsScalarTower R' R M]

@[simps!]
def compBilinForm (f : R →ₗ[R'] R') (B : BilinForm R M) : BilinForm R' M :=
  compr₂ (restrictScalars₁₂ R' R' B) f

end LinearMap

namespace LinearMap

namespace BilinForm

section Comp

variable {M' : Type w} [AddCommMonoid M'] [Module R M']

def comp (B : BilinForm R M') (l r : M →ₗ[R] M') : BilinForm R M := B.compl₁₂ l r

def compLeft (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.comp f LinearMap.id

def compRight (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.comp LinearMap.id f

@[simp]
theorem comp_apply (B : BilinForm R M') (l r : M →ₗ[R] M') (v w) : B.comp l r v w = B (l v) (r w) :=
  rfl

@[simp]
theorem comp_id_left (B : BilinForm R M) (r : M →ₗ[R] M) :
    B.comp LinearMap.id r = B.compRight r := by
  ext
  rfl

@[simp]
theorem comp_id_right (B : BilinForm R M) (l : M →ₗ[R] M) :
    B.comp l LinearMap.id = B.compLeft l := by
  ext
  rfl

@[simp]
theorem compLeft_id (B : BilinForm R M) : B.compLeft LinearMap.id = B := by
  ext
  rfl

@[simp]
theorem compRight_id (B : BilinForm R M) : B.compRight LinearMap.id = B := by
  ext
  rfl

@[simp high]
theorem comp_id_id (B : BilinForm R M) : B.comp LinearMap.id LinearMap.id = B := by
  ext
  rfl

theorem comp_inj (B₁ B₂ : BilinForm R M') {l r : M →ₗ[R] M'} (hₗ : Function.Surjective l)
    (hᵣ : Function.Surjective r) : B₁.comp l r = B₂.comp l r ↔ B₁ = B₂ := by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext x y
    cases' hₗ x with x' hx
    subst hx
    cases' hᵣ y with y' hy
    subst hy
    rw [← comp_apply, ← comp_apply, h]
  · -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    rw [h]

end Comp

variable {M' M'' : Type*}

variable [AddCommMonoid M'] [AddCommMonoid M''] [Module R M'] [Module R M'']

section congr

def congr (e : M ≃ₗ[R] M') : BilinForm R M ≃ₗ[R] BilinForm R M' :=
  LinearEquiv.congrRight (LinearEquiv.congrLeft _ _ e) ≪≫ₗ LinearEquiv.congrLeft _ _ e

@[simp]
theorem congr_apply (e : M ≃ₗ[R] M') (B : BilinForm R M) (x y : M') :
    congr e B x y = B (e.symm x) (e.symm y) :=
  rfl

@[simp]
theorem congr_symm (e : M ≃ₗ[R] M') : (congr e).symm = congr e.symm := by
  ext
  simp only [congr_apply, LinearEquiv.symm_symm]
  rfl

@[simp]
theorem congr_refl : congr (LinearEquiv.refl R M) = LinearEquiv.refl R _ :=
  LinearEquiv.ext fun _ => ext₂ fun _ _ => rfl

end congr

section congrRight₂

variable {N₁ N₂ N₃ : Type*}

variable [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]

variable [Module R N₁] [Module R N₂] [Module R N₃]

def _root_.LinearEquiv.congrRight₂ (e : N₁ ≃ₗ[R] N₂) : BilinMap R M N₁ ≃ₗ[R] BilinMap R M N₂ :=
  LinearEquiv.congrRight (LinearEquiv.congrRight e)

end congrRight₂

section LinMulLin

def linMulLin (f g : M →ₗ[R] R) : BilinForm R M := (LinearMap.mul R R).compl₁₂ f g

variable {f g : M →ₗ[R] R}

end LinMulLin

section Basis

variable {F₂ : BilinForm R M}

variable {ι : Type*} (b : Basis ι R M)

theorem ext_basis (h : ∀ i j, B (b i) (b j) = F₂ (b i) (b j)) : B = F₂ :=
  b.ext fun i => b.ext fun j => h i j

theorem sum_repr_mul_repr_mul (x y : M) :
    ((b.repr x).sum fun i xi => (b.repr y).sum fun j yj => xi • yj • B (b i) (b j)) = B x y := by
  conv_rhs => rw [← b.linearCombination_repr x, ← b.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, sum_left, sum_right, smul_left, smul_right,
    smul_eq_mul]

end Basis

end BilinForm

end LinearMap
