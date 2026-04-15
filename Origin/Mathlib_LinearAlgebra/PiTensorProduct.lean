/-
Extracted from LinearAlgebra/PiTensorProduct.lean
Genuine: 10 of 12 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Tensor product of an indexed family of modules over commutative semirings

We define the tensor product of an indexed family `s : ι → Type*` of modules over commutative
semirings. We denote this space by `⨂[R] i, s i` and define it as `FreeAddMonoid (R × Π i, s i)`
quotiented by the appropriate equivalence relation. The treatment follows very closely that of the
binary tensor product in `Mathlib/LinearAlgebra/TensorProduct/Basic.lean`.

## Main definitions

* `PiTensorProduct R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor product
  of all the `s i`'s. This is denoted by `⨂[R] i, s i`.
* `tprod R f` with `f : Π i, s i` is the tensor product of the vectors `f i` over all `i : ι`.
  This is bundled as a multilinear map from `Π i, s i` to `⨂[R] i, s i`.
* `liftAddHom` constructs an `AddMonoidHom` from `(⨂[R] i, s i)` to some space `F` from a
  function `φ : (R × Π i, s i) → F` with the appropriate properties.
* `lift φ` with `φ : MultilinearMap R s E` is the corresponding linear map
  `(⨂[R] i, s i) →ₗ[R] E`. This is bundled as a linear equivalence.
* `PiTensorProduct.reindex e` re-indexes the components of `⨂[R] i : ι, M` along `e : ι ≃ ι₂`.
* `PiTensorProduct.tmulEquiv` equivalence between a `TensorProduct` of `PiTensorProduct`s and
  a single `PiTensorProduct`.

## Notation

* `⨂[R] i, s i` is defined as localized notation in scope `TensorProduct`.
* `⨂ₜ[R] i, f i` with `f : ∀ i, s i` is defined globally as the tensor product of all the `f i`'s.

## Implementation notes

* We define it via `FreeAddMonoid (R × Π i, s i)` with the `R` representing a "hidden" tensor
  factor, rather than `FreeAddMonoid (Π i, s i)` to ensure that, if `ι` is an empty type,
  the space is isomorphic to the base ring `R`.
* We have not restricted the index type `ι` to be a `Fintype`, as nothing we do here strictly
  requires it. However, problems may arise in the case where `ι` is infinite; use at your own
  caution.
* Instead of requiring `DecidableEq ι` as an argument to `PiTensorProduct` itself, we include it
  as an argument in the constructors of the relation. A decidability instance still has to come
  from somewhere due to the use of `Function.update`, but this hides it from the downstream user.
  See the implementation notes for `MultilinearMap` for an extended discussion of this choice.

## TODO

* Define tensor powers, symmetric subspace, etc.
* API for the various ways `ι` can be split into subsets; connect this with the binary
  tensor product.
* Include connection with holors.
* Port more of the API from the binary tensor product over to this case.

## Tags

multilinear, tensor, tensor product
-/

open Function

section Semiring

variable {ι ι₂ ι₃ : Type*}

variable {R : Type*} [CommSemiring R]

variable {R₁ R₂ : Type*}

variable {s : ι → Type*} [∀ i, AddCommMonoid (s i)] [∀ i, Module R (s i)]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {E : Type*} [AddCommMonoid E] [Module R E]

variable {F : Type*} [AddCommMonoid F]

namespace PiTensorProduct

variable (R) (s)

inductive Eqv : FreeAddMonoid (R × Π i, s i) → FreeAddMonoid (R × Π i, s i) → Prop
  | of_zero : ∀ (r : R) (f : Π i, s i) (i : ι) (_ : f i = 0), Eqv (FreeAddMonoid.of (r, f)) 0
  | of_zero_scalar : ∀ f : Π i, s i, Eqv (FreeAddMonoid.of (0, f)) 0
  | of_add : ∀ (_ : DecidableEq ι) (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i),
      Eqv (FreeAddMonoid.of (r, update f i m₁) + FreeAddMonoid.of (r, update f i m₂))
        (FreeAddMonoid.of (r, update f i (m₁ + m₂)))
  | of_add_scalar : ∀ (r r' : R) (f : Π i, s i),
      Eqv (FreeAddMonoid.of (r, f) + FreeAddMonoid.of (r', f)) (FreeAddMonoid.of (r + r', f))
  | of_smul : ∀ (_ : DecidableEq ι) (r : R) (f : Π i, s i) (i : ι) (r' : R),
      Eqv (FreeAddMonoid.of (r, update f i (r' • f i))) (FreeAddMonoid.of (r' * r, f))
  | add_comm : ∀ x y, Eqv (x + y) (y + x)

end PiTensorProduct

variable (R) (s)

def PiTensorProduct : Type _ :=
  (addConGen (PiTensorProduct.Eqv R s)).Quotient

variable {R}

scoped[TensorProduct] notation3:100"⨂["R"] "(...)", "r:(scoped f => PiTensorProduct R f) => r

open TensorProduct

namespace PiTensorProduct

section Module

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable (R) {s}

def tprodCoeff (r : R) (f : Π i, s i) : ⨂[R] i, s i :=
  AddCon.mk' _ <| FreeAddMonoid.of (r, f)

variable {R}

theorem zero_tprodCoeff (f : Π i, s i) : tprodCoeff R 0 f = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_scalar _

theorem zero_tprodCoeff' (z : R) (f : Π i, s i) (i : ι) (hf : f i = 0) : tprodCoeff R z f = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero _ _ i hf

theorem add_tprodCoeff [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i) :
    tprodCoeff R z (update f i m₁) + tprodCoeff R z (update f i m₂) =
      tprodCoeff R z (update f i (m₁ + m₂)) :=
  Quotient.sound' <| AddConGen.Rel.of _ _ (Eqv.of_add _ z f i m₁ m₂)

theorem add_tprodCoeff' (z₁ z₂ : R) (f : Π i, s i) :
    tprodCoeff R z₁ f + tprodCoeff R z₂ f = tprodCoeff R (z₁ + z₂) f :=
  Quotient.sound' <| AddConGen.Rel.of _ _ (Eqv.of_add_scalar z₁ z₂ f)

theorem smul_tprodCoeff_aux [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R) :
    tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r * z) f :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_smul _ _ _ _ _

theorem smul_tprodCoeff [DecidableEq ι] (z : R) (f : Π i, s i) (i : ι) (r : R₁) [SMul R₁ R]
    [IsScalarTower R₁ R R] [SMul R₁ (s i)] [IsScalarTower R₁ R (s i)] :
    tprodCoeff R z (update f i (r • f i)) = tprodCoeff R (r • z) f := by
  have h₁ : r • z = r • (1 : R) * z := by rw [smul_mul_assoc, one_mul]
  have h₂ : r • f i = (r • (1 : R)) • f i := (smul_one_smul _ _ _).symm
  rw [h₁, h₂]
  exact smul_tprodCoeff_aux z f i _

def liftAddHom (φ : (R × Π i, s i) → F)
    (C0 : ∀ (r : R) (f : Π i, s i) (i : ι) (_ : f i = 0), φ (r, f) = 0)
    (C0' : ∀ f : Π i, s i, φ (0, f) = 0)
    (C_add : ∀ [DecidableEq ι] (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i),
      φ (r, update f i m₁) + φ (r, update f i m₂) = φ (r, update f i (m₁ + m₂)))
    (C_add_scalar : ∀ (r r' : R) (f : Π i, s i), φ (r, f) + φ (r', f) = φ (r + r', f))
    (C_smul : ∀ [DecidableEq ι] (r : R) (f : Π i, s i) (i : ι) (r' : R),
      φ (r, update f i (r' • f i)) = φ (r' * r, f)) :
    (⨂[R] i, s i) →+ F :=
  (addConGen (PiTensorProduct.Eqv R s)).lift (FreeAddMonoid.lift φ) <|
    AddCon.addConGen_le fun x y hxy ↦
      match hxy with
      | Eqv.of_zero r' f i hf =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, C0 r' f i hf]
      | Eqv.of_zero_scalar f =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, C0']
      | Eqv.of_add inst z f i m₁ m₂ =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, @C_add inst]
      | Eqv.of_add_scalar z₁ z₂ f =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, C_add_scalar]
      | Eqv.of_smul inst z f i r' =>
        (AddCon.ker_rel _).2 <| by simp [FreeAddMonoid.lift_eval_of, @C_smul inst]
      | Eqv.add_comm x y =>
        (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]
