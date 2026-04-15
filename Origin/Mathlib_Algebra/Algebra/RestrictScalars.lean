/-
Extracted from Algebra/Algebra/RestrictScalars.lean
Genuine: 6 of 24 | Dissolved: 0 | Infrastructure: 18
-/
import Origin.Core
import Mathlib.Algebra.Algebra.Tower

/-!

# The `RestrictScalars` type alias

See the documentation attached to the `RestrictScalars` definition for advice on how and when to
use this type alias. As described there, it is often a better choice to use the `IsScalarTower`
typeclass instead.

## Main definitions

* `RestrictScalars R S M`: the `S`-module `M` viewed as an `R` module when `S` is an `R`-algebra.
  Note that by default we do *not* have a `Module S (RestrictScalars R S M)` instance
  for the original action.
  This is available as a def `RestrictScalars.moduleOrig` if really needed.
* `RestrictScalars.addEquiv : RestrictScalars R S M ≃+ M`: the additive equivalence
  between the restricted and original space (in fact, they are definitionally equal,
  but sometimes it is helpful to avoid using this fact, to keep instances from leaking).
* `RestrictScalars.ringEquiv : RestrictScalars R S A ≃+* A`: the ring equivalence
   between the restricted and original space when the module is an algebra.

## See also

There are many similarly-named definitions elsewhere which do not refer to this type alias. These
refer to restricting the scalar type in a bundled type, such as from `A →ₗ[R] B` to `A →ₗ[S] B`:

* `LinearMap.restrictScalars`
* `LinearEquiv.restrictScalars`
* `AlgHom.restrictScalars`
* `AlgEquiv.restrictScalars`
* `Submodule.restrictScalars`
* `Subalgebra.restrictScalars`
-/

variable (R S M A : Type*)

@[nolint unusedArguments]
def RestrictScalars (_R _S M : Type*) : Type _ := M

instance [I : Inhabited M] : Inhabited (RestrictScalars R S M) := I

instance [I : AddCommMonoid M] : AddCommMonoid (RestrictScalars R S M) := I

instance [I : AddCommGroup M] : AddCommGroup (RestrictScalars R S M) := I

section Module

section

variable [Semiring S] [AddCommMonoid M]

def RestrictScalars.moduleOrig [I : Module S M] : Module S (RestrictScalars R S M) := I

variable [CommSemiring R] [Algebra R S]

section

attribute [local instance] RestrictScalars.moduleOrig

instance RestrictScalars.module [Module S M] : Module R (RestrictScalars R S M) :=
  Module.compHom M (algebraMap R S)

instance RestrictScalars.isScalarTower [Module S M] : IsScalarTower R S (RestrictScalars R S M) :=
  ⟨fun r S M ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩

end

instance RestrictScalars.opModule [Module Sᵐᵒᵖ M] : Module Rᵐᵒᵖ (RestrictScalars R S M) :=
  letI : Module Sᵐᵒᵖ (RestrictScalars R S M) := ‹Module Sᵐᵒᵖ M›
  Module.compHom M (RingHom.op <| algebraMap R S)

instance RestrictScalars.isCentralScalar [Module S M] [Module Sᵐᵒᵖ M] [IsCentralScalar S M] :
    IsCentralScalar R (RestrictScalars R S M) where
  op_smul_eq_smul r _x := (op_smul_eq_smul (algebraMap R S r) (_ : M) : _)

def RestrictScalars.lsmul [Module S M] : S →ₐ[R] Module.End R (RestrictScalars R S M) :=
  -- We use `RestrictScalars.moduleOrig` in the implementation,
  -- but not in the type.
  letI : Module S (RestrictScalars R S M) := RestrictScalars.moduleOrig R S M
  Algebra.lsmul R R (RestrictScalars R S M)

end

variable [AddCommMonoid M]

def RestrictScalars.addEquiv : RestrictScalars R S M ≃+ M :=
  AddEquiv.refl M

variable [CommSemiring R] [Semiring S] [Algebra R S] [Module S M]

theorem RestrictScalars.smul_def (c : R) (x : RestrictScalars R S M) :
    c • x = (RestrictScalars.addEquiv R S M).symm
      (algebraMap R S c • RestrictScalars.addEquiv R S M x) :=
  rfl

@[simp]
theorem RestrictScalars.addEquiv_map_smul (c : R) (x : RestrictScalars R S M) :
    RestrictScalars.addEquiv R S M (c • x) = algebraMap R S c • RestrictScalars.addEquiv R S M x :=
  rfl

theorem RestrictScalars.addEquiv_symm_map_algebraMap_smul (r : R) (x : M) :
    (RestrictScalars.addEquiv R S M).symm (algebraMap R S r • x) =
      r • (RestrictScalars.addEquiv R S M).symm x :=
  rfl

theorem RestrictScalars.addEquiv_symm_map_smul_smul (r : R) (s : S) (x : M) :
    (RestrictScalars.addEquiv R S M).symm ((r • s) • x) =
      r • (RestrictScalars.addEquiv R S M).symm (s • x) := by
  rw [Algebra.smul_def, mul_smul]
  rfl

theorem RestrictScalars.lsmul_apply_apply (s : S) (x : RestrictScalars R S M) :
    RestrictScalars.lsmul R S M s x =
      (RestrictScalars.addEquiv R S M).symm (s • RestrictScalars.addEquiv R S M x) :=
  rfl

end Module

section Algebra

instance [I : Semiring A] : Semiring (RestrictScalars R S A) := I

instance [I : Ring A] : Ring (RestrictScalars R S A) := I

instance [I : CommSemiring A] : CommSemiring (RestrictScalars R S A) := I

instance [I : CommRing A] : CommRing (RestrictScalars R S A) := I

variable [Semiring A]

def RestrictScalars.ringEquiv : RestrictScalars R S A ≃+* A :=
  RingEquiv.refl _

variable [CommSemiring S] [Algebra S A] [CommSemiring R] [Algebra R S]

@[simp]
theorem RestrictScalars.ringEquiv_map_smul (r : R) (x : RestrictScalars R S A) :
    RestrictScalars.ringEquiv R S A (r • x) =
      algebraMap R S r • RestrictScalars.ringEquiv R S A x :=
  rfl

instance RestrictScalars.algebra : Algebra R (RestrictScalars R S A) :=
  { (algebraMap S A).comp (algebraMap R S) with
    smul := (· • ·)
    commutes' := fun _ _ ↦ Algebra.commutes' (A := A) _ _
    smul_def' := fun _ _ ↦ Algebra.smul_def' (A := A) _ _ }

@[simp]
theorem RestrictScalars.ringEquiv_algebraMap (r : R) :
    RestrictScalars.ringEquiv R S A (algebraMap R (RestrictScalars R S A) r) =
      algebraMap S A (algebraMap R S r) :=
  rfl

end Algebra
