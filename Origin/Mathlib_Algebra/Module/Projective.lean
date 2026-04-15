/-
Extracted from Algebra/Module/Projective.lean
Genuine: 10 of 14 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!

# Projective modules

This file contains a definition of a projective module, the proof that
our definition is equivalent to a lifting property, and the
proof that all free modules are projective.

## Main definitions

Let `R` be a ring (or a semiring) and let `M` be an `R`-module.

* `Module.Projective R M` : the proposition saying that `M` is a projective `R`-module.

## Main theorems

* `Module.projective_lifting_property` : a map from a projective module can be lifted along
  a surjection.

* `Module.Projective.of_lifting_property` : If for all R-module surjections `A →ₗ B`, all
  maps `M →ₗ B` lift to `M →ₗ A`, then `M` is projective.

* `Module.Projective.of_free` : Free modules are projective

## Implementation notes

The actual definition of projective we use is that the natural R-module map
from the free R-module on the type M down to M splits. This is more convenient
than certain other definitions which involve quantifying over universes,
and also universe-polymorphic (the ring and module can be in different universes).

We require that the module sits in at least as high a universe as the ring:
without this, free modules don't even exist,
and it's unclear if projective modules are even a useful notion.

## References

https://en.wikipedia.org/wiki/Projective_module

## TODO

- Direct sum of two projective modules is projective.
- Arbitrary sum of projective modules is projective.

All of these should be relatively straightforward.

## Tags

projective module

-/

universe w v u

open LinearMap hiding id

open Finsupp

class Module.Projective (R : Type*) [Semiring R] (P : Type*) [AddCommMonoid P] [Module R P] :
    Prop where
  out : ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (Finsupp.linearCombination R id) s

namespace Module

section Semiring

variable {R : Type*} [Semiring R] {P : Type*} [AddCommMonoid P] [Module R P] {M : Type*}
  [AddCommMonoid M] [Module R M] {N : Type*} [AddCommMonoid N] [Module R N]

theorem projective_def :
    Projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Function.LeftInverse (linearCombination R id) s :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem projective_def' :
    Projective R P ↔ ∃ s : P →ₗ[R] P →₀ R, Finsupp.linearCombination R id ∘ₗ s = .id := by
  simp_rw [projective_def, DFunLike.ext_iff, Function.LeftInverse, comp_apply, id_apply]

theorem _root_.LinearMap.exists_rightInverse_of_surjective [Projective R P]
    (f : M →ₗ[R] P) (hf_surj : range f = ⊤) : ∃ g : P →ₗ[R] M, f ∘ₗ g = LinearMap.id :=
  projective_lifting_property f (.id : P →ₗ[R] P) (LinearMap.range_eq_top.1 hf_surj)

open Function in

theorem _root_.Function.Surjective.surjective_linearMapComp_left [Projective R P]
    {f : M →ₗ[R] P} (hf_surj : Surjective f) : Surjective (fun g : N →ₗ[R] M ↦ f.comp g) :=
  surjective_comp_left_of_exists_rightInverse <|
    f.exists_rightInverse_of_surjective <| range_eq_top_of_surjective f hf_surj

theorem Projective.of_lifting_property'' {R : Type u} [Semiring R] {P : Type v} [AddCommMonoid P]
    [Module R P] (huniv : ∀ (f : (P →₀ R) →ₗ[R] P), Function.Surjective f →
      ∃ h : P →ₗ[R] (P →₀ R), f.comp h = .id) :
    Projective R P :=
  projective_def'.2 <| huniv (Finsupp.linearCombination R (id : P → P))
    (linearCombination_surjective _ Function.surjective_id)

variable {Q : Type*} [AddCommMonoid Q] [Module R Q]

-- INSTANCE (free from Core): [Projective

variable {ι : Type*} (A : ι → Type*) [∀ i : ι, AddCommMonoid (A i)] [∀ i : ι, Module R (A i)]

-- INSTANCE (free from Core): [h

theorem Projective.of_basis {ι : Type*} (b : Basis ι R P) : Projective R P := by
  -- need P →ₗ (P →₀ R) for definition of projective.
  -- get it from `ι → (P →₀ R)` coming from `b`.
  use b.constr ℕ fun i => Finsupp.single (b i) (1 : R)
  intro m
  simp only [b.constr_apply, mul_one, id, Finsupp.smul_single', Finsupp.linearCombination_single,
    map_finsuppSum]
  exact b.linearCombination_repr m

-- INSTANCE (free from Core): (priority

theorem Projective.of_split [Module.Projective R M]
    (i : P →ₗ[R] M) (s : M →ₗ[R] P) (H : s.comp i = LinearMap.id) : Module.Projective R P := by
  obtain ⟨g, hg⟩ := projective_lifting_property (Finsupp.linearCombination R id) s
    (fun x ↦ ⟨Finsupp.single x 1, by simp⟩)
  refine ⟨g.comp i, fun x ↦ ?_⟩
  rw [LinearMap.comp_apply, ← LinearMap.comp_apply, hg,
    ← LinearMap.comp_apply, H, LinearMap.id_apply]

theorem Projective.of_equiv {R S} [Semiring R] [Semiring S] {M N}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
    {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e₂ : M ≃ₛₗ[σ] N)
    [Projective R M] : Projective S N := by
  let e₁ : R ≃+* S := RingHomInvPair.toRingEquiv σ σ'
  obtain ⟨f, hf⟩ := ‹Projective R M›
  let g : N →ₗ[S] N →₀ S :=
  { toFun := fun x ↦ (equivCongrLeft e₂ (f (e₂.symm x))).mapRange e₁ e₁.map_zero
    map_add' := fun x y ↦ by ext; simp
    map_smul' := fun r v ↦ by ext i; simp [e₁, e₂.symm.map_smulₛₗ] }
  refine ⟨⟨g, fun x ↦ ?_⟩⟩
  replace hf := congr(e₂ $(hf (e₂.symm x)))
  simpa [linearCombination_apply, sum_mapRange_index, g, map_finsuppSum, e₂.map_smulₛₗ] using hf

theorem Projective.of_equiv' [Module.Projective R M]
    (e : M ≃ₗ[R] P) : Module.Projective R P :=
  .of_equiv e
