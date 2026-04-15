/-
Extracted from RingTheory/Flat/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Flat modules

A module `M` over a commutative semiring `R` is *mono-flat* if for all monomorphisms of modules
(i.e., injective linear maps) `N →ₗ[R] P`, the canonical map `N ⊗ M → P ⊗ M` is injective
(cf. [Katsov2004], [KatsovNam2011]).
To show a module is mono-flat, it suffices to check inclusions of finitely generated
submodules `N` into finitely generated modules `P`, and `P` can be further assumed to lie in
the same universe as `R`.

`M` is flat if `· ⊗ M` preserves finite limits (equivalently, pullbacks, or equalizers).
If `R` is a ring, an `R`-module `M` is flat if and only if it is mono-flat, and to show
a module is flat, it suffices to check inclusions of finitely generated ideals into `R`.
See <https://stacks.math.columbia.edu/tag/00HD>.

Currently, `Module.Flat` is defined to be equivalent to mono-flatness over a semiring.
It is left as a TODO item to introduce the genuine flatness over semirings and rename
the current `Module.Flat` to `Module.MonoFlat`.

## Main declaration

* `Module.Flat`: the predicate asserting that an `R`-module `M` is flat.

## Main theorems

* `Module.Flat.of_retract`: retracts of flat modules are flat
* `Module.Flat.of_linearEquiv`: modules linearly equivalent to a flat module are flat
* `Module.Flat.directSum`: arbitrary direct sums of flat modules are flat
* `Module.Flat.of_free`: free modules are flat
* `Module.Flat.of_projective`: projective modules are flat
* `Module.Flat.preserves_injective_linearMap`: If `M` is a flat module then tensoring with `M`
  preserves injectivity of linear maps. This lemma is fully universally polymorphic in all
  arguments, i.e. `R`, `M` and linear maps `N → N'` can all have different universe levels.
* `Module.Flat.iff_rTensor_preserves_injective_linearMap`: a module is flat iff tensoring modules
  in the higher universe preserves injectivity.
* `Module.Flat.lTensor_exact`: If `M` is a flat module then tensoring with `M` is an exact
  functor. This lemma is fully universally polymorphic in all arguments, i.e.
  `R`, `M` and linear maps `N → N' → N''` can all have different universe levels.
* `Module.Flat.iff_lTensor_exact`: a module is flat iff tensoring modules
  in the higher universe is an exact functor.

## TODO

* Generalize flatness to noncommutative semirings.

-/

assert_not_exists AddCircle

universe v' u v w

open TensorProduct

namespace Module

open Function (Surjective)

open LinearMap Submodule DirectSum

section Semiring

/-! ### Flatness over a semiring -/

variable {R : Type u} {M : Type v} {N P Q : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

theorem _root_.LinearMap.rTensor_injective_of_fg {f : N →ₗ[R] P}
    (h : ∀ (N' : Submodule R N) (P' : Submodule R P),
      N'.FG → P'.FG → ∀ h : N' ≤ P'.comap f, Function.Injective ((f.restrict h).rTensor M)) :
    Function.Injective (f.rTensor M) := fun x y eq ↦ by
  have ⟨N', Nfg, sub⟩ := Submodule.exists_fg_le_subset_range_rTensor_subtype {x, y} (by simp)
  obtain ⟨x, rfl⟩ := sub (.inl rfl)
  obtain ⟨y, rfl⟩ := sub (.inr rfl)
  simp_rw [← rTensor_comp_apply, show f ∘ₗ N'.subtype = (N'.map f).subtype ∘ₗ f.submoduleMap N'
    from rfl, rTensor_comp_apply] at eq
  have ⟨P', Pfg, le, eq⟩ := (Nfg.map _).exists_rTensor_fg_inclusion_eq eq
  simp_rw [← rTensor_comp_apply] at eq
  rw [h _ _ Nfg Pfg (map_le_iff_le_comap.mp le) eq]

lemma _root_.LinearMap.rTensor_injective_iff_subtype {f : N →ₗ[R] P} (hf : Function.Injective f)
    (e : P ≃ₗ[R] Q) : Function.Injective (f.rTensor M) ↔
      Function.Injective ((range <| e.toLinearMap ∘ₗ f).subtype.rTensor M) := by
  simp_rw [← EquivLike.injective_comp <| (LinearEquiv.ofInjective (e.toLinearMap ∘ₗ f)
    (e.injective.comp hf)).rTensor M, ← EquivLike.comp_injective _ (e.rTensor M),
    ← LinearEquiv.coe_coe, ← coe_comp, LinearEquiv.coe_rTensor, ← rTensor_comp]
  rfl

variable (R M) in
