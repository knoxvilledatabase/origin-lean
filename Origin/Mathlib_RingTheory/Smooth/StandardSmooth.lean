/-
Extracted from RingTheory/Smooth/StandardSmooth.lean
Genuine: 13 of 17 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Standard smooth algebras

A standard smooth algebra is an algebra that admits a `SubmersivePresentation`. A standard
smooth algebra is of relative dimension `n` if it admits a submersive presentation of
dimension `n`.

While every standard smooth algebra is smooth, the converse does not hold. But if `S` is `R`-smooth,
then `S` is `R`-standard smooth locally on `S`, i.e. there exists a set `{ t }` of `S` that
generates the unit ideal, such that `Sₜ` is `R`-standard smooth for every `t` (TODO, see below).

## Main definitions

All of these are in the `Algebra` namespace. Let `S` be an `R`-algebra.

- `Algebra.IsStandardSmooth`: `S` is `R`-standard smooth if `S` admits a submersive
  `R`-presentation.
- `Algebra.IsStandardSmooth.relativeDimension`: If `S` is `R`-standard smooth this is the dimension
  of an arbitrary submersive `R`-presentation of `S`. This is independent of the choice
  of the presentation (TODO, see below).
- `Algebra.IsStandardSmoothOfRelativeDimension n`: `S` is `R`-standard smooth of relative dimension
  `n` if it admits a submersive `R`-presentation of dimension `n`.

## TODO

- Show that locally on the target, smooth algebras are standard smooth.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

universe t t' w w' u v

open TensorProduct Module MvPolynomial

variable (n m : ℕ)

namespace Algebra

variable (R : Type u) (S : Type v) (ι : Type w) (σ : Type t) [CommRing R] [CommRing S] [Algebra R S]

attribute [local instance] Fintype.ofFinite

class IsStandardSmooth : Prop where
  out : ∃ (ι σ : Type) (_ : Finite σ), Finite ι ∧ Nonempty (SubmersivePresentation R S ι σ)

variable [Finite σ]

variable {R S ι σ} in

lemma SubmersivePresentation.isStandardSmooth [Finite ι] (P : SubmersivePresentation R S ι σ) :
    IsStandardSmooth R S := by
  exact ⟨_, _, _, inferInstance, ⟨P.reindex (Fintype.equivFin _).symm (Fintype.equivFin _).symm⟩⟩

noncomputable def IsStandardSmooth.relativeDimension [IsStandardSmooth R S] : ℕ :=
  letI := ‹IsStandardSmooth R S›.out.choose_spec.choose_spec.choose
  ‹IsStandardSmooth R S›.out.choose_spec.choose_spec.choose_spec.2.some.dimension

class IsStandardSmoothOfRelativeDimension : Prop where
  out : ∃ (ι σ : Type) (_ : Finite σ) (_ : Finite ι) (P : SubmersivePresentation R S ι σ),
    P.dimension = n

variable {R S ι σ n} in

lemma SubmersivePresentation.isStandardSmoothOfRelativeDimension [Finite ι]
    (P : SubmersivePresentation R S ι σ) (hP : P.dimension = n) :
    IsStandardSmoothOfRelativeDimension n R S := by
  refine ⟨⟨_, _, _, inferInstance,
    P.reindex (Fintype.equivFin _).symm (Fintype.equivFin σ).symm, ?_⟩⟩
  simp [hP]

variable {R} {S}

lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth
    [H : IsStandardSmoothOfRelativeDimension n R S] : IsStandardSmooth R S :=
  ⟨_, _, _, H.out.choose_spec.choose_spec.choose_spec.choose,
    H.out.choose_spec.choose_spec.choose_spec.choose_spec.nonempty⟩

lemma IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective
    (h : Function.Bijective (algebraMap R S)) :
    IsStandardSmoothOfRelativeDimension 0 R S :=
  ⟨_, _, _, inferInstance,
    SubmersivePresentation.ofBijectiveAlgebraMap h, Presentation.ofBijectiveAlgebraMap_dimension h⟩

variable (R) in

-- INSTANCE (free from Core): IsStandardSmoothOfRelativeDimension.id

-- INSTANCE (free from Core): (priority

lemma IsStandardSmooth.of_algEquiv {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T)
    [IsStandardSmooth R S] : IsStandardSmooth R T := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact (P.ofAlgEquiv e).isStandardSmooth

lemma IsStandardSmoothOfRelativeDimension.of_algEquiv {T : Type*} [CommRing T] [Algebra R T]
    (e : S ≃ₐ[R] T) [IsStandardSmoothOfRelativeDimension n R S] :
    IsStandardSmoothOfRelativeDimension n R T := by
  obtain ⟨_, _, _, _, ⟨P, hP⟩⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
  exact (P.ofAlgEquiv e).isStandardSmoothOfRelativeDimension (by simpa)

section Composition

variable (R S T) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

lemma IsStandardSmooth.trans [IsStandardSmooth R S] [IsStandardSmooth S T] :
    IsStandardSmooth R T where
  out := by
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
    obtain ⟨_, _, _, _, ⟨Q⟩⟩ := ‹IsStandardSmooth S T›
    exact ⟨_, _, _, inferInstance, ⟨Q.comp P⟩⟩

lemma IsStandardSmoothOfRelativeDimension.trans [IsStandardSmoothOfRelativeDimension n R S]
    [IsStandardSmoothOfRelativeDimension m S T] :
    IsStandardSmoothOfRelativeDimension (m + n) R T where
  out := by
    obtain ⟨_, _, _, _, P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    obtain ⟨_, _, _, _, Q, hQ⟩ := ‹IsStandardSmoothOfRelativeDimension m S T›
    refine ⟨_, _, _, inferInstance, Q.comp P, hP ▸ hQ ▸ ?_⟩
    apply PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension

end Composition

lemma IsStandardSmooth.localization_away (r : R) [IsLocalization.Away r S] :
    IsStandardSmooth R S where
  out := ⟨_, _, _, inferInstance, ⟨SubmersivePresentation.localizationAway S r⟩⟩

lemma IsStandardSmoothOfRelativeDimension.localization_away (r : R) [IsLocalization.Away r S] :
    IsStandardSmoothOfRelativeDimension 0 R S where
  out := ⟨_, _, _, inferInstance, SubmersivePresentation.localizationAway S r,
    Presentation.localizationAway_dimension_zero r⟩

section BaseChange

variable (T) [CommRing T] [Algebra R T]

-- INSTANCE (free from Core): IsStandardSmooth.baseChange

-- INSTANCE (free from Core): IsStandardSmoothOfRelativeDimension.baseChange

end BaseChange
