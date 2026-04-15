/-
Extracted from CategoryTheory/Adjunction/FullyFaithful.lean
Genuine: 2 of 10 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Adjoints of fully faithful functors

A left adjoint is
* faithful, if and only if the unit is a monomorphism
* full, if and only if the unit is a split epimorphism
* fully faithful, if and only if the unit is an isomorphism

A right adjoint is
* faithful, if and only if the counit is an epimorphism
* full, if and only if the counit is a split monomorphism
* fully faithful, if and only if the counit is an isomorphism

This is Lemma 4.5.13 in Riehl's *Category Theory in Context* [riehl2017].
See also https://stacks.math.columbia.edu/tag/07RB for the statements about fully faithful functors.

In the file `Mathlib/CategoryTheory/Monad/Adjunction.lean`, we prove that in fact, if there exists
an isomorphism `L ⋙ R ≅ 𝟭 C`, then the unit is an isomorphism, and similarly for the counit.
See `CategoryTheory.Adjunction.isIso_unit_of_iso` and
`CategoryTheory.Adjunction.isIso_counit_of_iso`.
-/

open CategoryTheory

namespace CategoryTheory.Adjunction

universe v₁ v₂ u₁ u₂

open Category Functor

open Opposite

attribute [local simp] Adjunction.homEquiv_unit Adjunction.homEquiv_counit

variable {C : Type u₁} [Category.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

variable {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R)

attribute [local simp] homEquiv_unit homEquiv_counit

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): unit_mono_of_L_faithful

set_option backward.isDefEq.respectTransparency false in

noncomputable def unitSplitEpiOfLFull [L.Full] (X : C) : SplitEpi (h.unit.app X) where
  section_ := L.preimage (h.counit.app (L.obj X))
  id := by simp [← h.unit_naturality (L.preimage (h.counit.app (L.obj X)))]

-- INSTANCE (free from Core): unit_isSplitEpi_of_L_full

-- INSTANCE (free from Core): [L.Full]

-- INSTANCE (free from Core): unit_isIso_of_L_fully_faithful

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): counit_epi_of_R_faithful

set_option backward.isDefEq.respectTransparency false in

noncomputable def counitSplitMonoOfRFull [R.Full] (X : D) : SplitMono (h.counit.app X) where
  retraction := R.preimage (h.unit.app (R.obj X))
  id := by simp [← h.counit_naturality (R.preimage (h.unit.app (R.obj X)))]

-- INSTANCE (free from Core): counit_isSplitMono_of_R_full

-- INSTANCE (free from Core): [R.Full]

-- INSTANCE (free from Core): counit_isIso_of_R_fully_faithful
