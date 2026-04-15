/-
Extracted from AlgebraicGeometry/Sites/MorphismProperty.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Site defined by a morphism property

Given a multiplicative morphism property `P` that is stable under base change, we define the
associated precoverage on the category of schemes, where coverings are given
by jointly surjective families of morphisms satisfying `P`.

-/

universe v u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

namespace Scheme

class IsJointlySurjectivePreserving (P : MorphismProperty Scheme.{u}) where
  exists_preimage_fst_triplet_of_prop {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hg : P g) (x : X) (y : Y) (h : f x = g y) :
    ∃ a : ↑(pullback f g), pullback.fst f g a = x

variable {P : MorphismProperty Scheme.{u}}

lemma IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
    [IsJointlySurjectivePreserving P] {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : P f) (x : X) (y : Y) (h : f x = g y) :
    ∃ a : ↑(pullback f g), pullback.snd f g a = y := by
  let iso := pullbackSymmetry f g
  haveI : HasPullback g f := hasPullback_symmetry f g
  obtain ⟨a, ha⟩ := exists_preimage_fst_triplet_of_prop hf y x h.symm
  use (pullbackSymmetry f g).inv a
  rwa [← Scheme.Hom.comp_apply, pullbackSymmetry_inv_comp_snd]

-- INSTANCE (free from Core): :

abbrev jointlySurjectivePrecoverage : Precoverage Scheme.{u} :=
  Types.jointlySurjectivePrecoverage.comap Scheme.forget

variable (P : MorphismProperty Scheme.{u})

def precoverage : Precoverage Scheme.{u} :=
  jointlySurjectivePrecoverage ⊓ P.precoverage
