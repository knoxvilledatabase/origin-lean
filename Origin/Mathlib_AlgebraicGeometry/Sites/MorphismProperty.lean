/-
Extracted from AlgebraicGeometry/Sites/MorphismProperty.lean
Genuine: 9 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Sites.MorphismProperty

noncomputable section

/-!

# Site defined by a morphism property

Given a multiplicative morphism property `P` that is stable under base change, we define the
associated (pre)topology on the category of schemes, where coverings are given
by jointly surjective families of morphisms satisfying `P`.

## TODO

- Define the small site on `Over P Q X`.

-/

universe v u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme

variable (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [P.RespectsIso]
  [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]

def pretopology : Pretopology Scheme.{u} where
  coverings Y S := ∃ (U : Cover.{u} P Y), S = Presieve.ofArrows U.obj U.map
  has_isos _ _ f _ := ⟨coverOfIsIso f, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨U, rfl⟩
    exact ⟨U.pullbackCover' f, (Presieve.ofArrows_pullback _ _ _).symm⟩
  transitive := by
    rintro X _ T ⟨U, rfl⟩ H
    choose V hV using H
    use U.bind (fun j => V (U.map j) ⟨j⟩)
    simpa only [Cover.bind, ← hV] using Presieve.ofArrows_bind U.obj U.map _
      (fun _ f H => (V f H).obj) (fun _ f H => (V f H).map)

abbrev grothendieckTopology : GrothendieckTopology Scheme.{u} :=
  (pretopology P).toGrothendieck

def surjectiveFamiliesPretopology [IsJointlySurjectivePreserving ⊤] : Pretopology Scheme.{u} where
  coverings X S :=
    ∀ x : X, ∃ (Y : Scheme.{u}) (y : Y) (f : Y ⟶ X) (hf : S f), f.base y = x
  has_isos X Y f hf x := by
    use Y, (inv f).base x, f
    simp [← Scheme.comp_base_apply]
  pullbacks X Y f S hS x := by
    obtain ⟨Z, z, g, hg, hz⟩ := hS (f.base x)
    obtain ⟨w, hw⟩ :=
      IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop (P := ⊤) trivial z x hz
    use pullback g f, w, pullback.snd g f
    simpa [hw] using Presieve.pullbackArrows.mk Z g hg
  transitive X S T hS hT x := by
    obtain ⟨Y, y, f, hf, hy⟩ := hS x
    obtain ⟨Z, z, g, hg, hz⟩ := hT f hf y
    use Z, z, g ≫ f
    simpa [hz, hy] using Presieve.bind_comp f hf hg

lemma pretopology_le_inf [IsJointlySurjectivePreserving ⊤] :
    pretopology P ≤ surjectiveFamiliesPretopology ⊓ P.pretopology := by
  rintro X S ⟨𝒰, rfl⟩
  refine ⟨fun x ↦ ?_, fun ⟨i⟩ ↦ 𝒰.map_prop i⟩
  obtain ⟨a, ha⟩ := 𝒰.covers x
  refine ⟨𝒰.obj (𝒰.f x), a, 𝒰.map (𝒰.f x), ⟨_⟩, ha⟩

lemma grothendieckTopology_eq_inf [IsJointlySurjectivePreserving ⊤] :
    grothendieckTopology P = (surjectiveFamiliesPretopology ⊓ P.pretopology).toGrothendieck := by
  apply le_antisymm ((Pretopology.gi Scheme.{u}).gc.monotone_l (pretopology_le_inf P))
  intro X S ⟨T, ⟨hs, hP⟩, hle⟩
  let _ : Type (u + 1) := Presieve X
  let J := (Y : Scheme.{u}) × (Y ⟶ X)
  choose Y y f hf hy using hs
  let 𝒰 : Cover.{u} P X :=
    { J := X
      obj := Y
      map := f
      f := id
      covers := fun x ↦ ⟨y x, hy x⟩
      map_prop := fun x ↦ hP (hf x)
    }
  refine ⟨Presieve.ofArrows 𝒰.obj 𝒰.map, ⟨𝒰, rfl⟩, ?_⟩
  rintro Z g ⟨x⟩
  exact hle _ (hf x)

variable {P}

lemma pretopology_cover {Y : Scheme.{u}} (𝒰 : Cover.{u} P Y) :
    pretopology P Y (Presieve.ofArrows 𝒰.obj 𝒰.map) :=
  ⟨𝒰, rfl⟩

lemma grothendieckTopology_cover {X : Scheme.{u}} (𝒰 : Cover.{v} P X) :
    grothendieckTopology P X (Sieve.generate (Presieve.ofArrows 𝒰.obj 𝒰.map)) := by
  let 𝒱 : Cover.{u} P X :=
    { J := X
      obj := fun x ↦ 𝒰.obj (𝒰.f x)
      map := fun x ↦ 𝒰.map (𝒰.f x)
      f := id
      covers := 𝒰.covers
      map_prop := fun _ ↦ 𝒰.map_prop _
    }
  refine ⟨_, pretopology_cover 𝒱, ?_⟩
  rintro _ _ ⟨y⟩
  exact ⟨_, 𝟙 _, 𝒰.map (𝒰.f y), ⟨_⟩, by simp⟩

section

variable {Q : MorphismProperty Scheme.{u}} [Q.IsMultiplicative] [Q.RespectsIso]
  [Q.IsStableUnderBaseChange] [IsJointlySurjectivePreserving Q]

lemma pretopology_le_pretopology (hPQ : P ≤ Q) :
    pretopology P ≤ pretopology Q := by
  rintro X - ⟨𝒰, rfl⟩
  use 𝒰.changeProp Q (fun j ↦ hPQ _ (𝒰.map_prop j))
  rfl

lemma grothendieckTopology_le_grothendieckTopology (hPQ : P ≤ Q) :
    grothendieckTopology P ≤ grothendieckTopology Q :=
  (Pretopology.gi Scheme.{u}).gc.monotone_l (pretopology_le_pretopology hPQ)

end

end AlgebraicGeometry.Scheme
