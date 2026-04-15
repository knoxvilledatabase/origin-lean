/-
Extracted from AlgebraicGeometry/Sites/Etale.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# The étale site

In this file we define the big étale site, i.e. the étale topology as a Grothendieck topology
on the category of schemes.

-/

universe v u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme

def etalePrecoverage : Precoverage Scheme.{u} :=
  precoverage @Etale

def etalePretopology : Pretopology Scheme.{u} :=
  pretopology @Etale

abbrev etaleTopology : GrothendieckTopology Scheme.{u} :=
  grothendieckTopology @Etale

lemma zariskiTopology_le_etaleTopology : zariskiTopology ≤ etaleTopology := by
  apply grothendieckTopology_monotone
  intro X Y f hf
  infer_instance

def smallEtaleTopology (X : Scheme.{u}) : GrothendieckTopology X.Etale :=
  X.smallGrothendieckTopology (P := @Etale)

def smallEtalePretopology (X : Scheme.{u}) : Pretopology X.Etale :=
  X.smallPretopology (Q := @Etale) (P := @Etale)

-- INSTANCE (free from Core): {S

set_option backward.isDefEq.respectTransparency false in

noncomputable

def geometricFiber (Ω : Type u) [Field Ω] [IsSepClosed Ω] : etaleTopology.Point where
  fiber := coyoneda.obj ⟨Spec (.of Ω)⟩
  jointly_surjective {S} R hR (f : Spec (.of Ω) ⟶ S) := by
    obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω S).symm.surjective f
    rw [mem_grothendieckTopology_iff] at hR
    obtain ⟨𝒰, hle⟩ := hR
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    refine ⟨𝒰.X i, 𝒰.f i, hle _ _ ⟨i⟩, ?_⟩
    let k := (𝒰.X i).residueField y
    let m : S.residueField (𝒰.f i y) ⟶ (𝒰.X i).residueField y :=
      (𝒰.f i).residueFieldMap y
    algebraize [((𝒰.f i).residueFieldMap y).hom, a.hom]
    let b : (𝒰.X i).residueField y →ₐ[S.residueField (𝒰.f i y)] Ω :=
      IsSepClosed.lift
    have hfac : (𝒰.f i).residueFieldMap y ≫ CommRingCat.ofHom b.toRingHom = a := by
      ext1; exact b.comp_algebraMap
    use Spec.map (CommRingCat.ofHom b.toRingHom) ≫ (𝒰.X i).fromSpecResidueField y
    simp [SpecToEquivOfField, ← hfac]

end AlgebraicGeometry.Scheme
