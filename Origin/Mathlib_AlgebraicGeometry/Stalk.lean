/-
Extracted from AlgebraicGeometry/Stalk.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Stalks of a Scheme

## Main definitions and results

- `AlgebraicGeometry.Scheme.fromSpecStalk`: The canonical morphism `Spec 𝒪_{X, x} ⟶ X`.
- `AlgebraicGeometry.Scheme.range_fromSpecStalk`: The range of the map `Spec 𝒪_{X, x} ⟶ X` is
  exactly the `y`s that specialize to `x`.
- `AlgebraicGeometry.SpecToEquivOfLocalRing`:
  Given a local ring `R` and scheme `X`, morphisms `Spec R ⟶ X` corresponds to pairs
  `(x, f)` where `x : X` and `f : 𝒪_{X, x} ⟶ R` is a local ring homomorphism.
-/

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace IsLocalRing

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)

section fromSpecStalk

noncomputable def IsAffineOpen.fromSpecStalk
    {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  Spec.map (X.presheaf.germ _ x hxU) ≫ hU.fromSpec

set_option backward.isDefEq.respectTransparency false in

theorem IsAffineOpen.fromSpecStalk_eq (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    hU.fromSpecStalk hxU = hV.fromSpecStalk hxV := by
  obtain ⟨U', h₁, h₂, h₃ : U' ≤ U ⊓ V⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  transitivity fromSpecStalk h₁ h₂
  · delta fromSpecStalk
    rw [← hU.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_left).op]
    erw [← Scheme.Spec_map (X.presheaf.map _).op, ← Scheme.Spec_map (X.presheaf.germ _ x h₂).op]
    rw [← Functor.map_comp_assoc, ← op_comp, TopCat.Presheaf.germ_res, Scheme.Spec_map,
      Quiver.Hom.unop_op]
  · delta fromSpecStalk
    rw [← hV.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_right).op]
    erw [← Scheme.Spec_map (X.presheaf.map _).op, ← Scheme.Spec_map (X.presheaf.germ _ x h₂).op]
    rw [← Functor.map_comp_assoc, ← op_comp, TopCat.Presheaf.germ_res, Scheme.Spec_map,
      Quiver.Hom.unop_op]

noncomputable def Scheme.fromSpecStalk (X : Scheme) (x : X) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  (isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))).fromSpecStalk
    (X.affineCover.covers x)
