/-
Extracted from CategoryTheory/Galois/EssSurj.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Essential surjectivity of fiber functors

Let `F : C ⥤ FintypeCat` be a fiber functor of a Galois category `C` and denote by
`H` the induced functor `C ⥤ Action FintypeCat (Aut F)`.

In this file we show that the essential image of `H` consists of the finite `Aut F`-sets where
the `Aut F` action is continuous.

## Main results

- `exists_lift_of_quotient_openSubgroup`: If `U` is an open subgroup of `Aut F`, then
  there exists an object `X` such that `F.obj X` is isomorphic to `Aut F ⧸ U` as
  `Aut F`-sets.
- `exists_lift_of_continuous`: If `X` is a finite, discrete `Aut F`-set, then
  there exists an object `A` such that `F.obj A` is isomorphic to `X` as
  `Aut F`-sets.

## Strategy

We first show that every finite, discrete `Aut F`-set `Y` has a decomposition into connected
components and each connected component is of the form `Aut F ⧸ U` for an open subgroup `U`.
Since `H` preserves finite coproducts, it hence suffices to treat the case `Y = Aut F ⧸ U`.
For the case `Y = Aut F ⧸ U` we closely follow the second part of Stacks Project Tag 0BN4.

-/

noncomputable section

universe u₁ u₂

namespace CategoryTheory

namespace PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] {F : C ⥤ FintypeCat.{u₁}}

open Limits Functor

variable [GaloisCategory C] [FiberFunctor F]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

set_option backward.privateInPublic true in

-- INSTANCE (free from Core): fintypeQuotient

set_option backward.privateInPublic true in

-- INSTANCE (free from Core): fintypeQuotientStabilizer

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

lemma has_decomp_quotients (X : Action FintypeCat G)
    [TopologicalSpace X.V] [DiscreteTopology X.V] [ContinuousSMul G X.V] :
    ∃ (ι : Type) (_ : Finite ι) (f : ι → OpenSubgroup (G)),
      Nonempty ((∐ fun i ↦ G ⧸ₐ (f i).toSubgroup) ≅ X) := by
  obtain ⟨ι, hf, f, u, hc⟩ := has_decomp_connected_components' X
  letI (i : ι) : TopologicalSpace (f i).V := ⊥
  haveI (i : ι) : DiscreteTopology (f i).V := ⟨rfl⟩
  have (i : ι) : ContinuousSMul G (f i).V := ContinuousSMul.mk <| by
    let r : f i ⟶ X := Sigma.ι f i ≫ u.hom
    let r'' (p : G × (f i).V) : G × X.V := (p.1, r.hom p.2)
    let q (p : G × X.V) : X.V := (X.ρ p.1).hom p.2
    let q' (p : G × (f i).V) : (f i).V := ((f i).ρ p.1).hom p.2
    have heq : q ∘ r'' = r.hom ∘ q' := by
      ext (p : G × (f i).V)
      exact (ConcreteCategory.congr_hom (r.comm p.1) p.2).symm
    have hrinj : Function.Injective r.hom :=
      (ConcreteCategory.mono_iff_injective_of_preservesPullback r).mp <| mono_comp _ _
    let t₁ : TopologicalSpace (G × (f i).V) := inferInstance
    change @Continuous _ _ _ ⊥ q'
    have : TopologicalSpace.induced r.hom inferInstance = ⊥ := by
      rw [← le_bot_iff]
      exact fun s _ ↦ ⟨r.hom '' s, ⟨isOpen_discrete (r.hom '' s), Set.preimage_image_eq s hrinj⟩⟩
    rw [← this, continuous_induced_rng, ← heq]
    exact Continuous.comp continuous_smul (by fun_prop)
  have (i : ι) : ∃ (U : OpenSubgroup (G)), (Nonempty ((f i) ≅ G ⧸ₐ U.toSubgroup)) := by
    obtain ⟨(x : (f i).V)⟩ := nonempty_fiber_of_isConnected (forget₂ _ _) (f i)
    let U : OpenSubgroup (G) := ⟨MulAction.stabilizer (G) x, stabilizer_isOpen (G) x⟩
    exact ⟨U, ⟨FintypeCat.isoQuotientStabilizerOfIsConnected (f i) x⟩⟩
  choose g ui using this
  exact ⟨ι, hf, g, ⟨(Sigma.mapIso (fun i ↦ (ui i).some)).symm ≪≫ u⟩⟩

set_option backward.isDefEq.respectTransparency false in

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

def fiberIsoQuotientStabilizer (X : C) [IsConnected X] (x : F.obj X) :
    (functorToAction F).obj X ≅ Aut F ⧸ₐ MulAction.stabilizer (Aut F) x :=
  haveI : IsConnected ((functorToAction F).obj X) := PreservesIsConnected.preserves
  letI : Fintype (Aut F ⧸ MulAction.stabilizer (Aut F) x) := fintypeQuotientStabilizer x
  FintypeCat.isoQuotientStabilizerOfIsConnected ((functorToAction F).obj X) x

open Action.FintypeCat

variable (V : OpenSubgroup (Aut F)) {U : OpenSubgroup (Aut F)}
  (h : Subgroup.Normal U.toSubgroup) {A : C} (u : (functorToAction F).obj A ≅ Aut F ⧸ₐ U.toSubgroup)

private def quotientToEndObjectHom :
    V.toSubgroup ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup →* End A :=
  let ff : (functorToAction F).FullyFaithful := FullyFaithful.ofFullyFaithful (functorToAction F)
  let e : End A ≃* End (Aut F ⧸ₐ U.toSubgroup) := (ff.mulEquivEnd A).trans (Iso.conj u)
  e.symm.toMonoidHom.comp (quotientToEndHom V.toSubgroup U.toSubgroup)

private lemma functorToAction_map_quotientToEndObjectHom
    (m : SingleObj.star (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup) ⟶
      SingleObj.star (V ⧸ Subgroup.subgroupOf U.toSubgroup V.toSubgroup)) :
    (functorToAction F).map (quotientToEndObjectHom V h u m) =
      u.hom ≫ quotientToEndHom V.toSubgroup U.toSubgroup m ≫ u.inv := by
  simp [← cancel_epi u.inv, ← cancel_mono u.hom, ← Iso.conj_apply, quotientToEndObjectHom]
