/-
Extracted from RepresentationTheory/Homological/GroupCohomology/Shapiro.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Shapiro's lemma for group cohomology

Given a commutative ring `k` and a subgroup `S ≤ G`, the file
`Mathlib/RepresentationTheory/Coinduced.lean` proves that the functor
`Coind_S^G : Rep k S ⥤ Rep k G` preserves epimorphisms. Since `Res(S) : Rep k G ⥤ Rep k S` is left
adjoint to `Coind_S^G`, this means `Res(S)` preserves projective objects. Since `Res(S)` is also
exact, given a projective resolution `P` of `k` as a trivial `k`-linear `G`-representation,
`Res(S)(P)` is a projective resolution of `k` as a trivial `k`-linear `S`-representation.

Since `Hom(Res(S)(P), A) ≅ Hom(P, Coind_S^G(A))` for any `S`-representation `A`, we conclude
Shapiro's lemma for group cohomology: `Hⁿ(G, Coind_S^G(A)) ≅ Hⁿ(S, A)` for all `n`.

## Main definitions

* `groupCohomology.coindIso A n`: Shapiro's lemma for group cohomology: an isomorphism
  `Hⁿ(G, Coind_S^G(A)) ≅ Hⁿ(S, A)`, given a subgroup `S ≤ G` and an `S`-representation `A`.

!-/

universe u

namespace groupCohomology

open CategoryTheory Finsupp TensorProduct Rep

variable {k G : Type u} [CommRing k] [Group G] {S : Subgroup G} (A : Rep k S)

set_option backward.isDefEq.respectTransparency false in

noncomputable def linearYonedaObjResProjectiveResolutionIso
    (P : ProjectiveResolution (trivial k G k)) (A : Rep.{u} k S) :
    ((resFunctor S.subtype).mapProjectiveResolution P).complex.linearYonedaObj k A ≅
      P.complex.linearYonedaObj k (coind S.subtype A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ ↦ (resCoindHomEquiv.{u} _ _ _).toModuleIso) fun _ _ _ ↦
      ModuleCat.hom_ext (LinearMap.ext fun f => Rep.hom_ext <| by
        ext; simp [← ModuleCat.ofHom_comp, resCoindHomEquiv, hom_comm_apply])

noncomputable def coindIso (A : Rep k S) (n : ℕ) :
    groupCohomology (coind S.subtype A) n ≅ groupCohomology A n :=
  (HomologicalComplex.homologyFunctor _ _ _).mapIso
    (inhomogeneousCochainsIso (coind S.subtype A) ≪≫
    (linearYonedaObjResProjectiveResolutionIso (barResolution k G) A).symm) ≪≫
  (groupCohomologyIso A n ((resFunctor _).mapProjectiveResolution <| barResolution k G)).symm

end groupCohomology
