/-
Extracted from RingTheory/DividedPowers/DPMorphism.lean
Genuine: 4 of 5 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-! # Divided power morphisms

Let `A` and `B` be commutative (semi)rings, let `I` be an ideal of `A` and let `J` be an ideal of
`B`. Given divided power structures on `I` and `J`, a ring morphism `A →+* B` is a *divided
power morphism* if it is compatible with these divided power structures.

## Main definitions

* `DividedPowers.IsDPMorphism` : given divided power structures on the `A`-ideal `I` and the
  `B`-ideal `J`, a ring morphism `A →+* B` is a divided power morphism if it is compatible with
  these divided power structures.
* `DividedPowers.DPMorphism` : a bundled version of `IsDPMorphism`.
* `DividedPowers.ideal_from_ringHom` : given a ring homomorphism `A →+* B` and ideals `I ⊆ A` and
  `J ⊆ B` such that `I.map f ≤ J`, this is the `A`-ideal on which
  `f (hI.dpow n x) = hJ.dpow n (f x)`.
* `DividedPowers.DPMorphism.fromGens` : the `DPMorphism` induced by a ring morphism, given that
  divided powers are compatible on a generating set.

## Main results

* `DividedPowers.dpow_eq_from_gens` : if two divided power structures on an ideal `I` agree on a
  generating set, then they are equal.

## Implementation remarks

We provided both a bundled and an unbundled definition of divided power morphisms. For developing
the basic theory, the unbundled version `IsDPMorphism` is more convenient. However, we anticipate
that the bundled version `DPMorphism` will be better for the development of crystalline
cohomology.

## References

* [P. Berthelot, *Cohomologie cristalline des schémas de
  caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus, *Notes on crystalline
  cohomology*][BerthelotOgus-1978]

* [N. Roby, *Lois polynomes et lois formelles en théorie des
  modules*][Roby-1963]

* [N. Roby, *Les algèbres à puissances dividées*][Roby-1965]
-/

open Ideal Set SetLike

namespace DividedPowers

structure IsDPMorphism {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
    (hI : DividedPowers I) (hJ : DividedPowers J) (f : A →+* B) : Prop where
  ideal_comp : I.map f ≤ J
  dpow_comp : ∀ {n : ℕ}, ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a)

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
  (hI : DividedPowers I) (hJ : DividedPowers J)

lemma isDPMorphism_def (f : A →+* B) :
    IsDPMorphism hI hJ f ↔ I.map f ≤ J ∧ ∀ {n}, ∀ a ∈ I, hJ.dpow n (f a) = f (hI.dpow n a) :=
  ⟨fun h ↦ ⟨h.ideal_comp, h.dpow_comp⟩, fun ⟨h1, h2⟩ ↦ IsDPMorphism.mk h1 h2⟩

-- DISSOLVED: isDPMorphism_iff

namespace IsDPMorphism

variable {hI hJ} {C : Type*} [CommSemiring C] {K : Ideal C} (hK : DividedPowers K)

theorem map_dpow {f : A →+* B} (hf : IsDPMorphism hI hJ f) {n : ℕ} {a : A} (ha : a ∈ I) :
    f (hI.dpow n a) = hJ.dpow n (f a) := (hf.2 a ha).symm

theorem comp {f : A →+* B} {g : B →+* C} (hg : IsDPMorphism hJ hK g) (hf : IsDPMorphism hI hJ f) :
    IsDPMorphism hI hK (g.comp f) := by
  refine ⟨le_trans (map_map f g ▸ map_mono hf.1) hg.1, fun a ha ↦ ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← hf.2 a ha, hg.2]
  exact hf.1 (mem_map_of_mem f ha)

end IsDPMorphism
