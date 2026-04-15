/-
Extracted from CategoryTheory/Sites/LocallyFullyFaithful.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Locally fully faithful functors into sites

## Main results

- `CategoryTheory.Functor.IsLocallyFull`:
  A functor `G : C ⥤ D` is locally full w.r.t. a topology on `D` if for every
  `f : G.obj U ⟶ G.obj V`, the set of `G.map fᵢ : G.obj Wᵢ ⟶ G.obj U` such that `G.map fᵢ ≫ f` is
  in the image of `G` is a coverage of the topology on `D`.
- `CategoryTheory.Functor.IsLocallyFaithful`:
  A functor `G : C ⥤ D` is locally faithful w.r.t. a topology on `D` if for every `f₁ f₂ : U ⟶ V`
  whose images in `D` are equal, the set of `G.map gᵢ : G.obj Wᵢ ⟶ G.obj U` such that
  `gᵢ ≫ f₁ = gᵢ ≫ f₂` is a coverage of the topology on `D`.

## References

* [caramello2020]: Olivia Caramello, *Denseness conditions, morphisms and equivalences of toposes*

-/

universe w vC vD uC uD

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (G : C ⥤ D)

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

def Functor.imageSieve {U V : C} (f : G.obj U ⟶ G.obj V) : Sieve U where
  arrows _ i := ∃ l, G.map l = G.map i ≫ f
  downward_closed := by
    rintro Y₁ Y₂ i₁ ⟨l, hl⟩ i₂
    exact ⟨i₂ ≫ l, by simp [hl]⟩
