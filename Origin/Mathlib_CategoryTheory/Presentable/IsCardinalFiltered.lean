/-
Extracted from CategoryTheory/Presentable/IsCardinalFiltered.lean
Genuine: 10 of 10 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # κ-filtered category

If `κ` is a regular cardinal, we introduce the notion of `κ`-filtered
category `J`: it means that any functor `A ⥤ J` from a small category such
that `Arrow A` is of cardinality `< κ` admits a cocone.
This generalizes the notion of filtered category.
Indeed, we obtain the equivalence `IsCardinalFiltered J ℵ₀ ↔ IsFiltered J`.
The API is mostly parallel to that of filtered categories.

A preordered type `J` is a `κ`-filtered category (i.e. `κ`-directed set)
if any subset of `J` of cardinality `< κ` has an upper bound.

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

universe w v' v u' u

namespace CategoryTheory

open Limits Opposite

class IsCardinalFiltered (J : Type u) [Category.{v} J]
    (κ : Cardinal.{w}) [Fact κ.IsRegular] : Prop where
  nonempty_cocone {A : Type w} [SmallCategory A] (F : A ⥤ J)
    (hA : HasCardinalLT (Arrow A) κ) : Nonempty (Cocone F)

lemma hasCardinalLT_arrow_walkingParallelFamily {T : Type u}
    {κ : Cardinal.{w}} (hT : HasCardinalLT T κ) (hκ : Cardinal.aleph0 ≤ κ) :
    HasCardinalLT (Arrow (WalkingParallelFamily T)) κ := by
  simpa only [hasCardinalLT_iff_of_equiv (WalkingParallelFamily.arrowEquiv T),
    hasCardinalLT_option_iff _ _ hκ] using hT

namespace IsCardinalFiltered

variable {J : Type u} [Category.{v} J] {κ : Cardinal.{w}} [hκ : Fact κ.IsRegular]
  [IsCardinalFiltered J κ]

noncomputable def cocone {A : Type v'} [Category.{u'} A]
    (F : A ⥤ J) (hA : HasCardinalLT (Arrow A) κ) :
    Cocone F := by
  have := hA.small
  have := small_of_small_arrow.{w} A
  have := locallySmall_of_small_arrow.{w} A
  let e := (Shrink.equivalence.{w} A).trans (ShrinkHoms.equivalence.{w} (Shrink.{w} A))
  exact (Cocone.equivalenceOfReindexing e.symm (Iso.refl _)).inverse.obj
    (nonempty_cocone (κ := κ) (e.inverse ⋙ F) (by simpa)).some

variable (J) in

lemma of_le {κ' : Cardinal.{w}} [Fact κ'.IsRegular] (h : κ' ≤ κ) :
    IsCardinalFiltered J κ' where
  nonempty_cocone F hA := ⟨cocone F (hA.of_le h)⟩

variable (κ) in

lemma of_equivalence {J' : Type u'} [Category.{v'} J'] (e : J ≌ J') :
    IsCardinalFiltered J' κ where
  nonempty_cocone F hA := ⟨e.inverse.mapCoconeInv (cocone (F ⋙ e.inverse) hA)⟩

section max

variable {K : Type u'} (S : K → J) (hS : HasCardinalLT K κ)

noncomputable def max : J :=
  (cocone (κ := κ) (Discrete.functor S) (by simpa using hS)).pt

noncomputable def toMax (k : K) :
    S k ⟶ max S hS :=
  (cocone (κ := κ) (Discrete.functor S) (by simpa using hS)).ι.app ⟨k⟩

end max

section coeq

variable {K : Type v'} {j j' : J} (f : K → (j ⟶ j')) (hK : HasCardinalLT K κ)

noncomputable def coeq : J :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).pt

noncomputable def coeqHom : j' ⟶ coeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .one

noncomputable def toCoeq : j ⟶ coeq f hK :=
  (cocone (parallelFamily f)
    (hasCardinalLT_arrow_walkingParallelFamily hK hκ.out.aleph0_le)).ι.app .zero
