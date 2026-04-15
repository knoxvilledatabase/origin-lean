/-
Extracted from CategoryTheory/Generator/HomologicalComplex.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Generators of the category of homological complexes

Let `c : ComplexShape ι` be a complex shape with no loop.
If a category `C` has a separator, then `HomologicalComplex C c`
has a separating family, and a separator when suitable coproducts exist.

-/

universe t w v u

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] {ι : Type w} (c : ComplexShape ι) [c.HasNoLoop]

variable [HasZeroMorphisms C] [HasZeroObject C]

variable {α : Type t} {X : α → C} (hX : ObjectProperty.IsSeparating (.ofObj X))

variable (X) in

noncomputable def separatingFamily (j : α × ι) : HomologicalComplex C c :=
  evalCompCoyonedaCorepresentative c (X j.1) j.2

set_option backward.isDefEq.respectTransparency false in

include hX in

lemma isSeparating_separatingFamily :
    ObjectProperty.IsSeparating (.ofObj (separatingFamily c X)) := by
  intro K L f g h
  ext j
  apply hX
  rintro _ ⟨a⟩ p
  have H := evalCompCoyonedaCorepresentable c (X a) j
  apply H.homEquiv.symm.injective
  simpa only [H.homEquiv_symm_comp] using h _
    (ObjectProperty.ofObj_apply _ ⟨a, j⟩) (H.homEquiv.symm p)

end

variable [HasCoproductsOfShape ι C] [Preadditive C] [HasZeroObject C]

lemma isSeparator_coproduct_separatingFamily {X : C} (hX : IsSeparator X) :
    IsSeparator (∐ (fun i ↦ separatingFamily c (fun (_ : Unit) ↦ X) ⟨⟨⟩, i⟩)) := by
  let φ (i : ι) := separatingFamily c (fun (_ : Unit) ↦ X) ⟨⟨⟩, i⟩
  refine isSeparator_of_isColimit_cofan
    (isSeparating_separatingFamily c (X := fun (_ : Unit) ↦ X) (by simpa using hX))
      (c := Cofan.mk (∐ φ) (fun ⟨_, i⟩ ↦ Sigma.ι φ i)) ?_
  exact IsColimit.ofWhiskerEquivalence
    (Discrete.equivalence (Equiv.punitProd.{0} ι).symm) (coproductIsCoproduct φ)

-- INSTANCE (free from Core): [HasSeparator

end HomologicalComplex
