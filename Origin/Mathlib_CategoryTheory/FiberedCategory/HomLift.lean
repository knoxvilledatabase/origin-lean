/-
Extracted from CategoryTheory/FiberedCategory/HomLift.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# HomLift

Given a functor `p : 𝒳 ⥤ 𝒮`, this file provides API for expressing the fact that `p(φ) = f`
for given morphisms `φ` and `f`. The reason this API is needed is because, in general, `p.map φ = f`
does not make sense when the domain and/or codomain of `φ` and `f` are not definitionally equal.

## Main definition

Given morphism `φ : a ⟶ b` in `𝒳` and `f : R ⟶ S` in `𝒮`, `p.IsHomLift f φ` is a class
which expresses the fact that `f = p(φ)`.

We also define a macro `subst_hom_lift p f φ` which can be used to substitute `f` with `p(φ)` in a
goal, this tactic is just short for `obtain ⟨⟩ := (inferInstance : p.IsHomLift f φ)`, and
it is used to make the code more readable.

## Implementation
The class `IsHomLift` is defined as an inductive with the single constructor
`.map (φ : a ⟶ b) : IsHomLift p (p.map φ) φ`, similar to how `Eq a b` has the single constructor
`.rfl (a : α) : Eq a a`.

-/

universe u₁ v₁ u₂ v₂

open CategoryTheory Category

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒳] [Category.{v₂} 𝒮] (p : 𝒳 ⥤ 𝒮)

namespace CategoryTheory

class inductive Functor.IsHomLift : ∀ {R S : 𝒮} {a b : 𝒳} (_ : R ⟶ S) (_ : a ⟶ b), Prop
  | map {a b : 𝒳} (φ : a ⟶ b) : IsHomLift (p.map φ) φ

macro "subst_hom_lift" p:term:max f:term:max φ:term:max : tactic =>

  `(tactic| obtain ⟨⟩ := (inferInstance : Functor.IsHomLift $p $f $φ))

namespace IsHomLift
