/-
Extracted from AlgebraicTopology/DoldKan/SplitSimplicialObject.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Split simplicial objects in preadditive categories

In this file we define a functor `nondegComplex : SimplicialObject.Split C ⥤ ChainComplex C ℕ`
when `C` is a preadditive category with finite coproducts, and get an isomorphism
`toKaroubiNondegComplexFunctorIsoN₁ : nondegComplex ⋙ toKaroubi _ ≅ forget C ⋙ DoldKan.N₁`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category CategoryTheory.Preadditive

  CategoryTheory.Idempotents Opposite AlgebraicTopology AlgebraicTopology.DoldKan

  Simplicial DoldKan

namespace SimplicialObject

namespace Splitting

variable {C : Type*} [Category* C] {X : SimplicialObject C}
  (s : Splitting X)

noncomputable def πSummand [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    X.obj Δ ⟶ s.N A.1.unop.len :=
  s.desc Δ (fun B => by
    by_cases h : B = A
    · exact eqToHom (by subst h; rfl)
    · exact 0)

set_option backward.isDefEq.respectTransparency false in
