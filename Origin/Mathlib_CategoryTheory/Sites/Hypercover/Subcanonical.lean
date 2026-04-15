/-
Extracted from CategoryTheory/Sites/Hypercover/Subcanonical.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Covers in subcanonical topologies

In this file we provide API related to covers in subcanonical topologies.
-/

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace GrothendieckTopology.OneHypercover

variable {J : GrothendieckTopology C} [J.Subcanonical]

noncomputable def glueMorphisms {S T : C} (E : J.OneHypercover S) (f : ∀ i, E.X i ⟶ T)
    (h : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.p₁ k ≫ f i = E.p₂ k ≫ f j) :
    S ⟶ T :=
  (E.isStronglySheafFor
    (Subcanonical.isSheaf_of_isRepresentable (CategoryTheory.yoneda.obj T))).amalgamate f h

variable {S T : C} (E : J.OneHypercover S) (f : ∀ i, E.X i ⟶ T)
  (h : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.p₁ k ≫ f i = E.p₂ k ≫ f j)
