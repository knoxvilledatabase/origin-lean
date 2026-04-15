/-
Extracted from Algebra/Homology/Embedding/AreComplementary.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Complementary embeddings

Given two embeddings `e₁ : c₁.Embedding c` and `e₂ : c₂.Embedding c`
of complex shapes, we introduce a property `e₁.AreComplementary e₂`
saying that the image subsets of the indices of `c₁` and `c₂` form
a partition of the indices of `c`.

If `e₁.IsTruncLE` and `e₂.IsTruncGE`, and `K : HomologicalComplex C c`,
we construct a quasi-isomorphism `shortComplexTruncLEX₃ToTruncGE` between
the cokernel of `K.ιTruncLE e₁ : K.truncLE e₁ ⟶ K` and `K.truncGE e₂`.

-/

open CategoryTheory Limits

variable {ι ι₁ ι₂ : Type*} {c : ComplexShape ι} {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

namespace ComplexShape

namespace Embedding

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (e₁ : Embedding c₁ c) (e₂ : Embedding c₂ c)

structure AreComplementary : Prop where
  disjoint (i₁ : ι₁) (i₂ : ι₂) : e₁.f i₁ ≠ e₂.f i₂
  union (i : ι) : (∃ i₁, e₁.f i₁ = i) ∨ ∃ i₂, e₂.f i₂ = i

variable {e₁ e₂}

namespace AreComplementary

variable (ac : AreComplementary e₁ e₂)

include ac

lemma symm : AreComplementary e₂ e₁ where
  disjoint i₂ i₁ := (ac.disjoint i₁ i₂).symm
  union i := (ac.union i).symm

lemma exists_i₁ (i : ι) (hi : ∀ i₂, e₂.f i₂ ≠ i) :
    ∃ i₁, i = e₁.f i₁ := by
  obtain ⟨i₁, rfl⟩ | ⟨i₂, rfl⟩ := ac.union i
  · exact ⟨_, rfl⟩
  · exfalso
    exact hi i₂ rfl

lemma exists_i₂ (i : ι) (hi : ∀ i₁, e₁.f i₁ ≠ i) :
    ∃ i₂, i = e₂.f i₂ :=
  ac.symm.exists_i₁ i hi

variable (e₁ e₂) in
