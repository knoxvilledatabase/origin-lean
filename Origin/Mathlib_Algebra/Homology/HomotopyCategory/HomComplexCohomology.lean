/-
Extracted from Algebra/Homology/HomotopyCategory/HomComplexCohomology.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Cohomology of the hom complex

Given `ℤ`-indexed cochain complexes `K` and `L`, and `n : ℤ`, we introduce
a type `HomComplex.CohomologyClass K L n` which is the quotient
of `HomComplex.Cocycle K L n` which identifies cohomologous cocycles.
We construct this type of cohomology classes instead of using
the homology API because `Cochain K L` can be considered both
as a complex of abelian groups or as a complex of `R`-modules
when the category is `R`-linear. This also complements the API
around `HomComplex` which is centered on terms in types
`Cochain` or `Cocycle` which are suitable for computations.

We also show that `HomComplex.CohomologyClass K L n` identifies to
the type of morphisms between `K` and `L⟦n⟧` in the homotopy category.
-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

namespace CochainComplex

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

namespace HomComplex

def coboundaries : AddSubgroup (Cocycle K L n) where
  carrier := setOf (fun α ↦ ∃ (m : ℤ) (hm : m + 1 = n) (β : Cochain K L m), δ m n β = α)
  zero_mem' := ⟨n - 1, by simp, 0, by simp⟩
  add_mem' := by
    rintro α₁ α₂ ⟨m, hm, β₁, hβ₁⟩ ⟨m', hm', β₂, hβ₂⟩
    obtain rfl : m = m' := by lia
    exact ⟨m, hm, β₁ + β₂, by aesop⟩
  neg_mem' := by
    rintro α ⟨m, hm, β, hβ⟩
    exact ⟨m, hm, -β, by aesop⟩

variable {K L n} in

lemma mem_coboundaries_iff (α : Cocycle K L n) (m : ℤ) (hm : m + 1 = n) :
    α ∈ coboundaries K L n ↔ ∃ (β : Cochain K L m), δ m n β = α := by
  simp only [coboundaries, AddSubgroup.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk]
  grind

def CohomologyClass : Type v := Cocycle K L n ⧸ coboundaries K L n

-- INSTANCE (free from Core): :

namespace CohomologyClass

variable {K L n}

def mk (x : Cocycle K L n) : CohomologyClass K L n :=
  Quotient.mk _ x

lemma mk_surjective : Function.Surjective (mk : Cocycle K L n → _) :=
  Quotient.mk_surjective

variable (K L n) in
