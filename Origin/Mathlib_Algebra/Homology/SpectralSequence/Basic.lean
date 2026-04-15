/-
Extracted from Algebra/Homology/SpectralSequence/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Spectral sequences

In this file, we define the category `SpectralSequence C c r₀` of spectral sequences
in an abelian category `C` with `Eᵣ`-pages defined from `r₀ : ℤ` having differentials
given by complex shapes `c : ℤ → ComplexShape κ`, where `κ` is the index type
for the objects on each page (e.g. `κ := ℤ × ℤ` or `κ := ℕ × ℕ`).
A spectral sequence is defined as the data of a sequence of homological complexes
(the pages) and a sequence of isomorphisms between the homology of a page and the
next page.

-/

namespace CategoryTheory

open Category Limits

variable (C : Type*) [Category C] [Abelian C]
  {κ : Type*} (c : ℤ → ComplexShape κ) (r₀ : ℤ)

structure SpectralSequence where
  /-- the `r`th page of a spectral sequence is an homological complex -/
  page (r : ℤ) (hr : r₀ ≤ r := by lia) : HomologicalComplex C (c r)
  /-- the isomorphism between the homology of the `r`-th page at an object `pq : κ`
  and the corresponding object on the next page -/
  iso (r r' : ℤ) (pq : κ) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    (page r).homology pq ≅ (page r').X pq

namespace SpectralSequence

variable {C c r₀}
