/-
Extracted from Analysis/Complex/IntegerCompl.lean
Genuine: 3 of 8 | Dissolved: 3 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Integer Complement

We define the complement of the integers in the complex plane and give some basic lemmas about it.
We also show that the upper half plane embeds into the integer complement.

-/

open UpperHalfPlane

def Complex.integerComplement := (Set.range ((↑) : ℤ → ℂ))ᶜ

namespace Complex

local notation "ℂ_ℤ " => integerComplement

lemma integerComplement_eq : ℂ_ℤ = {z : ℂ | ¬ ∃ (n : ℤ), n = z} := rfl

lemma integerComplement.mem_iff {x : ℂ} : x ∈ ℂ_ℤ ↔ ¬ ∃ (n : ℤ), n = x := Iff.rfl

lemma UpperHalfPlane.coe_mem_integerComplement (z : ℍ) : ↑z ∈ ℂ_ℤ :=
  not_exists.mpr fun x hx ↦ ne_int z x hx.symm

lemma integerComplement.add_coe_int_mem {x : ℂ} (a : ℤ) : x + (a : ℂ) ∈ ℂ_ℤ ↔ x ∈ ℂ_ℤ := by
  simp only [mem_iff, not_iff_not]
  exact ⟨(Exists.elim · fun n hn ↦ ⟨n - a, by simp [hn]⟩),
    (Exists.elim · fun n hn ↦ ⟨n + a, by simp [hn]⟩)⟩

-- DISSOLVED: integerComplement.ne_zero

-- DISSOLVED: integerComplement_add_ne_zero

-- DISSOLVED: integerComplement.ne_one

end Complex
