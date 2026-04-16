/-
Extracted from Analysis/Complex/IntegerCompl.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

noncomputable section

/-!
# Integer Complement

We define the complement of the integers in the complex plane and give some basic lemmas about it.
We also show that the upper half plane embeds into the integer complement.

-/

open UpperHalfPlane

def Complex.integerComplement := (Set.range ((↑) : ℤ → ℂ))ᶜ

namespace Complex

local notation "ℂ_ℤ " => integerComplement

lemma UpperHalfPlane.coe_mem_integerComplement (z : ℍ) : ↑z ∈ ℂ_ℤ :=
  not_exists.mpr fun x hx ↦ ne_int z x hx.symm

lemma integerComplement.add_coe_int_mem {x : ℂ} (a : ℤ) : x + (a : ℂ) ∈ ℂ_ℤ ↔ x ∈ ℂ_ℤ := by
  simp only [mem_iff, not_iff_not]
  exact ⟨(Exists.elim · fun n hn ↦ ⟨n - a, by simp [hn]⟩),
    (Exists.elim · fun n hn ↦ ⟨n + a, by simp [hn]⟩)⟩

lemma integerComplement.ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) : x ≠ 0 :=
  fun hx' ↦ hx ⟨0, by exact_mod_cast hx'.symm⟩

lemma integerComplement_add_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) (a : ℤ) : x + (a : ℂ)  ≠ 0 :=
  integerComplement.ne_zero ((integerComplement.add_coe_int_mem a).mpr hx)

lemma integerComplement.ne_one {x : ℂ} (hx : x ∈ ℂ_ℤ): x ≠ 1 :=
  fun hx' ↦ hx ⟨1, by exact_mod_cast hx'.symm⟩

end Complex
