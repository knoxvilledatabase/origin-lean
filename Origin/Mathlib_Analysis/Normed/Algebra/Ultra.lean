/-
Extracted from Analysis/Normed/Algebra/Ultra.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Normed algebra preserves ultrametricity

This file contains the proof that a normed division ring over an ultrametric field is ultrametric.
-/

variable {K L : Type*} [NormedField K]

variable (L) in

theorem IsUltrametricDist.of_normedAlgebra' [SeminormedRing L] [NormOneClass L] [NormedAlgebra K L]
    [h : IsUltrametricDist L] : IsUltrametricDist K :=
  ⟨fun x y z => by
    simpa using h.dist_triangle_max (algebraMap K L x) (algebraMap K L y) (algebraMap K L z)⟩

variable (K) in

theorem IsUltrametricDist.of_normedAlgebra [NormedDivisionRing L] [NormedAlgebra K L]
    [h : IsUltrametricDist K] : IsUltrametricDist L := by
  rw [isUltrametricDist_iff_forall_norm_natCast_le_one] at h ⊢
  exact fun n => (algebraMap.coe_natCast (R := K) (A := L) n) ▸ norm_algebraMap' L (n : K) ▸ h n

variable (K L) in

theorem IsUltrametricDist.normedAlgebra_iff [NormedDivisionRing L] [NormedAlgebra K L] :
    IsUltrametricDist L ↔ IsUltrametricDist K :=
  ⟨fun _ => IsUltrametricDist.of_normedAlgebra' L, fun _ => IsUltrametricDist.of_normedAlgebra K⟩
