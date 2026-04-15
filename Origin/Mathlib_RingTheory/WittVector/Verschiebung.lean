/-
Extracted from RingTheory/WittVector/Verschiebung.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
## The Verschiebung operator

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

namespace WittVector

open MvPolynomial

variable {p : ℕ} {R S : Type*} [CommRing R] [CommRing S]

local notation "𝕎" => WittVector p -- type as `\bbW`

noncomputable section

def verschiebungFun (x : 𝕎 R) : 𝕎 R :=
  @mk' p _ fun n => if n = 0 then 0 else x.coeff (n - 1)

theorem verschiebungFun_coeff (x : 𝕎 R) (n : ℕ) :
    (verschiebungFun x).coeff n = if n = 0 then 0 else x.coeff (n - 1) := by
  simp only [verschiebungFun]

theorem verschiebungFun_coeff_zero (x : 𝕎 R) : (verschiebungFun x).coeff 0 = 0 := by
  rw [verschiebungFun_coeff, if_pos rfl]
