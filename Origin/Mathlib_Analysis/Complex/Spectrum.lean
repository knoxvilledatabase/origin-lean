/-
Extracted from Analysis/Complex/Spectrum.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Some lemmas on the spectrum and quasispectrum of elements and positivity on `ℂ`
-/

namespace SpectrumRestricts

variable {A : Type*} [Ring A]

set_option backward.isDefEq.respectTransparency false in

end SpectrumRestricts

namespace QuasispectrumRestricts

local notation "σₙ" => quasispectrum

variable {A : Type*} [NonUnitalRing A]

set_option backward.isDefEq.respectTransparency false in

lemma real_iff [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] {a : A} :
    QuasispectrumRestricts a Complex.reCLM ↔ ∀ x ∈ σₙ ℂ a, x = x.re := by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr,
    Unitization.quasispectrum_eq_spectrum_inr' _ ℂ, SpectrumRestricts.real_iff]

end QuasispectrumRestricts
