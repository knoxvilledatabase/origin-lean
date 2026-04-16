/-
Extracted from RingTheory/UniqueFactorizationDomain/GCDMonoid.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.RingTheory.UniqueFactorizationDomain.FactorSet
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

noncomputable section

/-!
# Building GCD out of unique factorization

## Main results
* `UniqueFactorizationMonoid.toGCDMonoid`: choose a GCD monoid structure given unique factorization.
-/

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

section

open Associates UniqueFactorizationMonoid

noncomputable def UniqueFactorizationMonoid.toNormalizedGCDMonoid (α : Type*)
    [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] [NormalizationMonoid α] :
    NormalizedGCDMonoid α :=
  { ‹NormalizationMonoid α› with
    gcd := fun a b => (Associates.mk a ⊓ Associates.mk b).out
    lcm := fun a b => (Associates.mk a ⊔ Associates.mk b).out
    gcd_dvd_left := fun a b => (out_dvd_iff a (Associates.mk a ⊓ Associates.mk b)).2 <| inf_le_left
    gcd_dvd_right := fun a b =>
      (out_dvd_iff b (Associates.mk a ⊓ Associates.mk b)).2 <| inf_le_right
    dvd_gcd := fun {a} {b} {c} hac hab =>
      show a ∣ (Associates.mk c ⊓ Associates.mk b).out by
        rw [dvd_out_iff, le_inf_iff, mk_le_mk_iff_dvd, mk_le_mk_iff_dvd]
        exact ⟨hac, hab⟩
    lcm_zero_left := fun a => show (⊤ ⊔ Associates.mk a).out = 0 by simp
    lcm_zero_right := fun a => show (Associates.mk a ⊔ ⊤).out = 0 by simp
    gcd_mul_lcm := fun a b => by
      rw [← out_mul, mul_comm, sup_mul_inf, mk_mul_mk, out_mk]
      exact normalize_associated (a * b)
    normalize_gcd := fun a b => by apply normalize_out _
    normalize_lcm := fun a b => by apply normalize_out _ }

instance (α) [CancelCommMonoidWithZero α] [UniqueFactorizationMonoid α] :
    Nonempty (NormalizedGCDMonoid α) := by
  letI := UniqueFactorizationMonoid.normalizationMonoid (α := α)
  classical exact ⟨UniqueFactorizationMonoid.toNormalizedGCDMonoid α⟩

end
