/-
Extracted from RingTheory/Ideal/Quotient/PowTransition.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The quotient map from `R ⧸ I ^ m` to `R ⧸ I ^ n` where `m ≥ n`

In this file we define the canonical quotient linear map from
`M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` and canonical quotient ring map from
`R ⧸ I ^ m` to `R ⧸ I ^ n`. These definitions will be used in theorems
related to `IsAdicComplete` to find a lift element from compatible sequences in the quotients.
We also include results about the relation between quotients of submodules and quotients of
ideals here.

## Main definitions
- `Submodule.factorPow`: the linear map from `M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` induced by
  the natural inclusion `I ^ n • ⊤ → I ^ m • ⊤`.
- `Ideal.Quotient.factorPow`: the ring homomorphism from `R ⧸ I ^ m`
  to `R ⧸ I ^ n` induced by the natural inclusion `I ^ n → I ^ m`.

## Main results
-/

open Ideal Quotient

variable {R : Type*} [Ring R] {I J K : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M]

lemma Ideal.Quotient.factor_ker (H : I ≤ J) [I.IsTwoSided] [J.IsTwoSided] :
    RingHom.ker (factor H) = J.map (Ideal.Quotient.mk I) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Ideal.Quotient.mk_surjective x with ⟨r, hr⟩
    rw [← hr] at h ⊢
    simp only [factor, RingHom.mem_ker, lift_mk, eq_zero_iff_mem] at h
    exact Ideal.mem_map_of_mem _ h
  · rcases mem_image_of_mem_map_of_surjective _ Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa [← eq, Ideal.Quotient.eq_zero_iff_mem] using hr

lemma Submodule.eq_factor_of_eq_factor_succ {p : ℕ → Submodule R M}
    (hp : Antitone p) (x : (n : ℕ) → M ⧸ (p n)) (h : ∀ m, x m = factor (hp m.le_succ) (x (m + 1)))
    {m n : ℕ} (g : m ≤ n) : x m = factor (hp g) (x n) := by
  have : n = m + (n - m) := (Nat.add_sub_of_le g).symm
  induction hmn : n - m generalizing m n with
  | zero =>
    rw [hmn, Nat.add_zero] at this
    subst this
    simp
  | succ k ih =>
    rw [hmn, ← add_assoc] at this
    subst this
    rw [ih (m.le_add_right k) (by simp), h]
    · simp
    · lia

lemma Ideal.Quotient.eq_factor_of_eq_factor_succ {I : ℕ → Ideal R} [∀ n, (I n).IsTwoSided]
    (hI : Antitone I) (x : (n : ℕ) → R ⧸ (I n)) (h : ∀ m, x m = factor (hI m.le_succ) (x (m + 1)))
    {m n : ℕ} (g : m ≤ n) : x m = factor (hI g) (x n) :=
  Submodule.eq_factor_of_eq_factor_succ hI x h g

lemma Ideal.map_mk_comap_factor [J.IsTwoSided] [K.IsTwoSided] (hIJ : J ≤ I) (hJK : K ≤ J) :
    (I.map (mk J)).comap (factor hJK) = I.map (mk K) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases mem_image_of_mem_map_of_surjective (mk J) Quotient.mk_surjective h with ⟨r, hr, eq⟩
    have : x - ((mk K) r) ∈ J.map (mk K) := by
      simp [← factor_ker hJK, ← eq]
    rcases mem_image_of_mem_map_of_surjective (mk K) Quotient.mk_surjective this with ⟨s, hs, eq'⟩
    rw [← add_sub_cancel ((mk K) r) x, ← eq', ← map_add]
    exact mem_map_of_mem (mk K) (Submodule.add_mem _ hr (hIJ hs))
  · rcases mem_image_of_mem_map_of_surjective (mk K) Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa only [← eq] using mem_map_of_mem (mk J) hr

namespace Submodule

open Submodule
