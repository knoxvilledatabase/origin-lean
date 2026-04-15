/-
Extracted from Algebra/Module/LocalizedModule/Basic.lean
Genuine: 7 of 8 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Localized Module

Given a commutative semiring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.

## Main definitions

* `LocalizedModule.r`: the equivalence relation defining this localization, namely
  `(m, s) ≈ (m', s')` if and only if there is some `u : S` such that `u • s' • m = u • s • m'`.
* `LocalizedModule M S`: the localized module by `S`.
* `LocalizedModule.mk`: the canonical map sending `(m, s) : M × S ↦ m/s : LocalizedModule M S`
* `LocalizedModule.liftOn`: any well-defined function `f : M × S → α` respecting `r` descents to
  a function `LocalizedModule M S → α`
* `LocalizedModule.liftOn₂`: any well-defined function `f : M × S → M × S → α` respecting `r`
  descents to a function `LocalizedModule M S → LocalizedModule M S`
* `LocalizedModule.mk_add_mk`: in the localized module
  `mk m s + mk m' s' = mk (s' • m + s • m') (s * s')`
* `LocalizedModule.mk_smul_mk` : in the localized module, for any `r : R`, `s t : S`, `m : M`,
  we have `mk r s • mk m t = mk (r • m) (s * t)` where `mk r s : Localization S` is localized ring
  by `S`.
* `LocalizedModule.isModule` : `LocalizedModule M S` is a `Localization S`-module.

## Future work

* Redefine `Localization` for monoids and rings to coincide with `LocalizedModule`.
-/

open Module

namespace LocalizedModule

universe u v

variable {R : Type u} [CommSemiring R] (S : Submonoid R)

variable (M : Type v) [AddCommMonoid M] [Module R M]

variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]

def r (a b : M × S) : Prop :=
  ∃ u : S, u • b.2 • a.1 = u • a.2 • b.1

lemma oreEqv_eq_r : (OreLocalization.oreEqv S M).r = r S M := by
  ext a b
  constructor
  · rintro ⟨u, v, h₁, h₂⟩
    use u
    simp only [Submonoid.smul_def, smul_smul, h₂]
    rw [mul_comm, mul_smul, ← h₁, mul_comm, mul_smul, Submonoid.smul_def]
  · rintro ⟨u, hu⟩
    use u * a.2, u * b.2
    rw [mul_smul, ← hu, mul_smul, Submonoid.coe_mul, mul_assoc, mul_assoc, mul_comm (a.2 : R)]
    simp [Submonoid.smul_def]

theorem r.isEquiv : IsEquiv _ (r S M) :=
  { refl := fun ⟨m, s⟩ => ⟨1, by rw [one_smul]⟩
    trans := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ => by
      use u1 * u2 * s2
      -- Put everything in the same shape, sorting the terms using `simp`
      have hu1' := congr_arg ((u2 * s3) • ·) hu1.symm
      have hu2' := congr_arg ((u1 * s1) • ·) hu2.symm
      simp only [← mul_smul, mul_comm, mul_left_comm] at hu1' hu2' ⊢
      rw [hu2', hu1']
    symm := fun ⟨_, _⟩ ⟨_, _⟩ ⟨u, hu⟩ => ⟨u, hu.symm⟩ }

-- INSTANCE (free from Core): r.setoid

abbrev _root_.LocalizedModule : Type max u v :=
  OreLocalization S M

private lemma example_localization_eq_localizedModule
    {R} [CommSemiring R] (S : Submonoid R) : Localization S = LocalizedModule S R := by
  with_reducible rfl

variable {M S}

abbrev mk (m : M) (s : S) : LocalizedModule S M := m /ₒ s

theorem mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔ ∃ u : S, u • s' • m = u • s • m' := by
  rw [mk, mk, OreLocalization.oreDiv_eq_iff]
  exact congr($(oreEqv_eq_r S M) ⟨m, s⟩ ⟨m', s'⟩)
