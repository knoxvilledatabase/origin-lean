/-
Extracted from RingTheory/Valuation/RankOne.lean
Genuine: 8 of 13 | Dissolved: 2 | Infrastructure: 3
-/
import Origin.Core

/-!
# Rank one valuations

We define rank one valuations.

## Main Definitions
* `RankOne` : A valuation has rank one if it is nontrivial and its image (defined as
  `MonoidWithZeroHom.valueGroup₀ v`) is contained in `ℝ≥0`. Note that this class includes the data
  of an inclusion morphism `MonoidWithZeroHom.valueGroup₀ v → ℝ≥0`.
* `RankOne.restrict_RankOne` is the `RankOne` instance for the restriction of a valuation to its
  image, as defined in

## Tags

valuation, rank one
-/

noncomputable section

open Function Multiplicative MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

open scoped NNReal

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

class RankLeOne (v : Valuation R Γ₀) where
  /-- The inclusion morphism from `Γ₀` to `ℝ≥0`. -/
  hom' (v) : ValueGroup₀ v →*₀ ℝ≥0
  strictMono' : StrictMono hom'

class RankOne (v : Valuation R Γ₀) extends RankLeOne v, Valuation.IsNontrivial v

open WithZero

set_option backward.isDefEq.respectTransparency false in

lemma nonempty_rankOne_iff_mulArchimedean {v : Valuation R Γ₀} [v.IsNontrivial] :
    Nonempty v.RankOne ↔ MulArchimedean (ValueGroup₀ v) := by
  constructor
  · intro h
    obtain hv := Nonempty.some h
    exact MulArchimedean.comap hv.hom'.toMonoidHom hv.strictMono'
  · intro _
    obtain ⟨f, hf⟩ :=
      Archimedean.exists_orderAddMonoidHom_real_injective (Additive (ValueGroup₀ v)ˣ)
    let e := AddMonoidHom.toMultiplicativeRight (α := (ValueGroup₀ v)ˣ) (β := ℝ) f
    have he : StrictMono e := by
      simp only [AddMonoidHom.coe_toMultiplicativeRight, AddMonoidHom.coe_coe, e]
      -- toAdd_strictMono is already in an applied form, do defeq abuse instead
      exact StrictMono.comp strictMono_id (f.monotone'.strictMono_of_injective hf)
    let rf : Multiplicative ℝ →* ℝ≥0ˣ := {
      toFun x := Units.mk0 (.mk ((2 : ℝ) ^ (log (M := ℝ) x)) (by positivity)) <| by
        rw [ne_eq, Subtype.ext_iff]
        simp only [NNReal.val_eq_coe, NNReal.coe_mk, NNReal.coe_zero]
        positivity
      map_one' := by simp
      map_mul' _ _ := by
        rw [Units.ext_iff, Subtype.ext_iff]
        simp [log_mul, Real.rpow_add]
      }
    have H : StrictMono (map' (rf.comp e)) := by
      refine map'_strictMono ?_
      intro a b h
      simpa [← Units.val_lt_val, ← NNReal.coe_lt_coe, rf] using he h
    exact ⟨{
      hom' := withZeroUnitsEquiv.toMonoidWithZeroHom.comp <| (map' (rf.comp e)).comp
        withZeroUnitsEquiv.symm.toMonoidWithZeroHom
      strictMono' := withZeroUnitsEquiv_strictMono.comp <| H.comp
        withZeroUnitsEquiv_symm_strictMono
    }⟩

namespace RankOne

variable (v : Valuation R Γ₀) [hv : RankOne v]

abbrev hom := RankLeOne.hom' v

lemma strictMono : StrictMono (hom v) := hv.strictMono'

-- DISSOLVED: nontrivial

theorem zero_of_hom_zero {x : ValueGroup₀ v} (hx : hom v x = 0) : x = 0 := by
  refine (eq_of_le_of_not_lt (zero_le' (a := x)) fun h_lt ↦ ?_).symm
  have hs := strictMono v h_lt
  rw [map_zero, hx] at hs
  exact hs.false

theorem hom_eq_zero_iff {x : ValueGroup₀ v} : hom v x = 0 ↔ x = 0 :=
  ⟨fun h ↦ zero_of_hom_zero v h, fun h ↦ by rw [h, map_zero]⟩

def unit : Γ₀ˣ :=
  Units.mk0 (v (nontrivial v).choose) ((nontrivial v).choose_spec).1

-- DISSOLVED: unit_ne_one

-- INSTANCE (free from Core): :

section Restrict

-- INSTANCE (free from Core): isNontrivial_restrict

variable (K : Type*) [Field K] (v : Valuation K Γ₀) [RankOne v]

-- INSTANCE (free from Core): restrict_RankOne
