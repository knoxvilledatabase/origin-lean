/-
Extracted from LinearAlgebra/AffineSpace/Basis.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Affine bases and barycentric coordinates

Suppose `P` is an affine space modelled on the module `V` over the ring `k`, and `p : ι → P` is an
affine-independent family of points spanning `P`. Given this data, each point `q : P` may be written
uniquely as an affine combination: `q = w₀ p₀ + w₁ p₁ + ⋯` for some (finitely-supported) weights
`wᵢ`. For each `i : ι`, we thus have an affine map `P →ᵃ[k] k`, namely `q ↦ wᵢ`. This family of
maps is known as the family of barycentric coordinates. It is defined in this file.

## The construction

Fixing `i : ι`, and allowing `j : ι` to range over the values `j ≠ i`, we obtain a basis `bᵢ` of `V`
defined by `bᵢ j = p j -ᵥ p i`. Let `fᵢ j : V →ₗ[k] k` be the corresponding dual basis and let
`fᵢ = ∑ j, fᵢ j : V →ₗ[k] k` be the corresponding "sum of all coordinates" form. Then the `i`th
barycentric coordinate of `q : P` is `1 - fᵢ (q -ᵥ p i)`.

## Main definitions

* `fintypeAffineCoords`: the `AffineSubspace` of `ι → k` (for `Fintype ι`) where coordinates sum
  to `1`.
* `finsuppAffineCoords`: the `AffineSubspace` of `ι →₀ k` where coordinates sum to `1`.
* `AffineBasis`: a structure representing an affine basis of an affine space.
* `AffineBasis.coord`: the map `P →ᵃ[k] k` corresponding to `i : ι`.
* `AffineBasis.coord_apply_eq`: the behaviour of `AffineBasis.coord i` on `p i`.
* `AffineBasis.coord_apply_ne`: the behaviour of `AffineBasis.coord i` on `p j` when `j ≠ i`.
* `AffineBasis.coord_apply`: the behaviour of `AffineBasis.coord i` on `p j` for general `j`.
* `AffineBasis.coord_apply_combination`: the characterisation of `AffineBasis.coord i` in terms
  of affine combinations, i.e., `AffineBasis.coord i (w₀ p₀ + w₁ p₁ + ⋯) = wᵢ`.

## TODO

* Construct the affine equivalence between `P` and `finsuppAffineCoords ι k`.

-/

open Affine Module Set

open scoped Pointwise

section Coordinates

variable {ι k V P : Type*} [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

variable (ι k) in

def fintypeAffineCoords [Fintype ι] : AffineSubspace k (ι → k) :=
  (affineSpan k {(1 : k)}).comap (Fintype.linearCombination k (1 : ι → k)).toAffineMap

lemma mem_fintypeAffineCoords_iff_sum [Fintype ι] {w : ι → k} :
    w ∈ fintypeAffineCoords ι k ↔ ∑ i, w i = 1 := by
  simp [fintypeAffineCoords, Fintype.linearCombination_apply]

lemma AffineIndependent.injOn_affineCombination_fintypeAffineCoords [Fintype ι] {p : ι → P}
    (h : AffineIndependent k p) :
    InjOn (Finset.univ.affineCombination k p) (fintypeAffineCoords ι k) :=
  fun w₁ hw₁ w₂ hw₂ he ↦ (affineIndependent_iff_eq_of_fintype_affineCombination_eq k p).1
    h w₁ w₂ (mem_fintypeAffineCoords_iff_sum.1 hw₁) (mem_fintypeAffineCoords_iff_sum.1 hw₂) he

variable (ι k) in

noncomputable def finsuppAffineCoords : AffineSubspace k (ι →₀ k) :=
  (affineSpan k {(1 : k)}).comap (Finsupp.linearCombination k (1 : ι → k)).toAffineMap

lemma mem_finsuppAffineCoords_iff_linearCombination {w : ι →₀ k} :
    w ∈ finsuppAffineCoords ι k ↔ Finsupp.linearCombination k (1 : ι → k) w = 1 := by
  simp [finsuppAffineCoords]

end Coordinates

universe u₁ u₂ u₃ u₄

structure AffineBasis (ι : Type u₁) (k : Type u₂) {V : Type u₃} (P : Type u₄) [AddCommGroup V]
  [AffineSpace V P] [Ring k] [Module k V] where
  /-- The underlying family of points.

  Do NOT use directly. Use the coercion instead. -/
  protected toFun : ι → P
  protected ind' : AffineIndependent k toFun
  protected tot' : affineSpan k (range toFun) = ⊤

variable {ι ι' G G' k V P : Type*} [AddCommGroup V] [AffineSpace V P]

namespace AffineBasis

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P) {s : Finset ι} {i j : ι} (e : ι ≃ ι')

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): instFunLike
