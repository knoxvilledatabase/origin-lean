/-
Extracted from Data/Finset/Finsupp.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Finitely supported product of finsets

This file defines the finitely supported product of finsets as a `Finset (ι →₀ α)`.

## Main declarations

* `Finset.finsupp`: Finitely supported product of finsets. `s.finset t` is the product of the `t i`
  over all `i ∈ s`.
* `Finsupp.pi`: `f.pi` is the finset of `Finsupp`s whose `i`-th value lies in `f i`. This is the
  special case of `Finset.finsupp` where we take the product of the `f i` over the support of `f`.

## Implementation notes

We make heavy use of the fact that `0 : Finset α` is `{0}`. This scalar actions convention turns out
to be precisely what we want here too.
-/

noncomputable section

open Finsupp

open Pointwise

variable {ι α : Type*} [Zero α] {s : Finset ι} {f : ι →₀ α}

namespace Finset

open scoped Classical in

protected def finsupp (s : Finset ι) (t : ι → Finset α) : Finset (ι →₀ α) :=
  (s.pi t).map ⟨indicator s, indicator_injective s⟩

theorem mem_finsupp_iff {t : ι → Finset α} :
    f ∈ s.finsupp t ↔ f.support ⊆ s ∧ ∀ i ∈ s, f i ∈ t i := by
  classical
  refine mem_map.trans ⟨?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨support_indicator_subset _ _, fun i hi => ?_⟩
    convert mem_pi.1 hf i hi
    exact indicator_of_mem hi _
  · refine fun h => ⟨fun i _ => f i, mem_pi.2 h.2, ?_⟩
    ext i
    exact ite_eq_left_iff.2 fun hi => (notMem_support_iff.1 fun H => hi <| h.1 H).symm
