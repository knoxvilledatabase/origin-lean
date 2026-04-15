/-
Extracted from Data/Fin/FlagRange.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Range of `f : Fin (n + 1) → α` as a `Flag`

Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.
Then the range of `f` is a maximal chain.

We formulate this result in terms of `IsMaxChain` and `Flag`.
-/

open Set

variable {α : Type*} [PartialOrder α] [BoundedOrder α] {n : ℕ} {f : Fin (n + 1) → α}

theorem IsMaxChain.range_fin_of_covBy (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
    (hcovBy : ∀ k : Fin n, f k.castSucc ⩿ f k.succ) :
    IsMaxChain (· ≤ ·) (range f) := by
  have hmono : Monotone f := Fin.monotone_iff_le_succ.2 fun k ↦ (hcovBy k).1
  refine ⟨hmono.isChain_range, fun t htc hbt ↦ hbt.antisymm fun x hx ↦ ?_⟩
  rw [mem_range]; by_contra! h
  suffices ∀ k, f k < x by simpa [hlast] using this (.last _)
  intro k
  induction k using Fin.induction with
  | zero => simpa [h0, bot_lt_iff_ne_bot] using (h 0).symm
  | succ k ihk =>
    rw [range_subset_iff] at hbt
    exact (htc.lt_of_le (hbt k.succ) hx (h _)).resolve_right ((hcovBy k).2 ihk)
