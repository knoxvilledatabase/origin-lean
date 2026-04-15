/-
Extracted from Topology/EMetricSpace/BoundedVariation.lean
Genuine: 17 of 17 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Functions of bounded variation

We study functions of bounded variation. In particular, we show that a bounded variation function
is a difference of monotone functions, and differentiable almost everywhere. This implies that
Lipschitz functions from the real line into finite-dimensional vector space are also differentiable
almost everywhere.

## Main definitions and results

* `eVariationOn f s` is the total variation of the function `f` on the set `s`, in `ℝ≥0∞`.
* `BoundedVariationOn f s` registers that the variation of `f` on `s` is finite.
* `LocallyBoundedVariationOn f s` registers that `f` has finite variation on any compact
  subinterval of `s`.
* `variationOnFromTo f s a b` is the signed variation of `f` on `s ∩ Icc a b`, converted to `ℝ`.

* `eVariationOn.Icc_add_Icc` states that the variation of `f` on `[a, c]` is the sum of its
  variations on `[a, b]` and `[b, c]`.
* `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn` proves that a function
  with locally bounded variation is the difference of two monotone functions.
* `LipschitzWith.locallyBoundedVariationOn` shows that a Lipschitz function has locally
  bounded variation.

We also give several variations around these results.

## Implementation

We define the variation as an extended nonnegative real, to allow for infinite variation. This makes
it possible to use the complete linear order structure of `ℝ≥0∞`. The proofs would be much
more tedious with an `ℝ`-valued or `ℝ≥0`-valued variation, since one would always need to check
that the sets one uses are nonempty and bounded above as these are only conditionally complete.
-/

open scoped NNReal ENNReal Topology UniformConvergence

open Set Filter OrderDual

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]

noncomputable def eVariationOn (f : α → E) (s : Set α) : ℝ≥0∞ :=
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))

def BoundedVariationOn (f : α → E) (s : Set α) :=
  eVariationOn f s ≠ ∞

def LocallyBoundedVariationOn (f : α → E) (s : Set α) :=
  ∀ a b, a ∈ s → b ∈ s → BoundedVariationOn f (s ∩ Icc a b)

/-! ### Basic computations of variation -/

namespace eVariationOn

theorem nonempty_monotone_mem {s : Set α} (hs : s.Nonempty) :
    Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } := by
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨fun _ => x, fun i j _ => le_rfl, fun _ => hx⟩⟩

theorem eq_of_edist_zero_on {f f' : α → E} {s : Set α} (h : ∀ ⦃x⦄, x ∈ s → edist (f x) (f' x) = 0) :
    eVariationOn f s = eVariationOn f' s := by
  dsimp only [eVariationOn]
  congr 1 with p : 1
  congr 1 with i : 1
  rw [edist_congr_right (h <| p.snd.prop.2 (i + 1)), edist_congr_left (h <| p.snd.prop.2 i)]

theorem eq_of_eqOn {f f' : α → E} {s : Set α} (h : EqOn f f' s) :
    eVariationOn f s = eVariationOn f' s :=
  eq_of_edist_zero_on fun x xs => by rw [h xs, edist_self]

theorem sum_le {f : α → E} {s : Set α} {n : ℕ} {u : ℕ → α} (hu : Monotone u) (us : ∀ i, u i ∈ s) :
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f s :=
  le_iSup_of_le ⟨n, u, hu, us⟩ le_rfl

theorem sum_le_of_monotoneOn_Icc {f : α → E} {s : Set α} {m n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Icc m n)) (us : ∀ i ∈ Icc m n, u i ∈ s) :
    (∑ i ∈ Finset.Ico m n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f s := by
  rcases le_total n m with hnm | hmn
  · simp [Finset.Ico_eq_empty_of_le hnm]
  let π := projIcc m n hmn
  let v i := u (π i)
  calc
    ∑ i ∈ Finset.Ico m n, edist (f (u (i + 1))) (f (u i))
        = ∑ i ∈ Finset.Ico m n, edist (f (v (i + 1))) (f (v i)) :=
      Finset.sum_congr rfl fun i hi ↦ by
        rw [Finset.mem_Ico] at hi
        simp only [v, π, projIcc_of_mem hmn ⟨hi.1, hi.2.le⟩,
          projIcc_of_mem hmn ⟨hi.1.trans i.le_succ, hi.2⟩]
    _ ≤ ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) :=
      Finset.sum_mono_set _ (Nat.Iio_eq_range n ▸ Finset.Ico_subset_Iio_self)
    _ ≤ eVariationOn f s :=
      sum_le (fun i j h ↦ hu (π i).2 (π j).2 (monotone_projIcc hmn h)) fun i ↦ us _ (π i).2

theorem sum_le_of_monotoneOn_Iic {f : α → E} {s : Set α} {n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Iic n)) (us : ∀ i ≤ n, u i ∈ s) :
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f s := by
  simpa using sum_le_of_monotoneOn_Icc (m := 0) (hu.mono Icc_subset_Iic_self) fun i hi ↦ us i hi.2

theorem eVariationOn_eq_strictMonoOn (f : α → E) (s : Set α) :
    eVariationOn f s =
      ⨆ p : (n : ℕ) × { u : ℕ → α // StrictMonoOn u (Iic n) ∧ ∀ i ∈ Iic n, u i ∈ s },
        ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have : ∃ p : (n : ℕ) × { u : ℕ → α // StrictMonoOn u (Iic n) ∧ ∀ i ∈ Iic n, u i ∈ s },
        (p.2 : ℕ → α) p.1 = u n ∧
        ∑ x ∈ Finset.range n, edist (f (u (x + 1))) (f (u x)) =
        ∑ i ∈ Finset.range p.1, edist (f ((p.2 : ℕ → α) (i + 1))) (f ((p.2 : ℕ → α) i)) := by
      induction n with
      | zero => exact ⟨⟨0, ⟨u, by grind [StrictMonoOn], fun i hi ↦ u_mem _⟩⟩, by simp⟩
      | succ n ih =>
        rcases ih with ⟨⟨m, v, v_mono, v_mem⟩, hv, h'v⟩
        simp only [Finset.sum_range_succ, Sigma.exists, Subtype.exists, mem_Iic, exists_and_left,
          exists_prop]
        rcases (u_mono (Nat.le_add_right n 1)).eq_or_lt with hn | hn
        · simp only [← hn, edist_self, add_zero]
          exact ⟨m, v, hv, ⟨v_mono, v_mem⟩, h'v⟩
        · refine ⟨m + 1, fun i ↦ if i ≤ m then v i else u (n + 1), by simp,
            by grind [StrictMonoOn], ?_⟩
          simp only [h'v, ← hv, Order.add_one_le_iff, Finset.sum_range_succ, lt_self_iff_false,
            ↓reduceIte, le_refl]
          congr 1
          exact Finset.sum_congr rfl (by grind)
    rcases this with ⟨p, -, hp⟩
    rw [hp]
    apply le_iSup _ p
  · apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    apply sum_le_of_monotoneOn_Iic (by grind [MonotoneOn, StrictMonoOn]) (by grind)

theorem mono (f : α → E) {s t : Set α} (hst : t ⊆ s) : eVariationOn f t ≤ eVariationOn f s := by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, ut⟩⟩
  exact sum_le hu fun i => hst (ut i)

theorem _root_.BoundedVariationOn.mono {f : α → E} {s : Set α} (h : BoundedVariationOn f s)
    {t : Set α} (ht : t ⊆ s) : BoundedVariationOn f t :=
  ne_top_of_le_ne_top h (eVariationOn.mono f ht)

theorem _root_.BoundedVariationOn.locallyBoundedVariationOn {f : α → E} {s : Set α}
    (h : BoundedVariationOn f s) : LocallyBoundedVariationOn f s := fun _ _ _ _ =>
  h.mono inter_subset_left

theorem congr {f g : α → E} {s : Set α} (h : EqOn f g s) : eVariationOn f s = eVariationOn g s := by
  grind [eVariationOn]

theorem edist_le (f : α → E) {s : Set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    edist (f x) (f y) ≤ eVariationOn f s := by
  wlog hxy : y ≤ x generalizing x y
  · rw [edist_comm]
    exact this hy hx (le_of_not_ge hxy)
  let u : ℕ → α := fun n => if n = 0 then y else x
  have hu : Monotone u := monotone_nat_of_le_succ fun
  | 0 => hxy
  | (_ + 1) => le_rfl
  have us : ∀ i, u i ∈ s := fun
  | 0 => hy
  | (_ + 1) => hx
  simpa only [Finset.sum_range_one] using sum_le (n := 1) hu us

theorem eq_zero_iff (f : α → E) {s : Set α} :
    eVariationOn f s = 0 ↔ ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) = 0 := by
  constructor
  · rintro h x xs y ys
    rw [← nonpos_iff_eq_zero, ← h]
    exact edist_le f xs ys
  · rintro h
    dsimp only [eVariationOn]
    rw [ENNReal.iSup_eq_zero]
    rintro ⟨n, u, um, us⟩
    exact Finset.sum_eq_zero fun i _ => h _ (us i.succ) _ (us i)

theorem constant_on {f : α → E} {s : Set α} (hf : (f '' s).Subsingleton) :
    eVariationOn f s = 0 := by
  rw [eq_zero_iff]
  rintro x xs y ys
  rw [hf ⟨x, xs, rfl⟩ ⟨y, ys, rfl⟩, edist_self]
