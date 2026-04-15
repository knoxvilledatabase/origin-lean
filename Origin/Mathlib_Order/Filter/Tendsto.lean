/-
Extracted from Order/Filter/Tendsto.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Convergence in terms of filters

The general notion of limit of a map with respect to filters on the source and target types
is `Filter.Tendsto`. It is defined in terms of the order and the push-forward operation.

For instance, anticipating on Topology.Basic, the statement: "if a sequence `u` converges to
some `x` and `u n` belongs to a set `M` for `n` large enough then `x` is in the closure of
`M`" is formalized as: `Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M`,
which is a special case of `mem_closure_of_tendsto` from `Topology/Basic`.
-/

open Set Filter

variable {α β γ : Type*} {ι : Sort*}

namespace Filter

lemma Tendsto.eventually_mem {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β}
    (hf : Tendsto f l₁ l₂) (h : s ∈ l₂) : ∀ᶠ x in l₁, f x ∈ s :=
  hf h

theorem Tendsto.eventually {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop}
    (hf : Tendsto f l₁ l₂) (h : ∀ᶠ y in l₂, p y) : ∀ᶠ x in l₁, p (f x) :=
  hf h

theorem not_tendsto_iff_exists_frequently_notMem {f : α → β} {l₁ : Filter α} {l₂ : Filter β} :
    ¬Tendsto f l₁ l₂ ↔ ∃ s ∈ l₂, ∃ᶠ x in l₁, f x ∉ s := by
  simp only [tendsto_iff_forall_eventually_mem, not_forall, exists_prop, not_eventually]

theorem Tendsto.frequently {f : α → β} {l₁ : Filter α} {l₂ : Filter β} {p : β → Prop}
    (hf : Tendsto f l₁ l₂) (h : ∃ᶠ x in l₁, p (f x)) : ∃ᶠ y in l₂, p y :=
  mt hf.eventually h

theorem Tendsto.frequently_map {l₁ : Filter α} {l₂ : Filter β} {p : α → Prop} {q : β → Prop}
    (f : α → β) (c : Filter.Tendsto f l₁ l₂) (w : ∀ x, p x → q (f x)) (h : ∃ᶠ x in l₁, p x) :
    ∃ᶠ y in l₂, q y :=
  c.frequently (h.mono w)
