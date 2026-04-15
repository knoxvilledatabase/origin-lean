/-
Extracted from Order/Filter/Prod.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Product and coproduct filters

In this file we prove some basic properties of `f ×ˢ g` and `Filter.coprod f g`. The product
of two filters is the largest filter `l` such that `Filter.Tendsto Prod.fst l f` and
`Filter.Tendsto Prod.snd l g`.

## Implementation details

The product filter cannot be defined using the monad structure on filters. For example:

```lean
F := do {x ← seq, y ← top, return (x, y)}
G := do {y ← top, x ← seq, return (x, y)}
```
hence:
```lean
s ∈ F  ↔  ∃ n, [n..∞] × univ ⊆ s
s ∈ G  ↔  ∀ i:ℕ, ∃ n, [n..∞] × {i} ⊆ s
```
Now `⋃ i, [i..∞] × {i}` is in `G` but not in `F`.
As product filter we want to have `F` as result.

-/

open Set

open Filter

namespace Filter

variable {α β γ δ : Type*} {ι : Sort*}

section Prod

variable {s : Set α} {t : Set β} {f : Filter α} {g : Filter β}

theorem prod_mem_prod (hs : s ∈ f) (ht : t ∈ g) : s ×ˢ t ∈ f ×ˢ g :=
  inter_mem_inf (preimage_mem_comap hs) (preimage_mem_comap ht)

theorem mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s ∈ f ×ˢ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ×ˢ t₂ ⊆ s := by
  constructor
  · rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩
    exact ⟨s₁, hs₁, s₂, hs₂, fun p ⟨h, h'⟩ => ⟨hts₁ h, hts₂ h'⟩⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, h⟩
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h
