/-
Extracted from Order/Filter/Pi.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# (Co)product of a family of filters

In this file we prove some basic properties of two filters on `Π i, α i`.

* `Filter.pi (f : Π i, Filter (α i))` to be the maximal filter on `Π i, α i` such that
  `∀ i, Filter.Tendsto (Function.eval i) (Filter.pi f) (f i)`. It is defined as
  `Π i, Filter.comap (Function.eval i) (f i)`. This is a generalization of binary products to
  indexed products.

* `Filter.coprodᵢ (f : Π i, Filter (α i))`: a generalization of `Filter.coprod`; it is the supremum
  of `comap (eval i) (f i)`.
-/

open Set Function Filter

namespace Filter

variable {ι : Type*} {α : ι → Type*} {f f₁ f₂ : (i : ι) → Filter (α i)} {s : (i : ι) → Set (α i)}
  {p : ∀ i, α i → Prop}

section Pi

theorem tendsto_eval_pi (f : ∀ i, Filter (α i)) (i : ι) : Tendsto (eval i) (pi f) (f i) :=
  tendsto_iInf' i tendsto_comap

theorem tendsto_pi {β : Type*} {m : β → ∀ i, α i} {l : Filter β} :
    Tendsto m l (pi f) ↔ ∀ i, Tendsto (fun x => m x i) l (f i) := by
  simp only [pi, tendsto_iInf, tendsto_comap_iff]; rfl

alias ⟨Tendsto.apply, _⟩ := tendsto_pi

theorem le_pi {g : Filter (∀ i, α i)} : g ≤ pi f ↔ ∀ i, Tendsto (eval i) g (f i) :=
  tendsto_pi
