/-
Extracted from Data/DFinsupp/Sigma.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `DFinsupp` on `Sigma` types

## Main definitions

* `DFinsupp.sigmaCurry`: turn a `DFinsupp` indexed by a `Sigma` type into a `DFinsupp` with two
  parameters.
* `DFinsupp.sigmaUncurry`: turn a `DFinsupp` with two parameters into a `DFinsupp` indexed by a
  `Sigma` type. Inverse of `DFinsupp.sigmaCurry`.
* `DFinsupp.sigmaCurryEquiv`: `DFinsupp.sigmaCurry` and `DFinsupp.sigmaUncurry` bundled into a
  bijection.

-/

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace DFinsupp

section Equiv

open Finset

variable {κ : Type*}

section SigmaCurry

variable {α : ι → Type*} {δ : ∀ i, α i → Type v}

variable [DecidableEq ι]

def sigmaCurry [∀ i j, Zero (δ i j)] (f : Π₀ (i : Σ _, _), δ i.1 i.2) :
    Π₀ (i) (j), δ i j where
  toFun := fun i ↦
  { toFun := fun j ↦ f ⟨i, j⟩,
    support' := f.support'.map (fun ⟨m, hm⟩ ↦
      ⟨m.filterMap (fun ⟨i', j'⟩ ↦ if h : i' = i then some <| h.rec j' else none),
        fun j ↦ (hm ⟨i, j⟩).imp_left (fun h ↦ (m.mem_filterMap _).mpr ⟨⟨i, j⟩, h, dif_pos rfl⟩)⟩) }
  support' := f.support'.map (fun ⟨m, hm⟩ ↦
    ⟨m.map Sigma.fst, fun i ↦ Decidable.or_iff_not_imp_left.mpr (fun h ↦ DFinsupp.ext
      (fun j ↦ (hm ⟨i, j⟩).resolve_left (fun H ↦ (Multiset.mem_map.not.mp h) ⟨⟨i, j⟩, H, rfl⟩)))⟩)
