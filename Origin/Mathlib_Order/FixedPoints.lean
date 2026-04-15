/-
Extracted from Order/FixedPoints.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fixed point construction on complete lattices

This file sets up the basic theory of fixed points of a monotone function in a complete lattice.

## Main definitions

* `OrderHom.lfp`: The least fixed point of a bundled monotone function.
* `OrderHom.gfp`: The greatest fixed point of a bundled monotone function.
* `OrderHom.prevFixed`: The greatest fixed point of a bundled monotone function smaller than or
  equal to a given element.
* `OrderHom.nextFixed`: The least fixed point of a bundled monotone function greater than or
  equal to a given element.
* `fixedPoints.completeLattice`: The Knaster-Tarski theorem: fixed points of a monotone
  self-map of a complete lattice form themselves a complete lattice.

## Tags

fixed point, complete lattice, monotone function
-/

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Function (fixedPoints IsFixedPt)

namespace OrderHom

section Basic

variable [CompleteLattice α] (f : α →o α)

def lfp : (α →o α) →o α where
  toFun f := sInf { a | f a ≤ a }
  monotone' _ _ hle := sInf_le_sInf fun a ha => (hle a).trans ha

def gfp : (α →o α) →o α where
  toFun f := sSup { a | a ≤ f a }
  monotone' _ _ hle := sSup_le_sSup fun a ha => le_trans ha (hle a)

theorem lfp_le {a : α} (h : f a ≤ a) : f.lfp ≤ a :=
  sInf_le h

theorem lfp_le_fixed {a : α} (h : f a = a) : f.lfp ≤ a :=
  f.lfp_le h.le

theorem le_lfp {a : α} (h : ∀ b, f b ≤ b → a ≤ b) : a ≤ f.lfp :=
  le_sInf h

theorem map_le_lfp {a : α} (ha : a ≤ f.lfp) : f a ≤ f.lfp :=
  f.le_lfp fun _ hb => (f.mono <| le_sInf_iff.1 ha _ hb).trans hb
