/-
Extracted from RingTheory/MvPolynomial/FreeCommRing.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Constructing Ring terms from MvPolynomial

This file provides tools for constructing ring terms that can be evaluated to particular
`MvPolynomial`s. The main motivation is in model theory. It can be used to construct first-order
formulas whose realization is a property of an `MvPolynomial`

## Main definitions

* `FirstOrder.Ring.genericPolyMap` is a function that given a finite set of monomials
  `monoms : ι → Finset (κ →₀ ℕ)` returns a function `ι → FreeCommRing ((Σ i : ι, monoms i) ⊕ κ)`
  such that `genericPolyMap monoms i` is a ring term that can be evaluated to a polynomial
  `p : MvPolynomial κ R` such that `p.support ⊆ monoms i`.

-/

assert_not_exists Cardinal

variable {ι κ R : Type*}

namespace FirstOrder

namespace Ring

open MvPolynomial FreeCommRing

noncomputable def genericPolyMap (monoms : ι → Finset (κ →₀ ℕ)) :
    ι → FreeCommRing ((Σ i : ι, monoms i) ⊕ κ) :=
  fun i => (monoms i).attach.sum
    (fun m => FreeCommRing.of (Sum.inl ⟨i, m⟩) *
      Finsupp.prod m.1 (fun j n => FreeCommRing.of (Sum.inr j) ^ n))

noncomputable def mvPolynomialSupportLEEquiv
    [DecidableEq κ] [CommRing R] [DecidableEq R]
    (monoms : ι → Finset (κ →₀ ℕ)) :
    { p : ι → MvPolynomial κ R // ∀ i, (p i).support ⊆ monoms i } ≃
      ((Σ i, monoms i) → R) :=
  { toFun := fun p i => (p.1 i.1).coeff i.2,
    invFun := fun p => ⟨fun i =>
      { toFun := fun m => if hm : m ∈ monoms i then p ⟨i, ⟨m, hm⟩⟩ else 0
        support := {m ∈ monoms i | ∃ hm : m ∈ monoms i, p ⟨i, ⟨m, hm⟩⟩ ≠ 0},
        mem_support_toFun := by simp },
      fun i => Finset.filter_subset _ _⟩,
    left_inv := fun p => by
      ext i m
      simp only [coeff, ne_eq, exists_prop, dite_eq_ite, Finsupp.coe_mk, ite_eq_left_iff]
      intro hm
      have : m ∉ (p.1 i).support := fun h => hm (p.2 i h)
      simpa [coeff, eq_comm, MvPolynomial.mem_support_iff] using this
    right_inv := fun p => by ext; simp [coeff] }
