/-
Extracted from Order/JordanHolder.lean
Genuine: 9 of 9 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Jordan-Hölder Theorem

This file proves the Jordan Hölder theorem for a `JordanHolderLattice`, a class also defined in
this file. Examples of `JordanHolderLattice` include `Subgroup G` if `G` is a group, and
`Submodule R M` if `M` is an `R`-module. Using this approach the theorem need not be proved
separately for both groups and modules, the proof in this file can be applied to both.

## Main definitions
The main definitions in this file are `JordanHolderLattice` and `CompositionSeries`,
and the relation `Equivalent` on `CompositionSeries`

A `JordanHolderLattice` is the class for which the Jordan Hölder theorem is proved. A
Jordan Hölder lattice is a lattice equipped with a notion of maximality, `IsMaximal`, and a notion
of isomorphism of pairs `Iso`. In the example of subgroups of a group, `IsMaximal H K` means that
`H` is a maximal normal subgroup of `K`, and `Iso (H₁, K₁) (H₂, K₂)` means that the quotient
`H₁ / K₁` is isomorphic to the quotient `H₂ / K₂`. `Iso` must be symmetric and transitive and must
satisfy the second isomorphism theorem `Iso (H, H ⊔ K) (H ⊓ K, K)`.

A `CompositionSeries X` is a finite nonempty series of elements of the lattice `X` such that
each element is maximal inside the next. The length of a `CompositionSeries X` is
one less than the number of elements in the series. Note that there is no stipulation
that a series start from the bottom of the lattice and finish at the top.
For a composition series `s`, `s.last` is the largest element of the series,
and `s.head` is the least element.

Two `CompositionSeries X`, `s₁` and `s₂` are equivalent if there is a bijection
`e : Fin s₁.length ≃ Fin s₂.length` such that for any `i`,
`Iso (s₁ i, s₁ i.succ) (s₂ (e i), s₂ (e i.succ))`

## Main theorems

The main theorem is `CompositionSeries.jordan_holder`, which says that if two composition
series have the same least element and the same largest element,
then they are `Equivalent`.

## TODO

Provide instances of `JordanHolderLattice` for subgroups, and potentially for modular lattices.

It is not entirely clear how this should be done. Possibly there should be no global instances
of `JordanHolderLattice`, and the instances should only be defined locally in order to prove
the Jordan-Hölder theorem for modules/groups and the API should be transferred because many of the
theorems in this file will have stronger versions for modules. There will also need to be an API for
mapping composition series across homomorphisms. It is also probably possible to
provide an instance of `JordanHolderLattice` for any `ModularLattice`, and in this case the
Jordan-Hölder theorem will say that there is a well-defined notion of length of a modular lattice.
However an instance of `JordanHolderLattice` for a modular lattice will not be able to contain
the correct notion of isomorphism for modules, so a separate instance for modules will still be
required and this will clash with the instance for modular lattices, and so at least one of these
instances should not be a global instance.

> [!NOTE]
> The previous paragraph indicates that the instance of `JordanHolderLattice` for submodules should
> be obtained via `ModularLattice`. This is not the case in `mathlib4`.
> See `JordanHolderModule.instJordanHolderLattice`.
-/

universe u

open Set RelSeries

class JordanHolderLattice (X : Type u) [Lattice X] where
  IsMaximal : X → X → Prop
  lt_of_isMaximal : ∀ {x y}, IsMaximal x y → x < y
  sup_eq_of_isMaximal : ∀ {x y z}, IsMaximal x z → IsMaximal y z → x ≠ y → x ⊔ y = z
  isMaximal_inf_left_of_isMaximal_sup :
    ∀ {x y}, IsMaximal x (x ⊔ y) → IsMaximal y (x ⊔ y) → IsMaximal (x ⊓ y) x
  Iso : X × X → X × X → Prop
  iso_symm : ∀ {x y}, Iso x y → Iso y x
  iso_trans : ∀ {x y z}, Iso x y → Iso y z → Iso x z
  second_iso : ∀ {x y}, IsMaximal x (x ⊔ y) → Iso (x, x ⊔ y) (x ⊓ y, y)

namespace JordanHolderLattice

variable {X : Type u} [Lattice X] [JordanHolderLattice X]

theorem isMaximal_inf_right_of_isMaximal_sup {x y : X} (hxz : IsMaximal x (x ⊔ y))
    (hyz : IsMaximal y (x ⊔ y)) : IsMaximal (x ⊓ y) y := by
  rw [inf_comm]
  rw [sup_comm] at hxz hyz
  exact isMaximal_inf_left_of_isMaximal_sup hyz hxz

theorem isMaximal_of_eq_inf (x b : X) {a y : X} (ha : x ⊓ y = a) (hxy : x ≠ y) (hxb : IsMaximal x b)
    (hyb : IsMaximal y b) : IsMaximal a y := by
  have hb : x ⊔ y = b := sup_eq_of_isMaximal hxb hyb hxy
  substs a b
  exact isMaximal_inf_right_of_isMaximal_sup hxb hyb

theorem second_iso_of_eq {x y a b : X} (hm : IsMaximal x a) (ha : x ⊔ y = a) (hb : x ⊓ y = b) :
    Iso (x, a) (b, y) := by substs a b; exact second_iso hm

theorem IsMaximal.iso_refl {x y : X} (h : IsMaximal x y) : Iso (x, y) (x, y) :=
  second_iso_of_eq h (sup_eq_right.2 (le_of_lt (lt_of_isMaximal h)))
    (inf_eq_left.2 (le_of_lt (lt_of_isMaximal h)))

end JordanHolderLattice

open JordanHolderLattice

attribute [symm] iso_symm

attribute [trans] iso_trans

abbrev CompositionSeries (X : Type u) [Lattice X] [JordanHolderLattice X] : Type u :=
  RelSeries {(x, y) : X × X | IsMaximal x y}

namespace CompositionSeries

variable {X : Type u} [Lattice X] [JordanHolderLattice X]

theorem lt_succ (s : CompositionSeries X) (i : Fin s.length) :
    s (Fin.castSucc i) < s (Fin.succ i) :=
  lt_of_isMaximal (s.step _)

protected theorem strictMono (s : CompositionSeries X) : StrictMono s :=
  Fin.strictMono_iff_lt_succ.2 s.lt_succ

protected theorem injective (s : CompositionSeries X) : Function.Injective s :=
  s.strictMono.injective
