/-
Extracted from Algebra/Quandle.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Racks and Quandles

This file defines racks and quandles, algebraic structures for sets
that bijectively act on themselves with a self-distributivity
property.  If `R` is a rack and `act : R → (R ≃ R)` is the self-action,
then the self-distributivity is, equivalently, that
```
act (act x y) = act x * act y * (act x)⁻¹
```
where multiplication is composition in `R ≃ R` as a group.
Quandles are racks such that `act x x = x` for all `x`.

One example of a quandle (not yet in mathlib) is the action of a Lie
algebra on itself, defined by `act x y = Ad (exp x) y`.

Quandles and racks were independently developed by multiple
mathematicians.  David Joyce introduced quandles in his thesis
[Joyce1982] to define an algebraic invariant of knot and link
complements that is analogous to the fundamental group of the
exterior, and he showed that the quandle associated to an oriented
knot is invariant up to orientation-reversed mirror image.  Racks were
used by Fenn and Rourke for framed codimension-2 knots and
links in [FennRourke1992]. Unital shelves are discussed in [crans2017].

The name "rack" came from wordplay by Conway and Wraith for the "wrack
and ruin" of forgetting everything but the conjugation operation for a
group.

## Main definitions

* `Shelf` is a type with a self-distributive action
* `UnitalShelf` is a shelf with a left and right unit
* `Rack` is a shelf whose action for each element is invertible
* `Quandle` is a rack whose action for an element fixes that element
* `Quandle.conj` defines a quandle of a group acting on itself by conjugation.
* `ShelfHom` is homomorphisms of shelves, racks, and quandles.
* `Rack.EnvelGroup` gives the universal group the rack maps to as a conjugation quandle.
* `Rack.oppositeRack` gives the rack with the action replaced by its inverse.

## Main statements
* `Rack.EnvelGroup` is left adjoint to `Quandle.Conj` (`toEnvelGroup.map`).
  The universality statements are `toEnvelGroup.univ` and `toEnvelGroup.univ_uniq`.

## Implementation notes
"Unital racks" are uninteresting (see `Rack.assoc_iff_id`, `UnitalShelf.assoc`), so we do not
define them.

## Notation

The following notation is localized in `quandles`:

* `x ◃ y` is `Shelf.act x y`
* `x ◃⁻¹ y` is `Rack.inv_act x y`
* `S →◃ S'` is `ShelfHom S S'`

Use `open quandles` to use these.

## TODO

* If `g` is the Lie algebra of a Lie group `G`, then `(x ◃ y) = Ad (exp x) x` forms a quandle.
* If `X` is a symmetric space, then each point has a corresponding involution that acts on `X`,
  forming a quandle.
* Alexander quandle with `a ◃ b = t * b + (1 - t) * b`, with `a` and `b` elements
  of a module over `Z[t,t⁻¹]`.
* If `G` is a group, `H` a subgroup, and `z` in `H`, then there is a quandle `(G/H;z)` defined by
  `yH ◃ xH = yzy⁻¹xH`.  Every homogeneous quandle (i.e., a quandle `Q` whose automorphism group acts
  transitively on `Q` as a set) is isomorphic to such a quandle.
  There is a generalization to this arbitrary quandles in [Joyce's paper (Theorem 7.2)][Joyce1982].

## Tags

rack, quandle
-/

open MulOpposite

universe u v

class Shelf (α : Type u) where
  /-- The action of the `Shelf` over `α` -/
  act : α → α → α
  /-- A verification that `act` is self-distributive -/
  self_distrib : ∀ {x y z : α}, act x (act y z) = act (act x y) (act x z)

class UnitalShelf (α : Type u) extends Shelf α, One α where
  one_act : ∀ a : α, act 1 a = a
  act_one : ∀ a : α, act a 1 = a
