/-
Extracted from Data/QPF/Multivariate/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Multivariate quotients of polynomial functors.

Basic definition of multivariate QPF. QPFs form a compositional framework
for defining inductive and coinductive types, their quotients and nesting.

The idea is based on building ever larger functors. For instance, we can define
a list using a shape functor:

```lean
inductive ListShape (a b : Type)
  | nil : ListShape
  | cons : a -> b -> ListShape
```

This shape can itself be decomposed as a sum of product which are themselves
QPFs. It follows that the shape is a QPF and we can take its fixed point
and create the list itself:

```lean
def List (a : Type) := fix ListShape a -- not the actual notation
```

We can continue and define the quotient on permutation of lists and create
the multiset type:

```lean
def Multiset (a : Type) := QPF.quot List.perm List a -- not the actual notion
```

And `Multiset` is also a QPF. We can then create a novel data type (for Lean):

```lean
inductive Tree (a : Type)
  | node : a -> Multiset Tree -> Tree
```

An unordered tree. This is currently not supported by Lean because it nests
an inductive type inside of a quotient. We can go further and define
unordered, possibly infinite trees:

```lean
coinductive Tree' (a : Type)
| node : a -> Multiset Tree' -> Tree'
```

by using the `cofix` construct. Those options can all be mixed and
matched because they preserve the properties of QPF. The latter example,
`Tree'`, combines fixed point, co-fixed point and quotients.

## Related modules

* constructions
  * Fix
  * Cofix
  * Quot
  * Comp
  * Sigma / Pi
  * Prj
  * Const

each proves that some operations on functors preserves the QPF structure
-/

set_option linter.style.longLine false in

/-!
## Reference

[Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

universe u

open MvFunctor

class MvQPF {n : ℕ} (F : TypeVec.{u} n → Type*) extends MvFunctor F where
  P : MvPFunctor.{u} n
  abs : ∀ {α}, P α → F α
  repr : ∀ {α}, F α → P α
  abs_repr : ∀ {α} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β} (f : α ⟹ β) (p : P α), abs (f <$$> p) = f <$$> abs p

namespace MvQPF

variable {n : ℕ} {F : TypeVec.{u} n → Type*} [q : MvQPF F]

open MvFunctor (LiftP LiftR)

/-!
### Show that every MvQPF is a lawful MvFunctor.
-/

protected theorem id_map {α : TypeVec n} (x : F α) : TypeVec.id <$$> x = x := by
  rw [← abs_repr x, ← abs_map]
  rfl
