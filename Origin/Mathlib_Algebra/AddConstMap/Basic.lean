/-
Extracted from Algebra/AddConstMap/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Maps (semi)conjugating a shift to a shift

Denote by $S^1$ the unit circle `UnitAddCircle`.
A common way to study a self-map $f\colon S^1\to S^1$ of degree `1`
is to lift it to a map $\tilde f\colon \mathbb R\to \mathbb R$
such that $\tilde f(x + 1) = \tilde f(x)+1$ for all `x`.

In this file we define a structure and a typeclass
for bundled maps satisfying `f (x + a) = f x + b`.

We use parameters `a` and `b` instead of `1` to accommodate for two use cases:

- maps between circles of different lengths;
- self-maps $f\colon S^1\to S^1$ of degree other than one,
  including orientation-reversing maps.
-/

assert_not_exists Finset

open Function Set

structure AddConstMap (G H : Type*) [Add G] [Add H] (a : G) (b : H) where
  /-- The underlying function of an `AddConstMap`.
  Use automatic coercion to function instead. -/
  protected toFun : G → H
  /-- An `AddConstMap` satisfies `f (x + a) = f x + b`. Use `map_add_const` instead. -/
  map_add_const' (x : G) : toFun (x + a) = toFun x + b
