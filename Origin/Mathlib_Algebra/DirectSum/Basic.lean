/-
Extracted from Algebra/DirectSum/Basic.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Direct sum

This file defines the direct sum of abelian groups, indexed by a discrete type.

## Notation

`⨁ i, β i` is the n-ary direct sum `DirectSum`.
This notation is in the `DirectSum` locale, accessible after `open DirectSum`.

## References

* https://en.wikipedia.org/wiki/Direct_sum
-/

open Function

universe u v w u₁

variable (ι : Type v) (β : ι → Type w)

def DirectSum [∀ i, AddCommMonoid (β i)] : Type _ :=
  Π₀ i, β i

deriving AddCommMonoid, Inhabited, DFunLike

set_option backward.inferInstanceAs.wrap.data false in

-- INSTANCE (free from Core): CoeFun

scoped[DirectSum] notation3 "⨁ "(...)", "r:(scoped f => DirectSum _ f) => r

-- INSTANCE (free from Core): [DecidableEq

namespace DirectSum

variable {ι}

def coeFnAddMonoidHom [∀ i, AddCommMonoid (β i)] : (⨁ i, β i) →+ (Π i, β i) where
  toFun x := x
  __ := DFinsupp.coeFnAddMonoidHom
