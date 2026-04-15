/-
Extracted from Algebra/Group/Invertible/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Invertible elements

This file defines a typeclass `Invertible a` for elements `a` with a two-sided
multiplicative inverse.

The intent of the typeclass is to provide a way to write e.g. `⅟2` in a ring
like `ℤ[1/2]` where some inverses exist but there is no general `⁻¹` operator;
or to specify that a field has characteristic `≠ 2`.
It is the `Type`-valued analogue to the `Prop`-valued `IsUnit`.

For constructions of the invertible element given a characteristic, see
`Algebra/CharP/Invertible` and other lemmas in that file.

## Notation

* `⅟a` is `Invertible.invOf a`, the inverse of `a`

## Implementation notes

The `Invertible` class lives in `Type`, not `Prop`, to make computation easier.
If multiplication is associative, `Invertible` is a subsingleton anyway.

The `simp` normal form tries to normalize `⅟a` to `a ⁻¹`. Otherwise, it pushes
`⅟` inside the expression as much as possible.

Since `Invertible a` is not a `Prop` (but it is a `Subsingleton`), we have to be careful about
coherence issues: we should avoid having multiple non-defeq instances for `Invertible a` in the
same context.  This file plays it safe and uses `def` rather than `instance` for most definitions,
users can choose which instances to use at the point of use.

For example, here's how you can use an `Invertible 1` instance:
```lean
variable {α : Type*} [Monoid α]

def something_that_needs_inverses (x : α) [Invertible x] := sorry

section
attribute [local instance] invertibleOne
def something_one := something_that_needs_inverses 1
end
```

### Typeclass search vs. unification for `simp` lemmas

Note that since typeclass search searches the local context first, an instance argument like
`[Invertible a]` might sometimes be filled by a different term than the one we'd find by
unification (i.e., the one that's used as an implicit argument to `⅟`).

This can cause issues with `simp`. Therefore, some lemmas are duplicated, with the `@[simp]`
versions using unification and the user-facing ones using typeclass search.

Since unification can make backwards rewriting (e.g. `rw [← mylemma]`) impractical, we still want
the instance-argument versions; therefore the user-facing versions retain the instance arguments
and the original lemma name, whereas the `@[simp]`/unification ones acquire a `'` at the end of
their name.

We modify this file according to the above pattern only as needed; therefore, most `@[simp]` lemmas
here are not part of such a duplicate pair. This is not (yet) intended as a permanent solution.

See Zulip: [https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Invertible.201.20simps/near/320558233]

## Tags

invertible, inverse element, invOf, a half, one half, a third, one third, ½, ⅓

-/

assert_not_exists MonoidWithZero DenselyOrdered

universe u

variable {α : Type u}

class Invertible [Mul α] [One α] (a : α) : Type u where
  /-- The inverse of an `Invertible` element -/
  invOf : α
  /-- `invOf a` is a left inverse of `a` -/
  invOf_mul_self : invOf * a = 1
  /-- `invOf a` is a right inverse of `a` -/
  mul_invOf_self : a * invOf = 1

prefix:max "⅟" => Invertible.invOf
