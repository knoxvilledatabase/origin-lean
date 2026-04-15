/-
Extracted from Order/ConditionallyCompletePartialOrder/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Conditionally complete partial orders

This file defines *conditionally complete partial orders* with suprema, infima or both. These are
partial orders where every nonempty, upwards (downwards) directed set which is
bounded above (below) has a least upper bound (greatest lower bound). This class extends `SupSet`
(`InfSet`) and the requirement is that `sSup` (`sInf`) must be the least upper bound.

The three classes defined herein are:

+ `ConditionallyCompletePartialOrderSup` for partial orders with suprema,
+ `ConditionallyCompletePartialOrderInf` for partial orders with infima, and
+ `ConditionallyCompletePartialOrder` for partial orders with both suprema and infima

One common use case for these classes is the order on a von Neumann algebra, or W⋆-algebra.
This is the strongest order-theoretic structure satisfied by a von Neumann algebra;
in particular it is *not* a conditionally complete *lattice*, and indeed it is a lattice if and only
if the algebra is commutative. In addition, `ℂ` can be made to satisfy this class (one must provide
a suitable `SupSet` instance), with the order `w ≤ z ↔ w.re ≤ z.re ∧ w.im = z.im`, which is
available in the `ComplexOrder` namespace.

These use cases are the motivation for defining three classes, as compared with other parts of the
order theory library, where only the supremum versions are defined (e.g., `CompletePartialOrder` and
`OmegaCompletePartialOrder`). We note that, if these classes are used outside of order theory, then
it is more likely that the infimum versions would be useful. Indeed, whenever the underlying type
has an antitone involution (e.g., if it is an ordered ring, then negation would be such a map),
then any `ConditionallyCompletePartialOrder{Sup,Inf}` is automatically a
`ConditionallyCompletePartialOrder`. Because of the `to_dual` attribute, the additional overhead
required to add and maintain the infimum version is minimal.

-/

variable {ι : Sort*} {α : Type*}

class ConditionallyCompletePartialOrderInf (α : Type*)
    extends PartialOrder α, InfSet α where
  /-- For each nonempty, directed set `s` which is bounded below, `sInf s` is
  the greatest lower bound of `s`. -/
  isGLB_csInf_of_directed :
    ∀ s, DirectedOn (· ≥ ·) s → s.Nonempty → BddBelow s → IsGLB s (sInf s)
