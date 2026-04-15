/-
Extracted from Topology/Bornology/Basic.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic theory of bornology

We develop the basic theory of bornologies. Instead of axiomatizing bounded sets and defining
bornologies in terms of those, we recognize that the cobounded sets form a filter and define a
bornology as a filter of cobounded sets which contains the cofinite filter.  This allows us to make
use of the extensive library for filters, but we also provide the relevant connecting results for
bounded sets.

The specification of a bornology in terms of the cobounded filter is equivalent to the standard
one (e.g., see [Bourbaki, *Topological Vector Spaces*][bourbaki1987], **covering bornology**, now
often called simply **bornology**) in terms of bounded sets (see `Bornology.ofBounded`,
`IsBounded.union`, `IsBounded.subset`), except that we do not allow the empty bornology (that is,
we require that *some* set must be bounded; equivalently, `∅` is bounded). In the literature the
cobounded filter is generally referred to as the *filter at infinity*.

## Main definitions

- `Bornology α`: a class consisting of `cobounded : Filter α` and a proof that this filter
  contains the `cofinite` filter.
- `Bornology.IsCobounded`: the predicate that a set is a member of the `cobounded α` filter. For
  `s : Set α`, one should prefer `Bornology.IsCobounded s` over `s ∈ cobounded α`.
- `bornology.IsBounded`: the predicate that states a set is bounded (i.e., the complement of a
  cobounded set). One should prefer `Bornology.IsBounded s` over `sᶜ ∈ cobounded α`.
- `BoundedSpace α`: a class extending `Bornology α` with the condition
  `Bornology.IsBounded (Set.univ : Set α)`

Although use of `cobounded α` is discouraged for indicating the (co)boundedness of individual sets,
it is intended for regular use as a filter on `α`.
-/

open Set Filter

variable {ι α β : Type*}

class Bornology (α : Type*) where
  /-- The filter of cobounded sets in a bornology. -/
  cobounded (α) : Filter α
  /-- The cobounded filter in a bornology is smaller than the cofinite filter. -/
  le_cofinite (α) : cobounded ≤ cofinite
