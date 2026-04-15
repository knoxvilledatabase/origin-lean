/-
Extracted from RingTheory/IdealFilter/Basic.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ideal Filters

An **ideal filter** is a filter in the lattice of ideals of a ring `A`.

## Main definitions

* `IdealFilter A`: the type of an ideal filter on a ring `A`.
* `IsUniform F` : a filter `F` is uniform if whenever `I` is an ideal in the filter, then for all
  `a : A`, the colon ideal `I.colon {a}` is in `F`.
* `IsTorsionElem` : Given a filter `F`, an element, `m`, of an `A`-module, `M`, is `F`-torsion if
  there exists an ideal `L` in `F` that annihilates `m`.
* `IsTorsion` : Given a filter `F`, an `A`-module, `M`, is `F`-torsion if every element is torsion.
* `gabrielComposition` : Given two filters `F` and `G`, the Gabriel composition of `F` and `G` is
  the set of ideals `L` of `A` such that there exists an ideal `K` in `G` with `K/L` `F`-torsion.
  This is again a filter.
* `IsGabriel F` : a filter `F` is a Gabriel filter if it is uniform and satisfies axiom T4:
  for all `I : Ideal A`, if there exists `J ∈ F` such that for all `a ∈ J` the colon ideal
  `I.colon {a}` is in `F`, then `I ∈ F`.

## Main statements

* `isGabriel_iff`: a filter is Gabriel iff it is uniform and `F • F = F`.

## Notation

* `F • G`: the Gabriel composition of ideal filters `F` and `G`, defined by
  `gabrielComposition F G`.

## Implementation notes

In the classical literature (e.g. Stenström), *right linear topologies* on a ring are often
described via filters of open **right** ideals, and the terminology is frequently abused by
identifying the topology with its filter of ideals.

In this development we work systematically with **left ideals**. Accordingly, Stenström’s
right-ideal construction `(L : a) = {x ∈ A | a * x ∈ L}` is replaced by the left ideal
`L.colon {a} = {a | x * a ∈ L}`.

With this convention, uniform filters correspond to linear (additive) topologies, while the
additional Gabriel condition (axiom T4) imposes an algebraic saturation property that does not
change the induced topology.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]
* [nLab: Uniform filter](<https://ncatlab.org/nlab/show/uniform+filter>)
* [nLab: Gabriel filter](<https://ncatlab.org/nlab/show/Gabriel+filter>)
* [nLab: Gabriel composition](<https://ncatlab.org/nlab/show/Gabriel+composition+of+filters>)

## Tags

ring theory, ideal, filter, uniform filter, Gabriel filter, torsion theory
-/

open scoped Pointwise

abbrev IdealFilter (A : Type*) [Ring A] := Order.PFilter (Ideal A)

namespace IdealFilter

variable {A : Type*} [Ring A]

class IsUniform (F : IdealFilter A) : Prop where
  /-- **Axiom T3.**  See [stenstrom1975]. -/
  colon_mem {I : Ideal A} (hI : I ∈ F) (a : A) : I.colon {a} ∈ F

def IsTorsionElem (F : IdealFilter A)
    {M : Type*} [AddCommMonoid M] [Module A M] (m : M) : Prop :=
  ∃ L ∈ F, ∀ a ∈ L, a • m = 0

def IsTorsion (F : IdealFilter A)
    (M : Type*) [AddCommMonoid M] [Module A M] : Prop :=
  ∀ m : M, IsTorsionElem F m

def IsTorsionQuot (F : IdealFilter A) (L K : Ideal A) : Prop :=
  ∀ k ∈ K, ∃ I ∈ F, I ≤ L.colon {k}

lemma isTorsionQuot_inter_left_iff {F : IdealFilter A} {L K : Ideal A} :
    IsTorsionQuot F (L ⊓ K) K ↔ IsTorsionQuot F L K := by
  constructor <;>
  · intro h k hk
    rcases h k hk with ⟨I, hI, hI_le⟩
    have hcol : (L ⊓ K).colon {k} = Submodule.colon L {k} :=
      Submodule.colon_inf_eq_left_of_subset (Set.singleton_subset_iff.mpr hk)
    exact ⟨I, hI, (by simpa [hcol] using hI_le)⟩
