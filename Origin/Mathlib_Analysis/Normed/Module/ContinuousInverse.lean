/-
Extracted from Analysis/Normed/Module/ContinuousInverse.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Continuous linear maps with a continuous left/right inverse

This file defines continuous linear maps which admit a continuous left/right inverse.

We prove that both of these classes of maps are closed under products, composition and contain
linear equivalences, and a sufficient criterion in finite dimension: a surjective linear map on a
finite-dimensional space always admits a continuous right inverse; an injective linear map on a
finite-dimensional space always admits a continuous left inverse.

We also prove an equivalent characterisation of admitting a continuous left inverse: `f` admits a
continuous left inverse if and only if it is injective, has closed range and its range admits a
closed complement. This characterisation is used to extract a complement from immersions, for use
in the regular value theorem. (For submersions, there is a natural choice of complement, and an
analogous statement is not necessary.)

This concept is used to give an equivalent definition of immersions and submersions of manifolds.

## Main definitions and results

* `ContinuousLinearMap.HasLeftInverse`: a continuous linear map admits a left inverse
  which is a continuous linear map itself
* `ContinuousLinearMap.HasRightInverse`: a continuous linear map admits a right inverse
  which is a continuous linear map itself

* `ContinuousLinearMap.HasLeftInverse.isClosed_range`: if `f` has a continuous left inverse,
  its range is closed
* `ContinuousLinearMap.HasLeftInverse.closedComplemented_range`: if `f` has a continuous left
  inverse, its range admits a closed complement
* `ContinuousLinearMap.HasLeftInverse.complement`: a choice of closed complement for `range f`
* `ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range`:
  if `f` is injective and has closed range with a closed complement, it admits a continuous left
  inverse

* `ContinuousLinearEquiv.hasLeftInverse` and `ContinuousLinearEquiv.hasRightInverse`:
  a continuous linear equivalence admits a continuous left (resp. right) inverse
* `ContinuousLinearMap.HasLeftInverse.comp`, `ContinuousLinearMap.HasRightInverse.comp`:
  if `f : E → F` and `g : F → G` both admit a continuous left (resp. right) inverse,
  so does `g.comp f`.
* `ContinuousLinearMap.HasLeftInverse.of_comp`, `ContinuousLinearMap.HasRightInverse.of_comp`:
  suppose `f : E → F` and `g : F → G` are continuous linear maps.
  If `g.comp f : E → G` admits a continuous left inverse, then so does `f`.
  If `g.comp f : E → G` admits a continuous right inverse, then so does `g`.
* `ContinuousLinearMap.HasLeftInverse.prodMap`, `ContinuousLinearMap.HasRightInverse.prodMap`:
  having a continuous left/right inverse is closed under taking products
* `ContinuousLinearMap.HasLeftInverse.inl`, `ContinuousLinearMap.HasLeftInverse.inr`:
  `ContinuousLinearMap.inl` and `.inr` have a continuous left inverse
* `ContinuousLinearMap.HasRightInverse.fst`, `ContinuousLinearMap.HasRightInverse.snd`:
  `ContinuousLinearMap.fst` and `.snd` have a continuous right inverse
* `ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional`:
  if `f : E → F` is injective and `F` is finite-dimensional, `f` has a continuous left inverse.
* `ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional`:
  if `f : E → F` is surjective and `F` is finite-dimensional, `f` has a continuous right inverse.

## TODO

* Suppose `E` and `F` are Banach and `f : E → F` is Fredholm.
  If `f` is surjective, it has a continuous right inverse.
  If `f` is injective, it has a continuous left inverse.

-/

open Function Set

variable {R : Type*} [Semiring R] {E E' F F' G : Type*}
  [TopologicalSpace E] [AddCommMonoid E] [Module R E]
  [TopologicalSpace E'] [AddCommMonoid E'] [Module R E']
  [TopologicalSpace F] [AddCommMonoid F] [Module R F]
  [TopologicalSpace F'] [AddCommMonoid F'] [Module R F']

noncomputable section

  ∃ g : F →L[R] E, LeftInverse g f

  ∃ g : F →L[R] E, RightInverse g f

namespace ContinuousLinearMap

namespace HasLeftInverse

variable {f : E →L[R] F}

def leftInverse (h : f.HasLeftInverse) : F →L[R] E := Classical.choose h

lemma leftInverse_leftInverse (h : f.HasLeftInverse) : LeftInverse h.leftInverse f :=
  Classical.choose_spec h

example (h : f.HasLeftInverse) (x : E) : h.leftInverse (f x) = x :=

  h.leftInverse_leftInverse x

lemma congr {g : E →L[R] F} (hf : f.HasLeftInverse) (hfg : g = f) :
    g.HasLeftInverse :=
  hfg ▸ hf

lemma _root_.ContinuousLinearEquiv.hasLeftInverse (f : E ≃L[R] F) :
    f.toContinuousLinearMap.HasLeftInverse :=
  ⟨f.symm, rightInverse_of_comp (by simp)⟩
