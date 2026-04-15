/-
Extracted from LinearAlgebra/TensorProduct/Decomposition.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Decomposition of tensor product

In this file we show that if `ℳ` is a decomposition of an `R`-module `M` indexed by a type `ι`,
then the `S`-module `S ⊗[R] M` has a decomposition `fun i ↦ (ℳ i).baseChange S` indexed by the
same `ι`.
-/

open TensorProduct LinearMap

namespace DirectSum

variable {ι R M S : Type*} [DecidableEq ι]
  [CommSemiring R] [AddCommMonoid M] [Module R M]
  (ℳ : ι → Submodule R M)
  [CommSemiring S] [Algebra R S]

section Decomposition

variable [Decomposition ℳ]

-- INSTANCE (free from Core): Decomposition.baseChange

theorem toBaseChange_injective (i : ι) : Function.Injective ((ℳ i).toBaseChange S) := fun x y h ↦ by
  have := (Function.Bijective.of_comp_iff (lmap (ℳ · |>.toBaseChange S))
    (by rw [← LinearEquiv.coe_trans]; exact LinearEquiv.bijective _)).1
    (decompose (M := S ⊗[R] M) fun i ↦ (ℳ i).baseChange S).bijective
  refine of_injective (β := fun i ↦ S ⊗[R] ℳ i) i <| this.injective ?_
  simpa using congr(of (fun i ↦ (ℳ i).baseChange S) i $h)

theorem toBaseChange_bijective (i : ι) : Function.Bijective ((ℳ i).toBaseChange S) :=
  ⟨toBaseChange_injective ℳ i, (ℳ i).toBaseChange_surjective S⟩

end Decomposition

namespace IsInternal

theorem baseChange (hm : IsInternal ℳ) : IsInternal fun i ↦ (ℳ i).baseChange S :=
  haveI := hm.chooseDecomposition
  Decomposition.isInternal _

theorem toBaseChange_bijective (hm : IsInternal ℳ) (i : ι) :
    Function.Bijective ((ℳ i).toBaseChange S) :=
  haveI := hm.chooseDecomposition
  DirectSum.toBaseChange_bijective ℳ i

theorem toBaseChange_injective (hm : IsInternal ℳ) (i : ι) :
    Function.Injective ((ℳ i).toBaseChange S) :=
  (toBaseChange_bijective ℳ hm i).injective

end IsInternal

end DirectSum
