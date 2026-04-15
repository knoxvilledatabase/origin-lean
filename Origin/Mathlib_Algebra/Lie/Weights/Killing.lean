/-
Extracted from Algebra/Lie/Weights/Killing.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Roots of Lie algebras with non-degenerate Killing forms

The file contains definitions and results about roots of Lie algebras with non-degenerate Killing
forms.

## Main definitions
* `LieAlgebra.IsKilling.ker_restrict_eq_bot_of_isCartanSubalgebra`: if the Killing form of
  a Lie algebra is non-singular, it remains non-singular when restricted to a Cartan subalgebra.
* `LieAlgebra.IsKilling.instIsLieAbelianOfIsCartanSubalgebra`: if the Killing form of a Lie
  algebra is non-singular, then its Cartan subalgebras are Abelian.
* `LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`: over a perfect field, if a Lie
  algebra has non-degenerate Killing form, Cartan subalgebras contain only semisimple elements.
* `LieAlgebra.IsKilling.span_weight_eq_top`: given a splitting Cartan subalgebra `H` of a
  finite-dimensional Lie algebra with non-singular Killing form, the corresponding roots span the
  dual space of `H`.
* `LieAlgebra.IsKilling.coroot`: the coroot corresponding to a root.
* `LieAlgebra.IsKilling.isCompl_ker_weight_span_coroot`: given a root `α` with respect to a Cartan
  subalgebra `H`, we have a natural decomposition of `H` as the kernel of `α` and the span of the
  coroot corresponding to `α`.
* `LieAlgebra.IsKilling.finrank_rootSpace_eq_one`: root spaces are one-dimensional.
* `LieAlgebra.IsKilling.lieIdeal_eq_inf_cartan_sup_biSup_rootSpace`: a Lie ideal decomposes as its
  intersection with the Cartan subalgebra plus a sum of root spaces.

-/

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

namespace LieAlgebra

namespace IsKilling

variable [IsKilling R L]

lemma ker_restrict_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker ((killingForm R L).restrict H) = ⊥ := by
  have h : Codisjoint (rootSpace H 0) (LieModule.posFittingComp R H L) :=
    (LieModule.isCompl_genWeightSpace_zero_posFittingComp R H L).codisjoint
  replace h : Codisjoint (H : Submodule R L) (LieModule.posFittingComp R H L : Submodule R L) := by
    rwa [codisjoint_iff, ← LieSubmodule.toSubmodule_inj, LieSubmodule.sup_toSubmodule,
      LieSubmodule.top_toSubmodule, rootSpace_zero_eq R L H, LieSubalgebra.coe_toLieSubmodule,
      ← codisjoint_iff] at h
  suffices this : ∀ m₀ ∈ H, ∀ m₁ ∈ LieModule.posFittingComp R H L, killingForm R L m₀ m₁ = 0 by
    simp [LinearMap.BilinForm.ker_restrict_eq_of_codisjoint h this]
  intro m₀ h₀ m₁ h₁
  exact killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting R L H (le_zeroRootSubalgebra R L H h₀) h₁
