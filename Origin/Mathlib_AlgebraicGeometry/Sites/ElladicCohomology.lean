/-
Extracted from AlgebraicGeometry/Sites/ElladicCohomology.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!

# `ℓ`-adic cohomology of a scheme

Let `X` be a scheme and `ℓ` be a prime number. In this file we define the sheaf
associated to the topological group `ℤ_[ℓ]` on the pro-étale site of `X`.
Its cohomology groups are the `ℓ`-adic cohomology groups of `X`.

## Main declarations

- `AlgebraicGeometry.Scheme.ellAdicSheaf`: The sheaf `U ↦ C(U, ℤ_[ℓ])`.
- `AlgebraicGeometry.Scheme.EllAdicCohomology`: The pro-étale cohomology groups `Hⁱ(X, ℤ_[ℓ])`.

## Notes

The `ℓ`-adic cohomology groups of `X : Scheme.{u}` are in `Type (u + 1)`, because
the pro-étale site of `X` has no essentially small subcategory with the same category of sheaves.
Eventually, we will be able to compare the `ℓ`-adic cohomology defined here with the classical
definition using étale cohomology. This will show that the groups defined here are indeed `u`-small.

## References

- [Bhatt, Bhargav and Scholze, Peter, The pro-étale topology for schemes][proetale2015]

-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

-- INSTANCE (free from Core): :

noncomputable def ellAdicSheaf (ℓ : ℕ) [Fact ℓ.Prime] :
    Sheaf (ProEt.topology X) Ab.{u} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafAb (ℤ_[ℓ]), .of_le proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

lemma isZero_ellAdicSheaf_of_isEmpty [IsEmpty X] : IsZero (X.ellAdicSheaf ℓ) :=
  (Sheaf.isTerminalOfEqTop (ProEt.topology_eq_top_of_isEmpty _) _).isZero

def EllAdicCohomology (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) : Type (u + 1) :=
  ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj <| X.ellAdicSheaf ℓ).H n

-- INSTANCE (free from Core): (ℓ

-- INSTANCE (free from Core): [IsEmpty

end AlgebraicGeometry.Scheme
