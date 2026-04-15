/-
Extracted from CategoryTheory/Preadditive/Projective/Resolution.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Projective resolutions

A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a quasi-isomorphism `P.π` from `C` to the chain complex consisting just
of `Z` in degree zero.

-/

universe v u v' u'

namespace CategoryTheory

open Category Limits ChainComplex HomologicalComplex

variable {C : Type u} [Category.{v} C]

open Projective

variable [HasZeroObject C] [HasZeroMorphisms C]

structure ProjectiveResolution (Z : C) where
  /-- the chain complex involved in the resolution -/
  complex : ChainComplex C ℕ
  /-- the chain complex must be degreewise projective -/
  projective : ∀ n, Projective (complex.X n) := by infer_instance
  /-- the chain complex must have homology -/
  [hasHomology : ∀ i, complex.HasHomology i]
  /-- the morphism to the single chain complex with `Z` in degree `0` -/
  π : complex ⟶ (ChainComplex.single₀ C).obj Z
  /-- the morphism to the single chain complex with `Z` in degree `0` is a quasi-isomorphism -/
  quasiIso : QuasiIso π := by infer_instance

open ProjectiveResolution in

attribute [instance] projective hasHomology ProjectiveResolution.quasiIso

class HasProjectiveResolution (Z : C) : Prop where
  out : Nonempty (ProjectiveResolution Z)

variable (C)

class HasProjectiveResolutions : Prop where
  out : ∀ Z : C, HasProjectiveResolution Z

-- INSTANCE (free from Core): 100]

namespace ProjectiveResolution

variable {C}

variable {Z : C} (P : ProjectiveResolution Z)

lemma complex_exactAt_succ (n : ℕ) :
    P.complex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt' P.π (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

lemma exact_succ (n : ℕ) :
    (ShortComplex.mk _ _ (P.complex.d_comp_d (n + 2) (n + 1) n)).Exact :=
  ((HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n) (by simp only [prev]; rfl)
    (by simp)).1 (P.complex_exactAt_succ n)
