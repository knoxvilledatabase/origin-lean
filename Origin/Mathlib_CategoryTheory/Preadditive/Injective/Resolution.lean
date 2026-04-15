/-
Extracted from CategoryTheory/Preadditive/Injective/Resolution.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Injective resolutions

An injective resolution `I : InjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed cochain complex `I.cocomplex` of injective objects,
along with a quasi-isomorphism `I.ι` from the cochain complex consisting just of `Z`
in degree zero to `I.cocomplex`.
```
Z ----> 0 ----> ... ----> 0 ----> ...
|       |                 |
|       |                 |
v       v                 v
I⁰ ---> I¹ ---> ... ----> Iⁿ ---> ...
```
-/

noncomputable section

universe v u

namespace CategoryTheory

open Limits HomologicalComplex CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C]

structure InjectiveResolution (Z : C) where
  /-- the cochain complex involved in the resolution -/
  cocomplex : CochainComplex C ℕ
  /-- the cochain complex must be degreewise injective -/
  injective : ∀ n, Injective (cocomplex.X n) := by infer_instance
  /-- the cochain complex must have homology -/
  [hasHomology : ∀ i, cocomplex.HasHomology i]
  /-- the morphism from the single cochain complex with `Z` in degree `0` -/
  ι : (single₀ C).obj Z ⟶ cocomplex
  /-- the morphism from the single cochain complex with `Z` in degree `0` is a quasi-isomorphism -/
  quasiIso : QuasiIso ι := by infer_instance

open InjectiveResolution in

attribute [instance] injective hasHomology InjectiveResolution.quasiIso

class HasInjectiveResolution (Z : C) : Prop where
  out : Nonempty (InjectiveResolution Z)

attribute [inherit_doc HasInjectiveResolution] HasInjectiveResolution.out

variable (C)

class HasInjectiveResolutions : Prop where
  out : ∀ Z : C, HasInjectiveResolution Z

-- INSTANCE (free from Core): 100]

end

namespace InjectiveResolution

variable {Z : C} (I : InjectiveResolution Z)

lemma cocomplex_exactAt_succ (n : ℕ) :
    I.cocomplex.ExactAt (n + 1) := by
  rw [← quasiIsoAt_iff_exactAt I.ι (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

lemma exact_succ (n : ℕ) :
    (ShortComplex.mk _ _ (I.cocomplex.d_comp_d n (n + 1) (n + 2))).Exact :=
  (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp)
    (by simp only [CochainComplex.next]; rfl)).1 (I.cocomplex_exactAt_succ n)
