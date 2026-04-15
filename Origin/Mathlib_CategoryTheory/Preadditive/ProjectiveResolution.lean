/-
Extracted from CategoryTheory/Preadditive/ProjectiveResolution.lean
Genuine: 10 of 12 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Projective resolutions

A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
an `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a quasi-isomorphism `P.π` from `C` to the chain complex consisting just
of `Z` in degree zero.

-/

universe v u

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

attribute [instance 100] HasProjectiveResolutions.out

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

@[simp]
theorem π_f_succ (n : ℕ) : P.π.f (n + 1) = 0 :=
  (isZero_single_obj_X _ _ _ _ (by simp)).eq_of_tgt _ _

@[reassoc (attr := simp)]
theorem complex_d_comp_π_f_zero :
    P.complex.d 1 0 ≫ P.π.f 0 = 0 := by
  rw [← P.π.comm 1 0, single_obj_d, comp_zero]

theorem complex_d_succ_comp (n : ℕ) :
    P.complex.d n (n + 1) ≫ P.complex.d (n + 1) (n + 2) = 0 := by
  simp

@[simp]
noncomputable def cokernelCofork : CokernelCofork (P.complex.d 1 0) :=
  CokernelCofork.ofπ _ P.complex_d_comp_π_f_zero

noncomputable def isColimitCokernelCofork : IsColimit (P.cokernelCofork) := by
  refine IsColimit.ofIsoColimit (P.complex.opcyclesIsCokernel 1 0 (by simp)) ?_
  refine Cofork.ext (P.complex.isoHomologyι₀.symm ≪≫ isoOfQuasiIsoAt P.π 0 ≪≫
    singleObjHomologySelfIso _ _ _) ?_
  rw [← cancel_mono (singleObjHomologySelfIso (ComplexShape.down ℕ) 0 _).inv,
    ← cancel_mono (isoHomologyι₀ _).hom]
  dsimp
  simp only [isoHomologyι₀_inv_naturality_assoc, p_opcyclesMap_assoc, single₀_obj_zero, assoc,
    Iso.hom_inv_id, comp_id, isoHomologyι_inv_hom_id, singleObjHomologySelfIso_inv_homologyι,
    singleObjOpcyclesSelfIso_hom, single₀ObjXSelf, Iso.refl_inv, id_comp]

instance (n : ℕ) : Epi (P.π.f n) := by
  cases n
  · exact epi_of_isColimit_cofork P.isColimitCokernelCofork
  · rw [π_f_succ]; infer_instance

variable (Z)

@[simps]
noncomputable def self [Projective Z] : ProjectiveResolution Z where
  complex := (ChainComplex.single₀ C).obj Z
  π := 𝟙 ((ChainComplex.single₀ C).obj Z)
  projective n := by
    cases n
    · simpa
    · apply IsZero.projective
      apply HomologicalComplex.isZero_single_obj_X
      simp

end ProjectiveResolution

end CategoryTheory
