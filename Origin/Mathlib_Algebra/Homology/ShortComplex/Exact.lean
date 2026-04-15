/-
Extracted from Algebra/Homology/ShortComplex/Exact.lean
Genuine: 20 of 23 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Exact short complexes

When `S : ShortComplex C`, this file defines a structure
`S.Exact` which expresses the exactness of `S`, i.e. there
exists a homology data `h : S.HomologyData` such that
`h.left.H` is zero. When `[S.HasHomology]`, it is equivalent
to the assertion `IsZero S.homology`.

Almost by construction, this notion of exactness is self dual,
see `Exact.op` and `Exact.unop`.

-/

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C D : Type*} [Category* C] [Category* D]

namespace ShortComplex

variable
  [HasZeroMorphisms C] [HasZeroMorphisms D] (S : ShortComplex C) {S₁ S₂ : ShortComplex C}

structure Exact : Prop where
  /-- the condition that there exists a homology data whose `left.H` field is zero -/
  condition : ∃ (h : S.HomologyData), IsZero h.left.H

variable {S}

lemma Exact.hasHomology (h : S.Exact) : S.HasHomology :=
  HasHomology.mk' h.condition.choose

lemma Exact.hasZeroObject (h : S.Exact) : HasZeroObject C :=
  ⟨h.condition.choose.left.H, h.condition.choose_spec⟩

variable (S)

lemma exact_iff_isZero_homology [S.HasHomology] :
    S.Exact ↔ IsZero S.homology := by
  constructor
  · rintro ⟨⟨h', z⟩⟩
    exact IsZero.of_iso z h'.left.homologyIso
  · intro h
    exact ⟨⟨_, h⟩⟩

variable {S}

lemma LeftHomologyData.exact_iff [S.HasHomology]
    (h : S.LeftHomologyData) :
    S.Exact ↔ IsZero h.H := by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso

lemma RightHomologyData.exact_iff [S.HasHomology]
    (h : S.RightHomologyData) :
    S.Exact ↔ IsZero h.H := by
  rw [S.exact_iff_isZero_homology]
  exact Iso.isZero_iff h.homologyIso

variable (S)

lemma exact_iff_isZero_leftHomology [S.HasHomology] :
    S.Exact ↔ IsZero S.leftHomology :=
  LeftHomologyData.exact_iff _

lemma exact_iff_isZero_rightHomology [S.HasHomology] :
    S.Exact ↔ IsZero S.rightHomology :=
  RightHomologyData.exact_iff _

variable {S}

lemma HomologyData.exact_iff (h : S.HomologyData) :
    S.Exact ↔ IsZero h.left.H := by
  haveI := HasHomology.mk' h
  exact LeftHomologyData.exact_iff h.left

lemma HomologyData.exact_iff' (h : S.HomologyData) :
    S.Exact ↔ IsZero h.right.H := by
  haveI := HasHomology.mk' h
  exact RightHomologyData.exact_iff h.right

variable (S)

lemma exact_iff_homology_iso_zero [S.HasHomology] [HasZeroObject C] :
    S.Exact ↔ Nonempty (S.homology ≅ 0) := by
  rw [exact_iff_isZero_homology]
  constructor
  · intro h
    exact ⟨h.isoZero⟩
  · rintro ⟨e⟩
    exact IsZero.of_iso (isZero_zero C) e

lemma exact_iff_of_iso (e : S₁ ≅ S₂) : S₁.Exact ↔ S₂.Exact :=
  ⟨exact_of_iso e, exact_of_iso e.symm⟩

lemma exact_and_mono_f_iff_of_iso (e : S₁ ≅ S₂) :
    S₁.Exact ∧ Mono S₁.f ↔ S₂.Exact ∧ Mono S₂.f := by
  have : Mono S₁.f ↔ Mono S₂.f :=
    (MorphismProperty.monomorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (ShortComplex.π₁.mapIso e) (ShortComplex.π₂.mapIso e) e.hom.comm₁₂)
  rw [exact_iff_of_iso e, this]

lemma exact_and_epi_g_iff_of_iso (e : S₁ ≅ S₂) :
    S₁.Exact ∧ Epi S₁.g ↔ S₂.Exact ∧ Epi S₂.g := by
  have : Epi S₁.g ↔ Epi S₂.g :=
    (MorphismProperty.epimorphisms C).arrow_mk_iso_iff
      (Arrow.isoMk (ShortComplex.π₂.mapIso e) (ShortComplex.π₃.mapIso e) e.hom.comm₂₃)
  rw [exact_iff_of_iso e, this]

lemma exact_of_isZero_X₂ (h : IsZero S.X₂) : S.Exact := by
  rw [(HomologyData.ofZeros S (IsZero.eq_of_tgt h _ _) (IsZero.eq_of_src h _ _)).exact_iff]
  exact h

lemma exact_iff_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    S₁.Exact ↔ S₂.Exact := by
  constructor
  · rintro ⟨h₁, z₁⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono φ h₁, z₁⟩
  · rintro ⟨h₂, z₂⟩
    exact ⟨HomologyData.ofEpiOfIsIsoOfMono' φ h₂, z₂⟩

variable {S}

lemma HomologyData.exact_iff_i_p_zero (h : S.HomologyData) :
    S.Exact ↔ h.left.i ≫ h.right.p = 0 := by
  haveI := HasHomology.mk' h
  rw [h.left.exact_iff, ← h.comm]
  constructor
  · intro z
    rw [IsZero.eq_of_src z h.iso.hom 0, zero_comp, comp_zero]
  · intro eq
    simp only [IsZero.iff_id_eq_zero, ← cancel_mono h.iso.hom, id_comp, ← cancel_mono h.right.ι,
      ← cancel_epi h.left.π, eq, zero_comp, comp_zero]

variable (S)

lemma exact_iff_i_p_zero [S.HasHomology] (h₁ : S.LeftHomologyData)
    (h₂ : S.RightHomologyData) :
    S.Exact ↔ h₁.i ≫ h₂.p = 0 :=
  (HomologyData.ofIsIsoLeftRightHomologyComparison' h₁ h₂).exact_iff_i_p_zero

lemma exact_iff_iCycles_pOpcycles_zero [S.HasHomology] :
    S.Exact ↔ S.iCycles ≫ S.pOpcycles = 0 :=
  S.exact_iff_i_p_zero _ _

lemma exact_iff_kernel_ι_comp_cokernel_π_zero [S.HasHomology]
    [HasKernel S.g] [HasCokernel S.f] :
    S.Exact ↔ kernel.ι S.g ≫ cokernel.π S.f = 0 := by
  haveI := HasLeftHomology.hasCokernel S
  haveI := HasRightHomology.hasKernel S
  exact S.exact_iff_i_p_zero (LeftHomologyData.ofHasKernelOfHasCokernel S)
    (RightHomologyData.ofHasCokernelOfHasKernel S)

variable {S}

variable (S)
