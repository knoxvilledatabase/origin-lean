/-
Extracted from Probability/Kernel/Disintegration/StandardBorel.lean
Genuine: 17 of 32 | Dissolved: 1 | Infrastructure: 14
-/
import Origin.Core

/-!
# Existence of disintegration of measures and kernels for standard Borel spaces

Let `κ : Kernel α (β × Ω)` be a finite kernel, where `Ω` is a standard Borel space. Then if `α` is
countable or `β` has a countably generated σ-algebra (for example if it is standard Borel), then
there exists a `Kernel (α × β) Ω` called conditional kernel and denoted by `condKernel κ` such that
`κ = fst κ ⊗ₖ condKernel κ`.
We also define a conditional kernel for a measure `ρ : Measure (β × Ω)`, where `Ω` is a standard
Borel space. This is a `Kernel β Ω` denoted by `ρ.condKernel` such that `ρ = ρ.fst ⊗ₘ ρ.condKernel`.

In order to obtain a disintegration for any standard Borel space `Ω`, we use that these spaces embed
measurably into `ℝ`: it then suffices to define a suitable kernel for `Ω = ℝ`.

For `κ : Kernel α (β × ℝ)`, the construction of the conditional kernel proceeds as follows:
* Build a measurable function `f : (α × β) → ℚ → ℝ` such that for all measurable sets
  `s` and all `q : ℚ`, `∫ x in s, f (a, x) q ∂(Kernel.fst κ a) = (κ a).real (s ×ˢ Iic (q : ℝ))`.
  We restrict to `ℚ` here to be able to prove the measurability.
* Extend that function to `(α × β) → StieltjesFunction ℝ`. See the file `MeasurableStieltjes.lean`.
* Finally obtain from the measurable Stieltjes function a measure on `ℝ` for each element of `α × β`
  in a measurable way: we have obtained a `Kernel (α × β) ℝ`.
  See the file `CDFToKernel.lean` for that step.

The first step (building the measurable function on `ℚ`) is done differently depending on whether
`α` is countable or not.
* If `α` is countable, we can provide for each `a : α` a function `f : β → ℚ → ℝ` and proceed as
  above to obtain a `Kernel β ℝ`. Since `α` is countable, measurability is not an issue and we can
  put those together into a `Kernel (α × β) ℝ`. The construction of that `f` is done in
  the `CondCDF.lean` file.
* If `α` is not countable, we can't proceed separately for each `a : α` and have to build a function
  `f : α × β → ℚ → ℝ` which is measurable on the product. We are able to do so if `β` has a
  countably generated σ-algebra (this is the case in particular for standard Borel spaces).
  See the file `Density.lean`.

The conditional kernel is defined under the typeclass assumption
`CountableOrCountablyGenerated α β`, which encodes the property
`Countable α ∨ CountablyGenerated β`.

Properties of integrals involving `condKernel` are collated in the file `Integral.lean`.
The conditional kernel is unique (almost everywhere w.r.t. `fst κ`): this is proved in the file
`Unique.lean`.

## Main definitions

* `ProbabilityTheory.Kernel.condKernel κ : Kernel (α × β) Ω`: conditional kernel described above.
* `MeasureTheory.Measure.condKernel ρ : Kernel β Ω`: conditional kernel of a measure.

## Main statements

* `ProbabilityTheory.Kernel.compProd_fst_condKernel`: `fst κ ⊗ₖ condKernel κ = κ`
* `MeasureTheory.Measure.compProd_fst_condKernel`: `ρ.fst ⊗ₘ ρ.condKernel = ρ`
-/

open MeasureTheory Set Filter MeasurableSpace

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {α β γ Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} [MeasurableSpace.CountablyGenerated γ]
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [Nonempty Ω]

section Real

/-! ### Disintegration of kernels from `α` to `γ × ℝ` for countably generated `γ` -/

lemma isRatCondKernelCDFAux_density_Iic (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsRatCondKernelCDFAux (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q)) κ (fst κ) where
  measurable := measurable_pi_iff.mpr fun _ ↦ measurable_density κ (fst κ) measurableSet_Iic
  mono' a q r hqr :=
    ae_of_all _ fun c ↦ density_mono_set le_rfl a c (Iic_subset_Iic.mpr (by exact_mod_cast hqr))
  nonneg' _ _ := ae_of_all _ fun _ ↦ density_nonneg le_rfl _ _ _
  le_one' _ _ := ae_of_all _ fun _ ↦ density_le_one le_rfl _ _ _
  tendsto_integral_of_antitone a s hs_anti hs_tendsto := by
    let s' : ℕ → Set ℝ := fun n ↦ Iic (s n)
    refine tendsto_integral_density_of_antitone le_rfl a s' ?_ ?_ (fun _ ↦ measurableSet_Iic)
    · refine fun i j hij ↦ Iic_subset_Iic.mpr ?_
      exact mod_cast hs_anti hij
    · ext x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le, s']
      rw [tendsto_atTop_atBot] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_lt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, lt_of_le_of_lt ?_ hq⟩
      exact mod_cast hi i le_rfl
  tendsto_integral_of_monotone a s hs_mono hs_tendsto := by
    rw [fst_real_apply _ _ MeasurableSet.univ]
    let s' : ℕ → Set ℝ := fun n ↦ Iic (s n)
    refine tendsto_integral_density_of_monotone (le_rfl : fst κ ≤ fst κ)
      a s' ?_ ?_ (fun _ ↦ measurableSet_Iic)
    · exact fun i j hij ↦ Iic_subset_Iic.mpr (by exact mod_cast hs_mono hij)
    · ext x
      simp only [mem_iUnion, mem_univ, iff_true]
      rw [tendsto_atTop_atTop] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_gt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, hq.le.trans ?_⟩
      exact mod_cast hi i le_rfl
  integrable a _ := integrable_density le_rfl a measurableSet_Iic
  setIntegral a _ hA _ := setIntegral_density le_rfl a measurableSet_Iic hA

lemma isRatCondKernelCDF_density_Iic (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsRatCondKernelCDF (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q)) κ (fst κ) :=
  (isRatCondKernelCDFAux_density_Iic κ).isRatCondKernelCDF

noncomputable

def condKernelCDF (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] : α × γ → StieltjesFunction ℝ :=
  stieltjesOfMeasurableRat (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q))
    (isRatCondKernelCDF_density_Iic κ).measurable

lemma isCondKernelCDF_condKernelCDF (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsCondKernelCDF (condKernelCDF κ) κ (fst κ) :=
  isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_density_Iic κ)

noncomputable

def condKernelReal (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] : Kernel (α × γ) ℝ :=
  (isCondKernelCDF_condKernelCDF κ).toKernel

-- INSTANCE (free from Core): instIsMarkovKernelCondKernelReal

lemma compProd_fst_condKernelReal (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernelReal κ = κ := by
  rw [condKernelReal, compProd_toKernel]

noncomputable

def condKernelUnitReal (κ : Kernel Unit (α × ℝ)) [IsFiniteKernel κ] : Kernel (Unit × α) ℝ :=
  (isCondKernelCDF_condCDF (κ ())).toKernel

-- INSTANCE (free from Core): instIsMarkovKernelCondKernelUnitReal

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): condKernelUnitReal.instIsCondKernel

end Real

section BorelSnd

/-! ### Disintegration of kernels on standard Borel spaces

Since every standard Borel space embeds measurably into `ℝ`, we can generalize a disintegration
property on `ℝ` to all these spaces. -/

open Classical in

noncomputable

def borelMarkovFromReal (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (η : Kernel α ℝ) :
    Kernel α Ω :=
  have he := measurableEmbedding_embeddingReal Ω
  let x₀ := (range_nonempty (embeddingReal Ω)).choose
  comapRight
    (piecewise ((Kernel.measurable_coe η he.measurableSet_range.compl) (measurableSet_singleton 0) :
        MeasurableSet {a | η a (range (embeddingReal Ω))ᶜ = 0})
      η (deterministic (fun _ ↦ x₀) measurable_const)) he

lemma borelMarkovFromReal_apply (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (η : Kernel α ℝ) (a : α) :
    borelMarkovFromReal Ω η a
      = if η a (range (embeddingReal Ω))ᶜ = 0 then (η a).comap (embeddingReal Ω)
        else (Measure.dirac (range_nonempty (embeddingReal Ω)).choose).comap (embeddingReal Ω) := by
  classical
  rw [borelMarkovFromReal, comapRight_apply, piecewise_apply, deterministic_apply]
  simp only [mem_preimage, mem_singleton_iff]
  split_ifs <;> rfl

lemma borelMarkovFromReal_apply' (Ω : Type*) [Nonempty Ω] [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (η : Kernel α ℝ) (a : α) {s : Set Ω} (hs : MeasurableSet s) :
    borelMarkovFromReal Ω η a s
      = if η a (range (embeddingReal Ω))ᶜ = 0 then η a (embeddingReal Ω '' s)
        else (embeddingReal Ω '' s).indicator 1 (range_nonempty (embeddingReal Ω)).choose := by
  have he := measurableEmbedding_embeddingReal Ω
  rw [borelMarkovFromReal_apply]
  split_ifs with h
  · rw [Measure.comap_apply _ he.injective he.measurableSet_image' _ hs]
  · rw [Measure.comap_apply _ he.injective he.measurableSet_image' _ hs, Measure.dirac_apply]

-- INSTANCE (free from Core): instIsSFiniteKernelBorelMarkovFromReal

-- INSTANCE (free from Core): instIsFiniteKernelBorelMarkovFromReal

-- INSTANCE (free from Core): instIsMarkovKernelBorelMarkovFromReal

lemma compProd_fst_borelMarkovFromReal_eq_comapRight_compProd
    (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ] (η : Kernel (α × β) ℝ) [IsSFiniteKernel η]
    (hη : (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω)))) ⊗ₖ η
      = map κ (Prod.map (id : β → β) (embeddingReal Ω))) :
    fst κ ⊗ₖ borelMarkovFromReal Ω η
      = comapRight (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω))) ⊗ₖ η)
        (MeasurableEmbedding.id.prodMap (measurableEmbedding_embeddingReal Ω)) := by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β → β) e)
  have hη' : fst κ' ⊗ₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β → β) e) :=
    MeasurableEmbedding.id.prodMap he
  change fst κ ⊗ₖ borelMarkovFromReal Ω η = comapRight (fst κ' ⊗ₖ η) h_prod_embed
  rw [comapRight_compProd_id_prod _ _ he]
  have h_fst : fst κ' = fst κ := by
    ext a u
    unfold κ'
    rw [fst_apply, map_apply _ (by fun_prop),
      Measure.map_map measurable_fst h_prod_embed.measurable, fst_apply]
    congr
  rw [h_fst]
  ext a t ht : 2
  simp_rw [compProd_apply ht]
  refine lintegral_congr_ae ?_
  have h_ae : ∀ᵐ t ∂(fst κ a), (a, t) ∈ {p : α × β | η p (range e)ᶜ = 0} := by
    rw [← h_fst]
    have h_compProd : κ' a (univ ×ˢ range e)ᶜ = 0 := by
      unfold κ'
      rw [map_apply' _ (by fun_prop)]
      swap; · exact (MeasurableSet.univ.prod he.measurableSet_range).compl
      suffices Prod.map id e ⁻¹' (univ ×ˢ range e)ᶜ = ∅ by rw [this]; simp
      ext x
      simp
    rw [← hη', compProd_null] at h_compProd
    swap; · exact (MeasurableSet.univ.prod he.measurableSet_range).compl
    simp only [preimage_compl, mem_univ, mk_preimage_prod_right] at h_compProd
    exact h_compProd
  filter_upwards [h_ae] with a ha
  rw [borelMarkovFromReal, comapRight_apply', comapRight_apply']
  rotate_left
  · exact measurable_prodMk_left ht
  · exact measurable_prodMk_left ht
  classical
  rw [piecewise_apply, if_pos]
  exact ha

lemma compProd_fst_borelMarkovFromReal (κ : Kernel α (β × Ω)) [IsSFiniteKernel κ]
    (η : Kernel (α × β) ℝ) [IsSFiniteKernel η]
    (hη : (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω)))) ⊗ₖ η
      = map κ (Prod.map (id : β → β) (embeddingReal Ω))) :
    fst κ ⊗ₖ borelMarkovFromReal Ω η = κ := by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β → β) e)
  have hη' : fst κ' ⊗ₖ η = κ' := hη
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β → β) e) :=
    MeasurableEmbedding.id.prodMap he
  have : κ = comapRight κ' h_prod_embed := by
    ext c t : 2
    unfold κ'
    rw [comapRight_apply, map_apply _ (by fun_prop), h_prod_embed.comap_map]
  conv_rhs => rw [this, ← hη']
  exact compProd_fst_borelMarkovFromReal_eq_comapRight_compProd κ η hη

end BorelSnd

section CountablyGenerated

open ProbabilityTheory.Kernel

noncomputable

def condKernelBorel (κ : Kernel α (γ × Ω)) [IsFiniteKernel κ] : Kernel (α × γ) Ω :=
  let κ' := map κ (Prod.map (id : γ → γ) (embeddingReal Ω))
  borelMarkovFromReal Ω (condKernelReal κ')

-- INSTANCE (free from Core): instIsMarkovKernelCondKernelBorel

-- INSTANCE (free from Core): condKernelBorel.instIsCondKernel

end CountablyGenerated

section Unit

variable (κ : Kernel Unit (α × Ω)) [IsFiniteKernel κ]

noncomputable

def condKernelUnitBorel : Kernel (Unit × α) Ω :=
  let κ' := map κ (Prod.map (id : α → α) (embeddingReal Ω))
  borelMarkovFromReal Ω (condKernelUnitReal κ')

-- INSTANCE (free from Core): instIsMarkovKernelCondKernelUnitBorel

-- INSTANCE (free from Core): condKernelUnitBorel.instIsCondKernel

end Unit

section Measure

variable {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

noncomputable

irreducible_def _root_.MeasureTheory.Measure.condKernel (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    Kernel α Ω :=
  comap (condKernelUnitBorel (const Unit ρ)) (fun a ↦ ((), a)) measurable_prodMk_left

lemma _root_.MeasureTheory.Measure.condKernel_apply (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ]
    (a : α) :
    ρ.condKernel a = condKernelUnitBorel (const Unit ρ) ((), a) := by
  rw [Measure.condKernel]; rfl

-- INSTANCE (free from Core): _root_.MeasureTheory.Measure.condKernel.instIsCondKernel

-- INSTANCE (free from Core): _root_.MeasureTheory.Measure.instIsMarkovKernelCondKernel

-- DISSOLVED: _root_.MeasureTheory.Measure.condKernel_apply_of_ne_zero

end Measure

section CountableOrCountablyGenerated

variable [h : CountableOrCountablyGenerated α β] (κ : Kernel α (β × Ω)) [IsFiniteKernel κ]

open Classical in

noncomputable

irreducible_def condKernel : Kernel (α × β) Ω :=
  if hα : Countable α then
    condKernelCountable (fun a ↦ (κ a).condKernel)
      fun x y h ↦ by simp [apply_congr_of_mem_measurableAtom _ h]
  else letI := h.countableOrCountablyGenerated.resolve_left hα; condKernelBorel κ

-- INSTANCE (free from Core): instIsMarkovKernelCondKernel

-- INSTANCE (free from Core): condKernel.instIsCondKernel

end CountableOrCountablyGenerated

end ProbabilityTheory.Kernel
