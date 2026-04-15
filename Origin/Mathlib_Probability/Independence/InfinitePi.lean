/-
Extracted from Probability/Independence/InfinitePi.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Independence of an infinite family of random variables

In this file we provide several results about independence of arbitrary families of random
variables, relying on `Measure.infinitePi`.

## Implementation note

There are several possible measurability assumptions:
* The map `ω ↦ (Xᵢ(ω))ᵢ` is measurable.
* For all `i`, the map `ω ↦ Xᵢ(ω)` is measurable.
* The map `ω ↦ (Xᵢ(ω))ᵢ` is almost everywhere measurable.
* For all `i`, the map `ω ↦ Xᵢ(ω)` is almost everywhere measurable.
Although the first two options are equivalent, the last two are not if the index set is not
countable.
-/

open MeasureTheory Measure ProbabilityTheory

namespace ProbabilityTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓧 : ι → Type*} {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {X : Π i, Ω → 𝓧 i}

lemma iIndepFun_iff_map_fun_eq_infinitePi_map₀ (mX : AEMeasurable (fun ω i ↦ X i ω) P) :
    iIndepFun X P ↔ P.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ P.map (X i)) where
  mp h := by
    have _ i := isProbabilityMeasure_map (mX.eval i)
    refine eq_infinitePi _ fun s t ht ↦ ?_
    rw [iIndepFun_iff_finset] at h
    have : (s : Set ι).pi t = s.restrict ⁻¹' (Set.univ.pi fun i ↦ t i) := by ext; simp
    rw [this, ← map_apply, AEMeasurable.map_map_of_aemeasurable]
    · have : s.restrict ∘ (fun ω i ↦ X i ω) = fun ω i ↦ s.restrict X i ω := by ext; simp
      rw [this, (iIndepFun_iff_map_fun_eq_pi_map ?_).1 (h s), pi_pi]
      · simp only [Finset.restrict]
        rw [s.prod_coe_sort fun i ↦ P.map (X i) (t i)]
      exact fun i ↦ mX.eval i
    any_goals fun_prop
    · exact mX
    · exact .univ_pi fun i ↦ ht i
  mpr h := by
    have _ i := isProbabilityMeasure_map (mX.eval i)
    rw [iIndepFun_iff_finset]
    intro s
    rw [iIndepFun_iff_map_fun_eq_pi_map]
    · have : s.restrict ∘ (fun ω i ↦ X i ω) = fun ω i ↦ s.restrict X i ω := by ext; simp
      rw [← this, ← AEMeasurable.map_map_of_aemeasurable, h, infinitePi_map_restrict]
      · simp
      · fun_prop
      exact mX
    exact fun i ↦ mX.eval i

lemma iIndepFun_iff_map_fun_eq_infinitePi_map₀' [Countable ι] (mX : ∀ i, AEMeasurable (X i) P) :
    iIndepFun X P ↔ P.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ P.map (X i)) :=
  iIndepFun_iff_map_fun_eq_infinitePi_map₀ <| aemeasurable_pi_iff.2 mX

lemma iIndepFun_iff_map_fun_eq_infinitePi_map (mX : ∀ i, Measurable (X i)) :
    iIndepFun X P ↔ P.map (fun ω i ↦ X i ω) = infinitePi (fun i ↦ P.map (X i)) :=
  iIndepFun_iff_map_fun_eq_infinitePi_map₀ <| measurable_pi_iff.2 mX |>.aemeasurable

lemma iIndepFun_infinitePi {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {P : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (P i)] {X : (i : ι) → Ω i → 𝓧 i}
    (mX : ∀ i, Measurable (X i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (infinitePi P) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop), infinitePi_map_pi _ mX]
  congrm infinitePi fun i ↦ ?_
  rw [← infinitePi_map_eval P i, map_map (mX i) (by fun_prop), Function.comp_def]

section curry

omit [IsProbabilityMeasure P]

section dependent

variable {κ : ι → Type*} {𝓧 : (i : ι) → κ i → Type*} {m𝓧 : ∀ i j, MeasurableSpace (𝓧 i j)}

lemma iIndepFun_uncurry {X : (i : ι) → (j : κ i) → Ω → 𝓧 i j} (mX : ∀ i j, Measurable (X i j))
    (h1 : iIndepFun (fun i ω ↦ (X i · ω)) P) (h2 : ∀ i, iIndepFun (X i) P) :
    iIndepFun (fun (p : (i : ι) × (κ i)) ω ↦ X p.1 p.2 ω) P := by
  have := h1.isProbabilityMeasure
  have : ∀ i j, IsProbabilityMeasure (P.map (X i j)) :=
    fun i j ↦ isProbabilityMeasure_map (mX i j).aemeasurable
  have : ∀ i, IsProbabilityMeasure (P.map (fun ω ↦ (X i · ω))) :=
    fun i ↦ isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  have : (MeasurableEquiv.piCurry 𝓧) ∘ (fun ω p ↦ X p.1 p.2 ω) = fun ω i j ↦ X i j ω := by
    ext; simp [Sigma.curry]
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop),
    ← (MeasurableEquiv.piCurry 𝓧).map_measurableEquiv_injective.eq_iff,
    map_map (by fun_prop) (by fun_prop), this,
    (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 h1,
    infinitePi_map_piCurry (fun i j ↦ P.map (X i j))]
  congrm infinitePi fun i ↦ ?_
  rw [(iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).1 (h2 i)]

lemma iIndepFun_uncurry_infinitePi {Ω : (i : ι) → κ i → Type*} {mΩ : ∀ i j, MeasurableSpace (Ω i j)}
    {X : (i : ι) → (j : κ i) → Ω i j → 𝓧 i j}
    (μ : (i : ι) → (j : κ i) → Measure (Ω i j)) [∀ i j, IsProbabilityMeasure (μ i j)]
    (mX : ∀ i j, Measurable (X i j)) :
    iIndepFun (fun (p : (i : ι) × κ i) (ω : Π i, Π j, Ω i j) ↦ X p.1 p.2 (ω p.1 p.2))
      (infinitePi (fun i ↦ infinitePi (μ i))) := by
  refine iIndepFun_uncurry (P := infinitePi (fun i ↦ infinitePi (μ i)))
    (X := fun i j ω ↦ X i j (ω i j)) (by fun_prop) ?_ fun i ↦ ?_
  · exact iIndepFun_infinitePi (P := fun i ↦ infinitePi (μ i))
      (X := fun i u j ↦ X i j (u j)) (by fun_prop)
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  change map ((fun f ↦ f i) ∘ (fun ω i j ↦ X i j (ω i j)))
    (infinitePi fun i ↦ infinitePi (μ i)) = _
  rw [← map_map (by fun_prop) (by fun_prop),
    infinitePi_map_pi (X := fun i ↦ (j : κ i) → Ω i j) (μ := fun i ↦ infinitePi (μ i))
      (f := fun i f j ↦ X i j (f j)), @infinitePi_map_eval .., infinitePi_map_pi]
  · congrm infinitePi fun j ↦ ?_
    change _ = map (((fun f ↦ f j) ∘ (fun f ↦ f i)) ∘ (fun ω i j ↦ X i j (ω i j)))
      (infinitePi fun i ↦ infinitePi (μ i))
    rw [← map_map (by fun_prop) (by fun_prop), infinitePi_map_pi (X := fun i ↦ (j : κ i) → Ω i j)
        (μ := fun i ↦ infinitePi (μ i)) (f := fun i f j ↦ X i j (f j)),
        ← map_map (by fun_prop) (by fun_prop),
        @infinitePi_map_eval .., infinitePi_map_pi, @infinitePi_map_eval ..]
    any_goals fun_prop
    · exact fun _ ↦ isProbabilityMeasure_map (by fun_prop)
    · exact fun _ ↦ isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))
  any_goals fun_prop
  exact fun _ ↦ isProbabilityMeasure_map (Measurable.aemeasurable (by fun_prop))

end dependent

section nondependent

variable {κ : Type*} {𝓧 : ι → κ → Type*} {m𝓧 : ∀ i j, MeasurableSpace (𝓧 i j)}

lemma iIndepFun_uncurry' {X : (i : ι) → (j : κ) → Ω → 𝓧 i j} (mX : ∀ i j, Measurable (X i j))
    (h1 : iIndepFun (fun i ω ↦ (X i · ω)) P) (h2 : ∀ i, iIndepFun (X i) P) :
    iIndepFun (fun (p : ι × κ) ω ↦ X p.1 p.2 ω) P :=
  (iIndepFun_uncurry mX h1 h2).of_precomp (Equiv.sigmaEquivProd ι κ).surjective

lemma iIndepFun_uncurry_infinitePi' {Ω : ι → κ → Type*} {mΩ : ∀ i j, MeasurableSpace (Ω i j)}
    {X : (i : ι) → (j : κ) → Ω i j → 𝓧 i j}
    (μ : (i : ι) → (j : κ) → Measure (Ω i j)) [∀ i j, IsProbabilityMeasure (μ i j)]
    (mX : ∀ i j, Measurable (X i j)) :
    iIndepFun (fun (p : ι × κ) (ω : Π i, Π j, Ω i j) ↦ X p.1 p.2 (ω p.1 p.2))
      (infinitePi (fun i ↦ infinitePi (μ i))) :=
  (iIndepFun_uncurry_infinitePi μ mX).of_precomp (Equiv.sigmaEquivProd ι κ).surjective

end nondependent

end curry

end ProbabilityTheory
