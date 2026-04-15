/-
Extracted from Analysis/Meromorphic/NormalForm.lean
Genuine: 10 of 16 | Dissolved: 5 | Infrastructure: 1
-/
import Origin.Core

/-!
# Normal form of meromorphic functions and continuous extension

If a function `f` is meromorphic on `U` and if `g` differs from `f` only along a set that is
codiscrete within `U`, then `g` is likewise meromorphic. The set of meromorphic functions is
therefore huge, and `=ᶠ[codiscreteWithin U]` defines an equivalence relation.

This file implements continuous extension to provide an API that allows picking the 'unique best'
representative of any given equivalence class, where 'best' means that the representative can
locally near any point `x` be written 'in normal form', as `f =ᶠ[𝓝 x] fun z ↦ (z - x) ^ n • g`
where `g` is analytic and does not vanish at `x`.

The relevant notions are `MeromorphicNFAt` and `MeromorphicNFOn`; these guarantee normal
form at a single point and along a set, respectively.
-/

open Topology WithTop

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → 𝕜}
  {x : 𝕜}
  {U : Set 𝕜}

/-!
## Normal form of meromorphic functions at a given point

### Definition and characterizations
-/

variable (f x) in

def MeromorphicNFAt :=
  f =ᶠ[𝓝 x] 0 ∨
    ∃ (n : ℤ) (g : 𝕜 → E), AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧ f =ᶠ[𝓝 x] (· - x) ^ n • g

theorem meromorphicNFAt_iff_analyticAt_or :
    MeromorphicNFAt f x ↔
      AnalyticAt 𝕜 f x ∨ (MeromorphicAt f x ∧ meromorphicOrderAt f x < 0 ∧ f x = 0) := by
  constructor
  · rintro (h | ⟨n, g, h₁g, h₂g, h₃g⟩)
    · simp [(analyticAt_congr h).2 analyticAt_const]
    · have hf : MeromorphicAt f x := by
        apply MeromorphicAt.congr _ (h₃g.filter_mono nhdsWithin_le_nhds).symm
        fun_prop
      have : meromorphicOrderAt f x = n := by
        rw [meromorphicOrderAt_eq_int_iff hf]
        use g, h₁g, h₂g
        exact eventually_nhdsWithin_of_eventually_nhds h₃g
      by_cases! hn : 0 ≤ n
      · left
        rw [analyticAt_congr h₃g]
        apply (AnalyticAt.zpow_nonneg (by fun_prop) hn).smul h₁g
      · right
        use hf
        simp [this, WithTop.coe_lt_zero.2 hn, h₃g.eq_of_nhds,
          zero_zpow n hn.ne]
  · rintro (h | ⟨h₁, h₂, h₃⟩)
    · by_cases h₂f : analyticOrderAt f x = ⊤
      · rw [analyticOrderAt_eq_top] at h₂f
        tauto
      · right
        use analyticOrderNatAt f x
        have : analyticOrderAt f x ≠ ⊤ := h₂f
        rw [← ENat.coe_toNat_eq_self, eq_comm, h.analyticOrderAt_eq_natCast] at this
        obtain ⟨g, h₁g, h₂g, h₃g⟩ := this
        use g, h₁g, h₂g
        simpa
    · right
      lift meromorphicOrderAt f x to ℤ using LT.lt.ne_top h₂ with n hn
      obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff h₁).1 hn.symm
      use n, g, h₁g, h₂g
      filter_upwards [eventually_nhdsWithin_iff.1 h₃g]
      intro z hz
      by_cases h₁z : z = x
      · simp only [h₁z, Pi.smul_apply', Pi.pow_apply, sub_self]
        rw [h₃]
        apply (smul_eq_zero_of_left (zero_zpow n _) (g x)).symm
        by_contra hCon
        simp [hCon] at h₂
      · exact hz h₁z

/-!
### Relation to other properties of functions
-/

theorem MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt (hf : MeromorphicNFAt f x) :
    0 ≤ meromorphicOrderAt f x ↔ AnalyticAt 𝕜 f x := by
  constructor <;> intro h₂f
  · rw [meromorphicNFAt_iff_analyticAt_or] at hf
    rcases hf with h | ⟨_, h₃f, _⟩
    · exact h
    · by_contra h'
      exact lt_irrefl 0 (lt_of_le_of_lt h₂f h₃f)
  · rw [h₂f.meromorphicOrderAt_eq]
    simp

theorem AnalyticAt.meromorphicNFAt (hf : AnalyticAt 𝕜 f x) :
    MeromorphicNFAt f x := by
  simp [meromorphicNFAt_iff_analyticAt_or, hf]

theorem MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin {U : Set 𝕜}
    (hf : MeromorphicOn f U) :
    { x | MeromorphicNFAt f x } ∈ Filter.codiscreteWithin U := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with _ ha
  exact ha.meromorphicNFAt

/-!
### Vanishing and order
-/

-- DISSOLVED: MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff

/-!
### Local nature of the definition and local identity theorem
-/

theorem MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds {g : 𝕜 → E}
    (hf : MeromorphicNFAt f x) (hg : MeromorphicNFAt g x) :
    f =ᶠ[𝓝[≠] x] g ↔ f =ᶠ[𝓝 x] g := by
  constructor
  · intro h
    have t₀ := meromorphicOrderAt_congr h
    by_cases cs : meromorphicOrderAt f x = 0
    · rw [cs] at t₀
      have Z := (hf.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq cs.symm)).continuousAt
      have W := (hg.meromorphicOrderAt_nonneg_iff_analyticAt.1 (le_of_eq t₀)).continuousAt
      exact (Z.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE W).1 h
    · apply eventuallyEq_nhds_of_eventuallyEq_nhdsNE h
      let h₁f := cs
      rw [hf.meromorphicOrderAt_eq_zero_iff] at h₁f
      let h₁g := cs
      rw [t₀, hg.meromorphicOrderAt_eq_zero_iff] at h₁g
      simp only [not_not] at *
      rw [h₁f, h₁g]
  · exact (Filter.EventuallyEq.filter_mono · nhdsWithin_le_nhds)

theorem meromorphicNFAt_congr {g : 𝕜 → E} (hfg : f =ᶠ[𝓝 x] g) :
    MeromorphicNFAt f x ↔ MeromorphicNFAt g x := by
  constructor
  · rintro (h | ⟨n, h, h₁h, h₂h, h₃h⟩)
    · exact .inl (hfg.symm.trans h)
    · exact .inr ⟨n, h, h₁h, h₂h, hfg.symm.trans h₃h⟩
  · rintro (h | ⟨n, h, h₁h, h₂h, h₃h⟩)
    · exact .inl (hfg.trans h)
    · exact .inr ⟨n, h, h₁h, h₂h, hfg.trans h₃h⟩

/-!
### Criteria to guarantee normal form
-/

-- DISSOLVED: MeromorphicNFAt.smul_analytic

-- DISSOLVED: meromorphicNFAt_smul_iff_right_of_analyticAt

-- DISSOLVED: meromorphicNFAt_mul_iff_right

-- DISSOLVED: meromorphicNFAt_mul_iff_left

theorem meromorphicNFAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFAt (f i) x)
    (h₂f : Set.Subsingleton {σ ∈ s | f σ x = 0}) :
    MeromorphicNFAt (∏ i ∈ s, f i) x := by
  classical
  have h₃f {τ : ι} (h₁τ : τ ∈ s) (h₂τ : τ ∉ {σ ∈ s | f σ x = 0}) :
      AnalyticAt 𝕜 (f τ) x := by
    rw [← (h₁f τ h₁τ).meromorphicOrderAt_nonneg_iff_analyticAt]
    apply ((h₁f τ h₁τ).meromorphicOrderAt_eq_zero_iff.2 _).symm.le
    grind
  by_cases h₄f : {σ ∈ s | f σ x = 0} = ∅
  · exact (Finset.analyticAt_prod _ (fun σ hσ ↦ h₃f hσ (by aesop))).meromorphicNFAt
  rw [Finset.filter_eq_empty_iff] at h₄f
  push Not at h₄f
  obtain ⟨τ, h₁τ, h₂τ⟩ := h₄f
  have {μ : ι} (hμ : μ ∈ s.erase τ) : f μ x ≠ 0 := by
    by_contra
    have : τ = μ := h₂f (by aesop) (by aesop)
    aesop
  rw [← Finset.mul_prod_erase _ _ h₁τ, meromorphicNFAt_mul_iff_left]
  · apply h₁f τ h₁τ
  · apply Finset.analyticAt_prod _ (fun μ hμ ↦ h₃f (Finset.mem_of_mem_erase hμ) (by aesop))
  · rw [Finset.prod_apply, Finset.prod_ne_zero_iff]
    aesop

theorem meromorphicNFAt_fun_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFAt (f i) x)
    (h₂f : Set.Subsingleton {σ ∈ s | f σ x = 0}) :
    MeromorphicNFAt (fun a ↦ ∏ i ∈ s, f i a) x := by
  convert meromorphicNFAt_prod h₁f h₂f
  exact (Finset.prod_apply _ s f).symm

theorem meromorphicNFAt_finprod {x : 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i, MeromorphicNFAt (f i) x) (h₂f : Set.Subsingleton {σ | f σ x = 0}) :
    MeromorphicNFAt (∏ᶠ i, f i) x := by
  by_cases h₃f : Function.HasFiniteMulSupport f
  · simp_rw [finprod_eq_prod f h₃f]
    exact meromorphicNFAt_prod (by aesop) (fun _ _ _ _ ↦ by aesop)
  · exact finprod_of_not_hasFiniteMulSupport h₃f ▸ analyticAt_const.meromorphicNFAt
