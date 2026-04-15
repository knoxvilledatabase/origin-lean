/-
Extracted from Topology/ExtendFrom.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Extending a function from a subset

The main definition of this file is `extendFrom A f` where `f : X → Y`
and `A : Set X`. This defines a new function `g : X → Y` which maps any
`x₀ : X` to the limit of `f` as `x` tends to `x₀`, if such a limit exists.

This is analogous to the way `IsDenseInducing.extend` "extends" a function
`f : X → Z` to a function `g : Y → Z` along a dense inducing `i : X → Y`.

The main theorem we prove about this definition is `continuousOn_extendFrom`
which states that, for `extendFrom A f` to be continuous on a set `B ⊆ closure A`,
it suffices that `f` converges within `A` at any point of `B`, provided that
`f` is a function to a T₃ space.

-/

noncomputable section

open Topology

open Filter Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def extendFrom (A : Set X) (f : X → Y) : X → Y :=
  fun x ↦ @limUnder _ _ _ ⟨f x⟩ (𝓝[A] x) f

theorem tendsto_extendFrom {A : Set X} {f : X → Y} {x : X} (h : ∃ y, Tendsto f (𝓝[A] x) (𝓝 y)) :
    Tendsto f (𝓝[A] x) (𝓝 <| extendFrom A f x) :=
  tendsto_nhds_limUnder h

theorem extendFrom_eq [T2Space Y] {A : Set X} {f : X → Y} {x : X} {y : Y} (hx : x ∈ closure A)
    (hf : Tendsto f (𝓝[A] x) (𝓝 y)) : extendFrom A f x = y :=
  haveI := mem_closure_iff_nhdsWithin_neBot.mp hx
  tendsto_nhds_unique (tendsto_nhds_limUnder ⟨y, hf⟩) hf

theorem extendFrom_extends [T2Space Y] {f : X → Y} {A : Set X} (hf : ContinuousOn f A) :
    ∀ x ∈ A, extendFrom A f x = f x :=
  fun x x_in ↦ extendFrom_eq (subset_closure x_in) (hf x x_in)

theorem continuousOn_extendFrom [RegularSpace Y] {f : X → Y} {A B : Set X} (hB : B ⊆ closure A)
    (hf : ∀ x ∈ B, ∃ y, Tendsto f (𝓝[A] x) (𝓝 y)) : ContinuousOn (extendFrom A f) B := by
  set φ := extendFrom A f
  intro x x_in
  suffices ∀ V' ∈ 𝓝 (φ x), IsClosed V' → φ ⁻¹' V' ∈ 𝓝[B] x by
    simpa [ContinuousWithinAt, (closed_nhds_basis (φ x)).tendsto_right_iff]
  intro V' V'_in V'_closed
  obtain ⟨V, V_in, V_op, hV⟩ : ∃ V ∈ 𝓝 x, IsOpen V ∧ V ∩ A ⊆ f ⁻¹' V' := by
    have := tendsto_extendFrom (hf x x_in)
    rcases (nhdsWithin_basis_open x A).tendsto_left_iff.mp this V' V'_in with ⟨V, ⟨hxV, V_op⟩, hV⟩
    exact ⟨V, IsOpen.mem_nhds V_op hxV, V_op, hV⟩
  suffices ∀ y ∈ V ∩ B, φ y ∈ V' from
    mem_of_superset (inter_mem_inf V_in <| mem_principal_self B) this
  rintro y ⟨hyV, hyB⟩
  haveI := mem_closure_iff_nhdsWithin_neBot.mp (hB hyB)
  have limy : Tendsto f (𝓝[A] y) (𝓝 <| φ y) := tendsto_extendFrom (hf y hyB)
  have hVy : V ∈ 𝓝 y := IsOpen.mem_nhds V_op hyV
  have : V ∩ A ∈ 𝓝[A] y := by simpa only [inter_comm] using inter_mem_nhdsWithin A hVy
  exact V'_closed.mem_of_tendsto limy (mem_of_superset this hV)

theorem continuous_extendFrom [RegularSpace Y] {f : X → Y} {A : Set X} (hA : Dense A)
    (hf : ∀ x, ∃ y, Tendsto f (𝓝[A] x) (𝓝 y)) : Continuous (extendFrom A f) := by
  rw [← continuousOn_univ]
  exact continuousOn_extendFrom (fun x _ ↦ hA x) (by simpa using hf)
