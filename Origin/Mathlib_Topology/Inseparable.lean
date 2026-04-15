/-
Extracted from Topology/Inseparable.lean
Genuine: 15 of 16 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Inseparable points in a topological space

In this file we prove basic properties of the following notions defined elsewhere.

* `Specializes` (notation: `x ⤳ y`) : a relation saying that `𝓝 x ≤ 𝓝 y`;

* `Inseparable`: a relation saying that two points in a topological space have the same
  neighbourhoods; equivalently, they can't be separated by an open set;

* `InseparableSetoid X`: same relation, as a `Setoid`;

* `SeparationQuotient X`: the quotient of `X` by its `InseparableSetoid`.

We also prove various basic properties of the relation `Inseparable`.

## Notation

- `x ⤳ y`: notation for `Specializes x y`;
- `x ~ᵢ y` is used as a local notation for `Inseparable x y`;
- `𝓝 x` is the neighbourhoods filter `nhds x` of a point `x`, defined elsewhere.

## Tags

topological space, separation setoid
-/

open Set Filter Function Topology

variable {X Y Z α ι : Type*} {A : ι → Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [∀ i, TopologicalSpace (A i)] {x y z : X} {s : Set X} {f g : X → Y}

/-!
### `Specializes` relation
-/

theorem specializes_TFAE (x y : X) :
    List.TFAE [x ⤳ y,
      pure x ≤ 𝓝 y,
      ∀ s : Set X, IsOpen s → y ∈ s → x ∈ s,
      ∀ s : Set X, IsClosed s → x ∈ s → y ∈ s,
      y ∈ closure ({ x } : Set X),
      closure ({ y } : Set X) ⊆ closure { x },
      ClusterPt y (pure x)] := by
  tfae_have 1 → 2 := (pure_le_nhds _).trans
  tfae_have 2 → 3 := fun h s hso hy => h (hso.mem_nhds hy)
  tfae_have 3 → 4 := fun h s hsc hx => of_not_not fun hy => h sᶜ hsc.isOpen_compl hy hx
  tfae_have 4 → 5 := fun h => h _ isClosed_closure (subset_closure <| mem_singleton _)
  tfae_have 6 ↔ 5 := isClosed_closure.closure_subset_iff.trans singleton_subset_iff
  tfae_have 5 ↔ 7 := by
    rw [mem_closure_iff_clusterPt, principal_singleton]
  tfae_have 5 → 1 := by
    refine fun h => (nhds_basis_opens _).ge_iff.2 ?_
    rintro s ⟨hy, ho⟩
    rcases mem_closure_iff.1 h s ho hy with ⟨z, hxs, rfl : z = x⟩
    exact ho.mem_nhds hxs
  tfae_finish

theorem Specializes.not_disjoint (h : x ⤳ y) : ¬Disjoint (𝓝 x) (𝓝 y) := fun hd ↦
  absurd (hd.mono_right h) <| by simp [NeBot.ne']

theorem specializes_iff_pure : x ⤳ y ↔ pure x ≤ 𝓝 y :=
  (specializes_TFAE x y).out 0 1

alias ⟨Specializes.nhds_le_nhds, _⟩ := specializes_iff_nhds

alias ⟨Specializes.pure_le_nhds, _⟩ := specializes_iff_pure

theorem ker_nhds_eq_specializes : (𝓝 x).ker = {y | y ⤳ x} := by
  ext; simp [specializes_iff_pure, le_def]

theorem specializes_iff_forall_open : x ⤳ y ↔ ∀ s : Set X, IsOpen s → y ∈ s → x ∈ s :=
  (specializes_TFAE x y).out 0 2

theorem Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (hy : y ∈ s) : x ∈ s :=
  specializes_iff_forall_open.1 h s hs hy

theorem IsOpen.not_specializes (hs : IsOpen s) (hx : x ∉ s) (hy : y ∈ s) : ¬x ⤳ y := fun h =>
  hx <| h.mem_open hs hy

theorem specializes_iff_forall_closed : x ⤳ y ↔ ∀ s : Set X, IsClosed s → x ∈ s → y ∈ s :=
  (specializes_TFAE x y).out 0 3

theorem Specializes.mem_closed (h : x ⤳ y) (hs : IsClosed s) (hx : x ∈ s) : y ∈ s :=
  specializes_iff_forall_closed.1 h s hs hx

theorem IsClosed.not_specializes (hs : IsClosed s) (hx : x ∈ s) (hy : y ∉ s) : ¬x ⤳ y := fun h =>
  hy <| h.mem_closed hs hx

theorem specializes_iff_mem_closure : x ⤳ y ↔ y ∈ closure ({x} : Set X) :=
  (specializes_TFAE x y).out 0 4

alias ⟨Specializes.mem_closure, _⟩ := specializes_iff_mem_closure

theorem specializes_iff_closure_subset : x ⤳ y ↔ closure ({y} : Set X) ⊆ closure {x} :=
  (specializes_TFAE x y).out 0 5

alias ⟨Specializes.closure_subset, _⟩ := specializes_iff_closure_subset

theorem specializes_iff_clusterPt : x ⤳ y ↔ ClusterPt y (pure x) :=
  (specializes_TFAE x y).out 0 6

theorem Filter.HasBasis.specializes_iff {ι} {p : ι → Prop} {s : ι → Set X}
    (h : (𝓝 y).HasBasis p s) : x ⤳ y ↔ ∀ i, p i → x ∈ s i :=
  specializes_iff_pure.trans h.ge_iff

theorem specializes_rfl : x ⤳ x := le_rfl
