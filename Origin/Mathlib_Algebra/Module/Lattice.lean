/-
Extracted from Algebra/Module/Lattice.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Lattices

Let `A` be an `R`-algebra and `V` an `A`-module. Then an `R`-submodule `M` of `V` is a lattice,
if `M` is finitely generated and spans `V` as an `A`-module.

The typical use case is `A = K` is the fraction field of an integral domain `R` and `V = ι → K`
for some finite `ι`. The scalar multiple a lattice by a unit in `K` is again a lattice. This gives
rise to a homothety relation.

When `R` is a DVR and `ι = Fin 2`, then by taking the quotient of the type of `R`-lattices in
`ι → K` by the homothety relation, one obtains the vertices of what is called the Bruhat-Tits tree
of `GL 2 K`.

## Main definitions

- `Submodule.IsLattice`: An `R`-submodule `M` of `V` is a lattice, if it is finitely generated
  and its `A`-span is `V`.

## Main properties

Let `R` be a PID and `A = K` its field of fractions.

- `Submodule.IsLattice.free`: Every lattice in `V` is `R`-free.
- `Basis.extendOfIsLattice`: Any `R`-basis of a lattice `M` in `V` defines a `K`-basis of `V`.
- `Submodule.IsLattice.rank`: The `R`-rank of a lattice in `V` is equal to the `K`-rank of `V`.
- `Submodule.IsLattice.inf`: The intersection of two lattices is a lattice.

## Note

In the case `R = ℤ` and `A = K` a field, there is also `IsZLattice` where the finitely
generated condition is replaced by having the discrete topology. This is for example used
for complex tori.
-/

open Module

open scoped Pointwise

universe u

variable {R : Type*} [CommRing R]

namespace Submodule

class IsLattice (A : outParam Type*) [CommRing A] [Algebra R A]
    {V : Type*} [AddCommMonoid V] [Module R V] [Module A V] [IsScalarTower R A V]
    [Algebra R A] [IsScalarTower R A V] (M : Submodule R V) : Prop where
  fg : M.FG
  span_eq_top : Submodule.span A (M : Set V) = ⊤

namespace IsLattice

variable (A : Type*) [CommRing A] [Algebra R A]

variable {V : Type*} [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]

variable (M : Submodule R V)

-- INSTANCE (free from Core): finite

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): smul

lemma of_le_of_isLattice_of_fg {M N : Submodule R V} (hle : M ≤ N) [IsLattice A M]
    (hfg : N.FG) : IsLattice A N :=
  ⟨hfg, eq_top_iff.mpr <|
    le_trans (by rw [IsLattice.span_eq_top]) (Submodule.span_mono hle)⟩

-- INSTANCE (free from Core): sup

end

section Field

variable {K : Type*} [Field K] [Algebra R K]

lemma _root_.Submodule.span_range_eq_top_of_injective_of_rank_le {M N : Type u} [IsDomain R]
    [IsFractionRing R K] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module K N] [IsScalarTower R K N] [Module.Finite K N]
    {f : M →ₗ[R] N} (hf : Function.Injective f) (h : Module.rank K N ≤ Module.rank R M) :
    Submodule.span K (LinearMap.range f : Set N) = ⊤ := by
  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent R M
  replace hli := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
  rw [LinearIndependent.iff_fractionRing (R := R) (K := K)] at hli
  replace hs : Cardinal.mk s = Module.rank K N :=
    le_antisymm (LinearIndependent.cardinal_le_rank hli) (hs ▸ h)
  rw [← Module.finrank_eq_rank, Cardinal.mk_eq_nat_iff_fintype] at hs
  obtain ⟨hfin, hcard⟩ := hs
  have hsubset : Set.range (fun x : s ↦ f x.val) ⊆ (LinearMap.range f : Set N) := by
    rintro x ⟨a, rfl⟩
    simp
  rw [eq_top_iff, ← LinearIndependent.span_eq_top_of_card_eq_finrank' hli hcard]
  exact Submodule.span_mono hsubset

variable (K) {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

noncomputable def _root_.Module.Basis.extendOfIsLattice [IsFractionRing R K] {κ : Type*}
    {M : Submodule R V} [IsLattice K M] (b : Basis κ R M) :
    Basis κ K V :=
  have hli : LinearIndependent K (fun i ↦ (b i).val) := by
    rw [← LinearIndependent.iff_fractionRing (R := R), linearIndependent_iff']
    intro s g hs
    simp_rw [← Submodule.coe_smul_of_tower, ← Submodule.coe_sum, Submodule.coe_eq_zero] at hs
    exact linearIndependent_iff'.mp b.linearIndependent s g hs
  have hsp : ⊤ ≤ span K (Set.range fun i ↦ (M.subtype ∘ b) i) := by
    rw [← Submodule.span_span_of_tower R, Set.range_comp, ← Submodule.map_span]
    simp [b.span_eq, Submodule.map_top, span_eq_top]
  Basis.mk hli hsp
