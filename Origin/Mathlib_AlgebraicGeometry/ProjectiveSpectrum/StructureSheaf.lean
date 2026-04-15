/-
Extracted from AlgebraicGeometry/ProjectiveSpectrum/StructureSheaf.lean
Genuine: 10 of 11 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The structure sheaf on `ProjectiveSpectrum 𝒜`.

In `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean`, we have given a topology on
`ProjectiveSpectrum 𝒜`; in this file we will construct a sheaf on `ProjectiveSpectrum 𝒜`.

## Notation
- `A` is a commutative ring;
- `σ` is a class of additive subgroups of `A`;
- `𝒜 : ℕ → σ` is the grading of `A`;
- `U` is opposite object of some open subset of `ProjectiveSpectrum.top`.

## Main definitions and results
We define the structure sheaf as the subsheaf of all dependent function
`f : Π x : U, HomogeneousLocalization 𝒜 x` such that `f` is locally expressible as ratio of two
elements of the *same grading*, i.e. `∀ y ∈ U, ∃ (V ⊆ U) (i : ℕ) (a b ∈ 𝒜 i), ∀ z ∈ V, f z = a / b`.

* `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isLocallyFraction`: the predicate that
  a dependent function is locally expressible as a ratio of two elements of the same grading.
* `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.sectionsSubring`: the dependent functions
  satisfying the above local property forms a subring of all dependent functions
  `Π x : U, HomogeneousLocalization 𝒜 x`.
* `AlgebraicGeometry.Proj.StructureSheaf`: the sheaf with `U ↦ sectionsSubring U` and natural
  restriction map.

Then we establish that `Proj 𝒜` is a `LocallyRingedSpace`:
* `AlgebraicGeometry.Proj.stalkIso'`: for any `x : ProjectiveSpectrum 𝒜`, the stalk of
  `Proj.StructureSheaf` at `x` is isomorphic to `HomogeneousLocalization 𝒜 x`.
* `AlgebraicGeometry.Proj.toLocallyRingedSpace`: `Proj` as a locally ringed space.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

noncomputable section

namespace AlgebraicGeometry

open scoped DirectSum Pointwise

open DirectSum SetLike Localization TopCat TopologicalSpace CategoryTheory Opposite

variable {A σ : Type*}

variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

local notation3 "at " x =>

  HomogeneousLocalization.AtPrime 𝒜

    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x))

namespace ProjectiveSpectrum.StructureSheaf

variable {𝒜} in

def IsFraction {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, at x.1) : Prop :=
  ∃ (i : ℕ) (r s : 𝒜 i) (s_nin : ∀ x : U, s.1 ∉ x.1.asHomogeneousIdeal),
    ∀ x : U, f x = .mk ⟨i, r, s, s_nin x⟩

def isFractionPrelocal : PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x where
  pred f := IsFraction f
  res := by rintro V U i f ⟨j, r, s, h, w⟩; exact ⟨j, r, s, (h <| i ·), (w <| i ·)⟩

def isLocallyFraction : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x :=
  (isFractionPrelocal 𝒜).sheafify

namespace SectionSubring

variable {𝒜}

open Submodule SetLike.GradedMonoid HomogeneousLocalization

theorem zero_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜).pred (0 : ∀ x : U.unop, at x.1) := fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨0, zero_mem _⟩, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩

theorem one_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜).pred (1 : ∀ x : U.unop, at x.1) := fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨1, one_mem_graded _⟩, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩

theorem add_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : ∀ x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred b) :
    (isLocallyFraction 𝒜).pred (a + b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨sb * ra + sa * rb,
        add_mem (add_comm jb ja ▸ mul_mem_graded sb_mem ra_mem : sb * ra ∈ 𝒜 (ja + jb))
          (mul_mem_graded sa_mem rb_mem)⟩,
      ⟨sa * sb, mul_mem_graded sa_mem sb_mem⟩, fun y ↦
        y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, ext_iff_val, add_mk, add_comm (sa * rb)]

theorem neg_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a : ∀ x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) : (isLocallyFraction 𝒜).pred (-a) := fun x => by
  rcases ha x with ⟨V, m, i, j, ⟨r, r_mem⟩, ⟨s, s_mem⟩, nin, hy⟩
  refine ⟨V, m, i, j, ⟨-r, neg_mem r_mem⟩, ⟨s, s_mem⟩, nin, fun y => ?_⟩
  simp only [ext_iff_val, val_mk] at hy
  simp only [Pi.neg_apply, ext_iff_val, val_neg, hy, val_mk, neg_mk]

theorem mul_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : ∀ x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred b) :
    (isLocallyFraction 𝒜).pred (a * b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨ra * rb, SetLike.mul_mem_graded ra_mem rb_mem⟩,
      ⟨sa * sb, SetLike.mul_mem_graded sa_mem sb_mem⟩, fun y =>
      y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, ext_iff_val, Localization.mk_mul]

end SectionSubring

open SectionSubring

variable {𝒜}

def sectionsSubring (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Subring (∀ x : U.unop, at x.1) where
  carrier := {f | (isLocallyFraction 𝒜).pred f}
  zero_mem' := zero_mem' U
  one_mem' := one_mem' U
  add_mem' := add_mem' U _ _
  neg_mem' := neg_mem' U _
  mul_mem' := mul_mem' U _ _

end

def structureSheafInType : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜)

-- INSTANCE (free from Core): commRingStructureSheafInTypeObj
