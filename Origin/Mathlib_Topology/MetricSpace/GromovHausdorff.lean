/-
Extracted from Topology/MetricSpace/GromovHausdorff.lean
Genuine: 18 of 32 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core

/-!
# Gromov-Hausdorff distance

This file defines the Gromov-Hausdorff distance on the space of nonempty compact metric spaces
up to isometry.

We introduce the space of all nonempty compact metric spaces, up to isometry,
called `GHSpace`, and endow it with a metric space structure. The distance,
known as the Gromov-Hausdorff distance, is defined as follows: given two
nonempty compact spaces `X` and `Y`, their distance is the minimum Hausdorff distance
between all possible isometric embeddings of `X` and `Y` in all metric spaces.
To define properly the Gromov-Hausdorff space, we consider the non-empty
compact subsets of `ℓ^∞(ℝ)` up to isometry, which is a well-defined type,
and define the distance as the infimum of the Hausdorff distance over all
embeddings in `ℓ^∞(ℝ)`. We prove that this coincides with the previous description,
as all separable metric spaces embed isometrically into `ℓ^∞(ℝ)`, through an
embedding called the Kuratowski embedding.
To prove that we have a distance, we should show that if spaces can be coupled
to be arbitrarily close, then they are isometric. More generally, the Gromov-Hausdorff
distance is realized, i.e., there is a coupling for which the Hausdorff distance
is exactly the Gromov-Hausdorff distance. This follows from a compactness
argument, essentially following from Arzela-Ascoli.

## Main results

We prove the most important properties of the Gromov-Hausdorff space: it is a polish space,
i.e., it is complete and second countable. We also prove the Gromov compactness criterion.

-/

noncomputable section

open scoped Topology ENNReal Cardinal

open Set Function TopologicalSpace Filter Metric Quotient Bornology

open BoundedContinuousFunction Nat Int kuratowskiEmbedding

open Sum (inl inr)

local notation "ℓ_infty_ℝ" => lp (fun n : ℕ => ℝ) ∞

universe u v w

attribute [local instance] metricSpaceSum

namespace GromovHausdorff

/-! In this section, we define the Gromov-Hausdorff space, denoted `GHSpace` as the quotient
of nonempty compact subsets of `ℓ^∞(ℝ)` by identifying isometric sets.
Using the Kuratowski embedding, we get a canonical map `toGHSpace` mapping any nonempty
compact type to `GHSpace`. -/

section GHSpace

set_option backward.privateInPublic true in

private def IsometryRel (x : NonemptyCompacts ℓ_infty_ℝ) (y : NonemptyCompacts ℓ_infty_ℝ) : Prop :=
  Nonempty (x ≃ᵢ y)

set_option backward.privateInPublic true in

private theorem equivalence_isometryRel : Equivalence IsometryRel :=
  ⟨fun _ => Nonempty.intro (IsometryEquiv.refl _), fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

set_option backward.privateInPublic true in

set_option backward.privateInPublic.warn false in

-- INSTANCE (free from Core): IsometryRel.setoid

def GHSpace : Type :=
  Quotient IsometryRel.setoid

def toGHSpace (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] : GHSpace :=
  ⟦NonemptyCompacts.kuratowskiEmbedding X⟧

-- INSTANCE (free from Core): :

def GHSpace.Rep (p : GHSpace) : Type :=
  (Quotient.out p : NonemptyCompacts ℓ_infty_ℝ)

theorem eq_toGHSpace_iff {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
    {p : NonemptyCompacts ℓ_infty_ℝ} :
    ⟦p⟧ = toGHSpace X ↔ ∃ Ψ : X → ℓ_infty_ℝ, Isometry Ψ ∧ range Ψ = p := by
  simp only [toGHSpace, Quotient.eq]
  refine ⟨fun h => ?_, ?_⟩
  · rcases Setoid.symm h with ⟨e⟩
    have f := (kuratowskiEmbedding.isometry X).isometryEquivOnRange.trans e
    use fun x => f x, isometry_subtype_coe.comp f.isometry
    rw [range_comp', f.range_eq_univ, Set.image_univ, Subtype.range_coe]
  · rintro ⟨Ψ, ⟨isomΨ, rangeΨ⟩⟩
    have f :=
      ((kuratowskiEmbedding.isometry X).isometryEquivOnRange.symm.trans
          isomΨ.isometryEquivOnRange).symm
    have E : (range Ψ ≃ᵢ NonemptyCompacts.kuratowskiEmbedding X)
        = (p ≃ᵢ range (kuratowskiEmbedding X)) := by
      dsimp only [NonemptyCompacts.kuratowskiEmbedding]; rw [rangeΨ]; rfl
    exact ⟨cast E f⟩

theorem eq_toGHSpace {p : NonemptyCompacts ℓ_infty_ℝ} : ⟦p⟧ = toGHSpace p :=
  eq_toGHSpace_iff.2 ⟨fun x => x, isometry_subtype_coe, Subtype.range_coe⟩

-- INSTANCE (free from Core): repGHSpaceMetricSpace

-- INSTANCE (free from Core): rep_gHSpace_compactSpace

-- INSTANCE (free from Core): rep_gHSpace_nonempty

end

theorem GHSpace.toGHSpace_rep (p : GHSpace) : toGHSpace p.Rep = p := by
  change toGHSpace (Quot.out p : NonemptyCompacts ℓ_infty_ℝ) = p
  rw [← eq_toGHSpace]
  exact Quot.out_eq p

set_option backward.isDefEq.respectTransparency false in

theorem toGHSpace_eq_toGHSpace_iff_isometryEquiv {X : Type u} [MetricSpace X] [CompactSpace X]
    [Nonempty X] {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
    toGHSpace X = toGHSpace Y ↔ Nonempty (X ≃ᵢ Y) :=
  ⟨by
    simp only [toGHSpace]
    rw [Quotient.eq]
    rintro ⟨e⟩
    have I :
      (NonemptyCompacts.kuratowskiEmbedding X ≃ᵢ NonemptyCompacts.kuratowskiEmbedding Y) =
        (range (kuratowskiEmbedding X) ≃ᵢ range (kuratowskiEmbedding Y)) := by
      dsimp only [NonemptyCompacts.kuratowskiEmbedding]; rfl
    have f := (kuratowskiEmbedding.isometry X).isometryEquivOnRange
    have g := (kuratowskiEmbedding.isometry Y).isometryEquivOnRange.symm
    exact ⟨f.trans <| (cast I e).trans g⟩, by
    rintro ⟨e⟩
    simp only [toGHSpace]
    have f := (kuratowskiEmbedding.isometry X).isometryEquivOnRange.symm
    have g := (kuratowskiEmbedding.isometry Y).isometryEquivOnRange
    have I :
      (range (kuratowskiEmbedding X) ≃ᵢ range (kuratowskiEmbedding Y)) =
        (NonemptyCompacts.kuratowskiEmbedding X ≃ᵢ NonemptyCompacts.kuratowskiEmbedding Y) := by
      dsimp only [NonemptyCompacts.kuratowskiEmbedding]; rfl
    rw [Quotient.eq]
    exact ⟨cast I ((f.trans e).trans g)⟩⟩

-- INSTANCE (free from Core): :

def ghDist (X : Type u) (Y : Type v) [MetricSpace X] [Nonempty X] [CompactSpace X] [MetricSpace Y]
    [Nonempty Y] [CompactSpace Y] : ℝ :=
  dist (toGHSpace X) (toGHSpace Y)

theorem dist_ghDist (p q : GHSpace) : dist p q = ghDist p.Rep q.Rep := by
  rw [ghDist, p.toGHSpace_rep, q.toGHSpace_rep]

theorem ghDist_eq_hausdorffDist (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (Y : Type v) [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
    ∃ Φ : X → ℓ_infty_ℝ,
      ∃ Ψ : Y → ℓ_infty_ℝ,
        Isometry Φ ∧ Isometry Ψ ∧ ghDist X Y = hausdorffDist (range Φ) (range Ψ) := by
  let F := kuratowskiEmbedding (OptimalGHCoupling X Y)
  let Φ := F ∘ optimalGHInjl X Y
  let Ψ := F ∘ optimalGHInjr X Y
  refine ⟨Φ, Ψ, ?_, ?_, ?_⟩
  · exact (kuratowskiEmbedding.isometry _).comp (isometry_optimalGHInjl X Y)
  · exact (kuratowskiEmbedding.isometry _).comp (isometry_optimalGHInjr X Y)
  · rw [← image_univ, ← image_univ, image_comp F, image_univ, image_comp F (optimalGHInjr X Y),
      image_univ, ← hausdorffDist_optimal]
    exact (hausdorffDist_image (kuratowskiEmbedding.isometry _)).symm

-- INSTANCE (free from Core): :

end GHSpace --section

end GromovHausdorff

def TopologicalSpace.NonemptyCompacts.toGHSpace {X : Type u} [MetricSpace X]
    (p : NonemptyCompacts X) : GromovHausdorff.GHSpace :=
  GromovHausdorff.toGHSpace p

namespace GromovHausdorff

section NonemptyCompacts

variable {X : Type u} [MetricSpace X]

theorem toGHSpace_lipschitz :
    LipschitzWith 1 (NonemptyCompacts.toGHSpace : NonemptyCompacts X → GHSpace) :=
  LipschitzWith.mk_one ghDist_le_nonemptyCompacts_dist

theorem toGHSpace_continuous :
    Continuous (NonemptyCompacts.toGHSpace : NonemptyCompacts X → GHSpace) :=
  toGHSpace_lipschitz.continuous

end NonemptyCompacts

variable {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X] {Y : Type v} [MetricSpace Y]
  [CompactSpace Y] [Nonempty Y]

theorem ghDist_le_of_approx_subsets {s : Set X} (Φ : s → Y) {ε₁ ε₂ ε₃ : ℝ}
    (hs : ∀ x : X, ∃ y ∈ s, dist x y ≤ ε₁) (hs' : ∀ x : Y, ∃ y : s, dist x (Φ y) ≤ ε₃)
    (H : ∀ x y : s, |dist x y - dist (Φ x) (Φ y)| ≤ ε₂) : ghDist X Y ≤ ε₁ + ε₂ / 2 + ε₃ := by
  refine le_of_forall_pos_le_add fun δ δ0 => ?_
  rcases exists_mem_of_nonempty X with ⟨xX, _⟩
  rcases hs xX with ⟨xs, hxs, Dxs⟩
  have sne : s.Nonempty := ⟨xs, hxs⟩
  let _ : Nonempty s := sne.to_subtype
  have : 0 ≤ ε₂ := le_trans (abs_nonneg _) (H ⟨xs, hxs⟩ ⟨xs, hxs⟩)
  have : ∀ p q : s, |dist p q - dist (Φ p) (Φ q)| ≤ 2 * (ε₂ / 2 + δ) := fun p q =>
    calc
      |dist p q - dist (Φ p) (Φ q)| ≤ ε₂ := H p q
      _ ≤ 2 * (ε₂ / 2 + δ) := by linarith
  -- glue `X` and `Y` along the almost matching subsets
  let _ : MetricSpace (X ⊕ Y) :=
    glueMetricApprox (fun x : s => (x : X)) (fun x => Φ x) (ε₂ / 2 + δ) (by linarith) this
  let Fl := @Sum.inl X Y
  let Fr := @Sum.inr X Y
  have Il : Isometry Fl := Isometry.of_dist_eq fun x y => rfl
  have Ir : Isometry Fr := Isometry.of_dist_eq fun x y => rfl
  /- The proof goes as follows : the `ghDist` is bounded by the Hausdorff distance of the images
    in the coupling, which is bounded (using the triangular inequality) by the sum of the Hausdorff
    distances of `X` and `s` (in the coupling or, equivalently in the original space), of `s` and
    `Φ s`, and of `Φ s` and `Y` (in the coupling or, equivalently, in the original space).
    The first term is bounded by `ε₁`, by `ε₁`-density. The third one is bounded by `ε₃`.
    And the middle one is bounded by `ε₂/2` as in the coupling the points `x` and `Φ x` are
    at distance `ε₂/2` by construction of the coupling (in fact `ε₂/2 + δ` where `δ` is an
    arbitrarily small positive constant where positivity is used to ensure that the coupling
    is really a metric space and not a premetric space on `X ⊕ Y`). -/
  have : ghDist X Y ≤ hausdorffDist (range Fl) (range Fr) := ghDist_le_hausdorffDist Il Ir
  have :
    hausdorffDist (range Fl) (range Fr) ≤
      hausdorffDist (range Fl) (Fl '' s) + hausdorffDist (Fl '' s) (range Fr) :=
    have B : IsBounded (range Fl) := (isCompact_range Il.continuous).isBounded
    hausdorffDist_triangle
      (hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (sne.image _) B
        (B.subset (image_subset_range _ _)))
  have :
    hausdorffDist (Fl '' s) (range Fr) ≤
      hausdorffDist (Fl '' s) (Fr '' range Φ) + hausdorffDist (Fr '' range Φ) (range Fr) :=
    have B : IsBounded (range Fr) := (isCompact_range Ir.continuous).isBounded
    hausdorffDist_triangle'
      (hausdorffEDist_ne_top_of_nonempty_of_bounded ((range_nonempty _).image _) (range_nonempty _)
        (B.subset (image_subset_range _ _)) B)
  have : hausdorffDist (range Fl) (Fl '' s) ≤ ε₁ := by
    rw [← image_univ, hausdorffDist_image Il]
    have : 0 ≤ ε₁ := le_trans dist_nonneg Dxs
    refine hausdorffDist_le_of_mem_dist this (fun x _ => hs x) fun x _ =>
      ⟨x, mem_univ _, by simpa only [dist_self]⟩
  have : hausdorffDist (Fl '' s) (Fr '' range Φ) ≤ ε₂ / 2 + δ := by
    refine hausdorffDist_le_of_mem_dist (by linarith) ?_ ?_
    · intro x' hx'
      rcases (Set.mem_image _ _ _).1 hx' with ⟨x, ⟨x_in_s, xx'⟩⟩
      rw [← xx']
      use Fr (Φ ⟨x, x_in_s⟩), mem_image_of_mem Fr (mem_range_self _)
      exact le_of_eq (glueDist_glued_points (fun x : s => (x : X)) Φ (ε₂ / 2 + δ) ⟨x, x_in_s⟩)
    · intro x' hx'
      rcases (Set.mem_image _ _ _).1 hx' with ⟨y, ⟨y_in_s', yx'⟩⟩
      rcases mem_range.1 y_in_s' with ⟨x, xy⟩
      use Fl x, mem_image_of_mem _ x.2
      rw [← yx', ← xy, dist_comm]
      exact le_of_eq (glueDist_glued_points (Z := s) Subtype.val Φ (ε₂ / 2 + δ) x)
  have : hausdorffDist (Fr '' range Φ) (range Fr) ≤ ε₃ := by
    rw [← @image_univ _ _ Fr, hausdorffDist_image Ir]
    rcases exists_mem_of_nonempty Y with ⟨xY, _⟩
    rcases hs' xY with ⟨xs', Dxs'⟩
    have : 0 ≤ ε₃ := le_trans dist_nonneg Dxs'
    refine hausdorffDist_le_of_mem_dist this
      (fun x _ => ⟨x, mem_univ _, by simpa only [dist_self]⟩)
      fun x _ => ?_
    rcases hs' x with ⟨y, Dy⟩
    exact ⟨Φ y, mem_range_self _, Dy⟩
  linarith

end --section

-- INSTANCE (free from Core): :

section Complete

variable (X : ℕ → Type) [∀ n, MetricSpace (X n)] [∀ n, CompactSpace (X n)] [∀ n, Nonempty (X n)]

structure AuxGluingStruct (A : Type) [MetricSpace A] : Type 1 where
  Space : Type
  metric : MetricSpace Space
  embed : A → Space
  isom : Isometry embed

attribute [local instance] AuxGluingStruct.metric

-- INSTANCE (free from Core): (A

def auxGluing (n : ℕ) : AuxGluingStruct (X n) :=
  Nat.recOn n default fun n Y =>
    { Space := GlueSpace Y.isom (isometry_optimalGHInjl (X n) (X (n + 1)))
      metric := by infer_instance
      embed :=
        toGlueR Y.isom (isometry_optimalGHInjl (X n) (X (n + 1))) ∘ optimalGHInjr (X n) (X (n + 1))
      isom := (toGlueR_isometry _ _).comp (isometry_optimalGHInjr (X n) (X (n + 1))) }

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

end Complete --section

end GromovHausdorff --namespace
