/-
Extracted from Analysis/LocallyConvex/AbsConvex.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Absolutely convex sets

A set `s` in a commutative monoid `E` is called absolutely convex or disked if it is convex and
balanced. The importance of absolutely convex sets comes from the fact that every locally convex
topological vector space has a basis consisting of absolutely convex sets.

## Main definitions

* `absConvexHull`: the absolutely convex hull of a set `s` is the smallest absolutely convex set
  containing `s`;
* `closedAbsConvexHull`: the closed absolutely convex hull of a set `s` is the smallest absolutely
  convex set containing `s`;

## Main statements

* `absConvexHull_eq_convexHull_balancedHull`: when the locally convex space is a module, the
  absolutely convex hull of a set `s` equals the convex hull of the balanced hull of `s`;
* `convexHull_union_neg_eq_absConvexHull`: the convex hull of `s ∪ -s` is the absolutely convex hull
  of `s`;
* `closedAbsConvexHull_closure_eq_closedAbsConvexHull` : the closed absolutely convex hull of the
  closure of `s` equals the closed absolutely convex hull of `s`;

## Tags

disks, convex, balanced
-/

open NormedField Set

open NNReal Pointwise Topology

variable {𝕜 E : Type*}

section AbsolutelyConvex

variable (𝕜) [SeminormedRing 𝕜] [SMul 𝕜 E] [AddCommMonoid E] [PartialOrder 𝕜]

def AbsConvex (s : Set E) : Prop := Balanced 𝕜 s ∧ Convex 𝕜 s

variable {𝕜}

theorem AbsConvex.empty : AbsConvex 𝕜 (∅ : Set E) := ⟨balanced_empty, convex_empty⟩

theorem AbsConvex.univ : AbsConvex 𝕜 (univ : Set E) := ⟨balanced_univ, convex_univ⟩

theorem AbsConvex.inter {s t : Set E} (hs : AbsConvex 𝕜 s) (ht : AbsConvex 𝕜 t) :
    AbsConvex 𝕜 (s ∩ t) := ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

theorem AbsConvex.sInter {S : Set (Set E)} (h : ∀ s ∈ S, AbsConvex 𝕜 s) : AbsConvex 𝕜 (⋂₀ S) :=
  ⟨.sInter fun s hs => (h s hs).1, convex_sInter fun s hs => (h s hs).2⟩

theorem AbsConvex.iInter {ι : Sort*} {s : ι → Set E} (h : ∀ i, AbsConvex 𝕜 (s i)) :
    AbsConvex 𝕜 (⋂ i, s i) :=
  sInter_range s ▸ AbsConvex.sInter <| forall_mem_range.2 h

theorem AbsConvex.iInter₂ {ι : Sort*} {κ : ι → Sort*} {f : ∀ i, κ i → Set E}
    (h : ∀ i j, AbsConvex 𝕜 (f i j)) : AbsConvex 𝕜 (⋂ (i) (j), f i j) :=
  AbsConvex.iInter fun _ => (AbsConvex.iInter fun _ => h _ _)

variable (𝕜)
