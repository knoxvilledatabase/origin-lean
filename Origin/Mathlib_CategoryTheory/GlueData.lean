/-
Extracted from CategoryTheory/GlueData.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Gluing data

We define `GlueData` as a family of data needed to glue topological spaces, schemes, etc. We
provide the API to realize it as a multispan diagram, and also state lemmas about its
interaction with a functor that preserves certain pullbacks.

-/

noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u₁ u₂

variable (C : Type u₁) [Category.{v} C] {C' : Type u₂} [Category.{v} C']

structure GlueData where
  /-- The index type `J` of a gluing datum -/
  J : Type v
  /-- For each `i : J`, an object `U i` -/
  U : J → C
  /-- For each `i j : J`, an object `V i j` -/
  V : J × J → C
  /-- For each `i j : J`, a monomorphism `f i j : V i j ⟶ U i` -/
  f : ∀ i j, V (i, j) ⟶ U i
  f_mono : ∀ i j, Mono (f i j) := by infer_instance
  f_hasPullback : ∀ i j k, HasPullback (f i j) (f i k) := by infer_instance
  f_id : ∀ i, IsIso (f i i) := by infer_instance
  /-- For each `i j : J`, a transition map `t i j : V i j ⟶ V j i` -/
  t : ∀ i j, V (i, j) ⟶ V (j, i)
  t_id : ∀ i, t i i = 𝟙 _
  /-- The morphism via which `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through
  `V j k ×[U j] V j i ⟶ V j i` -/
  t' : ∀ i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
  t_fac : ∀ i j k, t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j
  cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _

attribute [simp] GlueData.t_id

attribute [instance] GlueData.f_id GlueData.f_mono GlueData.f_hasPullback

attribute [reassoc] GlueData.t_fac GlueData.cocycle

namespace GlueData

variable {C}

variable (D : GlueData C)
