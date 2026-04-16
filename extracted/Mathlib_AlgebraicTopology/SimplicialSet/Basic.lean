/-
Extracted from AlgebraicTopology/SimplicialSet/Basic.lean
Genuine: 52 | Conflates: 0 | Dissolved: 0 | Infrastructure: 22
-/
import Origin.Core
import Mathlib.AlgebraicTopology.SimplicialObject.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Types
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

noncomputable section

/-!
# Simplicial sets

A simplicial set is just a simplicial object in `Type`,
i.e. a `Type`-valued presheaf on the simplex category.

(One might be tempted to call these "simplicial types" when working in type-theoretic foundations,
but this would be unnecessarily confusing given the existing notion of a simplicial type in
homotopy type theory.)

We define the standard simplices `Δ[n]` as simplicial sets,
and their boundaries `∂Δ[n]` and horns `Λ[n, i]`.
(The notations are available via `Open Simplicial`.)

## Future work

There isn't yet a complete API for simplices, boundaries, and horns.
As an example, we should have a function that constructs
from a non-surjective order preserving function `Fin n → Fin n`
a morphism `Δ[n] ⟶ ∂Δ[n]`.
-/

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

open Simplicial

def SSet : Type (u + 1) :=
  SimplicialObject (Type u)

namespace SSet

instance largeCategory : LargeCategory SSet := by
  dsimp only [SSet]
  infer_instance

instance hasLimits : HasLimits SSet := by
  dsimp only [SSet]
  infer_instance

instance hasColimits : HasColimits SSet := by
  dsimp only [SSet]
  infer_instance

@[ext]
lemma hom_ext {X Y : SSet} {f g : X ⟶ Y} (w : ∀ n, f.app n = g.app n) : f = g :=
  SimplicialObject.hom_ext _ _ w

def uliftFunctor : SSet.{u} ⥤ SSet.{max u v} :=
  (SimplicialObject.whiskering _ _).obj CategoryTheory.uliftFunctor.{v, u}

def standardSimplex : SimplexCategory ⥤ SSet.{u} :=
  yoneda ⋙ uliftFunctor

scoped[Simplicial] notation3 "Δ[" n "]" => SSet.standardSimplex.obj (SimplexCategory.mk n)

@[inherit_doc SSet.standardSimplex]
instance : Inhabited SSet :=
  ⟨Δ[0]⟩

namespace standardSimplex

open Finset Opposite SimplexCategory

@[simp]
lemma map_id (n : SimplexCategory) :
    (SSet.standardSimplex.map (SimplexCategory.Hom.mk OrderHom.id : n ⟶ n)) = 𝟙 _ :=
  CategoryTheory.Functor.map_id _ _

def objEquiv (n : SimplexCategory) (m : SimplexCategoryᵒᵖ) :
    (standardSimplex.{u}.obj n).obj m ≃ (m.unop ⟶ n) :=
  Equiv.ulift.{u, 0}

abbrev objMk {n : SimplexCategory} {m : SimplexCategoryᵒᵖ}
    (f : Fin (len m.unop + 1) →o Fin (n.len + 1)) :
    (standardSimplex.{u}.obj n).obj m :=
  (objEquiv _ _).symm (Hom.mk f)

def _root_.SSet.yonedaEquiv (X : SSet.{u}) (n : SimplexCategory) :
    (standardSimplex.obj n ⟶ X) ≃ X.obj (op n) :=
  yonedaCompUliftFunctorEquiv X n

def id (n : ℕ) : Δ[n] _[n] := yonedaEquiv Δ[n] [n] (𝟙 Δ[n])

def const (n : ℕ) (k : Fin (n+1)) (m : SimplexCategoryᵒᵖ) : Δ[n].obj m :=
  objMk (OrderHom.const _ k )

@[simp]
lemma const_down_toOrderHom (n : ℕ) (k : Fin (n+1)) (m : SimplexCategoryᵒᵖ) :
    (const n k m).down.toOrderHom = OrderHom.const _ k :=
  rfl

def edge (n : ℕ) (a b : Fin (n+1)) (hab : a ≤ b) : Δ[n] _[1] := by
  refine objMk ⟨![a, b], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_one]
  apply Fin.mk_le_mk.mpr hab

def triangle {n : ℕ} (a b c : Fin (n+1)) (hab : a ≤ b) (hbc : b ≤ c) : Δ[n] _[2] := by
  refine objMk ⟨![a, b, c], ?_⟩
  rw [Fin.monotone_iff_le_succ]
  simp only [unop_op, len_mk, Fin.forall_fin_two]
  dsimp
  simp only [*, Matrix.tail_cons, Matrix.head_cons, true_and]

end standardSimplex

section

def asOrderHom {n} {m} (α : Δ[n].obj m) : OrderHom (Fin (m.unop.len + 1)) (Fin (n + 1)) :=
  α.down.toOrderHom

end

def boundary (n : ℕ) : SSet.{u} where
  obj m := { α : Δ[n].obj m // ¬Function.Surjective (asOrderHom α) }
  map {m₁ m₂} f α :=
    ⟨Δ[n].map f α.1, by
      intro h
      apply α.property
      exact Function.Surjective.of_comp h⟩

scoped[Simplicial] notation3 "∂Δ[" n "]" => SSet.boundary n

set_option linter.unusedVariables false in
/-- The inclusion of the boundary of the `n`-th standard simplex into that standard simplex. -/

def boundaryInclusion (n : ℕ) : ∂Δ[n] ⟶ Δ[n] where app m (α : { α : Δ[n].obj m // _ }) := α

def horn (n : ℕ) (i : Fin (n + 1)) : SSet where
  obj m := { α : Δ[n].obj m // Set.range (asOrderHom α) ∪ {i} ≠ Set.univ }
  map {m₁ m₂} f α :=
    ⟨Δ[n].map f α.1, by
      intro h; apply α.property
      rw [Set.eq_univ_iff_forall] at h ⊢; intro j
      apply Or.imp _ id (h j)
      intro hj
      exact Set.range_comp_subset_range _ _ hj⟩

scoped[Simplicial] notation3 "Λ[" n ", " i "]" => SSet.horn (n : ℕ) i

set_option linter.unusedVariables false in
/-- The inclusion of the `i`-th horn of the `n`-th standard simplex into that standard simplex. -/

def hornInclusion (n : ℕ) (i : Fin (n + 1)) : Λ[n, i] ⟶ Δ[n] where
  app m (α : { α : Δ[n].obj m // _ }) := α

namespace horn

open SimplexCategory Finset Opposite

@[simps]
def const (n : ℕ) (i k : Fin (n+3)) (m : SimplexCategoryᵒᵖ) : Λ[n+2, i].obj m := by
  refine ⟨standardSimplex.const _ k _, ?_⟩
  suffices ¬ Finset.univ ⊆ {i, k} by
    simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or, Fin.forall_fin_one,
      subset_iff, mem_univ, @eq_comm _ _ k]
  intro h
  have := (card_le_card h).trans card_le_two
  rw [card_fin] at this
  omega

@[simps]
def edge (n : ℕ) (i a b : Fin (n+1)) (hab : a ≤ b) (H : #{i, a, b} ≤ n) : Λ[n, i] _[1] := by
  refine ⟨standardSimplex.edge n a b hab, ?range⟩
  case range =>
    suffices ∃ x, ¬i = x ∧ ¬a = x ∧ ¬b = x by
      simpa only [unop_op, len_mk, Nat.reduceAdd, asOrderHom, yoneda_obj_obj, Set.union_singleton,
        ne_eq, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ, Set.mem_insert_iff,
        @eq_comm _ _ i, Set.mem_range, forall_const, not_forall, not_or, not_exists,
        Fin.forall_fin_two, Fin.isValue]
    contrapose! H
    replace H : univ ⊆ {i, a, b} :=
      fun x _ ↦ by simpa [or_iff_not_imp_left, eq_comm] using H x
    replace H := card_le_card H
    rwa [card_fin] at H

@[simps!]
def edge₃ (n : ℕ) (i a b : Fin (n+1)) (hab : a ≤ b) (H : 3 ≤ n) :
    Λ[n, i] _[1] :=
  horn.edge n i a b hab <| Finset.card_le_three.trans H

@[simps!]
def primitiveEdge {n : ℕ} {i : Fin (n+1)}
    (h₀ : 0 < i) (hₙ : i < Fin.last n) (j : Fin n) :
    Λ[n, i] _[1] := by
  refine horn.edge n i j.castSucc j.succ ?_ ?_
  · simp only [← Fin.val_fin_le, Fin.coe_castSucc, Fin.val_succ, le_add_iff_nonneg_right, zero_le]
  simp only [← Fin.val_fin_lt, Fin.val_zero, Fin.val_last] at h₀ hₙ
  obtain rfl|hn : n = 2 ∨ 2 < n := by
    rw [eq_comm, or_comm, ← le_iff_lt_or_eq]; omega
  · revert i j; decide
  · exact Finset.card_le_three.trans hn

@[simps]
def primitiveTriangle {n : ℕ} (i : Fin (n+4))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n+3))
    (k : ℕ) (h : k < n+2) : Λ[n+3, i] _[2] := by
  refine ⟨standardSimplex.triangle
    (n := n+3) ⟨k, by omega⟩ ⟨k+1, by omega⟩ ⟨k+2, by omega⟩ ?_ ?_, ?_⟩
  · simp only [Fin.mk_le_mk, le_add_iff_nonneg_right, zero_le]
  · simp only [Fin.mk_le_mk, add_le_add_iff_left, one_le_two]
  simp only [unop_op, SimplexCategory.len_mk, asOrderHom, SimplexCategory.Hom.toOrderHom_mk,
    OrderHom.const_coe_coe, Set.union_singleton, ne_eq, ← Set.univ_subset_iff, Set.subset_def,
    Set.mem_univ, Set.mem_insert_iff, Set.mem_range, Function.const_apply, exists_const,
    forall_true_left, not_forall, not_or, unop_op, not_exists,
    standardSimplex.triangle, OrderHom.coe_mk, @eq_comm _ _ i,
    standardSimplex.objMk, standardSimplex.objEquiv, Equiv.ulift]
  dsimp
  by_cases hk0 : k = 0
  · subst hk0
    use Fin.last (n+3)
    simp only [hₙ.ne, not_false_eq_true, Fin.zero_eta, zero_add, true_and]
    intro j
    fin_cases j <;> simp [Fin.ext_iff]
  · use 0
    simp only [h₀.ne', not_false_eq_true, true_and]
    intro j
    fin_cases j <;> simp [Fin.ext_iff, hk0]

@[simps]
def face {n : ℕ} (i j : Fin (n+2)) (h : j ≠ i) : Λ[n+1, i] _[n] :=
  ⟨(standardSimplex.objEquiv _ _).symm (SimplexCategory.δ j), by
    simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, SimplexCategory.δ, not_or,
      standardSimplex.objEquiv, asOrderHom, Equiv.ulift]⟩

protected
lemma hom_ext {n : ℕ} {i : Fin (n+2)} {S : SSet} (σ₁ σ₂ : Λ[n+1, i] ⟶ S)
    (h : ∀ (j) (h : j ≠ i), σ₁.app _ (face i j h) = σ₂.app _ (face i j h)) :
    σ₁ = σ₂ := by
  apply NatTrans.ext; apply funext; apply Opposite.rec; apply SimplexCategory.rec
  intro m; ext f
  obtain ⟨f', hf⟩ := (standardSimplex.objEquiv _ _).symm.surjective f.1
  obtain ⟨j, hji, hfj⟩ : ∃ j, ¬j = i ∧ ∀ k, f'.toOrderHom k ≠ j := by
    obtain ⟨f, hf'⟩ := f
    subst hf
    simpa [← Set.univ_subset_iff, Set.subset_def, asOrderHom, not_or] using hf'
  have H : f = (Λ[n+1, i].map (factor_δ f' j).op) (face i j hji) := by
    apply Subtype.ext
    apply (standardSimplex.objEquiv _ _).injective
    rw [← hf]
    exact (factor_δ_spec f' j hfj).symm
  have H₁ := congrFun (σ₁.naturality (factor_δ f' j).op) (face i j hji)
  have H₂ := congrFun (σ₂.naturality (factor_δ f' j).op) (face i j hji)
  dsimp at H₁ H₂
  rw [H, H₁, H₂, h _ hji]

end horn

section Examples

open Simplicial

noncomputable def S1 : SSet :=
  Limits.colimit <|
    Limits.parallelPair (standardSimplex.map <| SimplexCategory.δ 0 : Δ[0] ⟶ Δ[1])
      (standardSimplex.map <| SimplexCategory.δ 1)

end Examples

def Truncated (n : ℕ) :=
  SimplicialObject.Truncated (Type u) n

instance Truncated.largeCategory (n : ℕ) : LargeCategory (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

instance Truncated.hasLimits {n : ℕ} : HasLimits (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

instance Truncated.hasColimits {n : ℕ} : HasColimits (Truncated n) := by
  dsimp only [Truncated]
  infer_instance

def Truncated.uliftFunctor (k : ℕ) : SSet.Truncated.{u} k ⥤ SSet.Truncated.{max u v} k :=
  (whiskeringRight _ _ _).obj CategoryTheory.uliftFunctor.{v, u}

@[ext]
lemma Truncated.hom_ext {n : ℕ} {X Y : Truncated n} {f g : X ⟶ Y} (w : ∀ n, f.app n = g.app n) :
    f = g :=
  NatTrans.ext (funext w)

abbrev truncation (n : ℕ) : SSet ⥤ SSet.Truncated n := SimplicialObject.truncation n

instance {n} : Inhabited (SSet.Truncated n) :=
  ⟨(truncation n).obj <| Δ[0]⟩

open SimplexCategory

noncomputable section

protected abbrev Truncated.sk (n : ℕ) : SSet.Truncated n ⥤ SSet.{u} :=
  SimplicialObject.Truncated.sk n

protected abbrev Truncated.cosk (n : ℕ) : SSet.Truncated n ⥤ SSet.{u} :=
  SimplicialObject.Truncated.cosk n

abbrev sk (n : ℕ) : SSet ⥤ SSet := SimplicialObject.sk n

abbrev cosk (n : ℕ) : SSet ⥤ SSet := SimplicialObject.cosk n

end

section adjunctions

noncomputable def skAdj (n : ℕ) : Truncated.sk n ⊣ truncation.{u} n :=
  SimplicialObject.skAdj n

noncomputable def coskAdj (n : ℕ) : truncation.{u} n ⊣ Truncated.cosk n :=
  SimplicialObject.coskAdj n

namespace Truncated

instance cosk_reflective (n) : IsIso (coskAdj n).counit :=
  SimplicialObject.Truncated.cosk_reflective n

instance sk_coreflective (n) : IsIso (skAdj n).unit :=
  SimplicialObject.Truncated.sk_coreflective n

noncomputable def cosk.fullyFaithful (n) :
    (Truncated.cosk n).FullyFaithful :=
  SimplicialObject.Truncated.cosk.fullyFaithful n

instance cosk.full (n) : (Truncated.cosk n).Full :=
  SimplicialObject.Truncated.cosk.full n

instance cosk.faithful (n) : (Truncated.cosk n).Faithful :=
  SimplicialObject.Truncated.cosk.faithful n

noncomputable instance coskAdj.reflective (n) : Reflective (Truncated.cosk n) :=
  SimplicialObject.Truncated.coskAdj.reflective n

noncomputable def sk.fullyFaithful (n) :
    (Truncated.sk n).FullyFaithful := SimplicialObject.Truncated.sk.fullyFaithful n

instance sk.full (n) : (Truncated.sk n).Full := SimplicialObject.Truncated.sk.full n

instance sk.faithful (n) : (Truncated.sk n).Faithful :=
  SimplicialObject.Truncated.sk.faithful n

noncomputable instance skAdj.coreflective (n) : Coreflective (Truncated.sk n) :=
  SimplicialObject.Truncated.skAdj.coreflective n

end Truncated

end adjunctions

abbrev Augmented :=
  SimplicialObject.Augmented (Type u)

namespace Augmented

@[simps]
noncomputable def standardSimplex : SimplexCategory ⥤ SSet.Augmented.{u} where
  obj Δ :=
    { left := SSet.standardSimplex.obj Δ
      right := terminal _
      hom := { app := fun _ => terminal.from _ } }
  map θ :=
    { left := SSet.standardSimplex.map θ
      right := terminal.from _ }

end Augmented

section applications

variable {S : SSet}

lemma δ_comp_δ_apply {n} {i j : Fin (n + 2)} (H : i ≤ j) (x : S _[n + 2]) :
    S.δ i (S.δ j.succ x) = S.δ j (S.δ i.castSucc x) := congr_fun (S.δ_comp_δ H) x

lemma δ_comp_δ'_apply {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : Fin.castSucc i < j)
    (x : S _[n + 2]) : S.δ i (S.δ j x) =
      S.δ (j.pred fun (hj : j = 0) => by simp [hj, Fin.not_lt_zero] at H) (S.δ i.castSucc x) :=
  congr_fun (S.δ_comp_δ' H) x

lemma δ_comp_δ''_apply {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ Fin.castSucc j)
    (x : S _[n + 2]) :
    S.δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) (S.δ j.succ x) =
      S.δ j (S.δ i x) := congr_fun (S.δ_comp_δ'' H) x

lemma δ_comp_δ_self_apply {n} {i : Fin (n + 2)} (x : S _[n + 2]) :
    S.δ i (S.δ i.castSucc x) = S.δ i (S.δ i.succ x) := congr_fun S.δ_comp_δ_self x

lemma δ_comp_δ_self'_apply {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = Fin.castSucc i)
    (x : S _[n + 2]) : S.δ i (S.δ j x) = S.δ i (S.δ i.succ x) := congr_fun (S.δ_comp_δ_self' H) x

lemma δ_comp_σ_of_le_apply {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ Fin.castSucc j)
    (x : S _[n + 1]) :
    S.δ (Fin.castSucc i) (S.σ j.succ x) = S.σ j (S.δ i x) := congr_fun (S.δ_comp_σ_of_le H) x

@[simp]
lemma δ_comp_σ_self_apply {n} (i : Fin (n + 1)) (x : S _[n]) : S.δ i.castSucc (S.σ i x) = x :=
  congr_fun S.δ_comp_σ_self x

lemma δ_comp_σ_self'_apply {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = Fin.castSucc i)
    (x : S _[n]) : S.δ j (S.σ i x) = x := congr_fun (S.δ_comp_σ_self' H) x

@[simp]
lemma δ_comp_σ_succ_apply {n} (i : Fin (n + 1)) (x : S _[n]) : S.δ i.succ (S.σ i x) = x :=
  congr_fun S.δ_comp_σ_succ x

lemma δ_comp_σ_succ'_apply {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) (x : S _[n]) :
    S.δ j (S.σ i x) = x := congr_fun (S.δ_comp_σ_succ' H) x

lemma δ_comp_σ_of_gt_apply {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : Fin.castSucc j < i)
    (x : S _[n + 1]) : S.δ i.succ (S.σ (Fin.castSucc j) x) = S.σ j (S.δ i x) :=
  congr_fun (S.δ_comp_σ_of_gt H) x

lemma δ_comp_σ_of_gt'_apply {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i)
    (x : S _[n + 1]) : S.δ i (S.σ j x) =
      S.σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le)))
        (S.δ (i.pred fun (hi : i = 0) => by simp only [Fin.not_lt_zero, hi] at H) x) :=
  congr_fun (S.δ_comp_σ_of_gt' H) x

lemma σ_comp_σ_apply {n} {i j : Fin (n + 1)} (H : i ≤ j) (x : S _[n]) :
    S.σ i.castSucc (S.σ j x) = S.σ j.succ (S.σ i x) := congr_fun (S.σ_comp_σ H) x

end applications

end SSet
