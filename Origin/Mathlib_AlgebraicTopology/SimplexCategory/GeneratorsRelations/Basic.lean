/-
Extracted from AlgebraicTopology/SimplexCategory/GeneratorsRelations/Basic.lean
Genuine: 12 of 13 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Presentation of the simplex category by generators and relations.

We introduce `SimplexCategoryGenRel` as the category presented by generating
morphisms `δ i : [n] ⟶ [n + 1]` and `σ i : [n + 1] ⟶ [n]` and subject to the
simplicial identities, and we provide induction principles for reasoning about
objects and morphisms in this category.

This category admits a canonical functor `toSimplexCategory` to the usual simplex category.
The fact that this functor is an equivalence will be recorded in a separate file.
-/

open CategoryTheory

def FreeSimplexQuiver := ℕ

def FreeSimplexQuiver.mk (n : ℕ) : FreeSimplexQuiver := n

def FreeSimplexQuiver.len (x : FreeSimplexQuiver) : ℕ := x

namespace FreeSimplexQuiver

inductive Hom : FreeSimplexQuiver → FreeSimplexQuiver → Type
  | δ {n : ℕ} (i : Fin (n + 2)) : Hom (.mk n) (.mk (n + 1))
  | σ {n : ℕ} (i : Fin (n + 1)) : Hom (.mk (n + 1)) (.mk n)

-- INSTANCE (free from Core): quiv

abbrev δ {n : ℕ} (i : Fin (n + 2)) : FreeSimplexQuiver.mk n ⟶ .mk (n + 1) :=
  FreeSimplexQuiver.Hom.δ i

abbrev σ {n : ℕ} (i : Fin (n + 1)) : FreeSimplexQuiver.mk (n + 1) ⟶ .mk n :=
  FreeSimplexQuiver.Hom.σ i

inductive homRel : HomRel (Paths FreeSimplexQuiver)
  | δ_comp_δ {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i) ≫ (Paths.of FreeSimplexQuiver).map (δ j.succ))
    ((Paths.of FreeSimplexQuiver).map (δ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i.castSucc))
  | δ_comp_σ_of_le {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.castSucc) : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ j.succ))
    ((Paths.of FreeSimplexQuiver).map (σ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i))
  | δ_comp_σ_self {n : ℕ} {i : Fin (n + 1)} : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ i)) (𝟙 _)
  | δ_comp_σ_succ {n : ℕ} {i : Fin (n + 1)} : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ i)) (𝟙 _)
  | δ_comp_σ_of_gt {n : ℕ} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) : homRel
    ((Paths.of FreeSimplexQuiver).map (δ i.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ j.castSucc))
    ((Paths.of FreeSimplexQuiver).map (σ j) ≫ (Paths.of FreeSimplexQuiver).map (δ i))
  | σ_comp_σ {n : ℕ} {i j : Fin (n + 1)} (H : i ≤ j) : homRel
    ((Paths.of FreeSimplexQuiver).map (σ i.castSucc) ≫ (Paths.of FreeSimplexQuiver).map (σ j))
    ((Paths.of FreeSimplexQuiver).map (σ j.succ) ≫ (Paths.of FreeSimplexQuiver).map (σ i))

end FreeSimplexQuiver

def SimplexCategoryGenRel := Quotient FreeSimplexQuiver.homRel
  deriving Category

def SimplexCategoryGenRel.mk (n : ℕ) : SimplexCategoryGenRel where
  as := (Paths.of FreeSimplexQuiver).obj n

namespace SimplexCategoryGenRel

abbrev δ {n : ℕ} (i : Fin (n + 2)) : mk n ⟶ mk (n + 1) :=
  (Quotient.functor FreeSimplexQuiver.homRel).map <| (Paths.of FreeSimplexQuiver).map (.δ i)

abbrev σ {n : ℕ} (i : Fin (n + 1)) : mk (n + 1) ⟶ mk n :=
  (Quotient.functor FreeSimplexQuiver.homRel).map <| (Paths.of FreeSimplexQuiver).map (.σ i)

def len (x : SimplexCategoryGenRel) : ℕ := by rcases x with ⟨n⟩; exact n
