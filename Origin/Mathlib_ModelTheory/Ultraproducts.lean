/-
Extracted from ModelTheory/Ultraproducts.lean
Genuine: 5 of 8 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Ultraproducts and Łoś's Theorem

## Main Definitions

- `FirstOrder.Language.Ultraproduct.Structure` is the ultraproduct structure on `Filter.Product`.

## Main Results

- Łoś's Theorem: `FirstOrder.Language.Ultraproduct.sentence_realize`. An ultraproduct models a
  sentence `φ` if and only if the set of structures in the product that model `φ` is in the
  ultrafilter.

## Tags

ultraproduct, Los's theorem
-/

universe u v

variable {α : Type*} (M : α → Type*) (u : Ultrafilter α)

open FirstOrder Filter

namespace FirstOrder

namespace Language

open Structure

variable {L : Language.{u, v}} [∀ a, L.Structure (M a)]

namespace Ultraproduct

-- INSTANCE (free from Core): setoidPrestructure

variable {M} {u}

-- INSTANCE (free from Core): «structure»

theorem funMap_cast {n : ℕ} (f : L.Functions n) (x : Fin n → ∀ a, M a) :
    (funMap f fun i => (x i : (u : Filter α).Product M)) =
      (fun a => funMap f fun i => x i a : (u : Filter α).Product M) := by
  apply funMap_quotient_mk'

theorem term_realize_cast {β : Type*} (x : β → ∀ a, M a) (t : L.Term β) :
    (t.realize fun i => (x i : (u : Filter α).Product M)) =
      (fun a => t.realize fun i => x i a : (u : Filter α).Product M) := by
  convert @Term.realize_quotient_mk' L _ ((u : Filter α).productSetoid M)
      (Ultraproduct.setoidPrestructure M u) _ t x using 2
  ext a
  induction t with
  | var => rfl
  | func _ _ t_ih => simp only [Term.realize, t_ih]; rfl

variable [∀ a : α, Nonempty (M a)]

theorem boundedFormula_realize_cast {β : Type*} {n : ℕ} (φ : L.BoundedFormula β n)
    (x : β → ∀ a, M a) (v : Fin n → ∀ a, M a) :
    (φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
        (fun i => (v i : (u : Filter α).Product M))) ↔
      ∀ᶠ a : α in u, φ.Realize (fun i : β => x i a) fun i => v i a := by
  induction φ with
  | falsum => simp only [BoundedFormula.Realize, eventually_const]
  | equal =>
    have h2 : ∀ a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [BoundedFormula.Realize, h2]
    erw [(Sum.comp_elim ((↑) : (∀ a, M a) → (u : Filter α).Product M) x v).symm,
      term_realize_cast, term_realize_cast]
    exact Quotient.eq''
  | rel =>
    have h2 : ∀ a : α, (Sum.elim (fun i : β => x i a) fun i => v i a) = fun i => Sum.elim x v i a :=
      fun a => funext fun i => Sum.casesOn i (fun i => rfl) fun i => rfl
    simp only [BoundedFormula.Realize, h2]
    erw [(Sum.comp_elim ((↑) : (∀ a, M a) → (u : Filter α).Product M) x v).symm]
    conv_lhs => enter [2, i]; erw [term_realize_cast]
    apply relMap_quotient_mk'
  | imp _ _ ih ih' =>
    simp only [BoundedFormula.Realize, ih v, ih' v]
    rw [Ultrafilter.eventually_imp]
  | @all k φ ih =>
    simp only [BoundedFormula.Realize]
    apply Iff.trans (b := ∀ m : ∀ a : α, M a,
      φ.Realize (fun i : β => (x i : (u : Filter α).Product M))
        (Fin.snoc (((↑) : (∀ a, M a) → (u : Filter α).Product M) ∘ v)
          (m : (u : Filter α).Product M)))
    · exact Quotient.forall
    have h' :
      ∀ (m : ∀ a, M a) (a : α),
        (fun i : Fin (k + 1) => (Fin.snoc v m : _ → ∀ a, M a) i a) =
          Fin.snoc (fun i : Fin k => v i a) (m a) := by
      refine fun m a => funext (Fin.reverseInduction ?_ fun i _ => ?_)
      · simp only [Fin.snoc_last]
      · simp only [Fin.snoc_castSucc]
    simp only [← Fin.comp_snoc]
    simp only [Function.comp_def, ih, h']
    refine ⟨fun h => ?_, fun h m => ?_⟩
    · contrapose! h
      refine
        ⟨fun a : α =>
          Classical.epsilon fun m : M a =>
            ¬φ.Realize (fun i => x i a) (Fin.snoc (fun i => v i a) m),
          ?_⟩
      exact Filter.mem_of_superset h fun a ha => Classical.epsilon_spec ha
    · rw [Filter.eventually_iff] at *
      exact Filter.mem_of_superset h fun a ha => ha (m a)

theorem realize_formula_cast {β : Type*} (φ : L.Formula β) (x : β → ∀ a, M a) :
    (φ.Realize fun i => (x i : (u : Filter α).Product M)) ↔
      ∀ᶠ a : α in u, φ.Realize fun i => x i a := by
  simp_rw [Formula.Realize, ← boundedFormula_realize_cast φ x, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

theorem sentence_realize (φ : L.Sentence) :
    (u : Filter α).Product M ⊨ φ ↔ ∀ᶠ a : α in u, M a ⊨ φ := by
  simp_rw [Sentence.Realize]
  rw [← realize_formula_cast φ, iff_eq_eq]
  exact congr rfl (Subsingleton.elim _ _)

-- INSTANCE (free from Core): Product.instNonempty

end Ultraproduct

end Language

end FirstOrder
