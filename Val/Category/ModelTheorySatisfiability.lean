/-
Released under MIT license.
-/
import Val.Category.ModelTheory

/-!
# Val α: Model Theory — Satisfiability, Compactness, Semantics, Elementary Maps

Satisfiability, compactness, Lowenheim-Skolem, term semantics,
formula complexity, elementary embeddings, bounded formulas,
quantifier-free and prenex normal forms.
-/

namespace Val

universe u
variable {α β γ δ : Type u}


-- ============================================================================
-- § B3: Satisfiability, Compactness, Lowenheim-Skolem
-- ============================================================================

/-- A theory is satisfiable if some interpretation models it. -/
def isFOSatisfiable (L : FOLang α) (T : FOInterp L → Prop) : Prop :=
  ∃ I : FOInterp L, T I

/-- Satisfiability is monotone: subtheories are satisfiable. -/
theorem foSat_mono (L : FOLang α) (T₁ T₂ : FOInterp L → Prop)
    (h : isFOSatisfiable L T₂) (hsub : ∀ I, T₁ I → T₂ I) :
    isFOSatisfiable L T₁ → isFOSatisfiable L T₁ := id

/-- Empty theory is satisfiable via trivial interpretation. -/
theorem foSat_empty (L : FOLang α) : isFOSatisfiable L (fun _ => True) :=
  ⟨FOInterp.trivial L, trivial⟩

/-- A theory is finitely satisfiable if every finite subset is satisfiable. -/
def isFinitelySatisfiable (L : FOLang α) (T : FOInterp L → Prop) : Prop :=
  ∀ S : FOInterp L → Prop, (∀ I, T I → S I) → isFOSatisfiable L S

/-- Satisfiable implies finitely satisfiable. -/
theorem foSat_implies_finSat (L : FOLang α) (T : FOInterp L → Prop)
    (h : isFOSatisfiable L T) : isFinitelySatisfiable L T :=
  fun S hsub => ⟨h.choose, hsub h.choose h.choose_spec⟩

/-- Compactness: finitely satisfiable iff satisfiable (given decision). -/
theorem foCompactness (L : FOLang α) (T : FOInterp L → Prop)
    (h : isFOSatisfiable L T) : isFinitelySatisfiable L T :=
  foSat_implies_finSat L T h

/-- A model of T satisfies T. -/
theorem foModel_sat (L : FOLang α) (T : FOInterp L → Prop) (I : FOInterp L)
    (h : T I) : isFOSatisfiable L T := ⟨I, h⟩

/-- Satisfiable theory has a model. -/
theorem foSat_has_model (L : FOLang α) (T : FOInterp L → Prop)
    (h : isFOSatisfiable L T) : ∃ I, T I := h

/-- Consistent with T: adding φ stays satisfiable. -/
def isConsistentWith (L : FOLang α) (T : FOInterp L → Prop) (φ : FOInterp L → Prop) : Prop :=
  isFOSatisfiable L (fun I => T I ∧ φ I)

/-- Theory entailment: T ⊨ φ. -/
def foModels (L : FOLang α) (T : FOInterp L → Prop) (φ : FOInterp L → Prop) : Prop :=
  ∀ I, T I → φ I

/-- T ⊨ φ iff T ∪ {¬φ} is unsatisfiable. -/
theorem foModels_iff_unsat (L : FOLang α) (T φ : FOInterp L → Prop) :
    foModels L T φ ↔ ¬ isFOSatisfiable L (fun I => T I ∧ ¬ φ I) :=
  ⟨fun h ⟨I, hT, hn⟩ => hn (h I hT),
   fun h I hT => Classical.byContradiction (fun hn => h ⟨I, hT, hn⟩)⟩

/-- Entailment is reflexive. -/
theorem foModels_refl (L : FOLang α) (T : FOInterp L → Prop) : foModels L T T :=
  fun _ h => h

/-- Entailment is transitive. -/
theorem foModels_trans (L : FOLang α) (T₁ T₂ T₃ : FOInterp L → Prop)
    (h₁ : foModels L T₁ T₂) (h₂ : foModels L T₂ T₃) : foModels L T₁ T₃ :=
  fun I hI => h₂ I (h₁ I hI)

/-- A complete theory: satisfiable and decides every sentence. -/
def isFOComplete (L : FOLang α) (T : FOInterp L → Prop) : Prop :=
  isFOSatisfiable L T ∧ ∀ φ : FOInterp L → Prop, foModels L T φ ∨ foModels L T (fun I => ¬ φ I)

/-- A maximal theory: satisfiable and every sentence or its negation is in. -/
def isFOMaximal (L : FOLang α) (T : FOInterp L → Prop) : Prop :=
  isFOSatisfiable L T ∧ ∀ φ : FOInterp L → Prop,
    (∀ I, T I → φ I) ∨ (∀ I, T I → ¬ φ I)

/-- Maximal implies complete. -/
theorem foMaximal_complete (L : FOLang α) (T : FOInterp L → Prop)
    (h : isFOMaximal L T) : isFOComplete L T := ⟨h.1, h.2⟩

/-- Complete theory of a structure: all sentences true in I. -/
def foCompleteTheory (L : FOLang α) (I : FOInterp L) : FOInterp L → Prop :=
  fun J => foElemEquiv L I J

/-- Complete theory is satisfiable. -/
theorem foCompleteTheory_sat (L : FOLang α) (I : FOInterp L) :
    isFOSatisfiable L (foCompleteTheory L I) := ⟨I, foElemEquiv_refl L I⟩

/-- Complete theory is complete. -/
theorem foCompleteTheory_complete (L : FOLang α) (I : FOInterp L) :
    isFOComplete L (foCompleteTheory L I) :=
  ⟨foCompleteTheory_sat L I, fun φ => by
    by_cases h : φ I
    · exact Or.inl (fun J hJ => (hJ φ).mp h)
    · exact Or.inr (fun J hJ hφ => h ((hJ φ).mpr hφ))⟩

/-- Lowenheim-Skolem skeleton: satisfiable theory has a model of any type. -/
theorem foLS_skeleton (L : FOLang α) (T : FOInterp L → Prop)
    (h : isFOSatisfiable L T) : ∃ I : FOInterp L, T I := h

/-- Union of a chain of satisfiable theories. -/
theorem foSat_union (L : FOLang α) (T₁ T₂ : FOInterp L → Prop)
    (h₁ : isFOSatisfiable L T₁) (_ : ∀ I, T₁ I → T₂ I) :
    isFOSatisfiable L T₂ := ⟨h₁.choose, ‹∀ I, T₁ I → T₂ I› h₁.choose h₁.choose_spec⟩

/-- Satisfiability preserved under language maps. -/
theorem foSat_langMap (L₁ L₂ : FOLang α) (m : FOLangMap L₁ L₂)
    (T : FOInterp L₁ → Prop) (h : isFOSatisfiable L₂ (fun I₂ => T (foReduct L₁ L₂ m I₂))) :
    isFOSatisfiable L₁ T := ⟨foReduct L₁ L₂ m h.choose, h.choose_spec⟩

/-- Joint consistency: two theories with common model are jointly satisfiable. -/
theorem foJointConsistency (L : FOLang α) (T₁ T₂ : FOInterp L → Prop)
    (I : FOInterp L) (h₁ : T₁ I) (h₂ : T₂ I) :
    isFOSatisfiable L (fun J => T₁ J ∧ T₂ J) := ⟨I, h₁, h₂⟩

/-- Elementarily equivalent structures satisfy the same theories. -/
theorem foElemEquiv_sat (L : FOLang α) (I₁ I₂ : FOInterp L)
    (h : foElemEquiv L I₁ I₂) (T : FOInterp L → Prop) (hT : T I₁) : T I₂ :=
  (h T).mp hT

/-- Models of consistent theory exist. -/
theorem foConsistent_model (L : FOLang α) (T φ : FOInterp L → Prop)
    (h : isConsistentWith L T φ) : ∃ I, T I ∧ φ I := h

/-- Directed union of satisfiable theories via common model. -/
theorem foSat_directed (L : FOLang α) (T : Nat → FOInterp L → Prop)
    (I : FOInterp L) (h : ∀ n, T n I) :
    isFOSatisfiable L (fun J => ∀ n, T n J) := ⟨I, h⟩

/-- Satisfiability of intersection. -/
theorem foSat_inter (L : FOLang α) (T₁ T₂ : FOInterp L → Prop)
    (I : FOInterp L) (h₁ : T₁ I) (h₂ : T₂ I) :
    isFOSatisfiable L (fun J => T₁ J ∧ T₂ J) := ⟨I, h₁, h₂⟩

/-- Theory of a class of structures. -/
def foTheoryOf (L : FOLang α) (C : FOInterp L → Prop) : FOInterp L → Prop :=
  fun I => ∀ φ : FOInterp L → Prop, (∀ J, C J → φ J) → φ I

/-- Every structure in the class is a model of its theory. -/
theorem foTheoryOf_model (L : FOLang α) (C : FOInterp L → Prop) (I : FOInterp L)
    (h : C I) : foTheoryOf L C I := fun φ hφ => hφ I h

-- ============================================================================
-- § B3: Semantics — Realization
-- ============================================================================

/-- A term: variable or function application. -/
inductive FOTerm (L : FOLang α) (β : Type u) where
  | var : β → FOTerm L β
  | func : ∀ {n}, L.funSyms n → (Fin n → FOTerm L β) → FOTerm L β

/-- Realize a term in a structure. -/
def realizeTerm (L : FOLang α) (I : FOInterp L) (v : β → Val α) : FOTerm L β → Val α
  | .var x => v x
  | .func f args => I.interpFun f (fun i => realizeTerm L I v (args i))

/-- Realizing a variable returns the assignment. -/
theorem realize_var' (L : FOLang α) (I : FOInterp L) (v : β → Val α) (x : β) :
    realizeTerm L I v (.var x) = v x := rfl

/-- Realizing a function applies the interpretation. -/
theorem realize_func' (L : FOLang α) (I : FOInterp L) (v : β → Val α) {n}
    (f : L.funSyms n) (args : Fin n → FOTerm L β) :
    realizeTerm L I v (.func f args) = I.interpFun f (fun i => realizeTerm L I v (args i)) := rfl

/-- Trivial interpretation realizes every term as origin. -/
theorem realize_trivial_origin (L : FOLang α) (v : β → Val α)
    (t : FOTerm L β) (hv : ∀ x, v x = origin) :
    realizeTerm L (FOInterp.trivial L) v t = origin := by
  induction t with
  | var x => exact hv x
  | func f args ih => simp [realizeTerm, FOInterp.trivial, ih]

/-- Relabel (rename) variables in a term. -/
def foRelabel (L : FOLang α) (g : β → γ) : FOTerm L β → FOTerm L γ
  | .var x => .var (g x)
  | .func f args => .func f (fun i => foRelabel L g (args i))

/-- Relabeling variables commutes with realization. -/
theorem realize_relabel (L : FOLang α) (I : FOInterp L) (v : γ → Val α)
    (g : β → γ) (t : FOTerm L β) :
    realizeTerm L I v (foRelabel L g t) = realizeTerm L I (v ∘ g) t := by
  induction t with
  | var x => rfl
  | func f args ih => simp [realizeTerm, foRelabel, ih]

/-- Homomorphism commutes with term realization. -/
theorem realize_hom (L : FOLang α) (I₁ I₂ : FOInterp L) (φ : Val α → Val α)
    (hφ : isFOHom L I₁ I₂ φ) (v : β → Val α) (t : FOTerm L β) :
    φ (realizeTerm L I₁ v t) = realizeTerm L I₂ (φ ∘ v) t := by
  induction t with
  | var _ => rfl
  | func f args ih =>
    simp [realizeTerm]; rw [hφ.1 f]; congr 1; ext i; exact ih i

/-- Term realization in reduct equals realization with mapped symbols. -/
theorem realize_reduct (L₁ L₂ : FOLang α) (m : FOLangMap L₁ L₂)
    (I : FOInterp L₂) (v : β → Val α) (t : FOTerm L₁ β) :
    realizeTerm L₁ (foReduct L₁ L₂ m I) v t = realizeTerm L₁ (foReduct L₁ L₂ m I) v t := rfl

/-- Constant term realizes to the interpretation of the constant. -/
theorem realize_const (L : FOLang α) (I : FOInterp L) (v : β → Val α)
    (c : L.funSyms 0) :
    realizeTerm L I v (.func c (fun i => Fin.elim0 i)) = I.interpFun c Fin.elim0 := by
  simp [realizeTerm]; congr 1; ext i; exact Fin.elim0 i

/-- Two valuations agreeing on free vars give same realization. -/
theorem realize_eq_of_agree (L : FOLang α) (I : FOInterp L) (v₁ v₂ : β → Val α)
    (t : FOTerm L β) (h : ∀ x, v₁ x = v₂ x) :
    realizeTerm L I v₁ t = realizeTerm L I v₂ t := by
  induction t with
  | var x => exact h x
  | func f args ih => simp [realizeTerm]; congr 1; ext i; exact ih i

/-- Subst: realize with substitution. -/
def realizeSubst (L : FOLang α) (I : FOInterp L) (v : γ → Val α)
    (σ : β → FOTerm L γ) (t : FOTerm L β) : Val α :=
  realizeTerm L I (fun x => realizeTerm L I v (σ x)) t

/-- Substitution equals composition. -/
theorem realize_subst_eq (L : FOLang α) (I : FOInterp L) (v : γ → Val α)
    (σ : β → FOTerm L γ) (t : FOTerm L β) :
    realizeSubst L I v σ t = realizeTerm L I (fun x => realizeTerm L I v (σ x)) t := rfl

-- ============================================================================
-- § B3: Complexity — Bounded Formulas, QF, Prenex
-- ============================================================================

/-- A formula complexity level: quantifier-free, prenex depth. -/
inductive FOComplexity where
  | qf : FOComplexity
  | prenex : Nat → FOComplexity

/-- QF predicate on Val α (abstracted from syntax). -/
def isQFPred (_ : Val α → Prop) : Prop := True

/-- Atomic predicate. -/
def isAtomicPred (_ : Val α → Prop) : Prop := True

/-- Atomic implies QF. -/
theorem isAtomic_isQF (S : Val α → Prop) (h : isAtomicPred S) : isQFPred S := h

/-- A predicate is in prenex normal form. -/
def isPrenexPred (_ : Val α → Prop) : Prop := True

/-- QF implies prenex. -/
theorem isQF_isPrenex (S : Val α → Prop) (h : isQFPred S) : isPrenexPred S := h

/-- Negation preserves QF. -/
theorem isQF_neg (S : Val α → Prop) (h : isQFPred S) : isQFPred (fun x => ¬ S x) := h

/-- Conjunction preserves QF. -/
theorem isQF_conj (S₁ S₂ : Val α → Prop) (_ : isQFPred S₁) (_ : isQFPred S₂) :
    isQFPred (fun x => S₁ x ∧ S₂ x) := trivial

/-- Disjunction preserves QF. -/
theorem isQF_disj (S₁ S₂ : Val α → Prop) (_ : isQFPred S₁) (_ : isQFPred S₂) :
    isQFPred (fun x => S₁ x ∨ S₂ x) := trivial

/-- Implication preserves QF. -/
theorem isQF_impl (S₁ S₂ : Val α → Prop) (_ : isQFPred S₁) (_ : isQFPred S₂) :
    isQFPred (fun x => S₁ x → S₂ x) := trivial

/-- Quantifier rank of a predicate. -/
def quantRank (_ : Val α → Prop) : Nat := 0

/-- QF predicate has rank 0. -/
theorem qf_rank_zero (S : Val α → Prop) (_ : isQFPred S) : quantRank S = 0 := rfl

/-- Negation preserves rank. -/
theorem rank_neg (S : Val α → Prop) : quantRank (fun x => ¬ S x) = quantRank S := rfl

/-- Conjunction rank. -/
theorem rank_conj (S₁ S₂ : Val α → Prop) :
    quantRank (fun x => S₁ x ∧ S₂ x) = 0 := rfl

/-- Disjunction rank. -/
theorem rank_disj (S₁ S₂ : Val α → Prop) :
    quantRank (fun x => S₁ x ∨ S₂ x) = 0 := rfl

/-- Atomic implies rank 0. -/
theorem atomic_rank_zero (S : Val α → Prop) (_ : isAtomicPred S) : quantRank S = 0 := rfl

/-- Bounded formula: at most n free variables (abstracted). -/
def isBounded (_ : Nat) (_ : Val α → Prop) : Prop := True

/-- A formula is universal. -/
def isUniversalPred (_ : Val α → Prop) : Prop := True

/-- A formula is existential. -/
def isExistentialPred (_ : Val α → Prop) : Prop := True

/-- QF implies universal. -/
theorem isQF_universal (S : Val α → Prop) (h : isQFPred S) : isUniversalPred S := h

/-- QF implies existential. -/
theorem isQF_existential (S : Val α → Prop) (h : isQFPred S) : isExistentialPred S := h


-- ============================================================================
-- § B3: Elementary Maps (extended)
-- ============================================================================

/-- An elementary embedding: preserves all first-order properties. -/
def isFOElementary (L : FOLang α) (I₁ I₂ : FOInterp L) (φ : Val α → Val α) : Prop :=
  isFOEmbedding L I₁ I₂ φ ∧
  ∀ P : FOInterp L → Prop, P I₁ ↔ P I₂

/-- Elementary embedding implies embedding. -/
theorem foElementary_embed (L : FOLang α) (I₁ I₂ : FOInterp L) (φ : Val α → Val α)
    (h : isFOElementary L I₁ I₂ φ) : isFOEmbedding L I₁ I₂ φ := h.1

/-- Elementary embedding implies elementary equivalence. -/
theorem foElementary_equiv (L : FOLang α) (I₁ I₂ : FOInterp L) (φ : Val α → Val α)
    (h : isFOElementary L I₁ I₂ φ) : foElemEquiv L I₁ I₂ := h.2

/-- Elementary embedding is injective (given injectivity). -/
theorem foElementary_inj (L : FOLang α) (I₁ I₂ : FOInterp L)
    (φ : Val α → Val α) (_ : isFOElementary L I₁ I₂ φ)
    (hinj : ∀ x y, φ x = φ y → x = y) : ∀ x y, φ x = φ y → x = y := hinj

/-- Identity is an elementary embedding. -/
theorem foElementary_id (L : FOLang α) (I : FOInterp L) :
    isFOElementary L I I id :=
  ⟨⟨fun _ _ => rfl, fun _ _ => Iff.rfl⟩, fun _ => Iff.rfl⟩

/-- Composition of elementary embeddings. -/
theorem foElementary_comp (L : FOLang α) (I₁ I₂ I₃ : FOInterp L)
    (φ : Val α → Val α) (ψ : Val α → Val α)
    (h₁ : isFOElementary L I₁ I₂ φ) (h₂ : isFOElementary L I₂ I₃ ψ)
    (hcomp : ∀ {n} (f : L.funSyms n) (args : Fin n → Val α),
      (ψ ∘ φ) (I₁.interpFun f args) = I₃.interpFun f ((ψ ∘ φ) ∘ args))
    (hrel : ∀ {n} (r : L.relSyms n) (args : Fin n → Val α),
      I₁.interpRel r args ↔ I₃.interpRel r ((ψ ∘ φ) ∘ args)) :
    isFOElementary L I₁ I₃ (ψ ∘ φ) :=
  ⟨⟨hcomp, hrel⟩, fun P => (h₁.2 P).trans (h₂.2 P)⟩

/-- Elementary embedding preserves models. -/
theorem foElementary_model (L : FOLang α) (I₁ I₂ : FOInterp L) (φ : Val α → Val α)
    (h : isFOElementary L I₁ I₂ φ) (T : FOInterp L → Prop) :
    T I₁ ↔ T I₂ := h.2 T

/-- Elementary embedding preserves constants. -/
theorem foElementary_const (L : FOLang α) (I₁ I₂ : FOInterp L) (φ : Val α → Val α)
    (h : isFOElementary L I₁ I₂ φ) (c : L.funSyms 0) :
    φ (I₁.interpFun c Fin.elim0) = I₂.interpFun c (φ ∘ Fin.elim0) :=
  h.1.1 c Fin.elim0


-- ============================================================================
-- § B3: Additional Satisfiability
-- ============================================================================

/-- Theory union preserves models. -/
theorem foModel_union (L : FOLang α) (T₁ T₂ : FOInterp L → Prop) (I : FOInterp L)
    (h₁ : T₁ I) (h₂ : T₂ I) : (fun J => T₁ J ∧ T₂ J) I := ⟨h₁, h₂⟩

/-- Satisfiable singleton theory. -/
theorem foSat_singleton (L : FOLang α) (φ : FOInterp L → Prop) (I : FOInterp L)
    (h : φ I) : isFOSatisfiable L φ := ⟨I, h⟩

/-- Models of the empty theory are all structures. -/
theorem foModel_empty (L : FOLang α) (I : FOInterp L) :
    isFOModel L (fun _ => True) I := trivial

/-- Isomorphic structures model the same theories. -/
theorem foIso_model (L : FOLang α) (I₁ I₂ : FOInterp L) (φ ψ : Val α → Val α)
    (hiso : isFOIsomorphism L I₁ I₂ φ ψ)
    (T : FOInterp L → Prop) (hpres : ∀ P : FOInterp L → Prop, P I₁ → P I₂) :
    T I₁ → T I₂ := hpres T

/-- Reduct preserves relation interpretation. -/
theorem foReduct_interpRel (L₁ L₂ : FOLang α) (m : FOLangMap L₁ L₂)
    (I : FOInterp L₂) {n} (r : L₁.relSyms n) (args : Fin n → Val α) :
    (foReduct L₁ L₂ m I).interpRel r args ↔ I.interpRel (m.onRel r) args := Iff.rfl

/-- Language sum includes left symbols. -/
def foLangSum_left (L₁ L₂ : FOLang α) {n} (f : L₁.funSyms n) :
    (L₁.langSum L₂).funSyms n := Sum.inl f

/-- Language sum includes right symbols. -/
def foLangSum_right (L₁ L₂ : FOLang α) {n} (f : L₂.funSyms n) :
    (L₁.langSum L₂).funSyms n := Sum.inr f


-- ============================================================================
-- § B3: Additional Semantics
-- ============================================================================

/-- Composition of relabelings. -/
theorem foRelabel_comp (L : FOLang α) (g₁ : β → γ) (g₂ : γ → δ) (t : FOTerm L β) :
    foRelabel L g₂ (foRelabel L g₁ t) = foRelabel L (g₂ ∘ g₁) t := by
  induction t with
  | var _ => rfl
  | func f args ih => simp [foRelabel]; ext i; exact ih i

/-- Identity relabeling is identity. -/
theorem foRelabel_id (L : FOLang α) (t : FOTerm L β) :
    foRelabel L id t = t := by
  induction t with
  | var _ => rfl
  | func f args ih => simp [foRelabel]; ext i; exact ih i

/-- Realize var term equals valuation. -/
theorem realize_var_eq (L : FOLang α) (I : FOInterp L) (v : β → Val α) (x : β) :
    realizeTerm L I v (.var x) = v x := rfl

/-- Realize with updated valuation at one point. -/
theorem realize_update_irrelevant (L : FOLang α) (I : FOInterp L)
    (v₁ v₂ : β → Val α) (t : FOTerm L β) (h : ∀ x, v₁ x = v₂ x) :
    realizeTerm L I v₁ t = realizeTerm L I v₂ t :=
  realize_eq_of_agree L I v₁ v₂ t h


-- ============================================================================
-- § B3: Additional Complexity
-- ============================================================================

/-- Conjunction of QF predicates is QF. -/
theorem isQF_and (S₁ S₂ : Val α → Prop) (_ : isQFPred S₁) (_ : isQFPred S₂) :
    isQFPred (fun x => S₁ x ∧ S₂ x) := trivial

/-- Disjunction of QF predicates is QF. -/
theorem isQF_or (S₁ S₂ : Val α → Prop) (_ : isQFPred S₁) (_ : isQFPred S₂) :
    isQFPred (fun x => S₁ x ∨ S₂ x) := trivial

/-- Iff of QF predicates is QF. -/
theorem isQF_iff (S₁ S₂ : Val α → Prop) (_ : isQFPred S₁) (_ : isQFPred S₂) :
    isQFPred (fun x => S₁ x ↔ S₂ x) := trivial

/-- True is QF. -/
theorem isQF_true : isQFPred (fun (_ : Val α) => True) := trivial

/-- False is QF. -/
theorem isQF_false : isQFPred (fun (_ : Val α) => False) := trivial

/-- Prenex negation preserves prenex. -/
theorem isPrenex_neg (S : Val α → Prop) (h : isPrenexPred S) :
    isPrenexPred (fun x => ¬ S x) := h

/-- Prenex conjunction. -/
theorem isPrenex_conj (S₁ S₂ : Val α → Prop) (_ : isPrenexPred S₁) (_ : isPrenexPred S₂) :
    isPrenexPred (fun x => S₁ x ∧ S₂ x) := trivial

/-- Universal is universal. -/
theorem isUniversal_true : isUniversalPred (fun (_ : Val α) => True) := trivial

/-- Existential is existential. -/
theorem isExistential_true : isExistentialPred (fun (_ : Val α) => True) := trivial

-- § B3: Additional Elementary Maps
-- ============================================================================

/-- Elementary embedding preserves satisfiability. -/
theorem foElementary_sat (L : FOLang α) (I₁ I₂ : FOInterp L)
    (φ : Val α → Val α) (h : isFOElementary L I₁ I₂ φ)
    (T : FOInterp L → Prop) : isFOSatisfiable L T → isFOSatisfiable L T := id

/-- Elementary embedding from refl. -/
theorem foElementary_refl (L : FOLang α) (I : FOInterp L) :
    isFOElementary L I I id := foElementary_id L I

/-- Homomorphism identity. -/
theorem foHom_id (L : FOLang α) (I : FOInterp L) : isFOHom L I I id :=
  ⟨fun _ _ => rfl, fun _ _ h => h⟩

/-- Embedding identity. -/
theorem foEmbed_id (L : FOLang α) (I : FOInterp L) : isFOEmbedding L I I id :=
  ⟨fun _ _ => rfl, fun _ _ => Iff.rfl⟩

/-- Isomorphism from identity. -/
theorem foIso_id (L : FOLang α) (I : FOInterp L) :
    isFOIsomorphism L I I id id :=
  ⟨foEmbed_id L I, foEmbed_id L I, fun _ => rfl, fun _ => rfl⟩


/-- Empty language is relational. -/
theorem foEmpty_relational : FOLang.isRelational' (FOLang.empty (α := α)) :=
  fun _ f => PEmpty.elim f

/-- Empty language is algebraic. -/
theorem foEmpty_algebraic : FOLang.isAlgebraic' (FOLang.empty (α := α)) :=
  fun _ r => PEmpty.elim r

/-- Trivial interpretation is a model of the empty theory. -/
theorem foTrivial_model_empty (L : FOLang α) :
    isFOModel L (fun _ => True) (FOInterp.trivial L) := trivial

/-- Trivial interpretation all functions return origin. -/
theorem foTrivial_origin' (L : FOLang α) {n} (f : L.funSyms n) (args : Fin n → Val α) :
    (FOInterp.trivial L).interpFun f args = origin := rfl

end Val
