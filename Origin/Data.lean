/-
Released under MIT license.
-/
import Origin.Core

/-!
# Data on Option α (Core-based)

GCD, primality, congruence, lists, sets, extended types, multisets,
finsets, matrices, complex numbers, fin types, finsupp, sigma types,
Option lifting demonstrations.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. GCD
-- ============================================================================

def optGcd (gcdF : α → α → α) : Option α → Option α → Option α := liftBin₂ gcdF
@[simp] theorem optGcd_none_left (gcdF : α → α → α) (b : Option α) :
    optGcd gcdF none b = none := by cases b <;> rfl
@[simp] theorem optGcd_none_right (gcdF : α → α → α) (a : Option α) :
    optGcd gcdF a none = none := by cases a <;> rfl
@[simp] theorem optGcd_some (gcdF : α → α → α) (a b : α) :
    optGcd gcdF (some a) (some b) = some (gcdF a b) := rfl
theorem optGcd_comm (gcdF : α → α → α)
    (h : ∀ a b : α, gcdF a b = gcdF b a) (a b : Option α) :
    optGcd gcdF a b = optGcd gcdF b a := by
  cases a <;> cases b <;> simp [optGcd, h]

-- ============================================================================
-- 2. PRIMALITY
-- ============================================================================

def optIsPrime (primeP : α → Prop) : Option α → Prop := liftPred primeP
@[simp] theorem optIsPrime_none (primeP : α → Prop) :
    optIsPrime primeP (none : Option α) = False := rfl

-- ============================================================================
-- 3. CONGRUENCE
-- ============================================================================

def optCong (modF : α → α → α) (a b n : α) : Prop := modF a n = modF b n
theorem optCong_refl (modF : α → α → α) (a n : α) : optCong modF a a n := rfl
theorem optCong_symm (modF : α → α → α) (a b n : α)
    (h : optCong modF a b n) : optCong modF b a n := h.symm
theorem optCong_trans (modF : α → α → α) (a b c n : α)
    (hab : optCong modF a b n) (hbc : optCong modF b c n) :
    optCong modF a c n := hab.trans hbc

-- ============================================================================
-- 4. LISTS
-- ============================================================================

variable {β : Type u}

def optAppend : Option (List α) → Option (List α) → Option (List α) := liftBin₂ (· ++ ·)
@[simp] theorem optAppend_none_left (ys : Option (List α)) :
    optAppend none ys = none := by cases ys <;> rfl
@[simp] theorem optAppend_none_right (xs : Option (List α)) :
    optAppend xs none = none := by cases xs <;> rfl
@[simp] theorem optAppend_some (xs ys : List α) :
    optAppend (some xs) (some ys) = some (xs ++ ys) := rfl
theorem optAppend_assoc (xs ys zs : List α) :
    optAppend (optAppend (some xs) (some ys)) (some zs) =
    optAppend (some xs) (optAppend (some ys) (some zs)) := by
  simp [List.append_assoc]
theorem list_reverse_involutive (xs : List α) :
    Option.map List.reverse (Option.map List.reverse (some xs)) = some xs := by
  simp [List.reverse_reverse]
theorem listMap_append (f : α → β) (xs ys : List α) :
    Option.map (List.map f) (optAppend (some xs) (some ys)) =
    optAppend (Option.map (List.map f) (some xs)) (Option.map (List.map f) (some ys)) := by
  simp [optAppend, List.map_append]

-- ============================================================================
-- 5. SETS
-- ============================================================================

def optInjective (f : α → α) : Prop := ∀ a b, f a = f b → a = b
def optSurjective (f : α → α) : Prop := ∀ b, ∃ a, f a = b
def optBijective (f : α → α) : Prop := optInjective f ∧ optSurjective f
theorem bijective_comp (f g : α → α)
    (hf : optBijective f) (hg : optBijective g) :
    optBijective (f ∘ g) := by
  constructor
  · intro a b h; exact hg.1 _ _ (hf.1 _ _ h)
  · intro c; obtain ⟨b, hb⟩ := hf.2 c; obtain ⟨a, ha⟩ := hg.2 b
    exact ⟨a, by simp [Function.comp, ha, hb]⟩

-- ============================================================================
-- 6. EXTENDED NUMBER TYPES
-- ============================================================================

def optIsTop (topP : α → Prop) : Option α → Prop := liftPred topP
def optIsBot (botP : α → Prop) : Option α → Prop := liftPred botP

-- ============================================================================
-- 7. MULTISETS (bags — unordered collections with multiplicity)
-- ============================================================================

def optMsetUnion : Option (List α) → Option (List α) → Option (List α) := liftBin₂ (· ++ ·)
@[simp] theorem optMsetUnion_none_left (b : Option (List α)) :
    optMsetUnion none b = none := by cases b <;> rfl
@[simp] theorem optMsetUnion_none_right (a : Option (List α)) :
    optMsetUnion a none = none := by cases a <;> rfl
theorem optMsetUnion_comm [DecidableEq α] (xs ys : List α) :
    (optMsetUnion (some xs) (some ys)).map List.length =
    (optMsetUnion (some ys) (some xs)).map List.length := by
  simp [optMsetUnion, List.length_append, Nat.add_comm]
def optMsetCard : Option (List α) → Option Nat :=
  Option.map List.length
@[simp] theorem optMsetCard_none : optMsetCard (none : Option (List α)) = none := rfl
theorem optMsetCard_union (xs ys : List α) :
    optMsetCard (optMsetUnion (some xs) (some ys)) =
    some (xs.length + ys.length) := by
  simp [optMsetCard, optMsetUnion, List.length_append]

-- ============================================================================
-- 8. FINSETS (finite sets as filtered lists on Option)
-- ============================================================================

def optFinsetMem [DecidableEq α] (a : α) : Option (List α) → Prop :=
  liftPred (a ∈ ·)
def optFinsetInter [DecidableEq α] : Option (List α) → Option (List α) → Option (List α) :=
  liftBin₂ (fun xs ys => xs.filter (· ∈ ys))
@[simp] theorem optFinsetInter_none_left [DecidableEq α] (b : Option (List α)) :
    optFinsetInter none b = none := by cases b <;> rfl
@[simp] theorem optFinsetInter_none_right [DecidableEq α] (a : Option (List α)) :
    optFinsetInter a none = none := by cases a <;> rfl
def optFinsetFilter (p : α → Bool) : Option (List α) → Option (List α) :=
  Option.map (List.filter p)
@[simp] theorem optFinsetFilter_none (p : α → Bool) :
    optFinsetFilter p (none : Option (List α)) = none := rfl

-- ============================================================================
-- 9. MATRICES (general n×m on Option)
-- ============================================================================

def optMatrix (n m : Nat) (α : Type u) := Option (Fin n → Fin m → α)
def optMatEntry {n m : Nat} (M : optMatrix n m α) (i : Fin n) (j : Fin m) : Option α :=
  M.map (fun f => f i j)
@[simp] theorem optMatEntry_none {n m : Nat} (i : Fin n) (j : Fin m) :
    optMatEntry (none : optMatrix n m α) i j = none := rfl
@[simp] theorem optMatEntry_some {n m : Nat} (f : Fin n → Fin m → α) (i : Fin n) (j : Fin m) :
    optMatEntry (some f : optMatrix n m α) i j = some (f i j) := rfl
def optMatAdd [Add α] {n m : Nat} : optMatrix n m α → optMatrix n m α → optMatrix n m α :=
  liftBin₂ (fun f g i j => f i j + g i j)
@[simp] theorem optMatAdd_none_left [Add α] {n m : Nat} (B : optMatrix n m α) :
    optMatAdd none B = none := by cases B <;> rfl

-- ============================================================================
-- 10. COMPLEX NUMBERS (abstract pair structure on Option)
-- ============================================================================

structure OptComplex (α : Type u) where
  re : Option α
  im : Option α
def optComplexAdd [Add α] (z w : OptComplex α) : OptComplex α :=
  ⟨liftBin₂ (· + ·) z.re w.re, liftBin₂ (· + ·) z.im w.im⟩
theorem optComplexAdd_re_none [Add α] (w : OptComplex α) :
    (optComplexAdd ⟨none, none⟩ w).re = none := by
  simp [optComplexAdd]
def optComplexConj : OptComplex α → OptComplex α
  | ⟨re, im⟩ => ⟨re, im.map id⟩
theorem optComplexConj_re (z : OptComplex α) :
    (optComplexConj z).re = z.re := by simp [optComplexConj]

-- ============================================================================
-- 11. FIN TYPES (finite bounded naturals on Option)
-- ============================================================================

def optFinVal {n : Nat} : Option (Fin n) → Option Nat := Option.map Fin.val
@[simp] theorem optFinVal_none {n : Nat} :
    optFinVal (none : Option (Fin n)) = none := rfl
@[simp] theorem optFinVal_some {n : Nat} (i : Fin n) :
    optFinVal (some i) = some i.val := rfl
theorem optFinVal_bound {n : Nat} (i : Fin n) :
    ∃ k, optFinVal (some i) = some k ∧ k < n :=
  ⟨i.val, rfl, i.isLt⟩

-- ============================================================================
-- 12. FINSUPP (finitely supported functions on Option)
-- ============================================================================

structure OptFinsupp (α β : Type u) where
  toFun : α → Option β
  support : List α
def optFinsuppApply {β : Type u} (f : OptFinsupp α β) (a : α) : Option β := f.toFun a
def optFinsuppMapRange {β γ : Type u} (g : β → γ) (f : OptFinsupp α β) : OptFinsupp α γ :=
  ⟨fun a => (f.toFun a).map g, f.support⟩
theorem optFinsuppMapRange_apply {β γ : Type u} (g : β → γ) (f : OptFinsupp α β) (a : α) :
    (optFinsuppMapRange g f).toFun a = (f.toFun a).map g := rfl

-- ============================================================================
-- 13. SIGMA TYPES (dependent pairs on Option)
-- ============================================================================

def optSigma {β : α → Type u} : Option (Sigma β) → Option α := Option.map Sigma.fst
@[simp] theorem optSigma_none {β : α → Type u} :
    optSigma (none : Option (Sigma β)) = none := rfl
@[simp] theorem optSigma_some {β : α → Type u} (p : Sigma β) :
    optSigma (some p) = some p.fst := rfl
def optSigmaSnd {β : α → Type u} (p : Sigma β) : Option (β p.fst) := some p.snd

theorem optMap_comp {γ : Type u} (f : α → β) (g : β → γ) (x : Option α) :
    Option.map g (Option.map f x) = Option.map (g ∘ f) x := by cases x <;> rfl
theorem optMap_id (x : Option α) : Option.map id x = x := by cases x <;> rfl
@[simp] theorem optBind_none (f : α → Option β) : none.bind f = none := rfl
theorem optBind_some (x : Option α) : x.bind some = x := by cases x <;> rfl
theorem liftBin₂_assoc {f : α → α → α}
    (hassoc : ∀ a b c : α, f (f a b) c = f a (f b c))
    (a b c : Option α) :
    liftBin₂ f (liftBin₂ f a b) c = liftBin₂ f a (liftBin₂ f b c) := by
  cases a <;> cases b <;> cases c <;> simp [liftBin₂, hassoc]

-- ============================================================================
-- STUBS — auto-generated by: python3 scripts/origin.py stub Data
-- Upgrade key declarations from stubs to real structures/theorems.
-- ============================================================================

-- Analysis/Filter.lean
-- COLLISION: principal' already in Order.lean — rename needed
-- COLLISION: top' already in Order.lean — rename needed
-- COLLISION: bot' already in Order.lean — rename needed
-- COLLISION: map' already in SetTheory.lean — rename needed
-- COLLISION: comap' already in Order.lean — rename needed
-- COLLISION: sup' already in SetTheory.lean — rename needed
-- COLLISION: inf' already in Order.lean — rename needed
-- COLLISION: cofinite' already in Order.lean — rename needed
-- COLLISION: bind' already in Order.lean — rename needed
-- COLLISION: iSup' already in Order.lean — rename needed
-- COLLISION: prod' already in SetTheory.lean — rename needed
-- COLLISION: le_iff' already in SetTheory.lean — rename needed
-- COLLISION: tendsto_iff' already in Order.lean — rename needed

-- Analysis/Topology.lean
-- COLLISION: mem_nhds' already in Topology.lean — rename needed
-- COLLISION: isOpen_iff' already in SetTheory.lean — rename needed
-- COLLISION: isClosed_iff' already in Topology.lean — rename needed
-- COLLISION: mem_interior_iff' already in Topology.lean — rename needed
-- COLLISION: isOpen' already in Analysis.lean — rename needed
-- COLLISION: ext' already in SetTheory.lean — rename needed

-- Array/Defs.lean

-- Array/ExtractLemmas.lean

-- BitVec.lean

-- Bool/AllAny.lean

-- Bool/Basic.lean

-- Bool/Count.lean

-- Bool/Set.lean
-- COLLISION: range_eq' already in Order.lean — rename needed
-- COLLISION: compl_singleton' already in Topology.lean — rename needed

-- Bracket.lean

-- Bundle.lean
-- COLLISION: for' already in SetTheory.lean — rename needed
-- COLLISION: TotalSpace' already in Topology.lean — rename needed
-- COLLISION: mk_inj' already in CategoryTheory.lean — rename needed
-- COLLISION: lift' already in SetTheory.lean — rename needed

-- Complex/Abs.lean

-- Complex/Basic.lean

-- Complex/BigOperators.lean

-- Complex/Cardinality.lean

-- Complex/Determinant.lean

-- Complex/Exponential.lean

-- Complex/ExponentialBounds.lean

-- Complex/FiniteDimensional.lean

-- Complex/Module.lean

-- Complex/Order.lean

-- Complex/Orientation.lean
-- COLLISION: orientation' already in LinearAlgebra2.lean — rename needed

-- Countable/Basic.lean

-- Countable/Defs.lean

-- DFinsupp/BigOperators.lean
-- COLLISION: evalAddMonoidHom' already in Algebra.lean — rename needed
-- COLLISION: prod_single_index' already in Algebra.lean — rename needed
-- COLLISION: prod_neg_index' already in Algebra.lean — rename needed
-- COLLISION: prod_comm' already in Order.lean — rename needed
-- COLLISION: sum_apply' already in Algebra.lean — rename needed

-- DFinsupp/Defs.lean

-- DFinsupp/Ext.lean
-- COLLISION: addHom_ext' already in Algebra.lean — rename needed

-- DFinsupp/FiniteInfinite.lean

-- DFinsupp/Interval.lean
-- COLLISION: pi' already in Order.lean — rename needed
-- COLLISION: mem_pi' already in Order.lean — rename needed
-- COLLISION: card_pi' already in SetTheory.lean — rename needed
-- COLLISION: card_Icc' already in Order.lean — rename needed
-- COLLISION: card_Ico' already in Order.lean — rename needed
-- COLLISION: card_Ioc' already in Order.lean — rename needed
-- COLLISION: card_Ioo' already in Order.lean — rename needed
-- COLLISION: card_uIcc' already in Order.lean — rename needed
-- COLLISION: card_Iic' already in Order.lean — rename needed
-- COLLISION: card_Iio' already in Order.lean — rename needed

-- DFinsupp/Lex.lean

-- DFinsupp/Module.lean

-- DFinsupp/Multiset.lean

-- DFinsupp/NeLocus.lean

-- DFinsupp/Notation.lean

-- DFinsupp/Order.lean
-- COLLISION: disjoint_iff' already in Order.lean — rename needed

-- DFinsupp/Sigma.lean
-- COLLISION: sigmaCurryEquiv' already in Algebra.lean — rename needed

-- DFinsupp/Submonoid.lean

-- DFinsupp/WellFounded.lean
-- COLLISION: acc' already in Order.lean — rename needed
-- COLLISION: wellFoundedLT' already in Order.lean — rename needed

-- DList/Instances.lean

-- ENNReal/Basic.lean
-- COLLISION: coe_sSup' already in Order.lean — rename needed
-- COLLISION: coe_sInf' already in Order.lean — rename needed

-- ENNReal/Inv.lean

-- ENNReal/Lemmas.lean
-- COLLISION: coe_finset_sup' already in Topology.lean — rename needed

-- ENNReal/Operations.lean

-- ENNReal/Real.lean
-- COLLISION: iInf_sum' already in Order.lean — rename needed

-- ENat/Basic.lean

-- ENat/BigOperators.lean

-- ENat/Defs.lean

-- ENat/Lattice.lean

-- Erased.lean
-- COLLISION: equiv' already in SetTheory.lean — rename needed
-- COLLISION: choice' already in SetTheory.lean — rename needed
-- COLLISION: join' already in Order.lean — rename needed

-- FP/Basic.lean
-- COLLISION: ofRat' already in Algebra.lean — rename needed
-- COLLISION: add' already in Order.lean — rename needed
-- COLLISION: sub' already in SetTheory.lean — rename needed
-- COLLISION: mul' already in Order.lean — rename needed
-- COLLISION: div' already in Order.lean — rename needed

-- Fin/Basic.lean

-- Fin/Fin2.lean

-- Fin/FlagRange.lean

-- Fin/Parity.lean

-- Fin/Tuple/Basic.lean

-- Fin/Tuple/BubbleSortInduction.lean

-- Fin/Tuple/Curry.lean
-- COLLISION: uncurry' already in Order.lean — rename needed

-- Fin/Tuple/Finset.lean

-- Fin/Tuple/NatAntidiagonal.lean

-- Fin/Tuple/Reflection.lean
-- COLLISION: exists_iff' already in Order.lean — rename needed

-- Fin/Tuple/Sort.lean

-- Fin/Tuple/Take.lean

-- Fin/VecNotation.lean

-- FinEnum.lean
-- COLLISION: ofList' already in SetTheory.lean — rename needed
-- COLLISION: toList' already in Control.lean — rename needed
-- COLLISION: card_eq_zero' already in SetTheory.lean — rename needed
-- COLLISION: card_pos_iff' already in SetTheory.lean — rename needed
-- COLLISION: card_pos' already in SetTheory.lean — rename needed
-- COLLISION: card_ne_zero' already in SetTheory.lean — rename needed
-- COLLISION: card_eq_one' already in SetTheory.lean — rename needed
-- COLLISION: ofIsEmpty' already in SetTheory.lean — rename needed

-- FinEnum/Option.lean

-- Finite/Card.lean

-- Finite/Defs.lean

-- Finite/Prod.lean

-- Finite/Set.lean

-- Finite/Sum.lean
-- COLLISION: sum_left' already in Algebra.lean — rename needed
-- COLLISION: sum_right' already in Algebra.lean — rename needed

-- Finmap.lean

-- Finset/Attach.lean

-- Finset/Basic.lean

-- Finset/Card.lean
-- COLLISION: lt_wf' already in SetTheory.lean — rename needed

-- Finset/Dedup.lean

-- Finset/Defs.lean

-- Finset/Density.lean

-- Finset/Disjoint.lean

-- Finset/Empty.lean

-- Finset/Erase.lean

-- Finset/Filter.lean

-- Finset/Fin.lean

-- Finset/Finsupp.lean

-- Finset/Fold.lean

-- Finset/Functor.lean

-- Finset/Grade.lean
-- COLLISION: isAtom_singleton' already in Order.lean — rename needed

-- Finset/Image.lean

-- Finset/Insert.lean

-- Finset/Interval.lean

-- Finset/Lattice/Basic.lean

-- Finset/Lattice/Fold.lean

-- Finset/Lattice/Lemmas.lean

-- Finset/Max.lean

-- Finset/MulAntidiagonal.lean

-- Finset/NAry.lean

-- Finset/NatAntidiagonal.lean

-- Finset/NatDivisors.lean

-- Finset/NoncommProd.lean
-- COLLISION: pi_ext' already in LinearAlgebra2.lean — rename needed

-- Finset/Option.lean

-- Finset/Order.lean
-- COLLISION: exists_le' already in Order.lean — rename needed

-- Finset/PImage.lean

-- Finset/Pairwise.lean

-- Finset/Pi.lean

-- Finset/PiInduction.lean

-- Finset/Piecewise.lean
-- COLLISION: piecewise_mem_Icc' already in Order.lean — rename needed

-- Finset/Powerset.lean

-- Finset/Preimage.lean

-- Finset/Prod.lean

-- Finset/Range.lean

-- Finset/SDiff.lean

-- Finset/SMulAntidiagonal.lean

-- Finset/Sigma.lean

-- Finset/Slice.lean

-- Finset/Sort.lean

-- Finset/Sum.lean

-- Finset/Sups.lean

-- Finset/Sym.lean

-- Finset/SymmDiff.lean

-- Finset/Union.lean

-- Finset/Update.lean

-- Finsupp/AList.lean

-- Finsupp/Antidiagonal.lean

-- Finsupp/Basic.lean

-- Finsupp/BigOperators.lean

-- Finsupp/Defs.lean
-- COLLISION: support_sub' already in Algebra.lean — rename needed

-- Finsupp/Fin.lean

-- Finsupp/Fintype.lean

-- Finsupp/Indicator.lean

-- Finsupp/Interval.lean

-- Finsupp/Lex.lean

-- Finsupp/MonomialOrder.lean

-- Finsupp/Multiset.lean

-- Finsupp/NeLocus.lean

-- Finsupp/Notation.lean

-- Finsupp/Order.lean

-- Finsupp/PWO.lean
-- COLLISION: isPWO' already in Order.lean — rename needed

-- Finsupp/Pointwise.lean
-- COLLISION: support_mul' already in Algebra.lean — rename needed

-- Finsupp/ToDFinsupp.lean

-- Finsupp/Weight.lean

-- Finsupp/WellFounded.lean

-- Fintype/Basic.lean

-- Fintype/BigOperators.lean

-- Fintype/Card.lean

-- Fintype/CardEmbedding.lean

-- Fintype/Fin.lean

-- Fintype/Lattice.lean

-- Fintype/List.lean

-- Fintype/Option.lean

-- Fintype/Order.lean
-- COLLISION: exists_ge' already in Order.lean — rename needed

-- Fintype/Perm.lean

-- Fintype/Pi.lean

-- Fintype/Powerset.lean

-- Fintype/Prod.lean
-- COLLISION: card_prod' already in SetTheory.lean — rename needed

-- Fintype/Quotient.lean

-- Fintype/Shrink.lean

-- Fintype/Sigma.lean

-- Fintype/Sort.lean

-- Fintype/Sum.lean

-- FunLike/Basic.lean
-- COLLISION: congr' already in Order.lean — rename needed
-- COLLISION: congr_arg' already in Order.lean — rename needed

-- FunLike/Embedding.lean
-- COLLISION: comp_injective' already in RingTheory2.lean — rename needed

-- FunLike/Equiv.lean

-- FunLike/Fintype.lean
-- COLLISION: stating' already in SetTheory.lean — rename needed

-- Holor.lean

-- Ineq.lean

-- Int/AbsoluteValue.lean

-- Int/Associated.lean

-- Int/Bitwise.lean

-- Int/CardIntervalMod.lean

-- Int/Cast/Basic.lean

-- Int/Cast/Defs.lean

-- Int/Cast/Field.lean

-- Int/Cast/Lemmas.lean

-- Int/CharZero.lean

-- Int/ConditionallyCompleteOrder.lean
-- COLLISION: csSup_mem' already in Order.lean — rename needed
-- COLLISION: csInf_mem' already in Order.lean — rename needed

-- Int/Defs.lean

-- Int/DivMod.lean

-- Int/GCD.lean
-- COLLISION: xgcdAux' already in Algebra.lean — rename needed
-- COLLISION: xgcd_zero_left' already in Algebra.lean — rename needed
-- COLLISION: xgcdAux_rec' already in Algebra.lean — rename needed
-- COLLISION: xgcd' already in Algebra.lean — rename needed
-- COLLISION: gcdA' already in Algebra.lean — rename needed
-- COLLISION: gcdB' already in Algebra.lean — rename needed
-- COLLISION: xgcdAux_fst' already in Algebra.lean — rename needed
-- COLLISION: P' already in Algebra.lean — rename needed
-- COLLISION: xgcdAux_P' already in Algebra.lean — rename needed
-- COLLISION: dvd_gcd' already in RingTheory2.lean — rename needed
-- COLLISION: gcd_mul_lcm' already in Algebra.lean — rename needed
-- COLLISION: gcd_comm' already in Algebra.lean — rename needed
-- COLLISION: lcm_comm' already in Algebra.lean — rename needed
-- COLLISION: lcm_assoc' already in Algebra.lean — rename needed
-- COLLISION: lcm_zero_left' already in Algebra.lean — rename needed
-- COLLISION: lcm_zero_right' already in Algebra.lean — rename needed
-- COLLISION: lcm_one_left' already in Algebra.lean — rename needed
-- COLLISION: lcm_one_right' already in Algebra.lean — rename needed

-- Int/Interval.lean

-- Int/LeastGreatest.lean

-- Int/Lemmas.lean

-- Int/Log.lean

-- Int/ModEq.lean

-- Int/NatPrime.lean

-- Int/Order/Basic.lean
-- COLLISION: mul_nonneg_iff' already in Algebra.lean — rename needed

-- Int/Order/Lemmas.lean

-- Int/Order/Units.lean

-- Int/Range.lean
-- COLLISION: mem_range_iff' already in LinearAlgebra2.lean — rename needed

-- Int/Sqrt.lean

-- Int/Star.lean

-- Int/SuccPred.lean
-- COLLISION: succ_iterate' already in Algebra.lean — rename needed
-- COLLISION: sub_one_covBy' already in Algebra.lean — rename needed

-- List/AList.lean

-- List/Basic.lean

-- List/Chain.lean

-- List/ChainOfFn.lean

-- List/Count.lean

-- List/Cycle.lean

-- List/Dedup.lean

-- List/Defs.lean

-- List/Destutter.lean

-- List/DropRight.lean

-- List/Duplicate.lean

-- List/EditDistance/Bounds.lean

-- List/EditDistance/Defs.lean

-- List/EditDistance/Estimator.lean

-- List/Enum.lean

-- List/FinRange.lean

-- List/Flatten.lean
-- COLLISION: length_flatMap' already in Algebra.lean — rename needed
-- COLLISION: countP_flatMap' already in Algebra.lean — rename needed

-- List/Forall2.lean

-- List/GetD.lean

-- List/Indexes.lean

-- List/Infix.lean

-- List/InsertIdx.lean

-- List/Intervals.lean

-- List/Iterate.lean

-- List/Lattice.lean

-- List/Lemmas.lean

-- List/Lex.lean
-- COLLISION: lt_iff_lex_lt' already in Topology.lean — rename needed

-- List/MinMax.lean

-- List/NatAntidiagonal.lean
-- COLLISION: map_swap_antidiagonal' already in Algebra.lean — rename needed

-- List/Nodup.lean
-- COLLISION: toList_nodup' already in Order.lean — rename needed

-- List/NodupEquivFin.lean

-- List/OfFn.lean

-- List/Pairwise.lean

-- List/Palindrome.lean

-- List/Perm/Basic.lean

-- List/Perm/Lattice.lean

-- List/Perm/Subperm.lean

-- List/Permutation.lean

-- List/Pi.lean

-- List/Prime.lean

-- List/ProdSigma.lean
-- COLLISION: length_sigma' already in Algebra.lean — rename needed

-- List/Range.lean

-- List/ReduceOption.lean

-- List/Rotate.lean

-- List/Sections.lean

-- List/Sigma.lean

-- List/Sort.lean

-- List/SplitBy.lean

-- List/SplitLengths.lean

-- List/Sublists.lean

-- List/Sym.lean

-- List/TFAE.lean

-- List/ToFinsupp.lean

-- List/Zip.lean

-- MLList/BestFirst.lean

-- MLList/Dedup.lean

-- MLList/DepthFirst.lean

-- MLList/IO.lean

-- MLList/Split.lean

-- Matrix/Basic.lean

-- Matrix/Basis.lean

-- Matrix/Block.lean

-- Matrix/ColumnRowPartitioned.lean

-- Matrix/Composition.lean

-- Matrix/ConjTranspose.lean

-- Matrix/DMatrix.lean

-- Matrix/Defs.lean

-- Matrix/Diagonal.lean

-- Matrix/DoublyStochastic.lean

-- Matrix/DualNumber.lean
-- COLLISION: dualNumberEquiv' already in Algebra.lean — rename needed

-- Matrix/Hadamard.lean

-- Matrix/Invertible.lean

-- Matrix/Kronecker.lean

-- Matrix/Mul.lean

-- Matrix/Notation.lean

-- Matrix/PEquiv.lean

-- Matrix/Rank.lean

-- Matrix/Reflection.lean

-- Matrix/RowCol.lean

-- Matroid/Basic.lean

-- Matroid/Closure.lean

-- Matroid/Constructions.lean

-- Matroid/Dual.lean

-- Matroid/IndepAxioms.lean

-- Matroid/Map.lean

-- Matroid/Restrict.lean
-- COLLISION: augment' already in Algebra.lean — rename needed

-- Matroid/Sum.lean

-- Multiset/Antidiagonal.lean

-- Multiset/Basic.lean
-- COLLISION: subsingletonEquiv' already in LinearAlgebra2.lean — rename needed

-- Multiset/Bind.lean

-- Multiset/Dedup.lean

-- Multiset/FinsetOps.lean

-- Multiset/Fintype.lean

-- Multiset/Fold.lean

-- Multiset/Functor.lean
-- COLLISION: naturality' already in CategoryTheory.lean — rename needed

-- Multiset/Interval.lean

-- Multiset/Lattice.lean

-- Multiset/NatAntidiagonal.lean

-- Multiset/Nodup.lean

-- Multiset/Pi.lean

-- Multiset/Powerset.lean

-- Multiset/Range.lean
-- COLLISION: range_add_eq_union' already in Order.lean — rename needed

-- Multiset/Sections.lean

-- Multiset/Sort.lean

-- Multiset/Sum.lean

-- Multiset/Sym.lean

-- NNRat/BigOperators.lean
-- COLLISION: coe_multiset_prod' already in Algebra.lean — rename needed

-- NNRat/Defs.lean
-- COLLISION: mul_den_eq_num' already in Algebra.lean — rename needed
-- COLLISION: den_mul_eq_num' already in Algebra.lean — rename needed

-- NNRat/Floor.lean

-- NNRat/Lemmas.lean

-- NNReal/Basic.lean

-- NNReal/Defs.lean

-- Nat/BinaryRec.lean

-- Nat/BitIndices.lean

-- Nat/Bits.lean

-- Nat/Bitwise.lean

-- Nat/Cast/Basic.lean

-- Nat/Cast/Commute.lean

-- Nat/Cast/Defs.lean

-- Nat/Cast/Field.lean

-- Nat/Cast/Order/Basic.lean

-- Nat/Cast/Order/Field.lean

-- Nat/Cast/Order/Ring.lean

-- Nat/Cast/SetInterval.lean

-- Nat/ChineseRemainder.lean

-- Nat/Choose/Basic.lean
-- COLLISION: multichoose' already in RingTheory2.lean — rename needed
-- COLLISION: multichoose_zero_right' already in RingTheory2.lean — rename needed
-- COLLISION: multichoose_zero_succ' already in RingTheory2.lean — rename needed
-- COLLISION: multichoose_succ_succ' already in RingTheory2.lean — rename needed
-- COLLISION: multichoose_one' already in RingTheory2.lean — rename needed
-- COLLISION: multichoose_two' already in RingTheory2.lean — rename needed

-- Nat/Choose/Bounds.lean

-- Nat/Choose/Cast.lean

-- Nat/Choose/Central.lean

-- Nat/Choose/Dvd.lean

-- Nat/Choose/Factorization.lean

-- Nat/Choose/Lucas.lean

-- Nat/Choose/Mul.lean

-- Nat/Choose/Multinomial.lean

-- Nat/Choose/Sum.lean

-- Nat/Choose/Vandermonde.lean
-- COLLISION: add_choose_eq' already in RingTheory2.lean — rename needed

-- Nat/Count.lean

-- Nat/Defs.lean

-- Nat/Digits.lean

-- Nat/Dist.lean

-- Nat/EvenOddRec.lean

-- Nat/Factorial/Basic.lean

-- Nat/Factorial/BigOperators.lean

-- Nat/Factorial/Cast.lean

-- Nat/Factorial/DoubleFactorial.lean

-- Nat/Factorial/SuperFactorial.lean

-- Nat/Factorization/Basic.lean
-- COLLISION: asserting' already in CategoryTheory.lean — rename needed

-- Nat/Factorization/Defs.lean

-- Nat/Factorization/Induction.lean

-- Nat/Factorization/PrimePow.lean

-- Nat/Factorization/Root.lean

-- Nat/Factors.lean

-- Nat/Fib/Basic.lean

-- Nat/Fib/Zeckendorf.lean

-- Nat/Find.lean

-- Nat/GCD/Basic.lean

-- Nat/GCD/BigOperators.lean

-- Nat/Hyperoperation.lean

-- Nat/Lattice.lean

-- Nat/Log.lean

-- Nat/MaxPowDiv.lean

-- Nat/ModEq.lean

-- Nat/Multiplicity.lean

-- Nat/Nth.lean

-- Nat/Order/Lemmas.lean

-- Nat/PSub.lean

-- Nat/Pairing.lean

-- Nat/PartENat.lean

-- Nat/Periodic.lean

-- Nat/Prime/Basic.lean

-- Nat/Prime/Defs.lean
-- COLLISION: exists_prime_and_dvd' already in RingTheory2.lean — rename needed

-- Nat/Prime/Factorial.lean

-- Nat/Prime/Infinite.lean

-- Nat/Prime/Int.lean

-- Nat/Prime/Nth.lean

-- Nat/Prime/Pow.lean

-- Nat/PrimeFin.lean

-- Nat/Set.lean

-- Nat/Size.lean

-- Nat/Sqrt.lean

-- Nat/Squarefree.lean

-- Nat/SuccPred.lean

-- Nat/Totient.lean

-- Nat/Upto.lean

-- Num/Basic.lean

-- Num/Bitwise.lean

-- Num/Lemmas.lean

-- Num/Prime.lean

-- Opposite.lean

-- Option/Basic.lean

-- Option/Defs.lean

-- Option/NAry.lean
-- COLLISION: map₂_swap' already in Order.lean — rename needed
-- COLLISION: map_map₂' already in Order.lean — rename needed
-- COLLISION: map₂_map_left' already in Order.lean — rename needed
-- COLLISION: map₂_map_right' already in Order.lean — rename needed
-- COLLISION: map₂_assoc' already in Order.lean — rename needed
-- COLLISION: map₂_comm' already in Order.lean — rename needed
-- COLLISION: map₂_left_comm' already in Order.lean — rename needed
-- COLLISION: map₂_right_comm' already in Order.lean — rename needed
-- COLLISION: map_map₂_distrib' already in Order.lean — rename needed
-- COLLISION: map_map₂_distrib_left' already in Order.lean — rename needed
-- COLLISION: map_map₂_distrib_right' already in Order.lean — rename needed
-- COLLISION: map₂_map_left_comm' already in Order.lean — rename needed
-- COLLISION: map_map₂_right_comm' already in Order.lean — rename needed
-- COLLISION: map_map₂_antidistrib' already in Order.lean — rename needed
-- COLLISION: map_map₂_antidistrib_left' already in Order.lean — rename needed
-- COLLISION: map_map₂_antidistrib_right' already in Order.lean — rename needed
-- COLLISION: map₂_map_left_anticomm' already in Order.lean — rename needed
-- COLLISION: map_map₂_right_anticomm' already in Order.lean — rename needed
-- COLLISION: map₂_left_identity' already in Order.lean — rename needed
-- COLLISION: map₂_right_identity' already in Order.lean — rename needed

-- Ordering/Basic.lean

-- Ordering/Lemmas.lean

-- Ordmap/Ordnode.lean
-- COLLISION: disjoint' already in Order.lean — rename needed

-- Ordmap/Ordset.lean

-- PEquiv.lean

-- PFun.lean
-- COLLISION: toSubtype' already in CategoryTheory.lean — rename needed
-- COLLISION: id_comp' already in Order.lean — rename needed

-- PFunctor/Multivariate/Basic.lean

-- PFunctor/Multivariate/M.lean

-- PFunctor/Multivariate/W.lean

-- PFunctor/Univariate/Basic.lean

-- PFunctor/Univariate/M.lean

-- PNat/Basic.lean

-- PNat/Defs.lean

-- PNat/Equiv.lean

-- PNat/Factors.lean
-- COLLISION: prod_inf' already in Order.lean — rename needed
-- COLLISION: prod_sup' already in Order.lean — rename needed

-- PNat/Find.lean

-- PNat/Interval.lean
-- COLLISION: map_subtype_embedding_Icc' already in Order.lean — rename needed
-- COLLISION: map_subtype_embedding_Ico' already in Order.lean — rename needed
-- COLLISION: map_subtype_embedding_uIcc' already in Order.lean — rename needed

-- PNat/Notation.lean
-- COLLISION: val' already in Order.lean — rename needed

-- PNat/Prime.lean

-- PNat/Xgcd.lean

-- Part.lean

-- Pi/Interval.lean
-- COLLISION: card_Ici' already in Order.lean — rename needed
-- COLLISION: card_Ioi' already in Order.lean — rename needed

-- Prod/Basic.lean

-- Prod/Lex.lean
-- COLLISION: monotone_fst' already in Order.lean — rename needed

-- Prod/PProd.lean

-- Prod/TProd.lean

-- QPF/Multivariate/Basic.lean

-- QPF/Multivariate/Constructions/Cofix.lean

-- QPF/Multivariate/Constructions/Comp.lean

-- QPF/Multivariate/Constructions/Const.lean
-- COLLISION: Const' already in Control.lean — rename needed

-- QPF/Multivariate/Constructions/Fix.lean
-- COLLISION: ind' already in Order.lean — rename needed

-- QPF/Multivariate/Constructions/Prj.lean

-- QPF/Multivariate/Constructions/Quot.lean

-- QPF/Multivariate/Constructions/Sigma.lean
-- COLLISION: Pi' already in Topology.lean — rename needed

-- QPF/Univariate/Basic.lean

-- Quot.lean
-- COLLISION: inference' already in RingTheory2.lean — rename needed
-- COLLISION: ind₂' already in CategoryTheory.lean — rename needed
-- COLLISION: inductionOn₂' already in SetTheory.lean — rename needed
-- COLLISION: exact' already in Algebra.lean — rename needed
-- COLLISION: sound' already in SetTheory.lean — rename needed
-- COLLISION: quot_mk_eq_iff' already in CategoryTheory.lean — rename needed

-- Rat/BigOperators.lean
-- COLLISION: cast_list_sum' already in Algebra.lean — rename needed
-- COLLISION: cast_multiset_sum' already in Algebra.lean — rename needed
-- COLLISION: cast_sum' already in Algebra.lean — rename needed
-- COLLISION: cast_list_prod' already in Algebra.lean — rename needed
-- COLLISION: cast_multiset_prod' already in Algebra.lean — rename needed
-- COLLISION: cast_prod' already in Algebra.lean — rename needed

-- Rat/Cardinal.lean

-- Rat/Cast/CharZero.lean

-- Rat/Cast/Defs.lean

-- Rat/Cast/Lemmas.lean

-- Rat/Cast/Order.lean

-- Rat/Defs.lean

-- Rat/Floor.lean

-- Rat/Init.lean
-- COLLISION: cast' already in Order.lean — rename needed
-- COLLISION: num' already in RingTheory2.lean — rename needed
-- COLLISION: den' already in RingTheory2.lean — rename needed

-- Rat/Lemmas.lean

-- Rat/Sqrt.lean

-- Rat/Star.lean

-- Real/Archimedean.lean

-- Real/Basic.lean

-- Real/Cardinality.lean

-- Real/ConjExponents.lean

-- Real/ENatENNReal.lean

-- Real/EReal.lean

-- Real/GoldenRatio.lean

-- Real/Hyperreal.lean

-- Real/Irrational.lean

-- Real/IsNonarchimedean.lean
-- COLLISION: add_pow_le' already in Algebra.lean — rename needed

-- Real/Pi/Bounds.lean

-- Real/Pi/Irrational.lean

-- Real/Pi/Leibniz.lean
-- COLLISION: states' already in Analysis.lean — rename needed

-- Real/Pi/Wallis.lean

-- Real/Pointwise.lean

-- Real/Sign.lean

-- Real/Sqrt.lean

-- Rel.lean

-- SProd.lean

-- Semiquot.lean

-- Seq/Computation.lean

-- Seq/Parallel.lean

-- Seq/Seq.lean

-- Seq/WSeq.lean

-- Set/Accumulate.lean

-- Set/Basic.lean
-- COLLISION: subset_left_of_subset_union' already in Topology.lean — rename needed
-- COLLISION: subset_right_of_subset_union' already in Topology.lean — rename needed

-- Set/BoolIndicator.lean

-- Set/Card.lean

-- Set/Constructions.lean
-- COLLISION: mk₂' already in Order.lean — rename needed

-- Set/Countable.lean

-- Set/Defs.lean
-- COLLISION: compl' already in Order.lean — rename needed

-- Set/Enumerate.lean

-- Set/Equitable.lean

-- Set/Finite/Basic.lean

-- Set/Finite/Lattice.lean

-- Set/Finite/Lemmas.lean

-- Set/Finite/List.lean

-- Set/Finite/Monad.lean

-- Set/Finite/Range.lean

-- Set/Function.lean

-- Set/Functor.lean

-- Set/Image.lean

-- Set/Lattice.lean

-- Set/List.lean

-- Set/MemPartition.lean

-- Set/Monotone.lean

-- Set/MulAntidiagonal.lean

-- Set/NAry.lean

-- Set/Notation.lean

-- Set/Operations.lean

-- Set/Opposite.lean

-- Set/Pairwise/Basic.lean

-- Set/Pairwise/Lattice.lean

-- Set/Pointwise/Iterate.lean

-- Set/Pointwise/SMul.lean
-- COLLISION: neg_smul' already in Algebra.lean — rename needed

-- Set/Pointwise/Support.lean

-- Set/Prod.lean

-- Set/SMulAntidiagonal.lean

-- Set/Semiring.lean
-- COLLISION: up' already in RingTheory2.lean — rename needed

-- Set/Sigma.lean

-- Set/Subset.lean

-- Set/Subsingleton.lean

-- Set/Sups.lean

-- Set/SymmDiff.lean

-- Set/UnionLift.lean

-- SetLike/Basic.lean
-- COLLISION: not_le_iff_exists' already in LinearAlgebra2.lean — rename needed
-- COLLISION: exists_of_lt' already in LinearAlgebra2.lean — rename needed
-- COLLISION: lt_iff_le_and_exists' already in LinearAlgebra2.lean — rename needed

-- Setoid/Basic.lean
-- COLLISION: quotientKerEquivRange' already in RingTheory2.lean — rename needed
-- COLLISION: subsingleton_iff' already in Order.lean — rename needed

-- Setoid/Partition.lean

-- Sigma/Basic.lean

-- Sigma/Interval.lean

-- Sigma/Lex.lean

-- Sigma/Order.lean

-- Sign.lean

-- Stream/Defs.lean
-- COLLISION: apply' already in Order.lean — rename needed

-- Stream/Init.lean

-- String/Basic.lean

-- String/Defs.lean

-- String/Lemmas.lean

-- Subtype.lean

-- Sum/Basic.lean

-- Sum/Interval.lean

-- Sum/Order.lean

-- Sym/Basic.lean

-- Sym/Card.lean

-- Sym/Sym2.lean

-- Sym/Sym2/Order.lean

-- Tree/Basic.lean

-- Tree/Get.lean

-- Tree/RBMap.lean

-- TwoPointing.lean

-- TypeMax.lean

-- TypeVec.lean

-- UInt.lean

-- ULift.lean
-- COLLISION: map_surjective' already in RingTheory2.lean — rename needed

-- Vector/Basic.lean

-- Vector/Defs.lean

-- Vector/MapLemmas.lean

-- Vector/Mem.lean

-- Vector/Snoc.lean

-- Vector/Zip.lean

-- Vector3.lean

-- W/Basic.lean

-- W/Cardinal.lean

-- W/Constructions.lean

-- ZMod/Aut.lean

-- ZMod/Basic.lean

-- ZMod/Coprime.lean

-- ZMod/Defs.lean

-- ZMod/Factorial.lean

-- ZMod/IntUnitsPower.lean

-- ZMod/Quotient.lean

-- ZMod/Units.lean
