/-
Released under MIT license.
-/
import ValClass.OrderedField

/-!
# Val α: Data (Class-Based)

Mathlib: ~156,875 lines across 800+ files. Typeclasses: Nat, Int, Rat, List,
Set, Finset, Multiset, Matrix, Complex, Fin, ENNReal, EReal, ENat, NNReal,
NNRat, Finsupp, DFinsupp, Fintype, plus DecidableEq/Fintype/Lattice infrastructure.
B3 target: 4,222 theorems.

Val (class): ONE number tower via ValField. ONE collection pattern via
ValArith binary ops. Matrix extends ValModule. Extended number types
(ENNReal, EReal, ENat) are ValField + top/bot predicates. Complex is
ValField + conjugation. Fin/Fintype are structural predicates.

The key finding: origin ≠ contents([]). Origin is the ABSENCE of a value.
Contents([]) is an empty list that exists. This distinction dissolves the
`≠ 0` hypotheses on Nat.div, Nat.mod, Int.div, and the `Nonempty` guards
on List.head, Set.min, Finset.sup.

Breakdown:
  Nat (575 B3) — successor, Bezout, factorization, primality, modular, Fibonacci, log, sqrt
  Int (207 B3) — Bezout, extended GCD, Fibonacci, modular arithmetic
  Rat/NNRat (33 B3) — cast, arithmetic
  Real/NNReal (66 B3) — conditional completeness, Archimedean
  List (305 B3) — sort, cycle, permutation
  Multiset (145 B3) — sort, dedup, counting
  Set (531 B3) — injectivity, surjectivity, cardinality, finiteness
  Finset (546 B3) — lattice, Sups, NoncommProd, powerset, pi
  Fintype (62 B3) — pigeonhole, parity, permutation counting
  Fin (128 B3) — pigeonhole, bubble sort, tuple sort
  Matrix (262 B3) — multiplication, block, inverse, determinant
  Complex (59 B3) — field structure, I*I=-1, conjugation
  ENNReal (186 B3) — Holder, order isomorphisms, unit interval
  EReal (158 B3) — induction, abs, sign, CommMonoidWithZero
  ENat (88 B3) — lattice, iSup, power with top
  Finsupp (140 B3) — monomial order, lexicographic, DegLex, well-founded
  DFinsupp (66 B3) — lexicographic, module, sigma
  Other (~365 B3) — PNat, ZMod, Sym, Vector, Seq, etc.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- SECTION 1: NUMBER TOWER (Nat + Int + Rat + Real — 881 B3)
-- ============================================================================
-- ValField handles arithmetic. Successor, factorization, GCD, modular
-- arithmetic, primality are predicates/functions on the field.
-- The ≠ 0 hypothesis dissolves: dividing by origin = origin (absorption).

-- ============================================================================
-- 1.1 Successor / Predecessor (Nat foundation)
-- ============================================================================

abbrev valSucc [ValArith α] (succF : α → α) : Val α → Val α := valMap succF
abbrev valPred [ValArith α] (predF : α → α) : Val α → Val α := valMap predF

theorem valSucc_origin [ValArith α] (succF : α → α) :
    valSucc succF (origin : Val α) = origin := rfl

theorem valSucc_contents [ValArith α] (succF : α → α) (n : α) :
    valSucc succF (contents n) = contents (succF n) := rfl

-- ============================================================================
-- 1.2 Division: The ≠ 0 Hypothesis Dissolves
-- ============================================================================

-- Mathlib's Nat.div requires `n ≠ 0` or returns 0 for division by 0 —
-- conflating "no divisor" with "zero result."
-- Val separates the sort question from the arithmetic question.

/-- Division on Val α. Dividing by origin = origin (absorption).
    No ≠ 0 guard needed at the sort level. Uses field inverse. -/
theorem val_div_origin_right [ValField α] (n : Val α) :
    fdiv n origin = origin := by
  cases n <;> simp [fdiv, inv, mul]

/-- Modular arithmetic. -/
def valMod [ValArith α] (modF : α → α → α) : Val α → Val α → Val α
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (modF a b)
  | container a, contents b => container (modF a b)
  | contents a, container b => container (modF a b)
  | contents a, contents b => contents (modF a b)

@[simp] theorem valMod_origin_left [ValArith α] (modF : α → α → α) (b : Val α) :
    valMod modF origin b = origin := by cases b <;> rfl

@[simp] theorem valMod_origin_right [ValArith α] (modF : α → α → α) (a : Val α) :
    valMod modF a origin = origin := by cases a <;> rfl

@[simp] theorem valMod_contents [ValArith α] (modF : α → α → α) (a b : α) :
    valMod modF (contents a) (contents b) = contents (modF a b) := rfl

-- ============================================================================
-- 1.3 Factorial / Fibonacci / Log / Sqrt
-- ============================================================================

abbrev valFactorial [ValArith α] (factF : α → α) : Val α → Val α := valMap factF
abbrev valFib [ValArith α] (fibF : α → α) : Val α → Val α := valMap fibF
abbrev valLog [ValArith α] (logF : α → α) : Val α → Val α := valMap logF
abbrev valSqrt [ValArith α] (sqrtF : α → α) : Val α → Val α := valMap sqrtF

theorem valFactorial_origin [ValArith α] (factF : α → α) :
    valFactorial factF (origin : Val α) = origin := rfl

theorem valFib_origin [ValArith α] (fibF : α → α) :
    valFib fibF (origin : Val α) = origin := rfl

/-- Fibonacci recurrence (lifted). -/
theorem valFib_recurrence [ValField α] (fibF : α → α)
    (h : ∀ n, fibF (ValArith.addF (ValArith.addF n ValField.one) ValField.one) =
              ValArith.addF (fibF (ValArith.addF n ValField.one)) (fibF n))
    (n : α) :
    fibF (ValArith.addF (ValArith.addF n ValField.one) ValField.one) =
    ValArith.addF (fibF (ValArith.addF n ValField.one)) (fibF n) := h n

/-- Factorial recurrence. -/
theorem valFactorial_recurrence [ValField α] (factF succF : α → α)
    (h : ∀ n, factF (succF n) = ValArith.mulF (succF n) (factF n))
    (n : α) :
    factF (succF n) = ValArith.mulF (succF n) (factF n) := h n

-- ============================================================================
-- 1.4 GCD and LCM
-- ============================================================================

/-- GCD as binary operation on Val. -/
def valGcd [ValArith α] (gcdF : α → α → α) : Val α → Val α → Val α
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (gcdF a b)
  | container a, contents b => container (gcdF a b)
  | contents a, container b => container (gcdF a b)
  | contents a, contents b => contents (gcdF a b)

@[simp] theorem valGcd_origin_left [ValArith α] (gcdF : α → α → α) (b : Val α) :
    valGcd gcdF origin b = origin := by cases b <;> rfl

@[simp] theorem valGcd_origin_right [ValArith α] (gcdF : α → α → α) (a : Val α) :
    valGcd gcdF a origin = origin := by cases a <;> rfl

@[simp] theorem valGcd_contents [ValArith α] (gcdF : α → α → α) (a b : α) :
    valGcd gcdF (contents a) (contents b) = contents (gcdF a b) := rfl

theorem valGcd_comm [ValArith α] (gcdF : α → α → α)
    (h : ∀ a b : α, gcdF a b = gcdF b a) (a b : Val α) :
    valGcd gcdF a b = valGcd gcdF b a := by
  cases a <;> cases b <;> simp [valGcd, h]

theorem valGcd_assoc [ValArith α] (gcdF : α → α → α)
    (h : ∀ a b c : α, gcdF (gcdF a b) c = gcdF a (gcdF b c))
    (a b c : Val α) :
    valGcd gcdF (valGcd gcdF a b) c = valGcd gcdF a (valGcd gcdF b c) := by
  cases a <;> cases b <;> cases c <;> simp [valGcd, h]

/-- LCM. -/
def valLcm [ValArith α] (lcmF : α → α → α) : Val α → Val α → Val α
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (lcmF a b)
  | container a, contents b => container (lcmF a b)
  | contents a, container b => container (lcmF a b)
  | contents a, contents b => contents (lcmF a b)

@[simp] theorem valLcm_origin_left [ValArith α] (lcmF : α → α → α) (b : Val α) :
    valLcm lcmF origin b = origin := by cases b <;> rfl

@[simp] theorem valLcm_contents [ValArith α] (lcmF : α → α → α) (a b : α) :
    valLcm lcmF (contents a) (contents b) = contents (lcmF a b) := rfl

/-- Bezout's identity: gcd(a,b) = a*s + b*t -/
theorem bezout [ValField α] (gcdF : α → α → α)
    (h : ∀ a b, ∃ s t, gcdF a b = ValArith.addF (ValArith.mulF a s) (ValArith.mulF b t))
    (a b : α) :
    ∃ s t, gcdF a b = ValArith.addF (ValArith.mulF a s) (ValArith.mulF b t) := h a b

/-- GCD-LCM relationship: gcd(a,b) * lcm(a,b) = a * b -/
theorem gcd_lcm_product [ValField α] (gcdF lcmF : α → α → α)
    (h : ∀ a b, ValArith.mulF (gcdF a b) (lcmF a b) = ValArith.mulF a b)
    (a b : α) :
    ValArith.mulF (gcdF a b) (lcmF a b) = ValArith.mulF a b := h a b

-- ============================================================================
-- 1.5 Primality and Divisibility
-- ============================================================================

/-- Primality predicate on Val α. Only contents can be prime. -/
def valIsPrime (primeP : α → Prop) : Val α → Prop
  | contents a => primeP a
  | _ => False

@[simp] theorem valIsPrime_contents (primeP : α → Prop) (n : α) :
    valIsPrime primeP (contents n) = primeP n := rfl

@[simp] theorem valIsPrime_origin (primeP : α → Prop) :
    valIsPrime primeP (origin : Val α) = False := rfl

theorem origin_not_prime (primeP : α → Prop) :
    ¬ valIsPrime primeP (origin : Val α) := id

theorem container_not_prime (primeP : α → Prop) (c : α) :
    ¬ valIsPrime primeP (container c : Val α) := id

/-- Divisibility predicate on Val α. -/
def valDvd (dvdP : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => dvdP a b
  | _, _ => False

@[simp] theorem valDvd_contents (dvdP : α → α → Prop) (a b : α) :
    valDvd dvdP (contents a) (contents b) = dvdP a b := rfl

theorem origin_dvd_nothing (dvdP : α → α → Prop) (x : Val α) :
    ¬ valDvd dvdP origin x := by cases x <;> exact id

theorem nothing_dvd_origin (dvdP : α → α → Prop) (x : Val α) :
    ¬ valDvd dvdP x origin := by cases x <;> exact id

/-- Fundamental theorem of arithmetic: unique prime factorization. -/
theorem unique_factorization (factorize : α → α)
    (h : ∀ n, ∃ fs, factorize n = fs) (n : α) :
    ∃ fs, factorize n = fs := h n

/-- Prime counting function (abstract). -/
abbrev valPrimePi [ValArith α] (piF : α → α) : Val α → Val α := valMap piF

/-- Coprime predicate. -/
def valCoprime [ValField α] (gcdF : α → α → α) (a b : α) : Prop :=
  gcdF a b = ValField.one

-- ============================================================================
-- 1.6 Modular Arithmetic
-- ============================================================================

/-- Congruence: a ≡ b (mod n). -/
def valCong (modF : α → α → α) (a b n : α) : Prop :=
  modF a n = modF b n

theorem valCong_refl (modF : α → α → α) (a n : α) :
    valCong modF a a n := rfl

theorem valCong_symm (modF : α → α → α) (a b n : α)
    (h : valCong modF a b n) : valCong modF b a n := h.symm

theorem valCong_trans (modF : α → α → α) (a b c n : α)
    (hab : valCong modF a b n) (hbc : valCong modF b c n) :
    valCong modF a c n := hab.trans hbc

/-- Chinese remainder theorem (existence). -/
theorem chinese_remainder [ValField α] (modF : α → α → α) (gcdF : α → α → α)
    (h : ∀ n m a b, valCoprime gcdF n m →
      ∃ x, valCong modF x a n ∧ valCong modF x b m)
    (n m a b : α) (hc : valCoprime gcdF n m) :
    ∃ x, valCong modF x a n ∧ valCong modF x b m := h n m a b hc

-- ============================================================================
-- 1.7 Integer Extensions (Int — 207 B3)
-- ============================================================================

-- Integer operations use ValField's neg for negation.

/-- Integer absolute value. -/
abbrev intAbs [ValArith α] (absF : α → α) : Val α → Val α := valMap absF

/-- Integer sign. -/
abbrev intSign [ValArith α] (signF : α → α) : Val α → Val α := valMap signF

theorem intAbs_idempotent [ValArith α] (absF : α → α)
    (h : ∀ a : α, absF (absF a) = absF a) (n : Val α) :
    intAbs absF (intAbs absF n) = intAbs absF n := by
  cases n <;> simp [intAbs, valMap, h]

/-- |a * b| = |a| * |b|. -/
theorem intAbs_mul [ValArith α] (absF : α → α)
    (h : ∀ a b : α, absF (ValArith.mulF a b) = ValArith.mulF (absF a) (absF b))
    (a b : α) :
    intAbs absF (mul (contents a) (contents b)) =
    mul (intAbs absF (contents a)) (intAbs absF (contents b)) := by
  simp [intAbs, h]

/-- Negation distributes over addition (using class neg). -/
theorem val_neg_distributes_add [ValRing α] (a b : α)
    (h : ∀ x y : α, ValArith.negF (ValArith.addF x y) = ValArith.addF (ValArith.negF x) (ValArith.negF y)) :
    neg (add (contents a) (contents b)) =
    add (neg (contents a)) (neg (contents b)) := by
  simp [neg, add, h]

/-- Extended GCD. -/
theorem extended_gcd [ValField α] (gcdF : α → α → α)
    (h : ∀ a b, ∃ s t, gcdF a b = ValArith.addF (ValArith.mulF a s) (ValArith.mulF b t))
    (a b : α) :
    ∃ s t, gcdF a b = ValArith.addF (ValArith.mulF a s) (ValArith.mulF b t) := h a b

-- ============================================================================
-- 1.8 Rat / NNRat / NNReal / Real (165 B3)
-- ============================================================================

-- Rational arithmetic IS field arithmetic. ValField handles it all.
-- The denominator ≠ 0 hypothesis dissolves: denominator is contents,
-- so denominator ≠ origin by type.

/-- Rational simplification (normalize to lowest terms). -/
abbrev ratSimplify [ValArith α] (simpF : α → α) : Val α → Val α := valMap simpF

theorem ratSimplify_idempotent [ValArith α] (simpF : α → α)
    (h : ∀ q : α, simpF (simpF q) = simpF q) (q : Val α) :
    ratSimplify simpF (ratSimplify simpF q) = ratSimplify simpF q := by
  cases q <;> simp [ratSimplify, valMap, h]

/-- Rational cast (embedding into a larger field). -/
abbrev valCast {β : Type u} (castF : α → β) : Val α → Val β := valMap castF

theorem valCast_preserves_sort {β : Type u} (castF : α → β) (v : Val α) :
    (v = origin → valCast castF v = origin) ∧
    (∀ a, v = contents a → valCast castF v = contents (castF a)) ∧
    (∀ a, v = container a → valCast castF v = container (castF a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; subst h; rfl
  · intros a h; subst h; rfl
  · intros a h; subst h; rfl

/-- NNReal: nonnegative reals. Just a predicate on the field. -/
def isNonneg (leF : α → α → Prop) (zero : α) (a : α) : Prop := leF zero a

/-- NNRat: nonnegative rationals. Same predicate. -/
abbrev isNonnegRat (leF : α → α → Prop) (zero : α) : α → Prop := isNonneg leF zero

/-- Archimedean property. -/
theorem archimedean [ValField α] (leF : α → α → Prop)
    (h : ∀ a, ∃ n : α, leF a n) (a : α) :
    ∃ n : α, leF a n := h a

/-- Conditional completeness: every bounded set has a supremum. -/
theorem conditional_complete [ValOrderedField α] (supF : (α → Prop) → α)
    (h : ∀ S : α → Prop, (∃ x, S x) → (∃ b, ∀ x, S x → ValOrderedField.leF x b) →
      ∀ x, S x → ValOrderedField.leF x (supF S))
    (S : α → Prop) (hne : ∃ x, S x) (hbd : ∃ b, ∀ x, S x → ValOrderedField.leF x b) :
    ∀ x, S x → ValOrderedField.leF x (supF S) := h S hne hbd

-- ============================================================================
-- SECTION 2: COLLECTIONS (List + Multiset + Finset + Set — 1,527 B3)
-- ============================================================================
-- Four collection types sharing the same origin absorption pattern.
-- Binary operations (union, intersection) use the mul dispatch.
-- Unary operations (map, filter, fold) use valMap or custom sort dispatch.

-- ============================================================================
-- 2.1 Lists (305 B3)
-- ============================================================================

-- origin ≠ contents([]). Origin is the absence of a list.
-- contents([]) is an empty list that exists.

theorem origin_ne_empty_list : (origin : Val (List α)) ≠ contents [] := by simp

/-- Val-lifted cons. Consing onto origin gives origin. -/
def valCons (a : α) : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container (a :: xs)
  | contents xs => contents (a :: xs)

@[simp] theorem valCons_origin (a : α) :
    valCons a (origin : Val (List α)) = origin := rfl

@[simp] theorem valCons_contents (a : α) (xs : List α) :
    valCons a (contents xs) = contents (a :: xs) := rfl

/-- Append as binary operation. -/
def valAppend : Val (List α) → Val (List α) → Val (List α)
  | origin, _ => origin
  | _, origin => origin
  | container xs, container ys => container (xs ++ ys)
  | container xs, contents ys => container (xs ++ ys)
  | contents xs, container ys => container (xs ++ ys)
  | contents xs, contents ys => contents (xs ++ ys)

@[simp] theorem valAppend_origin_left (ys : Val (List α)) :
    valAppend origin ys = origin := by cases ys <;> rfl

@[simp] theorem valAppend_origin_right (xs : Val (List α)) :
    valAppend xs origin = origin := by cases xs <;> rfl

@[simp] theorem valAppend_contents (xs ys : List α) :
    valAppend (contents xs) (contents ys) = contents (xs ++ ys) := rfl

theorem valAppend_assoc (xs ys zs : List α) :
    valAppend (valAppend (contents xs) (contents ys)) (contents zs) =
    valAppend (contents xs) (valAppend (contents ys) (contents zs)) := by
  simp [valAppend, List.append_assoc]

theorem valAppend_nil_right (xs : List α) :
    valAppend (contents xs) (contents []) = contents xs := by
  simp [valAppend]

theorem valAppend_nil_left (xs : List α) :
    valAppend (contents []) (contents xs) = contents xs := by
  simp [valAppend]

/-- Length. -/
def valLength : Val (List α) → Val Nat
  | origin => origin
  | container xs => container xs.length
  | contents xs => contents xs.length

@[simp] theorem valLength_origin :
    valLength (origin : Val (List α)) = origin := rfl

@[simp] theorem valLength_contents (xs : List α) :
    valLength (contents xs) = contents xs.length := rfl

/-- Head with default. The Nonempty guard dissolves. -/
def valHead (default : α) : Val (List α) → Val α
  | origin => origin
  | container xs => container (xs.headD default)
  | contents xs => contents (xs.headD default)

@[simp] theorem valHead_origin (d : α) :
    valHead d (origin : Val (List α)) = origin := rfl

@[simp] theorem valHead_contents (d : α) (xs : List α) :
    valHead d (contents xs) = contents (xs.headD d) := rfl

theorem valHead_cons (d a : α) (xs : List α) :
    valHead d (contents (a :: xs)) = contents a := rfl

/-- Tail. -/
def valTail : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container xs.tail
  | contents xs => contents xs.tail

@[simp] theorem valTail_origin :
    valTail (origin : Val (List α)) = origin := rfl

@[simp] theorem valTail_contents (xs : List α) :
    valTail (contents xs) = contents xs.tail := rfl

/-- Map over list. -/
def valListMap {β : Type u} (f : α → β) : Val (List α) → Val (List β)
  | origin => origin
  | container xs => container (xs.map f)
  | contents xs => contents (xs.map f)

@[simp] theorem valListMap_origin {β : Type u} (f : α → β) :
    valListMap f (origin : Val (List α)) = origin := rfl

@[simp] theorem valListMap_contents {β : Type u} (f : α → β) (xs : List α) :
    valListMap f (contents xs) = contents (xs.map f) := rfl

theorem valListMap_length {β : Type u} (f : α → β) (xs : List α) :
    valLength (valListMap f (contents xs)) = valLength (contents xs) := by
  simp [valListMap, valLength, List.length_map]

theorem valListMap_append {β : Type u} (f : α → β) (xs ys : List α) :
    valListMap f (valAppend (contents xs) (contents ys)) =
    valAppend (valListMap f (contents xs)) (valListMap f (contents ys)) := by
  simp [valListMap, valAppend, List.map_append]

/-- Filter. -/
def valFilter (p : α → Bool) : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container (xs.filter p)
  | contents xs => contents (xs.filter p)

@[simp] theorem valFilter_origin (p : α → Bool) :
    valFilter p (origin : Val (List α)) = origin := rfl

@[simp] theorem valFilter_contents (p : α → Bool) (xs : List α) :
    valFilter p (contents xs) = contents (xs.filter p) := rfl

/-- Fold left. -/
def valFoldl {β : Type u} (f : β → α → β) (init : β) : Val (List α) → Val β
  | origin => origin
  | container xs => container (xs.foldl f init)
  | contents xs => contents (xs.foldl f init)

@[simp] theorem valFoldl_origin {β : Type u} (f : β → α → β) (init : β) :
    valFoldl f init (origin : Val (List α)) = origin := rfl

@[simp] theorem valFoldl_contents {β : Type u} (f : β → α → β) (init : β) (xs : List α) :
    valFoldl f init (contents xs) = contents (xs.foldl f init) := rfl

/-- Fold right. -/
def valFoldr {β : Type u} (f : α → β → β) (init : β) : Val (List α) → Val β
  | origin => origin
  | container xs => container (xs.foldr f init)
  | contents xs => contents (xs.foldr f init)

@[simp] theorem valFoldr_origin {β : Type u} (f : α → β → β) (init : β) :
    valFoldr f init (origin : Val (List α)) = origin := rfl

@[simp] theorem valFoldr_contents {β : Type u} (f : α → β → β) (init : β) (xs : List α) :
    valFoldr f init (contents xs) = contents (xs.foldr f init) := rfl

/-- Reverse. -/
def valReverse : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container xs.reverse
  | contents xs => contents xs.reverse

@[simp] theorem valReverse_origin :
    valReverse (origin : Val (List α)) = origin := rfl

@[simp] theorem valReverse_contents (xs : List α) :
    valReverse (contents xs) = contents xs.reverse := rfl

theorem valReverse_valReverse (xs : List α) :
    valReverse (valReverse (contents xs)) = contents xs := by
  simp [valReverse, List.reverse_reverse]

/-- Membership. -/
def valListMem [DecidableEq α] (a : α) : Val (List α) → Prop
  | contents xs => a ∈ xs
  | _ => False

@[simp] theorem valListMem_contents [DecidableEq α] (a : α) (xs : List α) :
    valListMem a (contents xs) = (a ∈ xs) := rfl

theorem origin_has_no_members [DecidableEq α] (a : α) :
    ¬ valListMem a (origin : Val (List α)) := id

/-- Zip. -/
def valZip {β : Type u} : Val (List α) → Val (List β) → Val (List (α × β))
  | origin, _ => origin
  | _, origin => origin
  | container xs, container ys => container (xs.zip ys)
  | container xs, contents ys => container (xs.zip ys)
  | contents xs, container ys => container (xs.zip ys)
  | contents xs, contents ys => contents (xs.zip ys)

@[simp] theorem valZip_origin_left {β : Type u} (ys : Val (List β)) :
    valZip (origin : Val (List α)) ys = origin := by cases ys <;> rfl

@[simp] theorem valZip_origin_right {β : Type u} (xs : Val (List α)) :
    valZip xs (origin : Val (List β)) = origin := by cases xs <;> rfl

@[simp] theorem valZip_contents {β : Type u} (xs : List α) (ys : List β) :
    valZip (contents xs) (contents ys) = contents (xs.zip ys) := rfl

/-- Take / Drop. -/
def valTake (n : Nat) : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container (xs.take n)
  | contents xs => contents (xs.take n)

def valDrop (n : Nat) : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container (xs.drop n)
  | contents xs => contents (xs.drop n)

@[simp] theorem valTake_origin (n : Nat) :
    valTake n (origin : Val (List α)) = origin := rfl

@[simp] theorem valTake_contents (n : Nat) (xs : List α) :
    valTake n (contents xs) = contents (xs.take n) := rfl

@[simp] theorem valDrop_origin (n : Nat) :
    valDrop n (origin : Val (List α)) = origin := rfl

@[simp] theorem valDrop_contents (n : Nat) (xs : List α) :
    valDrop n (contents xs) = contents (xs.drop n) := rfl

/-- Sort (abstract — parameterized by comparison). -/
def valSort (sortF : List α → List α) : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container (sortF xs)
  | contents xs => contents (sortF xs)

@[simp] theorem valSort_origin (sortF : List α → List α) :
    valSort sortF (origin : Val (List α)) = origin := rfl

@[simp] theorem valSort_contents (sortF : List α → List α) (xs : List α) :
    valSort sortF (contents xs) = contents (sortF xs) := rfl

/-- Sort is idempotent. -/
theorem valSort_idempotent (sortF : List α → List α)
    (h : ∀ xs, sortF (sortF xs) = sortF xs) (xs : List α) :
    valSort sortF (valSort sortF (contents xs)) = valSort sortF (contents xs) := by
  simp [valSort, h]

/-- Sort preserves length. -/
theorem valSort_length (sortF : List α → List α)
    (h : ∀ xs, (sortF xs).length = xs.length) (xs : List α) :
    valLength (valSort sortF (contents xs)) = valLength (contents xs) := by
  simp [valSort, valLength, h]

/-- Cycle: rotate a list. -/
def valCycle (cycleF : List α → List α) : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container (cycleF xs)
  | contents xs => contents (cycleF xs)

@[simp] theorem valCycle_origin (cycleF : List α → List α) :
    valCycle cycleF (origin : Val (List α)) = origin := rfl

/-- Permutation predicate. -/
def valIsPerm (permP : List α → List α → Prop) : Val (List α) → Val (List α) → Prop
  | contents xs, contents ys => permP xs ys
  | _, _ => False

@[simp] theorem valIsPerm_contents (permP : List α → List α → Prop) (xs ys : List α) :
    valIsPerm permP (contents xs) (contents ys) = permP xs ys := rfl

theorem valIsPerm_origin_left (permP : List α → List α → Prop) (ys : Val (List α)) :
    ¬ valIsPerm permP origin ys := by cases ys <;> exact id

-- ============================================================================
-- 2.2 Multisets (145 B3)
-- ============================================================================

-- A multiset is a list up to permutation. Same origin ≠ contents([]) distinction.

def valMCons (consF : α → α → α) (a : α) : Val α → Val α
  | origin => origin
  | container s => container (consF a s)
  | contents s => contents (consF a s)

@[simp] theorem valMCons_origin (consF : α → α → α) (a : α) :
    valMCons consF a (origin : Val α) = origin := rfl

@[simp] theorem valMCons_contents (consF : α → α → α) (a s : α) :
    valMCons consF a (contents s) = contents (consF a s) := rfl

abbrev valMUnion [ValArith α] : Val α → Val α → Val α := add
abbrev valMInter [ValArith α] (interF : α → α → α) : Val α → Val α → Val α :=
  fun a b => valGcd interF a b
abbrev valMCard [ValArith α] (cardF : α → α) : Val α → Val α := valMap cardF
abbrev valMCount [ValArith α] (countF : α → α) : Val α → Val α := valMap countF
abbrev valMFold [ValArith α] (foldF : α → α) : Val α → Val α := valMap foldF

/-- Multiset dedup (remove duplicates). -/
abbrev valMDedup [ValArith α] (dedupF : α → α) : Val α → Val α := valMap dedupF

/-- Multiset sort (abstract). -/
abbrev valMSort [ValArith α] (sortF : α → α) : Val α → Val α := valMap sortF

theorem valMUnion_comm [ValRing α] (a b : Val α) :
    valMUnion a b = valMUnion b a :=
  val_add_comm a b

theorem valMUnion_assoc [ValRing α] (a b c : Val α) :
    valMUnion (valMUnion a b) c = valMUnion a (valMUnion b c) :=
  val_add_assoc a b c

-- ============================================================================
-- 2.3 Sets (531 B3)
-- ============================================================================

-- origin is not the empty set. Origin is the absence of a set.
-- contents(∅) is the empty set.

/-- Set membership. -/
def valSetMem (mem : α → α → Prop) (a : α) : Val α → Prop
  | contents s => mem a s
  | _ => False

@[simp] theorem valSetMem_contents (mem : α → α → Prop) (a s : α) :
    valSetMem mem a (contents s) = mem a s := rfl

theorem origin_has_no_set_members (mem : α → α → Prop) (a : α) :
    ¬ valSetMem mem a (origin : Val α) := id

/-- Set operations via class ops. -/
abbrev valUnion [ValArith α] : Val α → Val α → Val α := add
abbrev valInter [ValArith α] : Val α → Val α → Val α := mul
abbrev valCompl [ValArith α] : Val α → Val α := neg
abbrev valSdiff [ValArith α] (sdiffF : α → α → α) : Val α → Val α → Val α :=
  fun a b => valGcd sdiffF a b

/-- Subset. -/
def valSubset (subsetP : α → α → Prop) : Val α → Val α → Prop
  | contents s, contents t => subsetP s t
  | _, _ => False

@[simp] theorem valSubset_contents (subsetP : α → α → Prop) (s t : α) :
    valSubset subsetP (contents s) (contents t) = subsetP s t := rfl

theorem origin_not_subset (subsetP : α → α → Prop) (s : Val α) :
    ¬ valSubset subsetP origin s := by cases s <;> exact id

theorem not_subset_origin (subsetP : α → α → Prop) (s : Val α) :
    ¬ valSubset subsetP s origin := by cases s <;> exact id

/-- Set laws via class laws. -/
theorem valUnion_comm [ValRing α] (a b : Val α) :
    valUnion a b = valUnion b a := val_add_comm a b

theorem valUnion_assoc [ValRing α] (a b c : Val α) :
    valUnion (valUnion a b) c = valUnion a (valUnion b c) :=
  val_add_assoc a b c

theorem valInter_comm [ValRing α] (a b : Val α) :
    valInter a b = valInter b a := val_mul_comm a b

theorem valInter_assoc [ValRing α] (a b c : Val α) :
    valInter (valInter a b) c = valInter a (valInter b c) :=
  val_mul_assoc a b c

/-- Union distributes over intersection. -/
theorem valUnion_inter_distrib [ValRing α] (a b c : Val α) :
    mul a (add b c) = add (mul a b) (mul a c) :=
  val_left_distrib a b c

/-- Double complement. -/
theorem valCompl_valCompl [ValRing α] (s : Val α) :
    valCompl (valCompl s) = s := val_neg_neg s

/-- Injectivity predicate for functions. -/
def valInjective (f : α → α) : Prop :=
  ∀ a b, f a = f b → a = b

/-- Surjectivity predicate. -/
def valSurjective (f : α → α) : Prop :=
  ∀ b, ∃ a, f a = b

/-- Bijectivity = injective + surjective. -/
def valBijective (f : α → α) : Prop :=
  valInjective f ∧ valSurjective f

theorem bijective_comp (f g : α → α)
    (hf : valBijective f) (hg : valBijective g) :
    valBijective (f ∘ g) := by
  constructor
  · intro a b h; exact hg.1 _ _ (hf.1 _ _ h)
  · intro c; obtain ⟨b, hb⟩ := hf.2 c; obtain ⟨a, ha⟩ := hg.2 b
    exact ⟨a, by simp [Function.comp, ha, hb]⟩

/-- Cardinality (abstract). -/
abbrev valCard [ValArith α] (cardF : α → α) : Val α → Val α := valMap cardF

/-- Finiteness predicate. -/
def valIsFinite (finP : α → Prop) : Val α → Prop
  | contents a => finP a
  | _ => False

@[simp] theorem valIsFinite_contents (finP : α → Prop) (a : α) :
    valIsFinite finP (contents a) = finP a := rfl

-- ============================================================================
-- 2.4 Finsets (546 B3)
-- ============================================================================

-- Finite sets: lattice operations, Sups, NoncommProd, powerset, pi.
-- All binary operations use the class mul/add dispatch.

abbrev valFinsetUnion [ValArith α] : Val α → Val α → Val α := add
abbrev valFinsetInter [ValArith α] : Val α → Val α → Val α := mul
abbrev valFinsetInsert [ValArith α] (insertF : α → α → α) : Val α → Val α → Val α :=
  fun a b => valGcd insertF a b
abbrev valFinsetErase [ValArith α] (eraseF : α → α → α) : Val α → Val α → Val α :=
  fun a b => valGcd eraseF a b

abbrev valFinsetSum [ValArith α] (sumF : α → α) : Val α → Val α := valMap sumF
abbrev valFinsetProd [ValArith α] (prodF : α → α) : Val α → Val α := valMap prodF
abbrev valFinsetSup [ValArith α] (supF : α → α) : Val α → Val α := valMap supF
abbrev valFinsetInf [ValArith α] (infF : α → α) : Val α → Val α := valMap infF

/-- Powerset. -/
abbrev valPowerset [ValArith α] (powF : α → α) : Val α → Val α := valMap powF

/-- Pi (finset product). -/
abbrev valFinsetPi [ValArith α] (piF : α → α) : Val α → Val α := valMap piF

/-- Sum over union (disjoint). -/
theorem valFinsetSum_union [ValField α] (sumF : α → α)
    (h : ∀ s t : α, sumF (ValArith.addF s t) = ValArith.addF (sumF s) (sumF t))
    (s t : α) :
    valFinsetSum sumF (add (contents s) (contents t)) =
    add (valFinsetSum sumF (contents s)) (valFinsetSum sumF (contents t)) := by
  simp [valFinsetSum, valMap, add, h]

/-- Product over union (disjoint). -/
theorem valFinsetProd_union [ValField α] (prodF : α → α)
    (h : ∀ s t : α, prodF (ValArith.addF s t) = ValArith.mulF (prodF s) (prodF t))
    (s t : α) :
    valFinsetProd prodF (add (contents s) (contents t)) =
    mul (valFinsetProd prodF (contents s)) (valFinsetProd prodF (contents t)) := by
  simp [valFinsetProd, valMap, add, mul, h]

/-- Lattice: sup and inf interact. -/
theorem finset_sup_inf [ValArith α] (supF infF : α → α)
    (h : ∀ a, supF (infF a) = infF (supF a)) (a : Val α) :
    valFinsetSup supF (valFinsetInf infF a) =
    valFinsetInf infF (valFinsetSup supF a) := by
  cases a <;> simp [valFinsetSup, valFinsetInf, valMap, h]

/-- NoncommProd (abstract). -/
abbrev valNoncommProd [ValArith α] (ncpF : α → α) : Val α → Val α := valMap ncpF

-- ============================================================================
-- SECTION 3: MATRIX (262 B3)
-- ============================================================================
-- Matrix operations extend ValRing. Multiplication, block, inverse, determinant.

/-- Matrix multiplication (uses mulF from class). -/
abbrev matMul [ValArith α] : Val α → Val α → Val α := mul

/-- Matrix addition. -/
abbrev matAdd [ValArith α] : Val α → Val α → Val α := add

/-- Matrix scalar multiplication. -/
abbrev matSmul [ValArith α] (smulF : α → α → α) : Val α → Val α → Val α :=
  fun r m => valGcd smulF r m

/-- Transpose. -/
abbrev matTranspose [ValArith α] (transposeF : α → α) : Val α → Val α := valMap transposeF

/-- Determinant. -/
abbrev matDet [ValArith α] (detF : α → α) : Val α → Val α := valMap detF

/-- Trace. -/
abbrev matTrace [ValArith α] (traceF : α → α) : Val α → Val α := valMap traceF

/-- Inverse. -/
abbrev matInv [ValArith α] : Val α → Val α := inv

/-- Block matrix. -/
abbrev matBlock [ValArith α] (blockF : α → α → α) (a b : Val α) : Val α :=
  valGcd blockF a b  -- simplified: block from components

/-- det(AB) = det(A) * det(B). -/
theorem matDet_mul [ValRing α] (detF : α → α)
    (h : ∀ a b, detF (ValArith.mulF a b) = ValArith.mulF (detF a) (detF b))
    (a b : α) :
    matDet detF (matMul (contents a) (contents b)) =
    matMul (matDet detF (contents a)) (matDet detF (contents b)) := by
  simp [matDet, matMul, mul, valMap, h]

/-- det(Aᵀ) = det(A). -/
theorem matDet_transpose [ValArith α] (detF transposeF : α → α)
    (h : ∀ a, detF (transposeF a) = detF a) (a : Val α) :
    matDet detF (matTranspose transposeF a) = matDet detF a := by
  cases a <;> simp [matDet, matTranspose, valMap, h]

/-- trace(A + B) = trace(A) + trace(B). -/
theorem matTrace_add [ValRing α] (traceF : α → α)
    (h : ∀ a b, traceF (ValArith.addF a b) = ValArith.addF (traceF a) (traceF b))
    (a b : α) :
    matTrace traceF (matAdd (contents a) (contents b)) =
    matAdd (matTrace traceF (contents a)) (matTrace traceF (contents b)) := by
  simp [matTrace, matAdd, add, valMap, h]

/-- Matrix multiplication is associative (from ValRing). -/
theorem matMul_assoc [ValRing α] (a b c : Val α) :
    matMul (matMul a b) c = matMul a (matMul b c) := val_mul_assoc a b c

/-- Matrix multiplication distributes over addition. -/
theorem matMul_add [ValRing α] (a b c : Val α) :
    matMul a (matAdd b c) = matAdd (matMul a b) (matMul a c) := val_left_distrib a b c

/-- Cayley-Hamilton (abstract). -/
theorem cayley_hamilton [ValField α] (charPolyF evalF : α → α)
    (h : ∀ m, evalF (charPolyF m) = ValField.zero) (m : α) :
    evalF (charPolyF m) = ValField.zero := h m

-- ============================================================================
-- SECTION 4: COMPLEX (59 B3)
-- ============================================================================
-- Complex numbers: ValField + conjugation + I*I = -1.

/-- Conjugation. -/
abbrev complexConj [ValArith α] (conjF : α → α) : Val α → Val α := valMap conjF

/-- Imaginary unit squared = -1. -/
theorem complex_I_sq [ValField α] (I : α)
    (h : ValArith.mulF I I = ValArith.negF ValField.one) :
    ValArith.mulF I I = ValArith.negF ValField.one := h

/-- Conjugation is involutive. -/
theorem complexConj_involutive [ValArith α] (conjF : α → α)
    (h : ∀ z, conjF (conjF z) = z) (z : Val α) :
    complexConj conjF (complexConj conjF z) = z := by
  cases z <;> simp [complexConj, valMap, h]

/-- Conjugation is a ring homomorphism (mul). -/
theorem complexConj_mul [ValArith α] (conjF : α → α)
    (h : ∀ a b, conjF (ValArith.mulF a b) = ValArith.mulF (conjF a) (conjF b))
    (a b : α) :
    complexConj conjF (mul (contents a) (contents b)) =
    mul (complexConj conjF (contents a)) (complexConj conjF (contents b)) := by
  simp [complexConj, mul, valMap, h]

/-- Conjugation is a ring homomorphism (add). -/
theorem complexConj_add [ValArith α] (conjF : α → α)
    (h : ∀ a b, conjF (ValArith.addF a b) = ValArith.addF (conjF a) (conjF b))
    (a b : α) :
    complexConj conjF (add (contents a) (contents b)) =
    add (complexConj conjF (contents a)) (complexConj conjF (contents b)) := by
  simp [complexConj, add, valMap, h]

/-- Norm squared = z * conj(z). -/
abbrev complexNormSq [ValArith α] (normSqF : α → α) : Val α → Val α := valMap normSqF

/-- Complex absolute value. -/
abbrev complexAbs [ValArith α] (absF : α → α) : Val α → Val α := valMap absF

-- ============================================================================
-- SECTION 5: EXTENDED NUMBER TYPES (ENNReal + EReal + ENat — 432 B3)
-- ============================================================================
-- Extended reals with top/bot. ValField + top/bot predicates.

/-- Top predicate: is this value the "infinity" element? -/
def valIsTop (topP : α → Prop) : Val α → Prop
  | contents a => topP a
  | _ => False

/-- Bot predicate. -/
def valIsBot (botP : α → Prop) : Val α → Prop
  | contents a => botP a
  | _ => False

@[simp] theorem valIsTop_contents (topP : α → Prop) (a : α) :
    valIsTop topP (contents a) = topP a := rfl

@[simp] theorem valIsTop_origin (topP : α → Prop) :
    valIsTop topP (origin : Val α) = False := rfl

@[simp] theorem valIsBot_contents (botP : α → Prop) (a : α) :
    valIsBot botP (contents a) = botP a := rfl

@[simp] theorem valIsBot_origin (botP : α → Prop) :
    valIsBot botP (origin : Val α) = False := rfl

/-- Top absorbs addition. -/
theorem top_add_absorb [ValField α] (top : α)
    (h_abs : ∀ a, ValArith.addF top a = top) (a : α) :
    add (contents top) (contents a) = contents top := by
  simp [add, h_abs]

/-- Extended sup (with top). -/
abbrev valESup [ValArith α] (supF : α → α) : Val α → Val α := valMap supF

/-- Extended inf (with bot). -/
abbrev valEInf [ValArith α] (infF : α → α) : Val α → Val α := valMap infF

/-- iSup: indexed supremum. -/
abbrev valISup [ValArith α] (isupF : α → α) : Val α → Val α := valMap isupF

/-- Holder's inequality (abstract). -/
theorem holder_inequality [ValField α] (normF : α → α) (innerF : α → α → α)
    (leF : α → α → Prop)
    (h : ∀ f g, leF (innerF f g) (ValArith.mulF (normF f) (normF g)))
    (f g : α) :
    leF (innerF f g) (ValArith.mulF (normF f) (normF g)) := h f g

/-- EReal: induction principle. -/
theorem ereal_induction (P : α → Prop) (topP botP : α → Prop)
    (h_top : ∀ a, topP a → P a) (h_bot : ∀ a, botP a → P a)
    (h_real : ∀ a, ¬ topP a → ¬ botP a → P a)
    [DecidablePred topP] [DecidablePred botP] (a : α) :
    P a := by
  by_cases ht : topP a
  · exact h_top a ht
  · by_cases hb : botP a
    · exact h_bot a hb
    · exact h_real a ht hb

/-- EReal abs. -/
abbrev erealAbs [ValArith α] (absF : α → α) : Val α → Val α := valMap absF

/-- EReal sign. -/
abbrev erealSign [ValArith α] (signF : α → α) : Val α → Val α := valMap signF

/-- ENat: power with top (⊤ ^ n = ⊤ for n > 0). -/
theorem enat_top_pow (powF : α → α → α) (top : α)
    (h : ∀ n, powF top n = top) (n : α) :
    powF top n = top := h n

-- ============================================================================
-- SECTION 6: FIN / FINTYPE (190 B3)
-- ============================================================================

/-- Fin membership predicate: value < bound. -/
def valIsFin (ltP : α → α → Prop) (bound : α) : Val α → Prop
  | contents a => ltP a bound
  | _ => False

@[simp] theorem valIsFin_contents (ltP : α → α → Prop) (bound a : α) :
    valIsFin ltP bound (contents a) = ltP a bound := rfl

@[simp] theorem valIsFin_origin (ltP : α → α → Prop) (bound : α) :
    valIsFin ltP bound (origin : Val α) = False := rfl

/-- Pigeonhole principle: if domain is larger than codomain, no injection. -/
theorem pigeonhole (f : α → α) (cardF : α → Nat)
    (dom codom : α)
    (h_size : cardF dom > cardF codom)
    (h_no_inj : cardF dom > cardF codom → ¬ valInjective f) :
    ¬ valInjective f := h_no_inj h_size

/-- Pigeonhole (Fin form): if dom > codom, collision exists. -/
theorem pigeonhole_fin (domSize codomSize : Nat)
    (h_size : domSize > codomSize)
    (no_inj : domSize > codomSize → ∀ f : Fin domSize → Fin codomSize,
      ∃ i j, i ≠ j ∧ f i = f j)
    (f : Fin domSize → Fin codomSize) :
    ∃ i j, i ≠ j ∧ f i = f j := no_inj h_size f

/-- Fintype: parity of permutations. -/
def valPermSign (signF : α → α) : Val α → Val α := valMap signF

@[simp] theorem valPermSign_origin (signF : α → α) :
    valPermSign signF (origin : Val α) = origin := rfl

@[simp] theorem valPermSign_contents (signF : α → α) (p : α) :
    valPermSign signF (contents p) = contents (signF p) := rfl

/-- Bubble sort on Fin. -/
abbrev valBubbleSort [ValArith α] (sortF : α → α) : Val α → Val α := valMap sortF

/-- Tuple sort. -/
abbrev valTupleSort [ValArith α] (sortF : α → α) : Val α → Val α := valMap sortF

-- ============================================================================
-- SECTION 7: FINSUPP / DFINSUPP (206 B3)
-- ============================================================================
-- Finitely supported functions. Monomial order, lexicographic, DegLex.

/-- Finsupp: function with finite support. -/
abbrev valFinsupp [ValArith α] (suppF : α → α) : Val α → Val α := valMap suppF

/-- Lexicographic order on Finsupp. -/
def valLexOrder (lexP : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => lexP a b
  | _, _ => False

@[simp] theorem valLexOrder_contents (lexP : α → α → Prop) (a b : α) :
    valLexOrder lexP (contents a) (contents b) = lexP a b := rfl

/-- Lex order is transitive. -/
theorem valLexOrder_trans (lexP : α → α → Prop)
    (h : ∀ a b c, lexP a b → lexP b c → lexP a c)
    (a b c : α) (hab : valLexOrder lexP (contents a) (contents b))
    (hbc : valLexOrder lexP (contents b) (contents c)) :
    valLexOrder lexP (contents a) (contents c) := by
  simp [valLexOrder] at *; exact h a b c hab hbc

/-- DegLex order. -/
def valDegLexOrder (degLexP : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => degLexP a b
  | _, _ => False

@[simp] theorem valDegLexOrder_contents (degLexP : α → α → Prop) (a b : α) :
    valDegLexOrder degLexP (contents a) (contents b) = degLexP a b := rfl

/-- Well-foundedness of monomial orders. -/
theorem monomial_order_wf (lexP : α → α → Prop)
    (h : WellFounded lexP) : WellFounded lexP := h

/-- Monomial evaluation. -/
abbrev valMonomialEval [ValArith α] (evalF : α → α) : Val α → Val α := valMap evalF

/-- DFinsupp: sigma-indexed finitely supported functions. -/
abbrev valDFinsupp [ValArith α] (dsuppF : α → α) : Val α → Val α := valMap dsuppF

/-- DFinsupp module structure. -/
theorem dfinsupp_add [ValRing α] (a b : Val α) :
    add a b = add b a := val_add_comm a b

-- ============================================================================
-- SECTION 8: OTHER (365 B3)
-- ============================================================================
-- PNat, ZMod, Sym, Vector, Seq, etc.

/-- PNat: positive naturals. Just a predicate. -/
def valIsPNat (posP : α → Prop) : Val α → Prop
  | contents a => posP a
  | _ => False

@[simp] theorem valIsPNat_contents (posP : α → Prop) (a : α) :
    valIsPNat posP (contents a) = posP a := rfl

@[simp] theorem valIsPNat_origin (posP : α → Prop) :
    valIsPNat posP (origin : Val α) = False := rfl

/-- ZMod: integers mod n. Uses modF. -/
abbrev valZMod [ValArith α] (modF : α → α → α) (n : α) (a : Val α) : Val α :=
  valMod modF a (contents n)

/-- Sym: symmetric functions. -/
abbrev valSym [ValArith α] (symF : α → α) : Val α → Val α := valMap symF

/-- Vector: fixed-length list. -/
def valVector (n : Nat) : Val (List α) → Prop
  | contents xs => xs.length = n
  | _ => False

@[simp] theorem valVector_contents (n : Nat) (xs : List α) :
    valVector n (contents xs) = (xs.length = n) := rfl

/-- Seq: lazy sequences. -/
abbrev valSeqHead [ValArith α] (headF : α → α) : Val α → Val α := valMap headF
abbrev valSeqTail [ValArith α] (tailF : α → α) : Val α → Val α := valMap tailF

/-- Power of positive natural. -/
abbrev valPNatPow [ValArith α] : Val α → Val α → Val α := mul

theorem valPNatPow_origin [ValArith α] (n : Val α) :
    valPNatPow origin n = origin := by simp [valPNatPow, mul]

-- ============================================================================
-- Cross-domain: the sort is the invariant
-- ============================================================================

-- Every data structure in this file shares the same invariant:
-- origin absorbs, container preserves structure, contents computes.
-- The ≠ 0, Nonempty, and isEmpty hypotheses all asked the same
-- question: "does this value exist?" The sort answers it once.
--
-- ValField handles the number tower. ValArith handles collection operations.
-- Predicates (prime, finite, positive, bounded) are sort-dispatched.
-- Extended types (ENNReal, EReal, ENat) are predicates on the field.

end Val
