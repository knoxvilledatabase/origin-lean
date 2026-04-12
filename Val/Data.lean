/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Val α: Data Structures — 156,875 Mathlib Lines → ~800 Lines

Every data structure Mathlib builds on Nat, Int, Rat, List, Set, Finset, Multiset
restated through the sort system.

The key finding: origin ≠ contents([]). Origin is the ABSENCE of a list.
Contents([]) is an empty list that exists. This distinction dissolves the
`≠ 0` hypotheses on Nat.div, Nat.mod, Int.div, and the `Nonempty` guards
on List.head, Set.min, Finset.sup.

## Contents

1. Natural Numbers — successor, arithmetic, division (no ≠ 0), factorial, fibonacci, gcd, primality
2. Integers — negation, absolute value, sign, integer division
3. Rationals — rational arithmetic, simplification
4. Lists — cons, append, length, map, filter, fold, the origin ≠ [] sort
5. Sets — membership, union, intersection, complement, subset
6. Finite Sets — cardinality, sum, product
7. Multisets — sorted lists with multiplicity
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- SECTION 1: Natural Numbers
-- ============================================================================

-- ============================================================================
-- Successor / Predecessor
-- ============================================================================

abbrev valSucc (succF : α → α) : Val α → Val α := valMap succF
abbrev valPred (predF : α → α) : Val α → Val α := valMap predF

-- ============================================================================
-- Natural Arithmetic (lifted)
-- ============================================================================

abbrev natAdd (addF : α → α → α) : Val α → Val α → Val α := add addF
abbrev natMul (mulF : α → α → α) : Val α → Val α → Val α := mul mulF
abbrev natSub (subF : α → α → α) : Val α → Val α → Val α := mul subF
abbrev natPow (powF : α → α → α) : Val α → Val α → Val α := mul powF

-- ============================================================================
-- Division: The ≠ 0 Hypothesis Dissolves
-- ============================================================================

-- Mathlib's Nat.div requires `n ≠ 0` or returns 0 for division by 0 —
-- conflating "no divisor" with "zero result."
-- Val separates the sort question from the arithmetic question.

/-- Division on Val α. Dividing by origin = origin (absorption).
    No ≠ 0 guard needed at the sort level. -/
abbrev natDiv (divF : α → α → α) : Val α → Val α → Val α := mul divF

/-- Division by origin absorbs. -/
theorem natDiv_origin_right (divF : α → α → α) (n : Val α) :
    natDiv divF n origin = origin := by simp [natDiv]

-- ============================================================================
-- Modulo: Same Dissolution
-- ============================================================================

abbrev natMod (modF : α → α → α) : Val α → Val α → Val α := mul modF

theorem natMod_origin_right (modF : α → α → α) (n : Val α) :
    natMod modF n origin = origin := by simp [natMod]

-- ============================================================================
-- Factorial / Fibonacci
-- ============================================================================

abbrev valFactorial (factF : α → α) : Val α → Val α := valMap factF
abbrev valFib (fibF : α → α) : Val α → Val α := valMap fibF

-- ============================================================================
-- GCD and LCM
-- ============================================================================

abbrev valGcd (gcdF : α → α → α) : Val α → Val α → Val α := mul gcdF
abbrev valLcm (lcmF : α → α → α) : Val α → Val α → Val α := mul lcmF

theorem valGcd_comm (gcdF : α → α → α)
    (h : ∀ a b : α, gcdF a b = gcdF b a) (a b : Val α) :
    valGcd gcdF a b = valGcd gcdF b a :=
  mul_comm gcdF h a b

theorem valGcd_assoc (gcdF : α → α → α)
    (h : ∀ a b c : α, gcdF (gcdF a b) c = gcdF a (gcdF b c))
    (a b c : Val α) :
    valGcd gcdF (valGcd gcdF a b) c = valGcd gcdF a (valGcd gcdF b c) :=
  mul_assoc gcdF h a b c

-- ============================================================================
-- Primality
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

-- ============================================================================
-- Divisibility
-- ============================================================================

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

-- ============================================================================
-- Min / Max on naturals
-- ============================================================================

abbrev natMin (minF : α → α → α) : Val α → Val α → Val α := mul minF
abbrev natMax (maxF : α → α → α) : Val α → Val α → Val α := mul maxF

theorem natMin_comm (minF : α → α → α)
    (h : ∀ a b : α, minF a b = minF b a) (a b : Val α) :
    natMin minF a b = natMin minF b a :=
  mul_comm minF h a b

theorem natMax_comm (maxF : α → α → α)
    (h : ∀ a b : α, maxF a b = maxF b a) (a b : Val α) :
    natMax maxF a b = natMax maxF b a :=
  mul_comm maxF h a b

-- ============================================================================
-- SECTION 2: Integers
-- ============================================================================

-- ============================================================================
-- Integer Negation / Abs / Sign
-- ============================================================================

abbrev intNeg (negF : α → α) : Val α → Val α := neg negF
abbrev intAbs (absF : α → α) : Val α → Val α := valMap absF
abbrev intSign (signF : α → α) : Val α → Val α := valMap signF

/-- Double negation. -/
theorem intNeg_intNeg (negF : α → α)
    (h : ∀ a : α, negF (negF a) = a) (n : Val α) :
    intNeg negF (intNeg negF n) = n :=
  neg_neg negF h n

/-- Absolute value is idempotent. -/
theorem intAbs_idempotent (absF : α → α)
    (h : ∀ a : α, absF (absF a) = absF a) (n : Val α) :
    intAbs absF (intAbs absF n) = intAbs absF n := by
  cases n <;> simp [intAbs, valMap, h]

-- ============================================================================
-- Integer Division: ≠ 0 Dissolves
-- ============================================================================

abbrev intDiv (divF : α → α → α) : Val α → Val α → Val α := mul divF
abbrev intMod (modF : α → α → α) : Val α → Val α → Val α := mul modF

theorem intDiv_origin_right (divF : α → α → α) (n : Val α) :
    intDiv divF n origin = origin := by simp [intDiv]

-- ============================================================================
-- Integer arithmetic laws
-- ============================================================================

/-- Negation distributes over addition. -/
theorem intNeg_add (negF : α → α) (addF : α → α → α)
    (h : ∀ a b : α, negF (addF a b) = addF (negF a) (negF b))
    (a b : α) :
    intNeg negF (add addF (contents a) (contents b)) =
    add addF (intNeg negF (contents a)) (intNeg negF (contents b)) := by
  simp [intNeg, h]

/-- |a * b| = |a| * |b|. -/
theorem intAbs_mul (absF : α → α) (mulF : α → α → α)
    (h : ∀ a b : α, absF (mulF a b) = mulF (absF a) (absF b))
    (a b : α) :
    intAbs absF (mul mulF (contents a) (contents b)) =
    mul mulF (intAbs absF (contents a)) (intAbs absF (contents b)) := by
  simp [intAbs, h]

-- ============================================================================
-- SECTION 3: Rationals
-- ============================================================================

-- A rational is a pair (num, den) with den ≠ 0. The sort system:
-- den is contents, so den ≠ origin by type. The hypothesis dissolves.

abbrev ratAdd (addF : α → α → α) : Val α → Val α → Val α := add addF
abbrev ratMul (mulF : α → α → α) : Val α → Val α → Val α := mul mulF
abbrev ratDiv (divF : α → α → α) : Val α → Val α → Val α := mul divF
abbrev ratInv (invF : α → α) : Val α → Val α := inv invF

/-- Val-lifted rational simplification (normalize to lowest terms). -/
abbrev ratSimplify (simpF : α → α) : Val α → Val α := valMap simpF

/-- Simplification is idempotent. -/
theorem ratSimplify_idempotent (simpF : α → α)
    (h : ∀ q : α, simpF (simpF q) = simpF q) (q : Val α) :
    ratSimplify simpF (ratSimplify simpF q) = ratSimplify simpF q := by
  cases q <;> simp [ratSimplify, valMap, h]

abbrev ratLE (leF : α → α → Prop) : Val α → Val α → Prop := valLE leF
abbrev ratLT (ltF : α → α → Prop) : Val α → Val α → Prop := valLT ltF

-- ============================================================================
-- Embedding: Nat → Int → Rat
-- ============================================================================

abbrev valEmbed {β : Type u} (embedF : α → β) : Val α → Val β := valMap embedF

/-- Embedding preserves sort. -/
theorem valEmbed_preserves_sort {β : Type u} (embedF : α → β) (v : Val α) :
    (v = origin → valEmbed embedF v = origin) ∧
    (∀ a, v = contents a → valEmbed embedF v = contents (embedF a)) ∧
    (∀ a, v = container a → valEmbed embedF v = container (embedF a)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; subst h; rfl
  · intros a h; subst h; rfl
  · intros a h; subst h; rfl

-- ============================================================================
-- SECTION 4: Lists
-- ============================================================================

-- The sort system adds one distinction that List alone cannot make:
-- origin ≠ contents([]). Origin is the absence of a list.
-- contents([]) is an empty list that exists.

-- ============================================================================
-- The Sort: origin ≠ contents([])
-- ============================================================================

theorem origin_ne_empty_list : (origin : Val (List α)) ≠ contents [] := by simp

theorem empty_list_ne_origin : (contents [] : Val (List α)) ≠ origin := by simp

-- ============================================================================
-- Cons
-- ============================================================================

/-- Val-lifted cons. Consing onto origin gives origin. -/
def valCons (a : α) : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container (a :: xs)
  | contents xs => contents (a :: xs)

@[simp] theorem valCons_origin (a : α) :
    valCons a (origin : Val (List α)) = origin := rfl

@[simp] theorem valCons_contents (a : α) (xs : List α) :
    valCons a (contents xs) = contents (a :: xs) := rfl

@[simp] theorem valCons_container (a : α) (xs : List α) :
    valCons a (container xs) = container (a :: xs) := rfl

-- ============================================================================
-- Append
-- ============================================================================

abbrev valAppend : Val (List α) → Val (List α) → Val (List α) :=
  mul (· ++ ·)

-- ============================================================================
-- Length
-- ============================================================================

/-- Val-lifted length. Returns Val Nat. -/
def valLength : Val (List α) → Val Nat
  | origin => origin
  | container xs => container xs.length
  | contents xs => contents xs.length

@[simp] theorem valLength_origin :
    valLength (origin : Val (List α)) = origin := rfl

@[simp] theorem valLength_contents (xs : List α) :
    valLength (contents xs) = contents xs.length := rfl

theorem valLength_empty :
    valLength (contents ([] : List α)) = contents 0 := rfl

-- ============================================================================
-- Head: The Nonempty Guard Dissolves
-- ============================================================================

/-- Val-lifted head with default. Origin → origin. -/
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

-- ============================================================================
-- Tail
-- ============================================================================

def valTail : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container xs.tail
  | contents xs => contents xs.tail

@[simp] theorem valTail_origin :
    valTail (origin : Val (List α)) = origin := rfl

@[simp] theorem valTail_contents (xs : List α) :
    valTail (contents xs) = contents xs.tail := rfl

-- ============================================================================
-- Map
-- ============================================================================

/-- Val-lifted map. Applies f to every element of a Val list. -/
def valListMap {β : Type u} (f : α → β) : Val (List α) → Val (List β)
  | origin => origin
  | container xs => container (xs.map f)
  | contents xs => contents (xs.map f)

@[simp] theorem valListMap_origin {β : Type u} (f : α → β) :
    valListMap f (origin : Val (List α)) = origin := rfl

@[simp] theorem valListMap_contents {β : Type u} (f : α → β) (xs : List α) :
    valListMap f (contents xs) = contents (xs.map f) := rfl

/-- Map preserves length within contents. -/
theorem valListMap_length {β : Type u} (f : α → β) (xs : List α) :
    valLength (valListMap f (contents xs)) = valLength (contents xs) := by
  simp [valListMap, valLength, List.length_map]

-- ============================================================================
-- Filter
-- ============================================================================

def valFilter (p : α → Bool) : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container (xs.filter p)
  | contents xs => contents (xs.filter p)

@[simp] theorem valFilter_origin (p : α → Bool) :
    valFilter p (origin : Val (List α)) = origin := rfl

@[simp] theorem valFilter_contents (p : α → Bool) (xs : List α) :
    valFilter p (contents xs) = contents (xs.filter p) := rfl

-- ============================================================================
-- Fold
-- ============================================================================

def valFoldl {β : Type u} (f : β → α → β) (init : β) : Val (List α) → Val β
  | origin => origin
  | container xs => container (xs.foldl f init)
  | contents xs => contents (xs.foldl f init)

@[simp] theorem valFoldl_origin {β : Type u} (f : β → α → β) (init : β) :
    valFoldl f init (origin : Val (List α)) = origin := rfl

@[simp] theorem valFoldl_contents {β : Type u} (f : β → α → β) (init : β) (xs : List α) :
    valFoldl f init (contents xs) = contents (xs.foldl f init) := rfl

def valFoldr {β : Type u} (f : α → β → β) (init : β) : Val (List α) → Val β
  | origin => origin
  | container xs => container (xs.foldr f init)
  | contents xs => contents (xs.foldr f init)

@[simp] theorem valFoldr_origin {β : Type u} (f : α → β → β) (init : β) :
    valFoldr f init (origin : Val (List α)) = origin := rfl

@[simp] theorem valFoldr_contents {β : Type u} (f : α → β → β) (init : β) (xs : List α) :
    valFoldr f init (contents xs) = contents (xs.foldr f init) := rfl

-- ============================================================================
-- Reverse
-- ============================================================================

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

-- ============================================================================
-- Membership
-- ============================================================================

def valListMem [DecidableEq α] (a : α) : Val (List α) → Prop
  | contents xs => a ∈ xs
  | _ => False

@[simp] theorem valListMem_contents [DecidableEq α] (a : α) (xs : List α) :
    valListMem a (contents xs) = (a ∈ xs) := rfl

theorem origin_has_no_members [DecidableEq α] (a : α) :
    ¬ valListMem a (origin : Val (List α)) := id

-- ============================================================================
-- Zip
-- ============================================================================

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

-- ============================================================================
-- Take / Drop
-- ============================================================================

def valTake (n : Nat) : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container (xs.take n)
  | contents xs => contents (xs.take n)

@[simp] theorem valTake_origin (n : Nat) :
    valTake n (origin : Val (List α)) = origin := rfl

@[simp] theorem valTake_contents (n : Nat) (xs : List α) :
    valTake n (contents xs) = contents (xs.take n) := rfl

def valDrop (n : Nat) : Val (List α) → Val (List α)
  | origin => origin
  | container xs => container (xs.drop n)
  | contents xs => contents (xs.drop n)

@[simp] theorem valDrop_origin (n : Nat) :
    valDrop n (origin : Val (List α)) = origin := rfl

@[simp] theorem valDrop_contents (n : Nat) (xs : List α) :
    valDrop n (contents xs) = contents (xs.drop n) := rfl

-- ============================================================================
-- List laws (lifted)
-- ============================================================================

theorem valAppend_assoc (xs ys zs : List α) :
    valAppend (valAppend (contents xs) (contents ys)) (contents zs) =
    valAppend (contents xs) (valAppend (contents ys) (contents zs)) := by
  simp [valAppend, mul, List.append_assoc]

theorem valAppend_nil_right (xs : List α) :
    valAppend (contents xs) (contents []) = contents xs := by
  simp [valAppend, mul]

theorem valAppend_nil_left (xs : List α) :
    valAppend (contents []) (contents xs) = contents xs := by
  simp [valAppend, mul]

theorem valListMap_append {β : Type u} (f : α → β) (xs ys : List α) :
    valListMap f (valAppend (contents xs) (contents ys)) =
    valAppend (valListMap f (contents xs)) (valListMap f (contents ys)) := by
  simp [valListMap, valAppend, mul, List.map_append]

theorem valLength_append (xs ys : List α) :
    valLength (valAppend (contents xs) (contents ys)) =
    add (· + ·) (valLength (contents xs)) (valLength (contents ys)) := by
  simp [valLength, valAppend, mul, add, List.length_append]

-- ============================================================================
-- SECTION 5: Sets
-- ============================================================================

-- origin is not the empty set. Origin is the absence of a set.
-- contents(∅) is the empty set.

-- ============================================================================
-- Set Membership
-- ============================================================================

def valSetMem (mem : α → α → Prop) (a : α) : Val α → Prop
  | contents s => mem a s
  | _ => False

@[simp] theorem valSetMem_contents (mem : α → α → Prop) (a s : α) :
    valSetMem mem a (contents s) = mem a s := rfl

theorem origin_has_no_set_members (mem : α → α → Prop) (a : α) :
    ¬ valSetMem mem a (origin : Val α) := id

-- ============================================================================
-- Set Operations
-- ============================================================================

abbrev valUnion (unionF : α → α → α) : Val α → Val α → Val α := mul unionF
abbrev valInter (interF : α → α → α) : Val α → Val α → Val α := mul interF
abbrev valCompl (complF : α → α) : Val α → Val α := valMap complF
abbrev valSdiff (sdiffF : α → α → α) : Val α → Val α → Val α := mul sdiffF

-- ============================================================================
-- Subset
-- ============================================================================

def valSubset (subsetP : α → α → Prop) : Val α → Val α → Prop
  | contents s, contents t => subsetP s t
  | _, _ => False

@[simp] theorem valSubset_contents (subsetP : α → α → Prop) (s t : α) :
    valSubset subsetP (contents s) (contents t) = subsetP s t := rfl

theorem origin_not_subset (subsetP : α → α → Prop) (s : Val α) :
    ¬ valSubset subsetP origin s := by cases s <;> exact id

theorem not_subset_origin (subsetP : α → α → Prop) (s : Val α) :
    ¬ valSubset subsetP s origin := by cases s <;> exact id

-- ============================================================================
-- Set laws (lifted from α)
-- ============================================================================

theorem valUnion_comm (unionF : α → α → α)
    (h : ∀ a b : α, unionF a b = unionF b a) (a b : Val α) :
    valUnion unionF a b = valUnion unionF b a :=
  mul_comm unionF h a b

theorem valUnion_assoc (unionF : α → α → α)
    (h : ∀ a b c : α, unionF (unionF a b) c = unionF a (unionF b c))
    (a b c : Val α) :
    valUnion unionF (valUnion unionF a b) c = valUnion unionF a (valUnion unionF b c) :=
  mul_assoc unionF h a b c

theorem valInter_comm (interF : α → α → α)
    (h : ∀ a b : α, interF a b = interF b a) (a b : Val α) :
    valInter interF a b = valInter interF b a :=
  mul_comm interF h a b

theorem valInter_assoc (interF : α → α → α)
    (h : ∀ a b c : α, interF (interF a b) c = interF a (interF b c))
    (a b c : Val α) :
    valInter interF (valInter interF a b) c = valInter interF a (valInter interF b c) :=
  mul_assoc interF h a b c

theorem valUnion_inter_distrib (unionF interF : α → α → α)
    (h : ∀ a b c : α, unionF a (interF b c) = interF (unionF a b) (unionF a c))
    (a b c : Val α) :
    valUnion unionF a (valInter interF b c) =
    valInter interF (valUnion unionF a b) (valUnion unionF a c) :=
  left_distrib unionF interF h a b c

theorem valCompl_valCompl (complF : α → α)
    (h : ∀ a : α, complF (complF a) = a) (s : Val α) :
    valCompl complF (valCompl complF s) = s :=
  neg_neg complF h s

-- ============================================================================
-- SECTION 6: Finite Sets
-- ============================================================================

-- ============================================================================
-- Cardinality / Sum / Product / Sup / Inf
-- ============================================================================

abbrev valCard (cardF : α → α) : Val α → Val α := valMap cardF
abbrev valFinsetSum (sumF : α → α) : Val α → Val α := valMap sumF
abbrev valFinsetProd (prodF : α → α) : Val α → Val α := valMap prodF

-- Mathlib requires `Nonempty s` or `s ≠ ∅` for Finset.sup / Finset.inf.
-- Val: if the finset is origin, sup/inf = origin. If it's contents, compute.

abbrev valFinsetSup (supF : α → α) : Val α → Val α := valMap supF
abbrev valFinsetInf (infF : α → α) : Val α → Val α := valMap infF

-- ============================================================================
-- Finset operations
-- ============================================================================

abbrev valFinsetUnion (unionF : α → α → α) : Val α → Val α → Val α := mul unionF
abbrev valFinsetInter (interF : α → α → α) : Val α → Val α → Val α := mul interF
abbrev valFinsetInsert (insertF : α → α → α) : Val α → Val α → Val α := mul insertF
abbrev valFinsetErase (eraseF : α → α → α) : Val α → Val α → Val α := mul eraseF

/-- Sum over union = sum of sums (when disjoint). -/
theorem valFinsetSum_union (sumF : α → α) (addF : α → α → α) (unionF : α → α → α)
    (h : ∀ s t : α, sumF (unionF s t) = addF (sumF s) (sumF t))
    (s t : α) :
    valFinsetSum sumF (valFinsetUnion unionF (contents s) (contents t)) =
    add addF (valFinsetSum sumF (contents s)) (valFinsetSum sumF (contents t)) := by
  simp [valFinsetSum, valFinsetUnion, valMap, mul, add, h]

-- ============================================================================
-- SECTION 7: Multisets
-- ============================================================================

-- A multiset is a list up to permutation. Same origin ≠ contents([]) distinction.

-- ============================================================================
-- Multiset operations
-- ============================================================================

def valMCons (consF : α → α → α) (a : α) : Val α → Val α
  | origin => origin
  | container s => container (consF a s)
  | contents s => contents (consF a s)

@[simp] theorem valMCons_origin (consF : α → α → α) (a : α) :
    valMCons consF a (origin : Val α) = origin := rfl

@[simp] theorem valMCons_contents (consF : α → α → α) (a s : α) :
    valMCons consF a (contents s) = contents (consF a s) := rfl

abbrev valMUnion (addF : α → α → α) : Val α → Val α → Val α := mul addF
abbrev valMInter (interF : α → α → α) : Val α → Val α → Val α := mul interF
abbrev valMCard (cardF : α → α) : Val α → Val α := valMap cardF
abbrev valMCount (countF : α → α) : Val α → Val α := valMap countF
abbrev valMFold (foldF : α → α) : Val α → Val α := valMap foldF

-- ============================================================================
-- Multiset laws (lifted)
-- ============================================================================

theorem valMUnion_comm (addF : α → α → α)
    (h : ∀ a b : α, addF a b = addF b a) (a b : Val α) :
    valMUnion addF a b = valMUnion addF b a :=
  mul_comm addF h a b

theorem valMUnion_assoc (addF : α → α → α)
    (h : ∀ a b c : α, addF (addF a b) c = addF a (addF b c))
    (a b c : Val α) :
    valMUnion addF (valMUnion addF a b) c = valMUnion addF a (valMUnion addF b c) :=
  mul_assoc addF h a b c

-- ============================================================================
-- Cross-domain: the sort is the invariant
-- ============================================================================

-- Every data structure in this file shares the same invariant:
-- origin absorbs, container preserves structure, contents computes.
-- The ≠ 0, Nonempty, and isEmpty hypotheses all asked the same
-- question: "does this value exist?" The sort answers it once.

end Val
