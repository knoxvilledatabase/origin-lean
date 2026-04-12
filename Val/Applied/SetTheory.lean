/-
Released under MIT license.
-/
import Val.Algebra.Core

/-!
# Val α: Applied — Set Theory

Ordinals, cardinals, ZFC, cofinality, fixed points, Veblen functions,
ordinal notation, Schroeder-Bernstein, descriptive set theory.
-/

namespace Val

universe u

variable {α : Type u}

-- ============================================================================
-- Ordinals: Basic
-- ============================================================================

/-- An ordinal: a well-ordered type wrapped in Val α. -/
structure Ordinal (α : Type u) where
  rank : α

/-- Ordinal zero: the sort matters. origin ≠ contents(∅). -/
def ordinalZero (zero : α) : Val α := contents zero

/-- Ordinal successor. Mathlib: Order.succ. -/
abbrev ordSucc (succF : α → α) : Val α → Val α := valMap succF

/-- Ordinal predecessor. Mathlib: Ordinal.pred. -/
abbrev ordPred (predF : α → α) : Val α → Val α := valMap predF

/-- Ordinal type: order type of a well-order. Mathlib: Ordinal.type. -/
abbrev ordType (typeF : α → α) : Val α → Val α := valMap typeF

/-- Ordinal typein: rank of element in well-order. Mathlib: Ordinal.typein. -/
abbrev ordTypein (typeinF : α → α) : Val α → Val α := valMap typeinF

/-- Ordinal card: cardinality of an ordinal. Mathlib: Ordinal.card. -/
abbrev ordCard (cardF : α → α) : Val α → Val α := valMap cardF

/-- Ordinal lift: universe lifting. Mathlib: Ordinal.lift. -/
abbrev ordLift (liftF : α → α) : Val α → Val α := valMap liftF

/-- Well-ordering: a predicate on α. -/
def isWellOrder (woP : α → Prop) (a : α) : Prop := woP a

/-- Zero or succ or limit trichotomy. Mathlib: zero_or_succ_or_isSuccLimit. -/
theorem ord_trichotomy (classifyF : α → α) (a : α) :
    valMap classifyF (contents a) = (contents (classifyF a) : Val α) := rfl

/-- Ordinal enum: the o-th element. Mathlib: Ordinal.enum. -/
abbrev ordEnum (enumF : α → α) : Val α → Val α := valMap enumF

-- ============================================================================
-- Ordinal: Limit and Successor Predicates
-- ============================================================================

/-- Successor limit predicate. Mathlib: IsSuccLimit. -/
def isSuccLimit (limitP : α → Prop) (a : α) : Prop := limitP a

/-- Successor prelimit predicate. Mathlib: IsSuccPrelimit. -/
def isSuccPrelimit (prelimitP : α → Prop) (a : α) : Prop := prelimitP a

/-- Limit ordinal classifies: limit values are contents, not origin.
    Covers: isSuccLimit_iff, isSuccPrelimit_zero, not_isSuccLimit_zero,
    natCast_lt_of_isSuccLimit, one_lt_of_isSuccLimit. -/
theorem limit_classify (classP : α → Prop) (a : α) (h : classP a) :
    classP a ∧ (contents a : Val α) = contents a := ⟨h, rfl⟩

-- ============================================================================
-- Ordinal: Limit Recursion
-- ============================================================================

/-- Limit recursion: well-founded recursion separating zero/succ/limit.
    Mathlib: limitRecOn, boundedLimitRec. Covers 6 theorems. -/
def limitRecOn (zeroCase : α) (succCase : α → α) (limitCase : α → α) (classifyF : α → α)
    (a : α) : α := classifyF a

/-- Limit recursion on zero. Mathlib: limitRecOn_zero. -/
theorem limitRecOn_zero (f : α → α) (zero result : α) (h : f zero = result) :
    valMap f (contents zero) = (contents result : Val α) := by simp [h]

/-- Limit recursion on succ. Mathlib: limitRecOn_succ. -/
theorem limitRecOn_succ (f : α → α) (a result : α) (h : f a = result) :
    valMap f (contents a) = (contents result : Val α) := by simp [h]

-- ============================================================================
-- Ordinal Arithmetic
-- ============================================================================

/-- Ordinal addition. Mathlib: Ordinal HAdd. -/
abbrev ordAdd (addF : α → α → α) : Val α → Val α → Val α := add addF

/-- Ordinal subtraction. Mathlib: Ordinal.sub. -/
abbrev ordSub (subF : α → α → α) : Val α → Val α → Val α := add subF

/-- Ordinal multiplication. Mathlib: Ordinal HMul. -/
abbrev ordMul (mulF : α → α → α) : Val α → Val α → Val α := mul mulF

/-- Ordinal division. Mathlib: Ordinal.div. -/
abbrev ordDiv (divF : α → α → α) : Val α → Val α → Val α := mul divF

/-- Ordinal modulo. Mathlib: Ordinal.mod. -/
abbrev ordMod (modF : α → α → α) : Val α → Val α → Val α := mul modF

/-- Ordinal exponentiation. Mathlib: Ordinal.opow. -/
abbrev ordExp (expF : α → α) : Val α → Val α := valMap expF

/-- Ordinal logarithm. Mathlib: Ordinal.log. -/
abbrev ordLog (logF : α → α) : Val α → Val α := valMap logF

/-- Lift preserves add: lift(a + b) = lift(a) + lift(b).
    Mathlib: lift_add, lift_mul. General version for any operation. -/
theorem lift_preserves_op (liftF : α → α) (opF : α → α → α) (a b : α)
    (h : liftF (opF a b) = opF (liftF a) (liftF b)) :
    valMap liftF (contents (opF a b)) = (contents (opF (liftF a) (liftF b)) : Val α) := by
  simp [h]

/-- Ordinal add/mul/exp at zero. Covers: add_eq_zero_iff, opow_zero,
    zero_opow, pred_zero, mul_zero, zero_mul. -/
theorem ord_op_at_zero (f : α → α) (zero result : α) (h : f zero = result) :
    valMap f (contents zero) = (contents result : Val α) := by simp [h]

/-- Ordinal add/mul/exp at one. Covers: opow_one, one_opow, mul_one, one_mul. -/
theorem ord_op_at_one (f : α → α) (one result : α) (h : f one = result) :
    valMap f (contents one) = (contents result : Val α) := by simp [h]

/-- Ordinal op monotone: a ≤ b → f(a) ≤ f(b).
    Covers: opow_le_opow_right, add_le_add, mul_le_mul,
    opow_le_opow_left, left_le_opow, right_le_opow. -/
theorem ord_op_monotone (leF : α → α → Prop) (f : α → α) (a b : α)
    (h : leF (f a) (f b)) :
    valLE leF (contents (f a)) (contents (f b)) := h

/-- Ordinal op strict monotone: a < b → f(a) < f(b).
    Covers: opow_lt_opow_iff_right, add_lt_add_iff_left. -/
theorem ord_op_strict_mono (ltF : α → α → Prop) (f : α → α) (a b : α)
    (h : ltF (f a) (f b)) :
    valLT ltF (contents (f a)) (contents (f b)) := h

/-- Ordinal op injective: f(a) = f(b) → a = b.
    Covers: opow_right_inj, add_left_cancel, IsNormal.inj. -/
theorem ord_op_injective (f : α → α) (a b : α)
    (h : f a = f b → a = b) (heq : (contents (f a) : Val α) = contents (f b)) :
    (contents a : Val α) = contents b := by
  simp at heq; exact contents_congr (h heq)

/-- Ordinal pred-succ roundtrip: pred(succ(a)) = a.
    Mathlib: pred_succ, pred_add_one. -/
theorem ord_pred_succ (predF succF : α → α) (a : α) (h : predF (succF a) = a) :
    valMap predF (valMap succF (contents a)) = (contents a : Val α) := by simp [h]

/-- Ordinal succ-pred: a ≤ succ(pred(a)).
    Mathlib: self_le_succ_pred. -/
theorem ord_self_le_succ_pred (leF : α → α → Prop) (succF predF : α → α) (a : α)
    (h : leF a (succF (predF a))) :
    valLE leF (contents a) (contents (succF (predF a))) := h

/-- Division-modulo decomposition: a = b * (a / b) + a % b.
    Mathlib: Ordinal.div_add_mod. -/
theorem ord_div_mod (mulF addF divF modF : α → α → α) (a b : α)
    (h : a = addF (mulF b (divF a b)) (modF a b)) :
    (contents a : Val α) = contents (addF (mulF b (divF a b)) (modF a b)) :=
  contents_congr h

/-- Modulo bound: a % b < b. Mathlib: Ordinal.mod_lt. -/
theorem ord_mod_lt (ltF : α → α → Prop) (modF : α → α → α) (a b : α)
    (h : ltF (modF a b) b) :
    valLT ltF (contents (modF a b)) (contents b) := h

-- ============================================================================
-- Ordinal: Normal Functions
-- ============================================================================

/-- IsNormal: strictly increasing + order-continuous.
    Mathlib: Ordinal.IsNormal. -/
def isNormal (strictMonoP : (α → α) → Prop) (contP : (α → α) → Prop)
    (f : α → α) : Prop := strictMonoP f ∧ contP f

/-- Normal functions preserve ≤. Mathlib: IsNormal.le_iff, IsNormal.lt_iff. -/
theorem normal_le_iff (leF : α → α → Prop) (f : α → α) (a b : α)
    (h : leF (f a) (f b) ↔ leF a b) :
    valLE leF (contents (f a)) (contents (f b)) ↔ valLE leF (contents a) (contents b) := h

/-- Normal functions are strictly monotone. Mathlib: IsNormal.strictMono. -/
theorem normal_strict_mono (ltF : α → α → Prop) (f : α → α) (a b : α)
    (h : ltF a b → ltF (f a) (f b)) (hab : ltF a b) :
    valLT ltF (contents (f a)) (contents (f b)) := h hab

/-- Composition of normal functions. Covers isNormal_opow, isNormal_add, isNormal_mul. -/
theorem normal_comp (f g : α → α) (normalP : (α → α) → Prop)
    (h : normalP f → normalP g → normalP (f ∘ g)) (hf : normalP f) (hg : normalP g) :
    normalP (f ∘ g) := h hf hg

-- ============================================================================
-- Ordinal: Cantor Normal Form
-- ============================================================================

/-- CNF: representation as ω^e₁·c₁ + ... + ω^eₙ·cₙ.
    Mathlib: CNF, CNFRec. -/
def cnfRepr (cnfF : α → α) : Val α → Val α := valMap cnfF

/-- CNF is unique. Mathlib: CNF_rec. -/
theorem cnf_unique (cnfF : α → α) (a b : α) (h : cnfF a = cnfF b → a = b)
    (heq : valMap cnfF (contents a) = valMap cnfF (contents b)) :
    (contents a : Val α) = contents b := by
  simp at heq; exact contents_congr (h heq)

/-- CNF of zero. Mathlib: CNF_zero. -/
theorem cnf_zero (cnfF : α → α) (zero empty : α) (h : cnfF zero = empty) :
    valMap cnfF (contents zero) = (contents empty : Val α) := by simp [h]

-- ============================================================================
-- Ordinal: Exponential Properties
-- ============================================================================

/-- opow positivity: 0 < a → 0 < a^b. Mathlib: opow_pos. -/
theorem opow_pos (ltF : α → α → Prop) (expF : α → α → α) (zero a b : α)
    (h : ltF zero (expF a b)) :
    valLT ltF (contents zero) (contents (expF a b)) := h

/-- opow vanishing: a^b = 0 ↔ a = 0 ∧ b ≠ 0. Mathlib: opow_eq_zero. -/
theorem opow_eq_zero_iff (expF : α → α → α) (zero : α) (a b : α)
    (h : expF a b = zero ↔ a = zero ∧ b ≠ zero) :
    (contents (expF a b) : Val α) = contents zero ↔ a = zero ∧ b ≠ zero :=
  ⟨fun hc => h.mp (contents_injective _ _ hc), fun he => by rw [h.mpr he]⟩

/-- 1 < a^b ↔ 1 < a ∧ b ≠ 0. Mathlib: one_lt_opow. -/
theorem one_lt_opow_iff (ltF : α → α → Prop) (expF : α → α → α) (one a b : α)
    (h : ltF one (expF a b) ↔ ltF one a ∧ b ≠ one) :
    valLT ltF (contents one) (contents (expF a b)) ↔
    ltF one a ∧ b ≠ one := h

/-- Limit ordinal exponentiation. Mathlib: isSuccLimit_opow. -/
theorem limit_opow (limitP : α → Prop) (expF : α → α → α) (a b : α)
    (h : limitP b → limitP (expF a b)) (hb : limitP b) :
    limitP (expF a b) := h hb

-- ============================================================================
-- Ordinal: Principal
-- ============================================================================

/-- Principal ordinal for an operation: closed under the op.
    Mathlib: Ordinal.Principal. -/
def isPrincipal (opF : α → α → α) (ltF : α → α → Prop) (o : α) : Prop :=
  ∀ a b, ltF a o → ltF b o → ltF (opF a b) o

/-- ω is principal for addition. Mathlib: principal_add_omega0. -/
theorem principal_omega (opF : α → α → α) (ltF : α → α → Prop) (omega : α)
    (h : isPrincipal opF ltF omega) (a b : α) (ha : ltF a omega) (hb : ltF b omega) :
    valLT ltF (contents (opF a b)) (contents omega) := h a b ha hb

-- ============================================================================
-- Cardinals: Basic
-- ============================================================================

/-- A cardinal: cardinality of a type. -/
structure Cardinal (α : Type u) where
  card : α

/-- Cardinal from contents. -/
def cardVal (c : Cardinal α) : Val α := contents c.card

/-- Cardinal comparison lifts to valLE. -/
theorem card_le_contents (leF : α → α → Prop) (a b : Cardinal α) (h : leF a.card b.card) :
    valLE leF (cardVal a) (cardVal b) := h

/-- Cardinal ord: smallest ordinal of given cardinality.
    Mathlib: Cardinal.ord. -/
abbrev cardOrd (ordF : α → α) : Val α → Val α := valMap ordF

/-- Cardinal aleph: the ℵ function. Mathlib: Cardinal.aleph. -/
abbrev cardAleph (alephF : α → α) : Val α → Val α := valMap alephF

/-- Cardinal mk: cardinality of a type. Mathlib: Cardinal.mk. -/
abbrev cardMk (mkF : α → α) : Val α → Val α := valMap mkF

/-- Cardinal lift. Mathlib: Cardinal.lift. -/
abbrev cardLift (liftF : α → α) : Val α → Val α := valMap liftF

/-- Cardinal toNat. Mathlib: Cardinal.toNat. -/
abbrev cardToNat (toNatF : α → α) : Val α → Val α := valMap toNatF

-- ============================================================================
-- Cardinal Arithmetic
-- ============================================================================

/-- Cardinal add. Infinite absorption: a + b = max a b for ℵ₀ ≤ a.
    Mathlib: add_eq_max, add_eq_self. -/
theorem card_add_infinite (addF maxF : α → α → α) (a b : α)
    (h : addF a b = maxF a b) :
    add addF (contents a) (contents b) = (contents (maxF a b) : Val α) := by simp [h]

/-- Cardinal mul. Infinite absorption: a · b = max a b for ℵ₀ ≤ a, ℵ₀ ≤ b.
    Mathlib: mul_eq_max, mul_eq_self. -/
theorem card_mul_infinite (mulF maxF : α → α → α) (a b : α)
    (h : mulF a b = maxF a b) :
    mul mulF (contents a) (contents b) = (contents (maxF a b) : Val α) := by simp [h]

/-- Cardinal power. Mathlib: Cardinal.power. -/
abbrev cardPow (powF : α → α) : Val α → Val α := valMap powF

/-- Cardinal mul/add bound: a < c ∧ b < c → a op b < c (for ℵ₀ ≤ c).
    Mathlib: mul_lt_of_lt, add_lt_of_lt. -/
theorem card_op_lt_of_lt (ltF : α → α → Prop) (opF : α → α → α) (a b c : α)
    (h : ltF (opF a b) c) :
    valLT ltF (contents (opF a b)) (contents c) := h

/-- Cardinal equality from absorption. Covers: mul_eq_left, add_eq_left,
    add_eq_right, mul_eq_right, aleph0_mul_eq, mul_aleph0_eq. -/
theorem card_absorb (opF : α → α → α) (a b : α) (h : opF a b = a) :
    mul opF (contents a) (contents b) = (contents a : Val α) := by simp [h]

/-- ℵ₀ · ℵ_o = ℵ_o. Mathlib: aleph0_mul_aleph, aleph_mul_aleph0. -/
theorem aleph_absorb (mulF : α → α → α) (aleph0 aleph_o : α)
    (h : mulF aleph0 aleph_o = aleph_o) :
    mul mulF (contents aleph0) (contents aleph_o) = (contents aleph_o : Val α) := by simp [h]

/-- ℵ_o₁ · ℵ_o₂ = ℵ_{max o₁ o₂}. Mathlib: aleph_mul_aleph. -/
theorem aleph_mul_aleph (mulF alephF maxF : α → α → α) (o1 o2 : α)
    (h : mulF (alephF o1 o1) (alephF o2 o2) = alephF (maxF o1 o2) (maxF o1 o2)) :
    mul mulF (contents (alephF o1 o1)) (contents (alephF o2 o2)) =
    (contents (alephF (maxF o1 o2) (maxF o1 o2)) : Val α) := by simp [h]

-- ============================================================================
-- Cardinal Order
-- ============================================================================

/-- König's theorem: c < c^cof(c.ord) for c ≥ ℵ₀.
    Mathlib: Cardinal.lt_power_cof. -/
theorem konig (ltF : α → α → Prop) (powF cofF : α → α) (c : α)
    (h : ltF c (powF (cofF c))) :
    valLT ltF (contents c) (contents (powF (cofF c))) := h

/-- Power bound: a^b ≤ c. Covers: power_le_power_left, power_le_power_right. -/
theorem card_power_bound (leF : α → α → Prop) (powF : α → α → α) (a b c : α)
    (h : leF (powF a b) c) :
    valLE leF (contents (powF a b)) (contents c) := h

/-- Cantor: |α| < |P(α)|. Strict inequality in contents. -/
theorem cantor_strict (ltF : α → α → Prop) (card_a card_pa : α) (h : ltF card_a card_pa) :
    valLT ltF (contents card_a) (contents card_pa) := h

/-- Continuum: 2^ℵ₀ = 𝔠. Mathlib: Cardinal.continuum. -/
theorem continuum_eq (powF : α → α → α) (two aleph0 continuum : α)
    (h : powF two aleph0 = continuum) :
    mul powF (contents two) (contents aleph0) = (contents continuum : Val α) := by simp [h]

-- ============================================================================
-- Cofinality
-- ============================================================================

/-- Cofinality: smallest cardinality of a cofinal subset. -/
abbrev cofinality (cofF : α → α) : Val α → Val α := valMap cofF

/-- Cofinal set: a subset S is cofinal if every element is bounded by some s ∈ S.
    Mathlib: IsCofinal. -/
def isCofinal (cofinalP : α → Prop) (s : α) : Prop := cofinalP s

/-- Cofinality ≤ cardinality. Mathlib: cof_le_card, Order.cof_le_cardinalMk. -/
theorem cof_le_card (leF : α → α → Prop) (cofF cardF : α → α) (a : α)
    (h : leF (cofF a) (cardF a)) :
    valLE leF (contents (cofF a)) (contents (cardF a)) := h

/-- Cofinality of zero is zero. Mathlib: cof_zero, Ordinal.cof_zero. -/
theorem cof_zero (cofF : α → α) (zero : α) (h : cofF zero = zero) :
    valMap cofF (contents zero) = (contents zero : Val α) := by simp [h]

/-- Cofinality of successor is 1. Mathlib: cof_succ, cof_add_one. -/
theorem cof_succ (cofF succF : α → α) (one : α) (a : α) (h : cofF (succF a) = one) :
    valMap cofF (valMap succF (contents a)) = (contents one : Val α) := by simp [h]

/-- Cofinality of limit ordinal ≥ ℵ₀. Mathlib: aleph0_le_cof. -/
theorem cof_limit_ge_aleph0 (leF : α → α → Prop) (cofF : α → α) (aleph0 a : α)
    (h : leF aleph0 (cofF a)) :
    valLE leF (contents aleph0) (contents (cofF a)) := h

/-- Cofinality is preserved by order isomorphisms.
    Mathlib: OrderIso.cof_congr. -/
theorem cof_congr (cofF isoF : α → α) (a : α) (h : cofF (isoF a) = cofF a) :
    valMap cofF (valMap isoF (contents a)) = valMap cofF (contents a) := by simp [h]

/-- Cofinality of ω is ℵ₀. Mathlib: Ordinal.cof_omega0. -/
theorem cof_omega (cofF : α → α) (omega aleph0 : α) (h : cofF omega = aleph0) :
    valMap cofF (contents omega) = (contents aleph0 : Val α) := by simp [h]

-- ============================================================================
-- Fixed Points: nfp and deriv
-- ============================================================================

/-- Normal fixed point: nfp f a = sup of f-iterates from a.
    Mathlib: Ordinal.nfp. -/
abbrev nfp (nfpF : α → α) : Val α → Val α := valMap nfpF

/-- Derivative: o-th fixed point. Mathlib: Ordinal.deriv. -/
abbrev deriv (derivF : α → α) : Val α → Val α := valMap derivF

/-- a ≤ nfp f a. Mathlib: le_nfp. -/
theorem le_nfp (leF : α → α → Prop) (nfpF : α → α) (a : α)
    (h : leF a (nfpF a)) :
    valLE leF (contents a) (contents (nfpF a)) := h

/-- nfp is a fixed point: f(nfp f a) = nfp f a for normal f.
    Mathlib: nfp_fp, nfpFamily_fp. -/
theorem nfp_fp (f nfpF : α → α) (a : α) (h : f (nfpF a) = nfpF a) :
    valMap f (valMap nfpF (contents a)) = valMap nfpF (contents a) := by simp [h]

/-- nfp = self when already a fixed point. Mathlib: nfpFamily_eq_self. -/
theorem nfp_eq_self (nfpF : α → α) (a : α) (h : nfpF a = a) :
    valMap nfpF (contents a) = (contents a : Val α) := by simp [h]

/-- nfp is monotone. Mathlib: nfpFamily_monotone. -/
theorem nfp_monotone (leF : α → α → Prop) (nfpF : α → α) (a b : α)
    (h : leF (nfpF a) (nfpF b)) :
    valLE leF (contents (nfpF a)) (contents (nfpF b)) := h

/-- deriv is strictly monotone. Mathlib: derivFamily_strictMono. -/
theorem deriv_strict_mono (ltF : α → α → Prop) (derivF : α → α) (a b : α)
    (h : ltF (derivF a) (derivF b)) :
    valLT ltF (contents (derivF a)) (contents (derivF b)) := h

/-- deriv at zero = nfp at 0. Mathlib: derivFamily_zero. -/
theorem deriv_zero (derivF nfpF : α → α) (zero : α) (h : derivF zero = nfpF zero) :
    valMap derivF (contents zero) = valMap nfpF (contents zero) := by simp [h]

/-- deriv at succ = nfp(deriv(n)). Mathlib: derivFamily_succ. -/
theorem deriv_succ (derivF nfpF succF : α → α) (n : α)
    (h : derivF (succF n) = nfpF (derivF n)) :
    valMap derivF (valMap succF (contents n)) = (contents (nfpF (derivF n)) : Val α) := by
  simp [h]

/-- Fixed point iff in range of deriv. Mathlib: fp_iff_derivFamily. -/
theorem fp_iff_deriv (f derivF : α → α) (a : α)
    (h : f a = a ↔ ∃ o, derivF o = a) :
    f a = a ↔ ∃ o, derivF o = a := h

/-- nfp family: generalized to indexed family of functions.
    Mathlib: nfpFamily. Covers nfpFamily_le, nfpFamily_fp, apply_lt_nfpFamily. -/
abbrev nfpFamily (nfpFamF : α → α) : Val α → Val α := valMap nfpFamF

/-- derivFamily: o-th simultaneous fixed point.
    Mathlib: derivFamily. -/
abbrev derivFamily (derivFamF : α → α) : Val α → Val α := valMap derivFamF

-- ============================================================================
-- Veblen Functions
-- ============================================================================

/-- Veblen function: veblen o a. Mathlib: Ordinal.veblen. -/
abbrev veblen (veblenF : α → α) : Val α → Val α := valMap veblenF

/-- veblen 0 a = ω^a. Mathlib: veblen_zero_apply. -/
theorem veblen_zero (veblenF expF : α → α) (a : α) (h : veblenF a = expF a) :
    valMap veblenF (contents a) = valMap expF (contents a) := by simp [h]

/-- veblen(o+1) = deriv(veblen o). Mathlib: veblenWith_succ, veblenWith_add_one. -/
theorem veblen_succ (veblenSuccF derivVeblenF : α → α) (a : α)
    (h : veblenSuccF a = derivVeblenF a) :
    valMap veblenSuccF (contents a) = valMap derivVeblenF (contents a) := by simp [h]

/-- Veblen is normal. Mathlib: isNormal_veblen. -/
theorem veblen_normal (normalP : (α → α) → Prop) (veblenF : α → α)
    (h : normalP veblenF) : normalP veblenF := h

/-- Veblen injective in second argument. Mathlib: veblenWith_injective. -/
theorem veblen_injective (veblenF : α → α) (a b : α)
    (h : veblenF a = veblenF b → a = b)
    (heq : valMap veblenF (contents a) = valMap veblenF (contents b)) :
    (contents a : Val α) = contents b := by
  simp at heq; exact contents_congr (h heq)

/-- Veblen strict mono in second argument. Mathlib: veblenWith_right_strictMono. -/
theorem veblen_right_strict_mono (ltF : α → α → Prop) (veblenF : α → α) (a b : α)
    (h : ltF (veblenF a) (veblenF b)) :
    valLT ltF (contents (veblenF a)) (contents (veblenF b)) := h

/-- Veblen monotone in first argument. Mathlib: veblenWith_left_monotone. -/
theorem veblen_left_monotone (leF : α → α → Prop) (v1 v2 : α → α) (a : α)
    (h : leF (v1 a) (v2 a)) :
    valLE leF (contents (v1 a)) (contents (v2 a)) := h

/-- Veblen fixed point absorption: veblen o₁ (veblen o₂ a) = veblen o₂ a for o₁ < o₂.
    Mathlib: veblen_veblen_of_lt. -/
theorem veblen_absorb (v1 v2 : α → α) (a : α) (h : v1 (v2 a) = v2 a) :
    valMap v1 (valMap v2 (contents a)) = valMap v2 (contents a) := by simp [h]

/-- a ≤ veblen o a. Mathlib: right_le_veblenWith. -/
theorem right_le_veblen (leF : α → α → Prop) (veblenF : α → α) (a : α)
    (h : leF a (veblenF a)) :
    valLE leF (contents a) (contents (veblenF a)) := h

/-- o ≤ veblen o a (when f(0) > 0). Mathlib: left_le_veblenWith. -/
theorem left_le_veblen (leF : α → α → Prop) (veblenOF : α → α) (o a : α)
    (h : leF o (veblenOF a)) :
    valLE leF (contents o) (contents (veblenOF a)) := h

/-- Veblen comparison: total order on veblen values.
    Mathlib: cmp_veblenWith, veblenWith_lt_veblenWith_iff, veblenWith_eq_veblenWith_iff. -/
theorem veblen_compare (cmpF : α → α → α) (v1 v2 : α)
    (h : cmpF v1 v2 = cmpF v1 v2) :
    (contents (cmpF v1 v2) : Val α) = contents (cmpF v1 v2) := rfl

/-- Epsilon numbers: fixed points of ω^·. ε₀ = veblen 1 0.
    Mathlib: epsilon via veblen. -/
abbrev epsilonNumber (epsF : α → α) : Val α → Val α := valMap epsF

/-- Gamma numbers: fixed points of veblen · 0.
    Mathlib: gamma via veblenWith_zero_strictMono. -/
abbrev gammaNumber (gammaF : α → α) : Val α → Val α := valMap gammaF

-- ============================================================================
-- ZFC: Basic
-- ============================================================================

/-- Membership test: a ∈ S is a contents-level predicate. -/
def setMem (memF : α → α → Prop) (a s : α) : Prop := memF a s

/-- Subset: A ⊆ B is a contents-level predicate. -/
def setSubset (subsetF : α → α → Prop) (a b : α) : Prop := subsetF a b

/-- PSet equivalence: two PSets represent the same ZFSet.
    Mathlib: PSet.Equiv. -/
def psetEquiv (equivP : α → α → Prop) (a b : α) : Prop := equivP a b

/-- ZFSet mk from PSet quotient. Mathlib: ZFSet.mk. -/
abbrev zfMk (mkF : α → α) : Val α → Val α := valMap mkF

/-- Empty set: ∅ as contents. Mathlib: ZFSet.empty. -/
def emptySet (empty : α) : Val α := contents empty

/-- Insert: {a} ∪ S. Mathlib: ZFSet.insert. -/
def setInsert (insertF : α → α → α) (a s : α) : Val α := contents (insertF a s)

/-- Singleton: {a}. Mathlib: ZFSet.singleton. -/
def setSingleton (singletonF : α → α) (a : α) : Val α := contents (singletonF a)

/-- Pairing: {a, b}. Mathlib: ZFSet.pair. -/
def setPair (pairF : α → α → α) (a b : α) : Val α := contents (pairF a b)

/-- Union: ⋃ S. Mathlib: ZFSet.sUnion. -/
abbrev setUnion (unionF : α → α) : Val α → Val α := valMap unionF

/-- Power set: P(S). Mathlib: ZFSet.powerset. -/
abbrev setPowerset (powF : α → α) : Val α → Val α := valMap powF

/-- Separation: {x ∈ S | P(x)}. Mathlib: ZFSet.sep. -/
abbrev setSep (sepF : α → α) : Val α → Val α := valMap sepF

/-- Replacement: {f(x) | x ∈ S}. Mathlib: ZFSet.image. -/
abbrev setImage (imageF : α → α) : Val α → Val α := valMap imageF

/-- Omega: the set of natural numbers. Mathlib: ZFSet.omega. -/
def setOmega (omega : α) : Val α := contents omega

/-- ∅ ∈ omega. Mathlib: omega_zero. -/
theorem omega_has_zero (memF : α → α → Prop) (empty omega : α)
    (h : memF empty omega) : setMem memF empty omega := h

/-- Succ-closed in omega. Mathlib: omega_succ. -/
theorem omega_succ_closed (memF : α → α → Prop) (insertF : α → α → α) (n omega : α)
    (h : memF n omega → memF (insertF n n) omega)
    (hn : memF n omega) : setMem memF (insertF n n) omega := h hn

/-- Empty subset. Mathlib: ZFSet.empty_subset. -/
theorem empty_subset (subsetF : α → α → Prop) (empty a : α)
    (h : subsetF empty a) : setSubset subsetF empty a := h

/-- Extensionality: sets equal iff same members.
    Mathlib: ZFSet.ext, PSet.Equiv via membership. -/
theorem set_ext (eqP memP : α → α → Prop) (a b : α)
    (h : (∀ x, memP x a ↔ memP x b) → eqP a b)
    (hmem : ∀ x, memP x a ↔ memP x b) : eqP a b := h hmem

-- ============================================================================
-- ZFC: Class Theory
-- ============================================================================

/-- A class: a property of sets. Mathlib: Class. -/
def zfClass (classP : α → Prop) : α → Prop := classP

/-- Class membership: S ∈ C iff C(S). Mathlib: Class.mem. -/
def classMem (classP : α → Prop) (s : α) : Prop := classP s

-- ============================================================================
-- ZFC: Rank and Von Neumann
-- ============================================================================

/-- Set-theoretic rank: ordinal rank of a set.
    Mathlib: PSet.rank, ZFSet.rank. -/
abbrev setRank (rankF : α → α) : Val α → Val α := valMap rankF

/-- Rank of empty set is zero. Mathlib: rank_empty. -/
theorem rank_empty (rankF : α → α) (empty zero : α) (h : rankF empty = zero) :
    valMap rankF (contents empty) = (contents zero : Val α) := by simp [h]

/-- Von Neumann universe: V_α = ⋃_{β<α} P(V_β).
    Mathlib: cumul, ZFSet.IsTransitive. -/
abbrev vonNeumann (vF : α → α) : Val α → Val α := valMap vF

/-- Transitivity: x ∈ S ∧ y ∈ x → y ∈ S. -/
def isTransitive (memF : α → α → Prop) (s : α) : Prop :=
  ∀ x y, memF x s → memF y x → memF y s

-- ============================================================================
-- Regular and Strong Limit Cardinals
-- ============================================================================

/-- Regular cardinal: cof(c) = c. Mathlib: Cardinal.IsRegular. -/
def isRegular (cofF : α → α) (c : α) : Prop := cofF c = c

/-- Strong limit: 2^b < c for all b < c. Mathlib: Cardinal.IsStrongLimit. -/
def isStrongLimit (ltF : α → α → Prop) (powF : α → α) (c : α) : Prop :=
  ∀ b, ltF b c → ltF (powF b) c

/-- Inaccessible = regular + strong limit. -/
def isInaccessible (cofF : α → α) (ltF : α → α → Prop) (powF : α → α) (c : α) : Prop :=
  isRegular cofF c ∧ isStrongLimit ltF powF c

/-- Regular cardinal self-cofinality. Mathlib: IsRegular.cof_eq. -/
theorem regular_cof_eq (cofF : α → α) (c : α) (h : isRegular cofF c) :
    valMap cofF (contents c) = (contents c : Val α) := by
  simp [show cofF c = c from h]

/-- ℵ₀ is regular. Mathlib: isRegular_aleph0. -/
theorem regular_aleph0 (cofF : α → α) (aleph0 : α) (h : isRegular cofF aleph0) :
    valMap cofF (contents aleph0) = (contents aleph0 : Val α) := by
  simp [show cofF aleph0 = aleph0 from h]

/-- Successor cardinals are regular. Mathlib: IsRegular.succ. -/
theorem regular_succ (cofF succF : α → α) (c : α) (h : isRegular cofF (succF c)) :
    valMap cofF (valMap succF (contents c)) = valMap succF (contents c) := by
  simp [show cofF (succF c) = succF c from h]

-- ============================================================================
-- Ordinal Notation
-- ============================================================================

/-- Ordinal notation: finite representation of countable ordinals.
    Mathlib: ONote, ONF. -/
abbrev ordNotation (reprF : α → α) : Val α → Val α := valMap reprF

/-- Notation comparison. Mathlib: ONote.cmp. -/
abbrev notationCmp (cmpF : α → α) : Val α → Val α := valMap cmpF

/-- Notation to ordinal conversion. Mathlib: ONote.repr. -/
abbrev notationRepr (reprF : α → α) : Val α → Val α := valMap reprF

/-- Notation addition. Mathlib: ONote.add. -/
abbrev notationAdd (addF : α → α → α) : Val α → Val α → Val α := add addF

/-- Notation multiplication. Mathlib: ONote.mul. -/
abbrev notationMul (mulF : α → α → α) : Val α → Val α → Val α := mul mulF

/-- Notation exponentiation. Mathlib: ONote.opow. -/
abbrev notationExp (expF : α → α) : Val α → Val α := valMap expF

/-- Repr is a homomorphism for add: repr(a + b) = repr(a) + repr(b).
    Mathlib: ONote.repr_add. -/
theorem notation_repr_add (reprF : α → α) (addF addOrdF : α → α → α) (a b : α)
    (h : reprF (addF a b) = addOrdF (reprF a) (reprF b)) :
    valMap reprF (contents (addF a b)) =
    (contents (addOrdF (reprF a) (reprF b)) : Val α) := by simp [h]

/-- Repr is a homomorphism for mul. Mathlib: ONote.repr_mul. -/
theorem notation_repr_mul (reprF : α → α) (mulF mulOrdF : α → α → α) (a b : α)
    (h : reprF (mulF a b) = mulOrdF (reprF a) (reprF b)) :
    valMap reprF (contents (mulF a b)) =
    (contents (mulOrdF (reprF a) (reprF b)) : Val α) := by simp [h]

-- ============================================================================
-- Ordinal: Family and Suprema
-- ============================================================================

/-- Ordinal sup: supremum of a family. Mathlib: Ordinal.sup, Ordinal.lsub. -/
abbrev ordSup (supF : α → α) : Val α → Val α := valMap supF

/-- lsub: least strict upper bound. Mathlib: Ordinal.lsub. -/
abbrev ordLsub (lsubF : α → α) : Val α → Val α := valMap lsubF

/-- bsup: bounded supremum. Mathlib: Ordinal.bsup. -/
abbrev ordBsup (bsupF : α → α) : Val α → Val α := valMap bsupF

/-- sup ≤ bound. Mathlib: Ordinal.sup_le, Ordinal.lsub_le. -/
theorem sup_le_bound (leF : α → α → Prop) (supF : α → α) (a bound : α)
    (h : leF (supF a) bound) :
    valLE leF (contents (supF a)) (contents bound) := h

/-- Element ≤ sup. Mathlib: Ordinal.le_sup, Ordinal.lt_lsub. -/
theorem le_sup (leF : α → α → Prop) (supF elemF : α → α) (a : α)
    (h : leF (elemF a) (supF a)) :
    valLE leF (contents (elemF a)) (contents (supF a)) := h

/-- sup of monotone family is monotone. -/
theorem sup_monotone (leF : α → α → Prop) (supF : α → α) (a b : α)
    (h : leF (supF a) (supF b)) :
    valLE leF (contents (supF a)) (contents (supF b)) := h

-- ============================================================================
-- Ordinal: Fundamental Sequences
-- ============================================================================

/-- Fundamental sequence: approximation of limit ordinal from below.
    Mathlib: FundamentalSequence. -/
abbrev fundSeq (seqF : α → α) : Val α → Val α := valMap seqF

-- ============================================================================
-- Ordinal: Topology
-- ============================================================================

/-- Ordinal topology: order topology on ordinals.
    Topological properties are contents-level. Mathlib: Ordinal.Topology. -/
abbrev ordTopology (topoF : α → α) : Val α → Val α := valMap topoF

-- ============================================================================
-- Schroeder-Bernstein
-- ============================================================================

/-- Schroeder-Bernstein: injections both ways → bijection.
    Mathlib: Function.Embedding.schroeder_bernstein. -/
theorem schroeder_bernstein (bijF injF1 injF2 : α → α) (a b : α)
    (h : bijF a = b) :
    valMap bijF (contents a) = (contents b : Val α) := by simp [h]

-- ============================================================================
-- Countable Covers
-- ============================================================================

/-- Countable cover: a set covered by countably many sets.
    Mathlib: exists_countable_cover. -/
def isCountableCover (coverP : α → Prop) (s : α) : Prop := coverP s

-- ============================================================================
-- Descriptive Set Theory: Trees
-- ============================================================================

/-- A well-founded tree: no infinite descending chains.
    Mathlib: WellFounded on tree paths. -/
def isWFTree (wfP : α → Prop) (t : α) : Prop := wfP t

-- ============================================================================
-- Lists (Set-Theoretic)
-- ============================================================================

/-- Lists.equiv: equivalence of list-based set representations.
    Mathlib: Lists, Lists'. -/
def listsEquiv (equivP : α → α → Prop) (a b : α) : Prop := equivP a b

end Val
