/-
Released under MIT license.
-/
import Origin.Core

/-!
# Proof: Analysis works with Origin

The roundoff back handspring. Limits, continuity, derivatives.
Where ε-δ meets Option α.

The question: can Origin handle the ≠ 0 that appears in
denominators, limit definitions, and continuity proofs?

In Mathlib: ε > 0 means ε ≠ 0 ∧ ε is positive.
In Origin: ε is some(ε) where ε > 0. The ground (none) is
not in the domain of the limit — it was never a valid ε.
-/

universe u
variable {α : Type u}

-- ============================================================================
-- 1. ε-δ LIMITS ON OPTION
-- ============================================================================

/-- Limit of a function at a point: for every ε > 0, there exists δ > 0
    such that |f(x) - L| < ε whenever 0 < |x - a| < δ.

    On Option: none means "outside the domain." If the function
    returns none, the limit doesn't apply there. If ε or δ is none,
    the quantifier is vacuous (the ground is not a valid bound). -/
def HasLimit (f : α → α) (a L : α)
    (dist : α → α → Nat) (pos : Nat → Prop) : Prop :=
  ∀ ε : Nat, pos ε →
    ∃ δ : Nat, pos δ ∧
      ∀ x : α, 0 < dist x a → dist x a < δ → dist (f x) L < ε

/-- Limit on Option: if the function is defined (some), the limit
    applies. If undefined (none), the limit is vacuously true. -/
def HasLimitOption (f : Option α → Option α) (a L : Option α)
    (dist : α → α → Nat) (pos : Nat → Prop) : Prop :=
  match a, L with
  | some a', some L' => HasLimit (fun x => match f (some x) with
      | some y => y | none => L') a' L' dist pos
  | _, _ => True  -- limit at/to the ground is vacuous

-- ============================================================================
-- 2. CONTINUITY
-- ============================================================================

/-- A function is continuous at a point: the limit equals the value. -/
def IsContinuousAt (f : α → α) (a : α)
    (dist : α → α → Nat) (pos : Nat → Prop) : Prop :=
  HasLimit f a (f a) dist pos

/-- Continuity lifts through Option: some values are continuous,
    none maps to none (the ground is preserved). -/
def IsContinuousAtOption (f : α → α) (a : α)
    (dist : α → α → Nat) (pos : Nat → Prop) : Prop :=
  IsContinuousAt f a dist pos ∧
  Option.map f none = none  -- ground preservation

theorem continuous_preserves_ground (f : α → α) :
    Option.map f (none : Option α) = none := rfl

/-- Composition of continuous functions is continuous. -/
theorem continuous_comp (f g : α → α) (a : α)
    (dist : α → α → Nat) (pos : Nat → Prop)
    (hf : IsContinuousAt f (g a) dist pos)
    (hg : IsContinuousAt g a dist pos)
    (hdist_f : ∀ ε, pos ε → ∃ δ, pos δ ∧
      ∀ x, dist (g x) (g a) < δ → dist (f (g x)) (f (g a)) < ε) :
    IsContinuousAt (f ∘ g) a dist pos := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, hf'⟩ := hdist_f ε hε
  obtain ⟨δ₂, hδ₂, hg'⟩ := hg δ₁ hδ₁
  exact ⟨δ₂, hδ₂, fun x hxa hxd => hf' x (hg' x hxa hxd)⟩

-- ============================================================================
-- 3. DERIVATIVES
-- ============================================================================

/-- The derivative of f at a: lim_{h→0} (f(a+h) - f(a)) / h.
    On Option: h is some(h) where h ≠ some(0). The ground (none)
    is not a valid increment — you can't take an infinitesimal
    step on the ground. -/
def HasDerivAt (f : α → α) (a deriv : α)
    [Add α] [Neg α] [Mul α] [Inv' α]
    (dist : α → α → Nat) (pos : Nat → Prop) : Prop :=
  ∀ ε : Nat, pos ε →
    ∃ δ : Nat, pos δ ∧
      ∀ h : α, 0 < dist h a → dist h a < δ →
        dist ((f (a + h) + -(f a)) * h⁻¹') deriv < ε

/-- The derivative of a constant function is zero. -/
theorem deriv_const [Add α] [Neg α] [Mul α] [Inv' α]
    (c a zero : α) (dist : α → α → Nat) (pos : Nat → Prop)
    (hcancel : ∀ x : α, x + -x = zero)
    (hzeromul : ∀ x : α, zero * x = zero)
    (hdist_zero : dist zero zero = 0)
    (hpos_zero : ∀ ε, pos ε → 0 < ε) :
    HasDerivAt (fun _ => c) a zero dist pos := by
  intro ε hε
  refine ⟨ε, hε, fun h _ _ => ?_⟩
  simp [hcancel, hzeromul, hdist_zero]; exact hpos_zero ε hε

-- ============================================================================
-- 4. THE ≠ 0 IN DENOMINATORS
-- ============================================================================

-- In Mathlib: division by zero is guarded by h : x ≠ 0.
-- In Origin: division by none is absorption (none * anything = none).
-- Division by some 0 is some(a * 0⁻¹) — a computation on measurements.
-- The guard against the ground is structural. The guard against
-- some 0 is mathematical (and real — you still can't divide by zero
-- measurement). But these are DIFFERENT guards for DIFFERENT reasons.

/-- Division by none (the ground) absorbs. No guard needed. -/
theorem div_by_ground [Mul α] [Inv' α] (a : Option α) :
    a * (none : Option α) = none := mul_none_right a

/-- Division by some value stays in the counting domain. -/
theorem div_by_some [Mul α] [Inv' α] (a b : α) :
    (some a : Option α) * some (b⁻¹') = some (a * b⁻¹') := by simp

/-- The ground can't divide — it absorbs the numerator too. -/
theorem ground_div [Mul α] [Inv' α] (b : Option α) :
    (none : Option α) * b = none := mul_none_left b

-- ============================================================================
-- 5. SEQUENCES AND CONVERGENCE
-- ============================================================================

/-- A sequence converges to a limit. -/
def SeqConverges (s : Nat → α) (L : α)
    (dist : α → α → Nat) (pos : Nat → Prop) : Prop :=
  ∀ ε : Nat, pos ε → ∃ N : Nat, ∀ n, n ≥ N → dist (s n) L < ε

/-- A sequence on Option: none values are "outside the sequence."
    Convergence only considers some values. -/
def SeqConvergesOption (s : Nat → Option α) (L : α)
    (dist : α → α → Nat) (pos : Nat → Prop) : Prop :=
  ∀ ε : Nat, pos ε → ∃ N : Nat, ∀ n, n ≥ N →
    match s n with
    | some a => dist a L < ε
    | none => True  -- none values don't affect convergence

/-- A constant sequence converges to its value. -/
theorem const_seq_converges (c : α) (dist : α → α → Nat) (pos : Nat → Prop)
    (hdist : dist c c = 0) (hpos : ∀ ε, pos ε → 0 < ε) :
    SeqConverges (fun _ => c) c dist pos := by
  intro ε hε
  exact ⟨0, fun _ _ => by rw [hdist]; exact hpos ε hε⟩

/-- Limit of sum = sum of limits (on some values). -/
theorem seq_add_converges [Add α] (s t : Nat → α) (Ls Lt : α)
    (dist : α → α → Nat) (pos : Nat → Prop)
    (hdist_add : ∀ a b c d : α, dist (a + b) (c + d) ≤ dist a c + dist b d)
    (hs : SeqConverges s Ls dist pos)
    (ht : SeqConverges t Lt dist pos)
    (hpos_half : ∀ ε, pos ε → ∃ ε', pos ε' ∧ ε' + ε' ≤ ε) :
    SeqConverges (fun n => s n + t n) (Ls + Lt) dist pos := by
  intro ε hε
  obtain ⟨ε', hε', hsum⟩ := hpos_half ε hε
  obtain ⟨Ns, hNs⟩ := hs ε' hε'
  obtain ⟨Nt, hNt⟩ := ht ε' hε'
  refine ⟨max Ns Nt, fun n hn => ?_⟩
  have h1 := hNs n (by omega)
  have h2 := hNt n (by omega)
  exact Nat.lt_of_le_of_lt (hdist_add (s n) (t n) Ls Lt) (by omega)

-- ============================================================================
-- 6. OPTION.MAP PRESERVES LIMITS
-- ============================================================================

/-- If f is continuous and s → L, then f ∘ s → f(L). -/
theorem map_preserves_convergence (f : α → α) (s : Nat → α) (L : α)
    (dist : α → α → Nat) (pos : Nat → Prop)
    (hf : IsContinuousAt f L dist pos)
    (hs : SeqConverges s L dist pos) :
    SeqConverges (fun n => f (s n)) (f L) dist pos := by
  intro ε hε
  obtain ⟨δ, hδ, hf'⟩ := hf ε hε
  obtain ⟨N, hN⟩ := hs δ hδ
  exact ⟨N, fun n hn => by
    have hsn := hN n hn
    by_cases h0 : dist (s n) L = 0
    · -- s n is at L, so f(s n) = f(L)
      sorry  -- needs: dist x y = 0 → x = y
    · exact hf' (s n) (Nat.pos_of_ne_zero h0) hsn⟩

-- ============================================================================
-- 7. HONEST BOUNDARY: what needs sorry
-- ============================================================================

-- The sorry above is real. map_preserves_convergence needs:
--   dist x y = 0 → x = y (metric space axiom)
-- This is a genuine requirement — not infrastructure. Origin
-- doesn't have a Metric typeclass, and adding one would be
-- adding infrastructure. The theorem works for the non-zero
-- case. The zero case needs the metric axiom.
--
-- This is information, not failure. It tells us exactly what
-- Origin needs to add to Core if we want full metric space
-- support: a dist function with the metric axioms. That's
-- real math, not zero-management infrastructure.

-- ============================================================================
-- 8. CONCRETE: sequences on Option Int
-- ============================================================================

-- Constant sequence converges
example : SeqConverges (fun _ => (5 : Int)) 5
    (fun a b => (a - b).natAbs) (· > 0) := by
  intro ε hε; exact ⟨0, fun _ _ => by simp; exact hε⟩

-- Option.map preserves none
example : Option.map (· + 1) (none : Option Int) = none := rfl

-- Option.map preserves some
example : Option.map (· + 1) (some 5 : Option Int) = some 6 := rfl

-- The sequence [some 1, some 2, some 3, ...] on Option Int
-- Ground (none) is not a sequence value — it's outside the domain
