/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Analysis and Limits on Val α

Lifted convergence, unreachability, indeterminate forms.
The key finding: "indeterminate forms" are a sort question, not a value question.
Contents / contents is always contents. L'Hôpital resolves values; sorts are never in question.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Lifted Convergence
-- ============================================================================

/-- Lift a convergence predicate from α to Val α.
    Contents sequences converge to contents limits via α's predicate.
    Origin/container limits require constant sequences at that sort. -/
def liftConv (conv : (Nat → α) → α → Prop) : (Nat → Val α) → Val α → Prop
  | s, contents l => ∃ raw : Nat → α, (∀ n, s n = contents (raw n)) ∧ conv raw l
  | s, origin => ∀ n, s n = origin
  | s, container c => ∀ n, s n = container c

/-- If s converges to L in α, contents-lifted sequence converges to contents(L). -/
theorem contents_convergence_lifts (conv : (Nat → α) → α → Prop)
    (s : Nat → α) (L : α) (h : conv s L) :
    liftConv conv (fun n => contents (s n)) (contents L) :=
  ⟨s, fun _ => rfl, h⟩

-- ============================================================================
-- Unreachability
-- ============================================================================

/-- No contents sequence converges to origin under liftConv. -/
theorem origin_not_limit_of_contents (conv : (Nat → α) → α → Prop) (s : Nat → α) :
    ¬ liftConv conv (fun n => contents (s n)) origin := by
  intro h
  have : (fun n => contents (s n)) 0 = origin := h 0
  simp at this

/-- No contents sequence converges to container under liftConv. -/
theorem container_not_limit_of_contents (conv : (Nat → α) → α → Prop)
    (s : Nat → α) (c : α) :
    ¬ liftConv conv (fun n => contents (s n)) (container c) := by
  intro h
  have : (fun n => contents (s n)) 0 = container c := h 0
  simp at this

-- ============================================================================
-- Operations Preserve Convergence
-- ============================================================================

/-- Any binary operation faithful on contents preserves convergence. -/
theorem binary_preserves_convergence
    (conv : (Nat → α) → α → Prop)
    (f : α → α → α) (g : Val α → Val α → Val α)
    (hg : ∀ a b : α, g (contents a) (contents b) = contents (f a b))
    (hconv : ∀ s t L M, conv s L → conv t M →
      conv (fun n => f (s n) (t n)) (f L M))
    (s t : Nat → α) (L M : α) (hs : conv s L) (ht : conv t M) :
    liftConv conv
      (fun n => g (contents (s n)) (contents (t n)))
      (contents (f L M)) :=
  ⟨fun n => f (s n) (t n), fun n => hg (s n) (t n), hconv s t L M hs ht⟩

/-- Division preserves convergence with NO ≠ 0 hypothesis.
    Contents / contents is always contents. The sort is determined. -/
theorem div_preserves_convergence
    (conv : (Nat → α) → α → Prop)
    (mulF : α → α → α) (invF : α → α)
    (hconv_mul : ∀ s t L M, conv s L → conv t M →
      conv (fun n => mulF (s n) (t n)) (mulF L M))
    (hconv_inv : ∀ s L, conv s L → conv (fun n => invF (s n)) (invF L))
    (s t : Nat → α) (L M : α) (hs : conv s L) (ht : conv t M) :
    liftConv conv
      (fun n => fdiv mulF invF (contents (s n)) (contents (t n)))
      (contents (mulF L (invF M))) :=
  ⟨fun n => mulF (s n) (invF (t n)),
   fun _ => rfl,
   hconv_mul s (fun n => invF (t n)) L (invF M) hs (hconv_inv t M ht)⟩

-- ============================================================================
-- Indeterminate Forms Dissolve
-- ============================================================================

/-- "0/0" is contents. The sort is determined even when the value isn't. -/
theorem zero_div_zero_is_contents (mulF : α → α → α) (invF : α → α) (zero : α) :
    fdiv mulF invF (contents zero) (contents zero) =
    contents (mulF zero (invF zero)) := rfl

/-- "0/0" is never origin. -/
theorem zero_div_zero_ne_origin (mulF : α → α → α) (invF : α → α) (zero : α) :
    fdiv mulF invF (contents zero) (contents zero) ≠ (origin : Val α) := by
  simp [fdiv]

/-- Any contents / contents is contents. Unconditional. -/
theorem contents_div_contents_is_contents (mulF : α → α → α) (invF : α → α) (a b : α) :
    ∃ c : α, fdiv mulF invF (contents a) (contents b) = contents c :=
  ⟨mulF a (invF b), rfl⟩

/-- Contents / contents is never origin. -/
theorem contents_div_contents_ne_origin (mulF : α → α → α) (invF : α → α) (a b : α) :
    fdiv mulF invF (contents a) (contents b) ≠ (origin : Val α) := by simp [fdiv]

-- ============================================================================
-- Sequence Sort Preservation
-- ============================================================================

/-- Pointwise add of contents sequences gives contents. -/
theorem seq_add_contents (addF : α → α → α) (s t : Nat → α) (n : Nat) :
    add addF (contents (s n)) (contents (t n)) = contents (addF (s n) (t n)) := rfl

/-- Pointwise mul of contents sequences gives contents. -/
theorem seq_mul_contents (mulF : α → α → α) (s t : Nat → α) (n : Nat) :
    mul mulF (contents (s n)) (contents (t n)) = contents (mulF (s n) (t n)) := rfl

/-- No term of a contents sequence is origin. -/
theorem seq_never_origin (s : Nat → α) (n : Nat) :
    (contents (s n) : Val α) ≠ origin := by simp

end Val
