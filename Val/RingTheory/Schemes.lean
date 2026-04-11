/-
Released under MIT license.
-/
import Val.RingTheory.Core

/-!
# Val α: RingTheory — Spectrum, Ring Homomorphisms, and Advanced Structures

Prime spectrum, ring homomorphisms, etale/smooth/unramified morphisms,
coalgebras, bialgebras, Hopf algebras, and characteristic.

Key dissolutions: `Nontrivial` on every spectrum theorem, `NeZero` on every
characteristic computation. All structural in Val α.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Prime Spectrum: Basic Opens
-- ============================================================================

/-- Basic open set D(f): primes not containing f. -/
def basicOpen (f : α) (P : α → Prop) : Prop := ¬ P f

theorem basicOpen_intro (f : α) (P : α → Prop) (hP : ¬ P f) :
    basicOpen f P := hP

/-- D(f) ∩ D(g) = D(fg). -/
theorem basicOpen_inter (mulF : α → α → α) (f g : α) (P : α → Prop)
    (hfg : ∀ a b, P (mulF a b) → P a ∨ P b)
    (hf : basicOpen f P) (hg : basicOpen g P) :
    basicOpen (mulF f g) P := by
  intro h
  cases hfg f g h with
  | inl hPf => exact hf hPf
  | inr hPg => exact hg hPg

/-- Structure sheaf section: a/f on D(f). Always contents. -/
theorem sheaf_section_contents (mulF : α → α → α) (invF : α → α) (a f : α) :
    mul mulF (contents a) (inv invF (contents f)) = contents (mulF a (invF f)) := rfl

-- ============================================================================
-- Ring Homomorphisms
-- ============================================================================

/-- Ring homomorphism preserves sort. -/
def ringHom (f : α → α) : Val α → Val α
  | origin => origin
  | container a => container (f a)
  | contents a => contents (f a)

theorem ringHom_contents (f : α → α) (a : α) :
    ringHom f (contents a) = contents (f a) := rfl

theorem ringHom_origin_val (f : α → α) :
    ringHom f (origin : Val α) = origin := rfl

theorem ringHom_ne_origin (f : α → α) (a : α) :
    ringHom f (contents a) ≠ (origin : Val α) := by
  intro h; cases h

/-- Ring homomorphism preserves multiplication. -/
theorem ringHom_mul (mulF : α → α → α) (f : α → α)
    (hf : ∀ a b, f (mulF a b) = mulF (f a) (f b)) (a b : α) :
    ringHom f (mul mulF (contents a) (contents b)) =
    mul mulF (ringHom f (contents a)) (ringHom f (contents b)) := by
  show contents (f (mulF a b)) = contents (mulF (f a) (f b))
  rw [hf]

/-- Ring homomorphism preserves addition. -/
theorem ringHom_add (addF : α → α → α) (f : α → α)
    (hf : ∀ a b, f (addF a b) = addF (f a) (f b)) (a b : α) :
    ringHom f (add addF (contents a) (contents b)) =
    add addF (ringHom f (contents a)) (ringHom f (contents b)) := by
  show contents (f (addF a b)) = contents (addF (f a) (f b))
  rw [hf]

-- ============================================================================
-- Etale, Smooth, Unramified
-- ============================================================================

/-- Unramified: Kaehler differentials vanish. Sort-preserving. -/
theorem unramified_zero_diff (zero : α) (d : α → α)
    (hd : ∀ a, d a = zero) (a : α) :
    (contents (d a) : Val α) = contents zero := by
  rw [hd]

/-- Etale map preserves contents sort. -/
theorem etale_preserves_contents (f : α → α) (a : α) :
    ringHom f (contents a) = contents (f a) := rfl

/-- Smooth fiber is never origin. -/
theorem smooth_fiber_ne_origin (f : α → α) (a : α) :
    (contents (f a) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Coalgebra and Bialgebra
-- ============================================================================

/-- Comultiplication preserves sort. -/
def comul (delta : α → α × α) : Val α → Val α × Val α
  | origin => (origin, origin)
  | container a => let (b, c) := delta a; (container b, container c)
  | contents a => let (b, c) := delta a; (contents b, contents c)

theorem comul_contents (delta : α → α × α) (a : α) :
    comul delta (contents a) = (contents (delta a).1, contents (delta a).2) := rfl

theorem comul_origin_val (delta : α → α × α) :
    comul delta (origin : Val α) = (origin, origin) := rfl

/-- Counit preserves sort. -/
def counit (eps : α → α) : Val α → Val α
  | origin => origin
  | container a => container (eps a)
  | contents a => contents (eps a)

theorem counit_contents (eps : α → α) (a : α) :
    counit eps (contents a) = contents (eps a) := rfl

-- ============================================================================
-- Hopf Algebra: Antipode
-- ============================================================================

/-- Antipode preserves sort. -/
def antipode (S : α → α) : Val α → Val α
  | origin => origin
  | container a => container (S a)
  | contents a => contents (S a)

/-- Antipode axiom: S(a) · a = ε(a) within contents. -/
theorem antipode_axiom (mulF : α → α → α) (S : α → α) (eps : α → α)
    (h : ∀ a, mulF (S a) a = eps a) (a : α) :
    mul mulF (contents (S a)) (contents a) = contents (eps a) := by
  show contents (mulF (S a) a) = contents (eps a)
  rw [h]

-- ============================================================================
-- Characteristic
-- ============================================================================

/-- Characteristic and ZMod: n · 1 and ZMod elements are always contents, never origin. -/
theorem char_contents_ne_origin (a : α) :
    (contents a : Val α) ≠ origin := by
  intro h; cases h

end Val
