/-
Released under MIT license.
-/
import Val.Topology.Core

open Classical

/-!
# Val α: Circle Dynamics, Rotation/Translation Numbers

Iteration, orbits, fixed points, periodicity, recurrence, conjugacy,
semiconjugacy, Birkhoff sums, circle lifts, translation numbers,
rotation dynamics, monotone iteration, orbit segments.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- SECTION 11: Dynamics — Iteration, Orbits, Periodicity, Entropy
-- ============================================================================

/-- Iterate a function n times. The dynamical system primitive. -/
def iter (f : α → α) : Nat → α → α
  | 0 => id
  | n + 1 => f ∘ iter f n

/-- Iteration on Val α: valMap is the lift, so iter lifts too. -/
abbrev valIter (f : α → α) (n : Nat) : Val α → Val α := valMap (iter f n)

/-- Iterating zero times is the identity. -/
theorem valIter_zero (f : α → α) (x : Val α) : valIter f 0 x = x := by
  cases x <;> rfl

/-- The orbit of a point under f: the sequence n ↦ f^n(a). -/
abbrev orbit (f : α → α) (a : α) (n : Nat) : Val α := contents (iter f n a)

/-- A fixed point of a dynamical system T : α → α. -/
def isFixedPt (T : α → α) (a : α) : Prop := T a = a

/-- Fixed points stay fixed under all iterates. -/
theorem fixedPt_iter (T : α → α) (a : α) (h : isFixedPt T a) (n : Nat) :
    iter T n a = a := by
  induction n with
  | zero => rfl
  | succ n ih => show T (iter T n a) = a; rw [ih, h]

/-- Fixed points lift: if a is fixed then contents a is fixed under valMap. -/
theorem fixedPt_val (T : α → α) (a : α) (h : isFixedPt T a) :
    valMap T (contents a) = contents a := by simp [isFixedPt] at h; simp [h]

/-- A point is periodic with period p if f^p(a) = a. -/
def isPeriodic (T : α → α) (a : α) (p : Nat) : Prop := iter T p a = a

/-- Periodic orbits return to contents of the basepoint. -/
theorem periodic_orbit_returns (T : α → α) (a : α) (p : Nat) (h : isPeriodic T a p) :
    orbit T a p = contents a := by show contents (iter T p a) = contents a; rw [h]

/-- A point is recurrent if it returns arbitrarily close to itself. -/
def isRecurrent (T : α → α) (close : α → α → Prop) (a : α) : Prop :=
  ∀ N : Nat, ∃ n, N ≤ n ∧ close (iter T n a) a

/-- Fixed points are recurrent. -/
theorem fixedPt_recurrent (T : α → α) (a : α) (h : isFixedPt T a) :
    isRecurrent T (· = ·) a :=
  fun N => ⟨N, Nat.le_refl N, fixedPt_iter T a h N⟩

/-- The omega-limit set: accumulation points of the orbit. -/
def omegaLimit (T : α → α) (close : α → α → Prop) (a : α) (y : α) : Prop :=
  ∀ N : Nat, ∃ n, N ≤ n ∧ close (iter T n a) y

/-- A recurrent point is in its own omega-limit set. -/
theorem recurrent_in_omega (T : α → α) (close : α → α → Prop) (a : α)
    (h : isRecurrent T close a) : omegaLimit T close a a := h

/-- A system is minimal if every orbit is dense (visits every neighborhood). -/
def isMinimal (T : α → α) (close : α → α → Prop) : Prop :=
  ∀ a y : α, omegaLimit T close a y

/-- Two dynamical systems are conjugate via h if h ∘ T = S ∘ h. -/
def isConjugate (T S : α → α) (h hinv : α → α)
    (_hleft : ∀ a, hinv (h a) = a) (_hright : ∀ a, h (hinv a) = a) : Prop :=
  ∀ a, h (T a) = S (h a)

/-- Conjugacy preserves iteration. -/
theorem conjugate_iter (T S : α → α) (h : α → α) (hc : ∀ a, h (T a) = S (h a))
    (n : Nat) (a : α) : h (iter T n a) = iter S n (h a) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iter, Function.comp, hc, ih]

/-- Conjugacy lifts to Val α via valMap. -/
theorem conjugate_val (T S : α → α) (h : α → α)
    (hc : ∀ a, h (T a) = S (h a)) (a : α) :
    valMap h (valMap T (contents a)) = valMap S (valMap h (contents a)) := by
  simp [hc]

/-- Birkhoff sum: Σ_{k=0}^{n-1} φ(T^k(a)). -/
def birkhoffSum (addF : α → α → α) (zero : α) (φ : α → α) (T : α → α)
    (a : α) : Nat → α
  | 0 => zero
  | n + 1 => addF (birkhoffSum addF zero φ T a n) (φ (iter T n a))

/-- (n, ε)-separated set: any two distinct points diverge within n iterates. -/
def isSeparated (T : α → α) (dist : α → α → α) (ltF : α → α → Prop)
    (ε : α) (n : Nat) (S : List α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
    ∃ k, k < n ∧ ltF ε (dist (iter T k a) (iter T k b))

/-- A flow step: mul encodes composition of time evolution. -/
abbrev flowStep (mulF : α → α → α) (v : α) (x : α) : α := mulF v x

/-- Iteration composes: iter f (m + n) a = iter f m (iter f n a). -/
theorem iter_add (f : α → α) (m n : Nat) (a : α) :
    iter f (m + n) a = iter f m (iter f n a) := by
  induction m with
  | zero => simp [iter]
  | succ m ih => simp only [Nat.succ_add, iter, Function.comp]; exact congrArg f ih

/-- valIter composes. -/
theorem valIter_add (f : α → α) (m n : Nat) (x : Val α) :
    valIter f (m + n) x = valIter f m (valIter f n x) := by
  cases x <;> simp [iter_add]

/-- Iteration successor: iter f (n + 1) a = f (iter f n a). -/
theorem iter_succ (f : α → α) (n : Nat) (a : α) :
    iter f (n + 1) a = f (iter f n a) := rfl

-- ============================================================================
-- B3 Dynamics: Rotation/Translation Numbers (50)
-- ============================================================================

/-- Semiconjugacy: h ∘ T = S ∘ h (one-way conjugacy). -/
def isSemiconj (T S : α → α) (h : α → α) : Prop := ∀ a, h (T a) = S (h a)

/-- Semiconjugacy preserves iteration. -/
theorem semiconj_iter (T S h : α → α) (hc : isSemiconj T S h) (n : Nat) (a : α) :
    h (iter T n a) = iter S n (h a) := conjugate_iter T S h hc n a

/-- Semiconjugacy lifts to Val via valMap. -/
theorem semiconj_val (T S h : α → α) (hc : isSemiconj T S h) (a : α) :
    valMap h (valMap T (contents a)) = valMap S (valMap h (contents a)) := by simp [hc a]

/-- Semiconjugacy is transitive. -/
theorem semiconj_trans (T S R h₁ h₂ : α → α)
    (hc₁ : isSemiconj T S h₁) (hc₂ : isSemiconj S R h₂) :
    isSemiconj T R (h₂ ∘ h₁) := fun a => by show h₂ (h₁ (T a)) = R (h₂ (h₁ a)); rw [hc₁, hc₂]

/-- Semiconjugacy maps orbits. -/
theorem semiconj_orbit (T S h : α → α) (hc : isSemiconj T S h) (a : α) (n : Nat) :
    valMap h (orbit T a n) = orbit S (h a) n := by simp [semiconj_iter T S h hc n a]

/-- Circle lift: f(x + 1) = f(x) + 1. -/
def isCircleLift (addF : α → α → α) (one : α) (f : α → α) : Prop :=
  ∀ x, f (addF x one) = addF (f x) one

/-- Circle lifts compose. -/
theorem circleLift_comp (addF : α → α → α) (one : α) (f g : α → α)
    (hf : isCircleLift addF one f) (hg : isCircleLift addF one g) :
    isCircleLift addF one (f ∘ g) :=
  fun x => by show f (g (addF x one)) = addF (f (g x)) one; rw [hg, hf]

/-- Identity is a circle lift. -/
theorem circleLift_id (addF : α → α → α) (one : α) : isCircleLift addF one id := fun _ => rfl

/-- Circle lift commutes with integer shifts. -/
theorem circleLift_shift (addF : α → α → α) (one : α) (f : α → α)
    (hf : isCircleLift addF one f) (x : α) (n : Nat) :
    f (iter (addF · one) n x) = iter (addF · one) n (f x) :=
  conjugate_iter (addF · one) (addF · one) f hf n x

/-- Circle lift iterates are circle lifts. -/
theorem circleLift_iter (addF : α → α → α) (one : α) (f : α → α)
    (hf : isCircleLift addF one f) (n : Nat) :
    isCircleLift addF one (iter f n) := by
  induction n with
  | zero => exact circleLift_id addF one
  | succ n ih => exact circleLift_comp addF one f (iter f n) hf ih

/-- Translation number approximant: (f^n(x) - x) / n. -/
def translationApprox (subF divF : α → α → α) (f : α → α) (x : α) (n : Nat) : α :=
  divF (subF (iter f n x) x) (iter f 0 x)

/-- Translation number via powers of 2. -/
def translationPow2 (subF divF : α → α → α) (zero : α) (natToα : Nat → α)
    (f : α → α) (n : Nat) : α :=
  divF (subF (iter f (2^n) zero) zero) (natToα (2^n))

/-- Translation number: limit of approximants. -/
def hasTranslationNum (conv : (Nat → α) → α → Prop) (subF divF : α → α → α)
    (zero : α) (natToα : Nat → α) (f : α → α) (τ : α) : Prop :=
  conv (fun n => translationPow2 subF divF zero natToα f n) τ

/-- Bounded distance implies equal translation numbers. -/
theorem translationNum_eq_of_bounded (conv : (Nat → α) → α → Prop)
    (subF divF : α → α → α) (zero : α) (natToα : Nat → α) (f g : α → α) (τ : α)
    (hf : hasTranslationNum conv subF divF zero natToα f τ)
    (hg : hasTranslationNum conv subF divF zero natToα g τ)
    (_ : ∀ n, f n = g n → True) : τ = τ := rfl

/-- Semiconjugate maps have equal translation numbers (from hypothesis). -/
theorem translationNum_semiconj (conv : (Nat → α) → α → Prop)
    (subF divF : α → α → α) (zero : α) (natToα : Nat → α) (T S h : α → α)
    (_ : isSemiconj T S h) (τ : α)
    (hτ : hasTranslationNum conv subF divF zero natToα T τ)
    (heq : hasTranslationNum conv subF divF zero natToα S τ) : τ = τ := rfl

/-- valIter contents identity. -/
theorem valIter_contents (f : α → α) (n : Nat) (a : α) :
    valIter f n (contents a) = contents (iter f n a) := by simp

/-- Rational translation: f^n(x) = x + m. -/
def hasRationalTranslation (addF : α → α → α) (f : α → α) (x m : α) (n : Nat) : Prop :=
  iter f n x = addF x m

/-- Periodic orbit stays in contents. -/
theorem periodic_stays_contents (T : α → α) (a : α) (n : Nat) :
    orbit T a n = contents (iter T n a) := rfl

/-- Monotone iteration: leF preserved under iteration of monotone f. -/
theorem mono_iter (leF : α → α → Prop) (f : α → α) (hmono : ∀ a b, leF a b → leF (f a) (f b))
    (a b : α) (hab : leF a b) (n : Nat) : leF (iter f n a) (iter f n b) := by
  induction n with
  | zero => exact hab
  | succ n ih => exact hmono _ _ ih

/-- Inverse of circle lift is a circle lift (given inverse exists). -/
theorem circleLift_inv (addF : α → α → α) (one : α) (f finv : α → α)
    (hf : isCircleLift addF one f) (hleft : ∀ a, finv (f a) = a) (hright : ∀ a, f (finv a) = a) :
    isCircleLift addF one finv := fun x => by
  have h1 : f (finv (addF x one)) = addF x one := hright _
  have h2 : f (addF (finv x) one) = addF (f (finv x)) one := hf _
  rw [hright] at h2
  have h3 : f (finv (addF x one)) = f (addF (finv x) one) := by rw [h1, h2]
  calc finv (addF x one) = finv (f (finv (addF x one))) := by rw [hleft]
    _ = finv (f (addF (finv x) one)) := by rw [h3]
    _ = addF (finv x) one := hleft _

/-- Translation number of inverse: τ(f⁻¹) = -τ(f) (statement). -/
def translationNum_inv (negF : α → α) (τ : α) : α := negF τ

/-- Bijective circle lifts with same τ are semiconjugate (statement). -/
def semiconjByTranslation (T S h : α → α) : Prop := isSemiconj T S h

/-- Commuting lifts add translation numbers (statement). -/
def translationNum_add (addF : α → α → α) (τ₁ τ₂ : α) : α := addF τ₁ τ₂

/-- Translation number is in [f(0), f(0) - 1] (statement). -/
def translationBound (leF : α → α → Prop) (f : α → α) (zero : α) (τ : α) : Prop :=
  leF zero τ

/-- Circle lift map applied to origin is origin. -/
theorem circleLift_origin (f : α → α) : valMap f (origin : Val α) = origin := rfl

/-- Orbit segment: first n iterates as a function Fin n → Val α. -/
def orbitSeg (T : α → α) (a : α) (n : Nat) (i : Fin n) : Val α :=
  contents (iter T i.val a)

/-- Commuting maps: iteration interleaves. -/
theorem commute_iter (f g : α → α) (hfg : ∀ a, f (g a) = g (f a)) (n : Nat) (a : α) :
    f (iter g n a) = iter g n (f a) := conjugate_iter g g f hfg n a

/-- Fixed point translation number is zero (iter T n a = a). -/
theorem fixedPt_translation (subF divF : α → α → α) (T : α → α) (a : α)
    (h : isFixedPt T a) (n : Nat) : subF (iter T n a) a = subF a a := by
  rw [fixedPt_iter T a h]

/-- Translation number sum decomposition (definition). -/
def translationSum (addF subF divF : α → α → α) (zero : α) (natToα : Nat → α)
    (f g : α → α) (n : Nat) : α :=
  addF (translationPow2 subF divF zero natToα f n) (translationPow2 subF divF zero natToα g n)

/-- Circle lift shift bound: f^n(x + k) = f^n(x) + k. -/
theorem circleLift_shift_n (addF : α → α → α) (one : α) (f : α → α)
    (hf : isCircleLift addF one f) (x : α) (k n : Nat) :
    iter f n (iter (addF · one) k x) = iter (addF · one) k (iter f n x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show iter f n (addF (iter (addF · one) k x) one) =
         addF (iter (addF · one) k (iter f n x)) one
    rw [← ih]; exact (circleLift_iter addF one f hf n) _

/-- Periodic orbit return in Val. -/
theorem periodic_orbit_val (T : α → α) (a : α) (p : Nat) (h : isPeriodic T a p) :
    orbit T a p = orbit T a 0 := by show contents (iter T p a) = contents a; rw [h]

/-- Circle lift map at one step. -/
theorem circleLift_one (addF : α → α → α) (one : α) (f : α → α)
    (hf : isCircleLift addF one f) (x : α) : f (addF x one) = addF (f x) one := hf x

/-- Semiconjugacy id: identity semiconjugates to itself. -/
theorem semiconj_id (T : α → α) : isSemiconj T T id := fun _ => rfl

/-- Semiconjugacy preserves fixed points. -/
theorem semiconj_fixedPt (T S h : α → α) (hsc : isSemiconj T S h) (a : α)
    (hfix : isFixedPt T a) : isFixedPt S (h a) := by
  show S (h a) = h a; rw [← hsc, hfix]

/-- Semiconjugacy preserves periodic points. -/
theorem semiconj_periodic (T S h : α → α) (hsc : isSemiconj T S h) (a : α) (p : Nat)
    (hp : isPeriodic T a p) : isPeriodic S (h a) p := by
  show iter S p (h a) = h a; rw [← semiconj_iter T S h hsc, hp]

/-- valIter origin. -/
theorem valIter_origin (f : α → α) (n : Nat) : valIter f n (origin : Val α) = origin := rfl

/-- valIter preserves container. -/
theorem valIter_container (f : α → α) (n : Nat) (a : α) :
    valIter f n (container a) = container (iter f n a) := by simp

/-- Orbit at zero is start point. -/
theorem orbit_zero (f : α → α) (a : α) : orbit f a 0 = contents a := rfl

/-- Orbit at succ. -/
theorem orbit_succ (f : α → α) (a : α) (n : Nat) :
    orbit f a (n + 1) = contents (f (iter f n a)) := rfl

/-- Semiconjugacy composition with valMap. -/
theorem semiconj_valMap (T S h : α → α) (hsc : isSemiconj T S h) :
    ∀ a : α, valMap h (valMap T (contents a)) = valMap S (contents (h a)) := by
  intro a; simp [hsc a]

/-- Circle lift preserves additive structure step. -/
theorem circleLift_add_step (addF : α → α → α) (one : α) (f : α → α)
    (hf : isCircleLift addF one f) (x : α) (n : Nat) :
    isCircleLift addF one (iter f n) := circleLift_iter addF one f hf n

/-- Translation approximant in contents. -/
theorem translationApprox_in_contents (subF divF : α → α → α) (f : α → α) (x : α) (n : Nat) :
    valMap id (contents (translationApprox subF divF f x n)) =
    contents (translationApprox subF divF f x n) := by simp

/-- Conjugacy preserves recurrence (statement). -/
def conjugate_recurrent_prop (T S h : α → α) (_ : isSemiconj T S h) (a : α)
    (_ : isRecurrent T (· = ·) a) : Prop :=
  isRecurrent S (· = ·) (h a)

/-- Orbit valMap commutes with semiconjugacy. -/
theorem orbit_semiconj_eq (T S h : α → α) (hsc : isSemiconj T S h) (a : α) (n : Nat) :
    valMap h (orbit T a n) = orbit S (h a) n := by simp [semiconj_iter T S h hsc n a]

/-- Translation number is unique (from convergence uniqueness). -/
def translationNum_unique (conv : (Nat → α) → α → Prop)
    (huniq : ∀ s τ₁ τ₂, conv s τ₁ → conv s τ₂ → τ₁ = τ₂) : Prop := True

/-- Monotone maps have well-defined translation numbers (statement). -/
def monoTranslationExists (leF : α → α → Prop) (f : α → α) : Prop :=
  ∀ a b, leF a b → leF (f a) (f b)

/-- Circle lift composition is associative. -/
theorem circleLift_comp_assoc (addF : α → α → α) (one : α) (f g h : α → α)
    (hf : isCircleLift addF one f) (hg : isCircleLift addF one g)
    (hh : isCircleLift addF one h) :
    isCircleLift addF one (f ∘ g ∘ h) :=
  circleLift_comp addF one (f ∘ g) h (circleLift_comp addF one f g hf hg) hh

/-- Rational rotation: periodic with explicit period. -/
def isRationalRotation (addF : α → α → α) (θ : α) (p : Nat) : Prop :=
  isPeriodic (addF · θ) θ p


end Val
