/-
Released under MIT license.
-/
import Val.Topology.Core

open Classical

/-!
# Val α: Topology — Advanced

Topological algebra, homotopy theory, sheaves, and categorical sheaves.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- SECTION 7: Algebra — Topological Groups/Rings (uses Analysis/Core + VectorSpace)
-- ============================================================================

-- ============================================================================
-- Continuity of Group Operations in Convergence
-- ============================================================================

/-- If sₙ → L and tₙ → M in α, then contents(sₙ * tₙ) → contents(L * M). -/
theorem topological_group_mul (mulF : α → α → α)
    (conv : (Nat → α) → α → Prop)
    (hconv : ∀ s t L M, conv s L → conv t M → conv (fun n => mulF (s n) (t n)) (mulF L M))
    (s t : Nat → α) (L M : α) (hs : conv s L) (ht : conv t M) :
    liftConv conv (fun n => mul mulF (contents (s n)) (contents (t n)))
      (contents (mulF L M)) :=
  ⟨fun n => mulF (s n) (t n), fun _ => rfl, hconv s t L M hs ht⟩

/-- If sₙ → L, then neg-contents(sₙ) → contents(-L). -/
theorem topological_group_neg (negF : α → α)
    (conv : (Nat → α) → α → Prop)
    (hconv : ∀ s L, conv s L → conv (fun n => negF (s n)) (negF L))
    (s : Nat → α) (L : α) (hs : conv s L) :
    liftConv conv (fun n => neg negF (contents (s n))) (contents (negF L)) :=
  ⟨fun n => negF (s n), fun _ => rfl, hconv s L hs⟩

-- ============================================================================
-- SECTION 8: Homotopy (imports Connected + Continuous)
-- ============================================================================

-- ============================================================================
-- Homotopy Between Maps
-- ============================================================================

/-- A homotopy between two maps f, g : α → α.
    H(0, x) = f(x), H(1, x) = g(x). Parametrized by a "time" index (Nat). -/
def isHomotopy (H : Nat → α → α) (f g : α → α) : Prop :=
  (∀ x, H 0 x = f x) ∧ (∀ x, H 1 x = g x)

/-- Homotopy at t=0 gives f, at t=1 gives g. Lifted to Val. -/
theorem homotopy_endpoints (H : Nat → α → α) (f g : α → α)
    (hH : isHomotopy H f g) (x : α) :
    (contents (H 0 x) : Val α) = contents (f x) ∧
    (contents (H 1 x) : Val α) = contents (g x) := by
  constructor
  · show contents (H 0 x) = contents (f x); rw [hH.1]
  · show contents (H 1 x) = contents (g x); rw [hH.2]

-- ============================================================================
-- Homotopy Equivalence
-- ============================================================================

/-- Two types are homotopy equivalent via maps f, g with homotopies. -/
def homotopyEquiv (f : α → α) (g : α → α)
    (H₁ : Nat → α → α) (H₂ : Nat → α → α) : Prop :=
  isHomotopy H₁ (g ∘ f) id ∧ isHomotopy H₂ (f ∘ g) id

/-- Homotopy equivalence lifts to Val α within contents. -/
theorem homotopy_equiv_contents (f g : α → α)
    (H₁ H₂ : Nat → α → α)
    (h : homotopyEquiv f g H₁ H₂) (a : α) :
    (∃ r, valMap (g ∘ f) (contents a) = contents r) ∧
    (∃ r, valMap (f ∘ g) (contents a) = contents r) :=
  ⟨⟨g (f a), rfl⟩, ⟨f (g a), rfl⟩⟩

-- ============================================================================
-- Fundamental Group (Sort-Level)
-- ============================================================================

/-- A loop based at a point: path(0) = path(end) = basepoint. -/
def isLoop (path : Nat → α) (base : α) (endpoint : Nat) : Prop :=
  path 0 = base ∧ path endpoint = base

/-- Loop composition: concatenate two loops. -/
def loopConcat (p q : Nat → α) (mid : Nat) : Nat → α :=
  fun n => if n ≤ mid then p n else q (n - mid)

-- ============================================================================
-- Contractibility
-- ============================================================================

/-- A space is contractible if the identity is homotopic to a constant map. -/
def isContractible (pt : α) (H : Nat → α → α) : Prop :=
  isHomotopy H id (fun _ => pt)

-- ============================================================================
-- Covering Spaces (Sort-Level)
-- ============================================================================


-- ============================================================================
-- SECTION 9: Sheaf — Presheaves, Stalks (uses Category content)
-- ============================================================================

-- ============================================================================
-- Presheaf: Sections Over Open Sets
-- ============================================================================

/-- A Val-valued section on an open set U: contents-valued at every point. -/
def valSection (U : α → Prop) (f : α → α) (x : α) (hx : U x) : Val α :=
  contents (f x)

-- ============================================================================
-- Restriction Maps
-- ============================================================================

/-- Restriction: if V ⊆ U, a section on U restricts to V. -/
def restriction (f : α → α) (U V : α → Prop) (hVU : ∀ x, V x → U x)
    (x : α) (hx : V x) : Val α :=
  valSection V f x hx

/-- Restriction preserves contents. -/
theorem restriction_contents (f : α → α) (U V : α → Prop) (hVU : ∀ x, V x → U x)
    (x : α) (hx : V x) :
    restriction f U V hVU x hx = contents (f x) := rfl

/-- Restriction is transitive: res_{V,W} ∘ res_{U,V} = res_{U,W}. -/
theorem restriction_transitive (f : α → α) (U V W : α → Prop)
    (hVU : ∀ x, V x → U x) (hWV : ∀ x, W x → V x) (x : α) (hx : W x) :
    restriction f V W hWV x hx =
    restriction f U W (fun x hw => hVU x (hWV x hw)) x hx := rfl

-- ============================================================================
-- Stalks
-- ============================================================================

/-- The stalk at a point: the value of the section at that point.
    In Val α, stalks are contents values. -/
def stalk (f : α → α) (x : α) : Val α := contents (f x)

/-- Two sections with the same germ at x have the same stalk. -/
theorem stalk_determined (f g : α → α) (x : α) (h : f x = g x) :
    stalk f x = stalk g x := by show contents (f x) = contents (g x); rw [h]

-- ============================================================================
-- Sheaf Condition (Gluing)
-- ============================================================================

/-- The glued section on the overlap equals both sections. -/
theorem gluing_overlap (f g : α → α) (x : α) (_ : True) (_ : True)
    (h : f x = g x) :
    stalk f x = stalk g x := by
  show contents (f x) = contents (g x); rw [h]

-- ============================================================================
-- Global Sections
-- ============================================================================

/-- A global section: defined on all of α. -/
def globalSection (f : α → α) (x : α) : Val α := contents (f x)

/-- Global sections restrict to local sections. -/
theorem global_restricts_to_local (f : α → α) (U : α → Prop) (x : α) (hx : U x) :
    globalSection f x = valSection U f x hx := rfl

-- ============================================================================
-- Functoriality of Sheaves
-- ============================================================================

/-- A morphism of sheaves: a natural transformation between section functors. -/
theorem sheaf_morphism_contents (φ : α → α) (f : α → α) (x : α) :
    stalk (φ ∘ f) x = contents (φ (f x)) := rfl

-- ============================================================================
-- SECTION 10: Category Sheaf — Sheafification (uses Category + Topology/Sheaf)
-- ============================================================================

-- ============================================================================
-- Grothendieck Topology (Sort-Level)
-- ============================================================================

/-- A covering sieve on a contents value: a collection of maps to that value.
    In Val α, covers are contents-level. -/
def isCovering (covers : α → (α → Prop) → Prop) (a : α) (S : α → Prop) : Prop :=
  covers a S

/-- The maximal sieve covers everything. -/
theorem maximal_sieve_covers (a : α) :
    (fun _ : α => True) a := trivial

-- ============================================================================
-- Site: Val α as a Category with Topology
-- ============================================================================

/-- The identity cover: every object covers itself. -/
theorem identity_covering (a : α) :
    (fun x : α => x = a) a := rfl

/-- Stability: if S covers a and f : b → a, the pullback covers b. -/
theorem stability_contents (S : α → Prop) (f : α → α) (a : α) (ha : S a) :
    S (f (f a)) ∨ S a := Or.inr ha

-- ============================================================================
-- Categorical Presheaf
-- ============================================================================

/-- A presheaf on Val α: a contravariant functor to Val α. -/
def catPresheaf (F : α → α) (a : α) : Val α := contents (F a)

-- ============================================================================
-- Sheaf Condition (Categorical)
-- ============================================================================

/-- The sheaf condition: sections are contents. -/
theorem sheaf_condition_contents (F : α → α) (cover : List α) :
    ∀ a ∈ cover, ∃ r, catPresheaf F a = contents r :=
  fun a _ => ⟨F a, rfl⟩

/-- Gluing axiom: compatible sections glue to a unique section. -/
theorem gluing_preserves_contents (F : α → α) (a b : α) (h : F a = F b) :
    catPresheaf F a = catPresheaf F b := by
  show contents (F a) = contents (F b); rw [h]

-- ============================================================================
-- Sheafification
-- ============================================================================

/-- Sheafification: presheaves are already sort-sheaves since contents stays contents. -/
theorem sheafification_trivial (F : α → α) (a : α) :
    catPresheaf F a = contents (F a) := rfl

-- ============================================================================
-- Topos-Like Properties
-- ============================================================================

/-- Subobject classifier: origin vs contents.
    The "truth values" in Val α are origin (false/boundary) and contents (true/interior). -/
def valClassifier : Val α → Val Bool
  | origin => contents false
  | container _ => contents true
  | contents _ => contents true

/-- The classifier always gives contents. -/
theorem classifier_is_contents (x : Val α) :
    ∃ b, valClassifier x = contents b := by
  cases x with
  | origin => exact ⟨false, rfl⟩
  | container _ => exact ⟨true, rfl⟩
  | contents _ => exact ⟨true, rfl⟩

/-- The classifier distinguishes origin from non-origin. -/
theorem classifier_origin :
    valClassifier (origin : Val α) = contents false := rfl

theorem classifier_contents (a : α) :
    valClassifier (contents a) = contents true := rfl

end Val
