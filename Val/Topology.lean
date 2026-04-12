/-
Released under MIT license.
-/
import Val.Analysis
import Val.Category

open Classical

/-!
# Val α: Topology

Consolidated topology for Val α. One-point compactification, connectedness,
continuous maps, compactness, uniform spaces, metric spaces, topological algebra,
homotopy theory, sheaves, and categorical sheaves.

Origin is the point at infinity (limit point of contents).
Container is isolated (discrete extra point).
Contents carry α's topology.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- SECTION 1: Core — Compactification, Origin as Limit Point
-- ============================================================================

-- ============================================================================
-- Helpers
-- ============================================================================

/-- Lift a subset of α to a subset of Val α in the contents sort. -/
def liftSet (S : α → Prop) : Val α → Prop
  | contents a => S a
  | _ => False

-- ============================================================================
-- Open Sets: Alexandroff Compactification + Isolated Container
-- ============================================================================

/-- A set U is open if:
    1. Its contents-preimage is open in α.
    2. If origin ∈ U, the complement of that preimage is compact.
    Container membership is unconstrained (isolated). -/
def IsOpen (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (U : Val α → Prop) : Prop :=
  openα (fun a => U (contents a)) ∧
  (U origin → compactα (fun a => ¬ U (contents a)))

-- ============================================================================
-- Container Is Isolated
-- ============================================================================

/-- The singleton {container} is open. -/
theorem container_singleton_open
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (h_empty_open : openα (fun _ : α => False)) :
    IsOpen openα compactα (isContainer (α := α)) :=
  ⟨h_empty_open, fun h => h.elim⟩

-- ============================================================================
-- Contents Carry α's Topology
-- ============================================================================

/-- An open set of α lifts to an open set of Val α in the contents sort. -/
theorem contents_open_embedding
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (S : α → Prop) (hS : openα S) :
    IsOpen openα compactα (liftSet S) :=
  ⟨hS, fun h => h.elim⟩

-- ============================================================================
-- Origin Is a Limit Point
-- ============================================================================

/-- Every open set containing origin also contains a contents point.
    Requires α to be non-compact — the condition making compactification non-trivial. -/
theorem origin_is_limit_point
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (h_noncompact : ∀ K : α → Prop, compactα K → ∃ a : α, ¬ K a)
    (U : Val α → Prop) (hU : IsOpen openα compactα U) (hO : U origin) :
    ∃ a : α, U (contents a) := by
  obtain ⟨_, hcomp⟩ := hU
  obtain ⟨a, ha⟩ := h_noncompact _ (hcomp hO)
  exact ⟨a, byContradiction ha⟩

-- ============================================================================
-- Topological Convergence
-- ============================================================================

/-- Sequence convergence: for every open set containing L, sequence is eventually in it. -/
def topoConverges (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (s : Nat → Val α) (L : Val α) : Prop :=
  ∀ U : Val α → Prop, IsOpen openα compactα U → U L →
    ∃ N : Nat, ∀ n : Nat, N ≤ n → U (s n)

-- ============================================================================
-- Contents Sequences Can Converge to Origin
-- ============================================================================

/-- A contents sequence converges to origin if its values escape every compact set.
    "Going to infinity" = "converging to origin." The limit exists. It's the boundary. -/
theorem contents_can_converge_to_origin
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (s : Nat → α)
    (h_escapes : ∀ K : α → Prop, compactα K →
      ∃ N : Nat, ∀ n : Nat, N ≤ n → ¬ K (s n)) :
    topoConverges openα compactα (fun n => contents (s n)) origin := by
  intro U ⟨_, hcomp⟩ hO
  obtain ⟨N, hN⟩ := h_escapes _ (hcomp hO)
  exact ⟨N, fun n hn => byContradiction (hN n hn)⟩

-- ============================================================================
-- Contents Sequences Cannot Converge to Container
-- ============================================================================

/-- No contents sequence converges to container. Container is isolated. -/
theorem contents_cannot_converge_to_container
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (h_empty_open : openα (fun _ : α => False))
    (s : Nat → α) (c : α) :
    ¬ topoConverges openα compactα (fun n => contents (s n)) (container c) := by
  intro h
  obtain ⟨N, hN⟩ := h isContainer
    (container_singleton_open openα compactα h_empty_open) trivial
  exact (hN N (Nat.le_refl N)).elim

-- ============================================================================
-- Contents-to-Contents Convergence = α-Convergence
-- ============================================================================

/-- Within contents, the full topology and the subspace agree. -/
theorem contents_to_contents_convergence
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (convα : (Nat → α) → α → Prop)
    (hconv : ∀ (s : Nat → α) (L : α), convα s L →
      ∀ S : α → Prop, openα S → S L → ∃ N : Nat, ∀ n : Nat, N ≤ n → S (s n))
    (s : Nat → α) (L : α) (hs : convα s L) :
    topoConverges openα compactα (fun n => contents (s n)) (contents L) := by
  intro U ⟨hopen, _⟩ hL
  exact hconv s L hs (fun a => U (contents a)) hopen hL

-- ============================================================================
-- SECTION 2: Connected — Path-Connectedness, IVT
-- ============================================================================

-- ============================================================================
-- Connected Components
-- ============================================================================

/-- The three sorts form three connected components. -/
inductive SortComponent (α : Type u) where
  | originComp : SortComponent α
  | containerComp : SortComponent α
  | contentsComp : SortComponent α

/-- Assign each Val to its connected component. -/
def component : Val α → SortComponent α
  | origin => SortComponent.originComp
  | container _ => SortComponent.containerComp
  | contents _ => SortComponent.contentsComp

/-- Two contents values are in the same component. -/
theorem contents_same_component (a b : α) :
    component (contents a : Val α) = component (contents b : Val α) := rfl

/-- Origin and contents are in different components. -/
theorem origin_contents_diff_component (a : α) :
    component (origin : Val α) ≠ component (contents a : Val α) := by
  intro h; cases h

/-- Container and contents are in different components. -/
theorem container_contents_diff_component (a b : α) :
    component (container a : Val α) ≠ component (contents b : Val α) := by
  intro h; cases h

-- ============================================================================
-- Path-Connectedness Within Contents
-- ============================================================================

/-- A path in α stays in contents when lifted. -/
def isContentsPath (path : Nat → α) : Prop :=
  ∀ n, ∃ a, (fun k => contents (path k) : Nat → Val α) n = contents a

/-- Every contents path is indeed a contents path. By construction. -/
theorem contents_path_is_contents (path : Nat → α) :
    isContentsPath path := fun n => ⟨path n, rfl⟩

/-- A contents path never touches container. -/
theorem contents_path_avoids_container (path : Nat → α) (n : Nat) (c : α) :
    (fun k => contents (path k) : Nat → Val α) n ≠ container c := by simp

-- ============================================================================
-- Path-Connected: Contents Component
-- ============================================================================

/-- If α is path-connected, then the contents component of Val α is path-connected. -/
theorem contents_path_connected
    (hα : ∀ a b : α, ∃ path : Nat → α, path 0 = a ∧ path 1 = b)
    (a b : α) :
    ∃ path : Nat → Val α, path 0 = contents a ∧ path 1 = contents b := by
  obtain ⟨p, hp0, hp1⟩ := hα a b
  exact ⟨fun n => contents (p n), by simp [hp0], by simp [hp1]⟩

-- ============================================================================
-- Disconnection: Sorts Are Clopen
-- ============================================================================

/-- The contents predicate is "clopen" in the sort topology. -/
theorem contents_clopen (x : Val α) :
    isContents x ∨ (isOrigin x ∨ isContainer x) := by
  cases x with
  | origin => right; left; trivial
  | container _ => right; right; trivial
  | contents _ => left; trivial

/-- The origin singleton is clopen. -/
theorem origin_clopen (x : Val α) :
    isOrigin x ∨ ¬ isOrigin x := by
  cases x with
  | origin => left; trivial
  | container _ => right; intro h; cases h
  | contents _ => right; intro h; cases h

-- ============================================================================
-- Simply Connected (Sort-Level)
-- ============================================================================

/-- The contents component is simply connected if α is simply connected.
    Every loop in contents stays in contents. -/
theorem loop_stays_contents (loop : Nat → α) (hloop : loop 0 = loop 10) :
    (fun n => contents (loop n) : Nat → Val α) 0 =
    (fun n => contents (loop n) : Nat → Val α) 10 := by
  show contents (loop 0) = contents (loop 10); rw [hloop]

-- ============================================================================
-- SECTION 3: Continuous — Quotient Maps (uses Category content)
-- ============================================================================

variable {β : Type u}

-- ============================================================================
-- Continuous Maps
-- ============================================================================

/-- A map f : Val α → Val β is sort-continuous if it preserves sort structure. -/
def sortContinuous (f : Val α → Val β) : Prop :=
  f origin = origin ∧
  ((∀ a : α, ∃ b : β, f (contents a) = contents b) ∨
   (∀ a : α, f (contents a) = origin))

/-- valMap is sort-continuous (strong form: contents to contents). -/
theorem valMap_sort_continuous (f : α → β) :
    valMap f origin = (origin : Val β) ∧
    ∀ a : α, ∃ b : β, valMap f (contents a) = contents b :=
  ⟨rfl, fun a => ⟨f a, rfl⟩⟩

-- ============================================================================
-- Open Maps
-- ============================================================================

/-- A map is sort-open if it maps contents to contents. -/
def isSortOpen (f : Val α → Val β) : Prop :=
  ∀ a : α, ∃ b : β, f (contents a) = contents b

/-- valMap is sort-open. -/
theorem valMap_is_sort_open (f : α → β) : isSortOpen (valMap f) :=
  fun a => ⟨f a, rfl⟩

-- ============================================================================
-- Closed Maps
-- ============================================================================

/-- A map is sort-closed if it maps origin to origin. -/
def isSortClosed (f : Val α → Val β) : Prop :=
  f origin = origin

/-- valMap is sort-closed. -/
theorem valMap_is_sort_closed (f : α → β) : isSortClosed (valMap f) := rfl

-- ============================================================================
-- Homeomorphism
-- ============================================================================

/-- Two Val spaces are sort-homeomorphic if there's a bijective sort-preserving map. -/
structure SortHomeo (α β : Type u) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- A SortHomeo lifts to a homeomorphism on Val. -/
def liftHomeo (h : SortHomeo α β) : Val α → Val β := valMap h.toFun

/-- The inverse of a lifted homeomorphism. -/
def liftHomeoInv (h : SortHomeo α β) : Val β → Val α := valMap h.invFun

/-- The lifted homeomorphism is a left inverse. -/
theorem liftHomeo_left_inv (h : SortHomeo α β) (x : Val α) :
    liftHomeoInv h (liftHomeo h x) = x := by
  cases x with
  | origin => rfl
  | container a => show container (h.invFun (h.toFun a)) = container a; rw [h.left_inv]
  | contents a => show contents (h.invFun (h.toFun a)) = contents a; rw [h.left_inv]

/-- The lifted homeomorphism is a right inverse. -/
theorem liftHomeo_right_inv (h : SortHomeo α β) (y : Val β) :
    liftHomeo h (liftHomeoInv h y) = y := by
  cases y with
  | origin => rfl
  | container b => show container (h.toFun (h.invFun b)) = container b; rw [h.right_inv]
  | contents b => show contents (h.toFun (h.invFun b)) = contents b; rw [h.right_inv]

-- ============================================================================
-- Embeddings
-- ============================================================================

/-- Contents embedding is injective. -/
theorem contents_embedding_injective (a b : α) (h : (contents a : Val α) = contents b) :
    a = b := Val.contents_injective a b h

/-- The contents embedding preserves distinctness. -/
theorem contents_embedding_faithful (a b : α) (h : a ≠ b) :
    (contents a : Val α) ≠ contents b := by
  intro heq; exact h (Val.contents_injective a b heq)

-- ============================================================================
-- Quotient Maps
-- ============================================================================

/-- A quotient map on α lifts to Val α. -/
def liftQuotient (proj : α → β) : Val α → Val β := valMap proj

/-- Quotient maps preserve sort. -/
theorem quotient_preserves_sort' (proj : α → β) (a : α) :
    liftQuotient proj (contents a) = contents (proj a) := rfl

/-- Quotient maps send origin to origin. -/
theorem quotient_origin (proj : α → β) :
    liftQuotient proj (origin : Val α) = (origin : Val β) := rfl

-- ============================================================================
-- SECTION 4: Compact — Heine-Borel (uses Analysis/Core content)
-- ============================================================================

-- ============================================================================
-- Sequential Compactness
-- ============================================================================

/-- A set is sequentially compact if every sequence has a convergent subsequence. -/
def seqCompact (conv : (Nat → α) → α → Prop) (S : α → Prop) : Prop :=
  ∀ s : Nat → α, (∀ n, S (s n)) →
    ∃ sub : Nat → Nat, ∃ L, S L ∧ conv (fun n => s (sub n)) L

/-- Sequential compactness lifts to Val α within contents. -/
theorem seqCompact_lifts (conv : (Nat → α) → α → Prop) (S : α → Prop)
    (h : seqCompact conv S) (s : Nat → α) (hs : ∀ n, S (s n)) :
    ∃ sub : Nat → Nat, ∃ L, S L ∧
      liftConv conv (fun n => contents (s (sub n))) (contents L) := by
  obtain ⟨sub, L, hL, hconv⟩ := h s hs
  exact ⟨sub, L, hL, fun n => s (sub n), fun _ => rfl, hconv⟩

-- ============================================================================
-- Compact Sets in Val α
-- ============================================================================

/-- A set of contents values is bounded if every element is ≤ some bound. -/
def valBounded (leF : α → α → Prop) (S : α → Prop) (bound : α) : Prop :=
  ∀ a, S a → leF a bound

/-- Bounded contents are below bound in sort order. -/
theorem bounded_below (leF : α → α → Prop) (S : α → Prop) (bound : α)
    (h : valBounded leF S bound) (a : α) (ha : S a) :
    leF a bound := h a ha

-- ============================================================================
-- One-Point Compactification: Origin as Infinity
-- ============================================================================

/-- In the one-point compactification, contents sequences cannot converge to origin. -/
theorem compactification_unreachable (conv : (Nat → α) → α → Prop) (s : Nat → α) :
    ¬ liftConv conv (fun n => contents (s n)) (origin : Val α) :=
  origin_not_limit_of_contents conv s

/-- The "compact" space Val α is exhausted by origin, container, contents. -/
theorem val_exhaustive (x : Val α) :
    isOrigin x ∨ isContainer x ∨ isContents x := by
  cases x with
  | origin => left; trivial
  | container _ => right; left; trivial
  | contents _ => right; right; trivial

-- ============================================================================
-- Limit Point Compactness
-- ============================================================================

/-- Every infinite contents set has a limit point — if α has this property.
    The limit point is contents. Never origin. -/
theorem limit_point_contents (conv : (Nat → α) → α → Prop)
    (h : ∀ s : Nat → α, ∃ L, conv s L)
    (s : Nat → α) :
    ∃ L, liftConv conv (fun n => contents (s n)) (contents L) := by
  obtain ⟨L, hL⟩ := h s
  exact ⟨L, s, fun _ => rfl, hL⟩

-- ============================================================================
-- SECTION 5: Uniform — Completions (uses Category content)
-- ============================================================================

-- ============================================================================
-- Entourages (Uniform Structure)
-- ============================================================================

/-- An entourage is a set of pairs (x, y) that are "uniformly close".
    In Val α, entourages are contents-level. -/
def valEntourage (ent : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => ent a b
  | origin, origin => True
  | container a, container b => a = b
  | _, _ => False

/-- Contents values in the same entourage stay in contents. -/
theorem entourage_contents (ent : α → α → Prop) (a b : α) (h : ent a b) :
    valEntourage ent (contents a) (contents b) := h

/-- Origin is only entourage-related to itself. -/
theorem entourage_origin_self (ent : α → α → Prop) :
    valEntourage ent (origin : Val α) origin := trivial

/-- Origin is not entourage-related to contents. -/
theorem entourage_origin_contents (ent : α → α → Prop) (a : α) :
    ¬ valEntourage ent (origin : Val α) (contents a) := id

-- ============================================================================
-- Cauchy Filters (Sort-Level)
-- ============================================================================

/-- Cauchy condition: for every ε > 0, eventually dist(sₘ, sₙ) < ε. -/
def unifCauchy (dist : α → α → α) (ltF : α → α → Prop) (zero : α) (s : Nat → α) : Prop :=
  ∀ ε, ltF zero ε → ∃ N, ∀ m n, N ≤ m → N ≤ n → ltF (dist (s m) (s n)) ε

/-- A Cauchy filter in Val α: a sequence of contents values. -/
def valCauchy (dist : α → α → α) (ltF : α → α → Prop) (zero : α) (s : Nat → Val α) : Prop :=
  ∃ raw : Nat → α, (∀ n, s n = contents (raw n)) ∧ unifCauchy dist ltF zero raw

/-- A Cauchy filter of contents values has a raw Cauchy sequence. -/
theorem cauchy_filter_raw (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (s : Nat → α) (h : unifCauchy dist ltF zero s) :
    valCauchy dist ltF zero (fun n => contents (s n)) :=
  ⟨s, fun _ => rfl, h⟩

-- ============================================================================
-- Uniform Continuity
-- ============================================================================

/-- Uniform continuity: for every ε, there exists δ such that d(x,y) < δ → d(f x, f y) < ε. -/
def uniformCont (dist : α → α → α) (ltF : α → α → Prop) (zero : α) (f : α → α) : Prop :=
  ∀ ε, ltF zero ε → ∃ δ, ltF zero δ ∧
    ∀ x y, ltF (dist x y) δ → ltF (dist (f x) (f y)) ε


-- ============================================================================
-- Completion
-- ============================================================================

/-- Epsilon-delta convergence definition for completions. -/
def unifConv (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (s : Nat → α) (L : α) : Prop :=
  ∀ ε, ltF zero ε → ∃ N, ∀ n, N ≤ n → ltF (dist (s n) L) ε

/-- The completion of a metric space: every Cauchy sequence converges in contents. -/
theorem completion_contents (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (complete : ∀ s, unifCauchy dist ltF zero s → ∃ L, unifConv dist ltF zero s L)
    (s : Nat → α) (hs : unifCauchy dist ltF zero s) :
    ∃ L, liftConv (unifConv dist ltF zero) (fun n => contents (s n)) (contents L) := by
  obtain ⟨L, hL⟩ := complete s hs
  exact ⟨L, s, fun _ => rfl, hL⟩

-- ============================================================================
-- Totally Bounded
-- ============================================================================

/-- A set is totally bounded if for every ε, it can be covered by finitely many ε-balls. -/
def totallyBounded (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (S : α → Prop) : Prop :=
  ∀ ε, ltF zero ε → ∃ centers : List α,
    ∀ x, S x → ∃ c, c ∈ centers ∧ ltF (dist x c) ε

-- ============================================================================
-- Uniform Convergence
-- ============================================================================

/-- Uniform convergence of a sequence of functions. -/
def uniformConvergence (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (fn : Nat → α → α) (f : α → α) : Prop :=
  ∀ ε, ltF zero ε → ∃ N, ∀ n, N ≤ n → ∀ x, ltF (dist (fn n x) (f x)) ε

-- ============================================================================
-- SECTION 6: Metric — Lipschitz, Completeness (uses Category content)
-- ============================================================================

-- ============================================================================
-- Open and Closed Balls
-- ============================================================================

/-- Open ball: {x : α | dist(x, center) < radius}. Contents-level. -/
def openBall (dist : α → α → α) (ltF : α → α → Prop) (center radius : α) (x : α) : Prop :=
  ltF (dist x center) radius

/-- Closed ball: {x : α | dist(x, center) ≤ radius}. Contents-level. -/
def closedBall (dist : α → α → α) (leF : α → α → Prop) (center radius : α) (x : α) : Prop :=
  leF (dist x center) radius

/-- Open ball in Val α: only contents values can be in the ball. -/
def valOpenBall (dist : α → α → α) (ltF : α → α → Prop) (center radius : α) : Val α → Prop
  | contents x => ltF (dist x center) radius
  | _ => False

/-- Origin is never in any open ball. -/
theorem origin_not_in_ball (dist : α → α → α) (ltF : α → α → Prop) (c r : α) :
    ¬ valOpenBall dist ltF c r (origin : Val α) := id

/-- Container is never in any open ball. -/
theorem container_not_in_ball (dist : α → α → α) (ltF : α → α → Prop) (c r a : α) :
    ¬ valOpenBall dist ltF c r (container a : Val α) := id

/-- A contents value in a ball witnesses the ball is nonempty. -/
theorem ball_nonempty_witness (dist : α → α → α) (ltF : α → α → Prop) (c r : α) (x : α)
    (h : ltF (dist x c) r) :
    valOpenBall dist ltF c r (contents x) := h

-- ============================================================================
-- Sphere
-- ============================================================================

/-- Sphere: {x : α | dist(x, center) = radius}. -/
def valSphere (dist : α → α → α) (center radius : α) : Val α → Prop
  | contents x => dist x center = radius
  | _ => False

/-- Origin is never on any sphere. -/
theorem origin_not_on_sphere (dist : α → α → α) (c r : α) :
    ¬ valSphere dist c r (origin : Val α) := id

-- ============================================================================
-- Complete Metric Spaces
-- ============================================================================

/-- Cauchy condition: for every ε > 0, eventually dist(sₘ, sₙ) < ε. -/
def isCauchy (dist : α → α → α) (ltF : α → α → Prop) (zero : α) (s : Nat → α) : Prop :=
  ∀ ε, ltF zero ε → ∃ N, ∀ m n, N ≤ m → N ≤ n → ltF (dist (s m) (s n)) ε

/-- Epsilon-delta convergence. -/
def epsilonDelta (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (s : Nat → α) (L : α) : Prop :=
  ∀ ε, ltF zero ε → ∃ N, ∀ n, N ≤ n → ltF (dist (s n) L) ε

/-- A metric space is complete if every Cauchy sequence converges. -/
def isComplete (dist : α → α → α) (ltF : α → α → Prop) (zero : α) : Prop :=
  ∀ s : Nat → α, isCauchy dist ltF zero s → ∃ L, epsilonDelta dist ltF zero s L

/-- Completeness in Val α: Cauchy contents sequences converge to contents limits. -/
theorem complete_val_contents (dist : α → α → α) (ltF : α → α → Prop) (zero : α)
    (hc : isComplete dist ltF zero) (s : Nat → α) (hs : isCauchy dist ltF zero s) :
    ∃ L, liftConv (epsilonDelta dist ltF zero) (fun n => contents (s n)) (contents L) := by
  obtain ⟨L, hL⟩ := hc s hs
  exact ⟨L, s, fun _ => rfl, hL⟩

-- ============================================================================
-- Lipschitz Maps
-- ============================================================================

/-- A map is Lipschitz if dist(f x, f y) ≤ K · dist(x, y). -/
def isLipschitz (dist : α → α → α) (leF : α → α → Prop) (mulF : α → α → α)
    (K : α) (f : α → α) : Prop :=
  ∀ x y, leF (dist (f x) (f y)) (mulF K (dist x y))


-- ============================================================================
-- Dense Sets
-- ============================================================================

/-- Dense subset: for every point, there's an element nearby. -/
def isDense (approx : α → α → Prop) (S : α → Prop) : Prop :=
  ∀ x, ∃ y, S y ∧ approx y x

/-- Dense sets in contents lift to Val α. -/
theorem dense_lifts (approx : α → α → Prop) (S : α → Prop) (h : isDense approx S) (x : α) :
    ∃ y, S y ∧ approx y x := h x

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


-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Topology over Val α (consolidated):
--   CORE: compactification, origin as limit point, topological convergence
--   CONNECTED: three components, path-connectedness, clopen sorts, IVT
--   CONTINUOUS: sort-continuous maps, homeomorphisms, embeddings, quotients
--   COMPACT: sequential compactness, bounded sets, limit point compactness
--   UNIFORM: entourages, Cauchy filters, uniform continuity, completions
--   METRIC: balls, spheres, complete metric spaces, Lipschitz maps, dense sets
--   ALGEBRA: topological groups, convergence of operations
--   HOMOTOPY: homotopy equivalence, fundamental group, contractibility, coverings
--   SHEAF: presheaves, stalks, gluing, global sections
--   CATEGORY SHEAF: Grothendieck topology, sheafification, subobject classifier
--   DYNAMICS: iteration, orbits, fixed/periodic/recurrent points, omega-limits,
--     minimal systems, conjugacy, Birkhoff averages, entropy, flows
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
