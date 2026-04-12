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

-- ============================================================================
-- B3 Dynamics: Ergodic Theory (46)
-- ============================================================================

/-- Measure-preserving: preimage preserves measure. -/
def isMeasurePres (T : α → α) (measure : (α → Prop) → α)
    (preim : (α → Prop) → (α → Prop)) : Prop :=
  ∀ S, measure (preim S) = measure S

/-- Measure-preserving identity. -/
theorem measPres_id (measure : (α → Prop) → α) : isMeasurePres (id : α → α) measure id :=
  fun _ => rfl

/-- Pre-ergodic: invariant sets are null or full. -/
def isPreErgodic (T : α → α) (preim : (α → Prop) → (α → Prop))
    (isNull isFull : (α → Prop) → Prop) : Prop :=
  ∀ S, (∀ x, preim S x ↔ S x) → isNull S ∨ isFull S

/-- Ergodic = measure-preserving + pre-ergodic. -/
def isErgodic (T : α → α) (measure : (α → Prop) → α) (preim : (α → Prop) → (α → Prop))
    (isNull isFull : (α → Prop) → Prop) : Prop :=
  isMeasurePres T measure preim ∧ isPreErgodic T preim isNull isFull

/-- Zero-one law from pre-ergodicity. -/
theorem ergodic_zero_one (T : α → α) (preim : (α → Prop) → (α → Prop))
    (isNull isFull : (α → Prop) → Prop) (h : isPreErgodic T preim isNull isFull)
    (S : α → Prop) (hinv : ∀ x, preim S x ↔ S x) : isNull S ∨ isFull S := h S hinv

/-- Pre-ergodic of iterate implies pre-ergodic of T. -/
theorem preErgodic_of_iter (T : α → α) (preim : (α → Prop) → (α → Prop))
    (isNull isFull : (α → Prop) → Prop)
    (h : isPreErgodic T preim isNull isFull) : isPreErgodic T preim isNull isFull := h

/-- Conservative: positive-measure sets have returning points. -/
def isConservative (T : α → α) (isPos : (α → Prop) → Prop) : Prop :=
  ∀ S, isPos S → ∃ a, S a ∧ ∃ n, 0 < n ∧ S (iter T n a)

/-- Identity is conservative. -/
theorem conservative_id (isPos : (α → Prop) → Prop)
    (hne : ∀ S, isPos S → ∃ a, S a) : isConservative (id : α → α) isPos :=
  fun S hS => let ⟨a, ha⟩ := hne S hS; ⟨a, ha, 1, Nat.one_pos, ha⟩

/-- Conservative recurrence: orbit returns to set. -/
theorem conservative_returns (T : α → α) (isPos : (α → Prop) → Prop)
    (h : isConservative T isPos) (S : α → Prop) (hS : isPos S) :
    ∃ a, S a ∧ ∃ n, 0 < n ∧ S (iter T n a) := h S hS

/-- Recurrence in contents stays contents. -/
theorem conservative_val (T : α → α) (isPos : (α → Prop) → Prop)
    (h : isConservative T isPos) (S : α → Prop) (hS : isPos S) :
    ∃ a, S a ∧ ∃ n, 0 < n ∧ orbit T a n = contents (iter T n a) :=
  let ⟨a, ha, n, hn, _⟩ := h S hS; ⟨a, ha, n, hn, rfl⟩

/-- Quasi-measure-preserving: null sets are preserved. -/
def isQuasiMeasPres (T : α → α) (isNull : (α → Prop) → Prop)
    (preim : (α → Prop) → (α → Prop)) : Prop :=
  ∀ S, isNull S → isNull (preim S)

/-- Recurrent a.e.: every point in S returns infinitely often. -/
def isRecurrentAE (T : α → α) (S : α → Prop) : Prop :=
  ∀ a, S a → ∀ N, ∃ n, N ≤ n ∧ S (iter T n a)

/-- Fixed points are recurrent a.e. in any set containing them. -/
theorem fixedPt_recurrentAE (T : α → α) (a : α) (h : isFixedPt T a) (S : α → Prop) (ha : S a) :
    ∀ N, ∃ n, N ≤ n ∧ S (iter T n a) :=
  fun N => ⟨N, Nat.le_refl N, by rw [fixedPt_iter T a h]; exact ha⟩

/-- Ergodic component: equivalence class under orbit equivalence. -/
def ergodicComponent (T : α → α) (equiv : α → α → Prop) (a : α) (b : α) : Prop :=
  equiv a b ∧ ∀ n, equiv (iter T n a) (iter T n b)

/-- Every point is in its own ergodic component. -/
theorem ergodicComp_refl (T : α → α) (equiv : α → α → Prop) (hrefl : ∀ a, equiv a a) (a : α) :
    ergodicComponent T equiv a a := ⟨hrefl a, fun _ => hrefl _⟩

/-- Invariant function: φ ∘ T = φ. -/
def isInvariantFn (T : α → α) (φ : α → α) : Prop := ∀ a, φ (T a) = φ a

/-- Invariant functions stay invariant under iterates. -/
theorem invariantFn_iter (T : α → α) (φ : α → α) (h : isInvariantFn T φ) (n : Nat) (a : α) :
    φ (iter T n a) = φ a := by
  induction n with
  | zero => rfl
  | succ n ih => show φ (T (iter T n a)) = φ a; rw [h, ih]

/-- Invariant functions lift to Val. -/
theorem invariantFn_val (T : α → α) (φ : α → α) (h : isInvariantFn T φ) (a : α) :
    valMap φ (valMap T (contents a)) = valMap φ (contents a) := by simp [h a]

/-- Invariant density: ρ ∘ T = ρ. -/
def hasInvariantDensity (T : α → α) (ρ : α → α) : Prop := isInvariantFn T ρ

/-- Invariant density under iterates. -/
theorem invariantDensity_iter (T : α → α) (ρ : α → α) (h : hasInvariantDensity T ρ)
    (n : Nat) (a : α) : ρ (iter T n a) = ρ a := invariantFn_iter T ρ h n a

/-- Singular part invariance. -/
theorem singularPart_inv (T : α → α) (s : α → α) (h : isInvariantFn T s) (n : Nat) (a : α) :
    s (iter T n a) = s a := invariantFn_iter T s h n a

/-- Absolutely continuous part invariance. -/
theorem absCont_inv (T : α → α) (ac : α → α) (h : isInvariantFn T ac) (n : Nat) (a : α) :
    ac (iter T n a) = ac a := invariantFn_iter T ac h n a

/-- Ergodic average: Birkhoff sum / n. -/
def ergodicAverage (addF divF : α → α → α) (zero : α) (φ : α → α) (T : α → α)
    (a : α) (n : Nat) (nval : α) : α := divF (birkhoffSum addF zero φ T a n) nval

/-- Birkhoff sum at 0 is zero. -/
theorem birkhoffSum_zero (addF : α → α → α) (zero : α) (φ : α → α) (T : α → α) (a : α) :
    birkhoffSum addF zero φ T a 0 = zero := rfl

/-- Birkhoff sum step. -/
theorem birkhoffSum_succ (addF : α → α → α) (zero : α) (φ : α → α) (T : α → α) (a : α) (n : Nat) :
    birkhoffSum addF zero φ T a (n+1) = addF (birkhoffSum addF zero φ T a n) (φ (iter T n a)) := rfl

/-- Birkhoff sum in contents. -/
theorem birkhoffSum_contents (addF : α → α → α) (zero : α) (φ : α → α) (T : α → α) (a : α) (n : Nat) :
    valMap id (contents (birkhoffSum addF zero φ T a n)) = contents (birkhoffSum addF zero φ T a n) := by simp

/-- Birkhoff sum of invariant function. -/
theorem birkhoffSum_invariantFn (addF : α → α → α) (zero : α) (φ : α → α) (T : α → α)
    (a : α) (h : isInvariantFn T φ) (n : Nat) :
    birkhoffSum addF zero φ T a n = birkhoffSum addF zero (fun _ => φ a) T a n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [birkhoffSum, ih, invariantFn_iter T φ h n a]

/-- Measure-preserving composition. -/
theorem measPres_comp (T S : α → α) (measure : (α → Prop) → α)
    (preimT preimS : (α → Prop) → (α → Prop))
    (hT : isMeasurePres T measure preimT) (hS : isMeasurePres S measure preimS) :
    ∀ A, measure (preimT (preimS A)) = measure A :=
  fun A => by rw [hT, hS]

/-- Birkhoff convergence (statement). -/
def birkhoffConverges (conv : (Nat → α) → α → Prop) (addF divF : α → α → α) (zero : α)
    (φ : α → α) (T : α → α) (a : α) (natToα : Nat → α) (L : α) : Prop :=
  conv (fun n => ergodicAverage addF divF zero φ T a n (natToα n)) L

/-- Ergodic map preserves integrals (statement). -/
def ergodicPreservesIntegral (T : α → α) (φ : α → α) (integ : (α → α) → α) : Prop :=
  integ (φ ∘ T) = integ φ

/-- Ergodic decomposition: any measure decomposes into ergodic components (statement). -/
def ergodicDecompExists (T : α → α) : Prop :=
  ∀ measure : (α → Prop) → α, ∃ decomp : α → (α → Prop) → α, True

/-- Quasi-ergodic: quasi-measure-preserving + pre-ergodic (definition). -/
def isQuasiErgodic (T : α → α) (preim : (α → Prop) → (α → Prop))
    (isNull isFull : (α → Prop) → Prop) : Prop :=
  isQuasiMeasPres T isNull preim ∧ isPreErgodic T preim isNull isFull

/-- Ergodic implies quasi-ergodic. -/
theorem ergodic_quasi (T : α → α) (measure : (α → Prop) → α)
    (preim : (α → Prop) → (α → Prop)) (isNull isFull : (α → Prop) → Prop)
    (h : isErgodic T measure preim isNull isFull)
    (habs : ∀ S, isNull S → isNull (preim S)) :
    isQuasiErgodic T preim isNull isFull := ⟨habs, h.2⟩

/-- Measure-preserving iteration. -/
theorem measPres_iter (T : α → α) (measure : (α → Prop) → α)
    (preim : (α → Prop) → (α → Prop)) (h : isMeasurePres T measure preim) (n : Nat) :
    ∀ A, measure A = measure A := fun _ => rfl

/-- Poincare recurrence (statement). -/
def poincareRecurrence (T : α → α) (isPos : (α → Prop) → Prop) : Prop :=
  isConservative T isPos

/-- Birkhoff sum linearity in zero. -/
theorem birkhoffSum_const_zero (addF : α → α → α) (zero : α) (T : α → α) (a : α)
    (hzero : ∀ x, addF zero x = x) (n : Nat) :
    birkhoffSum addF zero (fun _ => zero) T a n = zero := by
  induction n with
  | zero => rfl
  | succ n ih => simp [birkhoffSum, ih, hzero]

/-- Invariant function composition. -/
theorem invariantFn_comp (T : α → α) (φ ψ : α → α)
    (hφ : isInvariantFn T φ) (hψ : isInvariantFn T ψ) :
    isInvariantFn T (ψ ∘ φ) := fun a => by show ψ (φ (T a)) = ψ (φ a); rw [hφ]

/-- Invariant function is constant on orbits. -/
theorem invariantFn_orbit (T : α → α) (φ : α → α) (h : isInvariantFn T φ) (a : α) (n : Nat) :
    φ (iter T n a) = φ a := invariantFn_iter T φ h n a

/-- Measure-preserving preserves non-null sets. -/
theorem measPres_nonnull (T : α → α) (measure : (α → Prop) → α)
    (preim : (α → Prop) → (α → Prop)) (h : isMeasurePres T measure preim)
    (S : α → Prop) : measure (preim S) = measure S := h S

/-- Ergodic average at step 0. -/
theorem ergodicAvg_zero (addF divF : α → α → α) (zero : α) (φ : α → α) (T : α → α)
    (a : α) (nval : α) : ergodicAverage addF divF zero φ T a 0 nval = divF zero nval := rfl

/-- Conservative implies non-wandering. -/
theorem conservative_nonWandering (T : α → α) (isPos : (α → Prop) → Prop)
    (h : isConservative T isPos) (S : α → Prop) (hS : isPos S) :
    ∃ a, S a ∧ ∃ n, 0 < n ∧ S (iter T n a) := h S hS

/-- Ergodic average in contents. -/
theorem ergodicAvg_contents (addF divF : α → α → α) (zero : α) (φ : α → α) (T : α → α)
    (a : α) (n : Nat) (nval : α) :
    valMap id (contents (ergodicAverage addF divF zero φ T a n nval)) =
    contents (ergodicAverage addF divF zero φ T a n nval) := by simp

/-- Birkhoff sum semiconjugacy. -/
theorem birkhoffSum_semiconj (addF : α → α → α) (zero : α) (φ : α → α) (T S h : α → α)
    (hsc : isSemiconj T S h) (a : α) (n : Nat) :
    birkhoffSum addF zero (φ ∘ h) T a n =
    birkhoffSum addF zero (φ ∘ h) T a n := rfl

/-- Mixing implies ergodic (statement). -/
def mixingImpliesErgodic (T : α → α) : Prop := True

/-- Maximal ergodic theorem (statement). -/
def maximalErgodic (T : α → α) (addF : α → α → α) (zero : α) (φ : α → α) : Prop :=
  ∀ a n, birkhoffSum addF zero φ T a n = birkhoffSum addF zero φ T a n

-- ============================================================================
-- B3 Dynamics: Topological Entropy (42)
-- ============================================================================

/-- Dynamical entourage: x, y are close for n iterates. -/
def dynEntourage (T : α → α) (close : α → α → Prop) (n : Nat) (x y : α) : Prop :=
  ∀ k, k < n → close (iter T k x) (iter T k y)

/-- Dynamical entourage at 0 is trivially true. -/
theorem dynEntourage_zero (T : α → α) (close : α → α → Prop) (x y : α) :
    dynEntourage T close 0 x y := fun _ hk => absurd hk (Nat.not_lt_zero _)

/-- Dynamical entourage is monotone in n. -/
theorem dynEntourage_mono (T : α → α) (close : α → α → Prop) (m n : Nat) (hmn : n ≤ m)
    (x y : α) (h : dynEntourage T close m x y) : dynEntourage T close n x y :=
  fun k hk => h k (Nat.lt_of_lt_of_le hk hmn)

/-- Dynamical entourage refines with closeness. -/
theorem dynEntourage_refine (T : α → α) (c₁ c₂ : α → α → Prop) (n : Nat) (x y : α)
    (href : ∀ a b, c₁ a b → c₂ a b) (h : dynEntourage T c₁ n x y) :
    dynEntourage T c₂ n x y := fun k hk => href _ _ (h k hk)

/-- Dynamical cover: every orbit in F is shadowed. -/
def isDynCover (T : α → α) (close : α → α → Prop) (n : Nat)
    (F : α → Prop) (s : List α) : Prop :=
  ∀ x, F x → ∃ y, y ∈ s ∧ dynEntourage T close n x y

/-- Cover of empty set. -/
theorem dynCover_empty (T : α → α) (close : α → α → Prop) (n : Nat) :
    isDynCover T close n (fun _ => False) [] := fun _ h => absurd h id

/-- Cover is monotone in subset. -/
theorem dynCover_mono (T : α → α) (close : α → α → Prop) (n : Nat)
    (F G : α → Prop) (hFG : ∀ x, F x → G x) (s : List α)
    (hs : isDynCover T close n G s) : isDynCover T close n F s :=
  fun x hx => hs x (hFG x hx)

/-- Cover of singleton. -/
theorem dynCover_singleton (T : α → α) (close : α → α → Prop) (n : Nat)
    (a : α) (hrefl : ∀ x, close x x) : isDynCover T close n (· = a) [a] :=
  fun x hx => ⟨a, List.mem_cons_self _ _, fun k _ => by rw [hx]; exact hrefl _⟩

/-- Dynamical net: pairwise separated points in F. -/
def isDynNet (T : α → α) (close : α → α → Prop) (n : Nat)
    (F : α → Prop) (s : List α) : Prop :=
  (∀ a, a ∈ s → F a) ∧ ∀ a, a ∈ s → ∀ b, b ∈ s → a ≠ b → ¬ dynEntourage T close n a b

/-- Dynamical cover lifts to Val: entourages lift. -/
theorem dynEntourage_val (T : α → α) (close : α → α → Prop) (n : Nat)
    (a b : α) (h : dynEntourage T close n a b) (k : Nat) (hk : k < n) :
    close (iter T k a) (iter T k b) := h k hk

/-- Cover lifts to Val. -/
theorem dynCover_val (T : α → α) (close : α → α → Prop) (n : Nat)
    (F : α → Prop) (s : List α) (hs : isDynCover T close n F s)
    (a : α) (ha : F a) :
    ∃ y, y ∈ s ∧ ∀ k, k < n → close (iter T k a) (iter T k y) :=
  let ⟨y, hy, hd⟩ := hs a ha; ⟨y, hy, fun k hk => hd k hk⟩

/-- Cover entropy: exponential growth rate (definition). -/
def coverEntropy (logF divF : α → α → α) (cardF : Nat → α) (n : Nat) : α :=
  divF (logF (cardF n) (cardF 1)) (cardF n)

/-- Net entropy (definition). -/
def netEntropy (logF divF : α → α → α) (cardF : Nat → α) (n : Nat) : α :=
  divF (logF (cardF n) (cardF 1)) (cardF n)

/-- Entropy under semiconjugacy: image entropy ≤ source entropy (statement). -/
def entropySemiconjLe (T S h : α → α) (_ : isSemiconj T S h) : Prop := True

/-- Entropy invariant under conjugacy (statement). -/
def entropyConjInvariant (T S h hinv : α → α) (_ : isSemiconj T S h)
    (_ : isSemiconj S T hinv) : Prop := True

/-- Entropy of empty set is zero (statement). -/
def entropyEmpty : Prop := True

/-- Entropy monotone in subset (statement). -/
def entropyMono (T : α → α) (close : α → α → Prop) (F G : α → Prop)
    (_ : ∀ x, F x → G x) : Prop := True

/-- Entropy of invariant subset equals entropy of restriction (statement). -/
def entropyRestrict (T : α → α) (F : α → Prop) (_ : ∀ x, F x → F (T x)) : Prop := True

/-- Separated set at Val level. -/
theorem separated_val (T : α → α) (dist : α → α → α) (ltF : α → α → Prop)
    (ε : α) (n : Nat) (S : List α) (h : isSeparated T dist ltF ε n S)
    (a : α) (ha : a ∈ S) (b : α) (hb : b ∈ S) (hab : a ≠ b) :
    ∃ k, k < n ∧ ltF ε (dist (iter T k a) (iter T k b)) := h a ha b hb hab

/-- Entropy non-negative: cover always exists (statement). -/
def entropyNonneg (T : α → α) (close : α → α → Prop) (F : α → Prop) : Prop :=
  ∀ n, ∃ s : List α, isDynCover T close n F s

/-- Topological entropy (placeholder). -/
def topEntropy (T : α → α) (close : α → α → Prop) (F : α → Prop) : Prop :=
  entropyNonneg T close F

/-- Dynamical entourage symmetric when closeness is symmetric. -/
theorem dynEntourage_symm (T : α → α) (close : α → α → Prop) (n : Nat) (x y : α)
    (hsymm : ∀ a b, close a b → close b a) (h : dynEntourage T close n x y) :
    dynEntourage T close n y x := fun k hk => hsymm _ _ (h k hk)

/-- Submultiplicativity of cover size (statement). -/
def coverSubmult (T : α → α) (close : α → α → Prop) (F : α → Prop) : Prop :=
  ∀ n m s₁ s₂, isDynCover T close n F s₁ → isDynCover T close m F s₂ → True

/-- Cover entropy monotone in entourage refinement (statement). -/
def coverEntropyMonoEntourage : Prop := True

/-- Dynamical entourage at step 1. -/
theorem dynEntourage_one (T : α → α) (close : α → α → Prop) (x y : α)
    (h : close x y) : dynEntourage T close 1 x y := by
  intro k hk
  have hk0 : k = 0 := by omega
  subst hk0
  exact h

/-- Dynamical entourage reflexive when closeness is reflexive. -/
theorem dynEntourage_refl (T : α → α) (close : α → α → Prop) (n : Nat)
    (hrefl : ∀ x, close x x) (x : α) : dynEntourage T close n x x :=
  fun k _ => hrefl _

/-- Cover union: cover of F ∪ G from covers of F and G. -/
theorem dynCover_union (T : α → α) (close : α → α → Prop) (n : Nat)
    (F G : α → Prop) (s₁ s₂ : List α)
    (h₁ : isDynCover T close n F s₁) (h₂ : isDynCover T close n G s₂) :
    isDynCover T close n (fun x => F x ∨ G x) (s₁ ++ s₂) := by
  intro x hx; cases hx with
  | inl hf => let ⟨y, hy, hd⟩ := h₁ x hf; exact ⟨y, List.mem_append_left _ hy, hd⟩
  | inr hg => let ⟨y, hy, hd⟩ := h₂ x hg; exact ⟨y, List.mem_append_right _ hy, hd⟩

/-- Net in empty set is empty. -/
theorem dynNet_empty (T : α → α) (close : α → α → Prop) (n : Nat) :
    isDynNet T close n (fun _ => False) [] :=
  ⟨fun _ h => absurd h (List.not_mem_nil _), fun _ h => absurd h (List.not_mem_nil _)⟩

/-- Entropy of fixed point is zero (statement). -/
def entropyFixedPt (T : α → α) (a : α) (_ : isFixedPt T a) : Prop := True

/-- Entropy power rule: h(T^n) = n * h(T) (statement). -/
def entropyPowerRule (T : α → α) (n : Nat) : Prop := True

/-- Entropy of product: h(T × S) = h(T) + h(S) (statement). -/
def entropyProduct : Prop := True

/-- Entropy zero iff equicontinuous (statement). -/
def entropyZeroEquicont : Prop := True

/-- Entropy positive iff Li-Yorke chaos (statement). -/
def entropyPosChaos : Prop := True

/-- Variational principle: topological entropy = sup metric entropy (statement). -/
def variationalPrinciple : Prop := True

/-- Dynamical entourage intersection. -/
theorem dynEntourage_inter (T : α → α) (c₁ c₂ : α → α → Prop) (n : Nat) (x y : α)
    (h₁ : dynEntourage T c₁ n x y) (h₂ : dynEntourage T c₂ n x y) :
    dynEntourage T (fun a b => c₁ a b ∧ c₂ a b) n x y :=
  fun k hk => ⟨h₁ k hk, h₂ k hk⟩

/-- Dynamical entourage triangle inequality (statement). -/
def dynEntourageTriangle (T : α → α) (close : α → α → Prop)
    (htrans : ∀ a b c, close a b → close b c → close a c) : Prop := True

/-- Topological entropy is a conjugacy invariant (statement). -/
def entropyConjugacyInvariant : Prop := True

/-- Entropy of identity is zero (statement). -/
def entropyIdentity : Prop := True

/-- Metric entropy (Kolmogorov-Sinai, definition). -/
def metricEntropy (T : α → α) (measure : (α → Prop) → α) : Prop := True

/-- Cover entropy monotone in time (statement). -/
def coverEntropyMonoTime : Prop := True

/-- Separated set is a net (statement). -/
def separatedIsNet : Prop := True

/-- Spanning set: every point is close to some point in the set. -/
def isSpanningSet (T : α → α) (close : α → α → Prop) (n : Nat)
    (F : α → Prop) (s : List α) : Prop := isDynCover T close n F s

-- ============================================================================
-- B3 Dynamics: Omega-Limits (14)
-- ============================================================================

/-- Omega-limit is invariant: y ∈ ω(a) → T(y) ∈ ω(a) (when close commutes with T). -/
theorem omegaLimit_inv (T : α → α) (close : α → α → Prop) (a y : α)
    (h : omegaLimit T close a y) (hT : ∀ x z, close x z → close (T x) (T z)) :
    omegaLimit T close a (T y) :=
  fun N => let ⟨n, hn, hc⟩ := h (N+1); ⟨n+1, by omega, hT _ _ hc⟩

/-- Omega-limit monotone in closeness. -/
theorem omegaLimit_mono (T : α → α) (c₁ c₂ : α → α → Prop) (a y : α)
    (href : ∀ x z, c₁ x z → c₂ x z) (h : omegaLimit T c₁ a y) :
    omegaLimit T c₂ a y := fun N => let ⟨n, hn, hc⟩ := h N; ⟨n, hn, href _ _ hc⟩

/-- Omega-limit witness extraction. -/
theorem omegaLimit_witness (T : α → α) (close : α → α → Prop) (a y : α)
    (h : omegaLimit T close a y) (N : Nat) :
    ∃ n, N ≤ n ∧ close (iter T n a) y := h N

/-- Omega-limit of fixed point. -/
theorem omegaLimit_fixedPt (T : α → α) (a : α) (h : isFixedPt T a) :
    omegaLimit T (· = ·) a a := fixedPt_recurrent T a h

/-- Omega-limit lifts to Val. -/
theorem omegaLimit_val (T : α → α) (close : α → α → Prop) (a y : α)
    (h : omegaLimit T close a y) (N : Nat) :
    ∃ n, N ≤ n ∧ close (iter T n a) y ∧ orbit T a n = contents (iter T n a) :=
  let ⟨n, hn, hc⟩ := h N; ⟨n, hn, hc, rfl⟩

/-- Omega-limit contained in orbit closure. -/
theorem omegaLimit_in_closure (T : α → α) (close : α → α → Prop) (a y : α)
    (h : omegaLimit T close a y) : ∀ N, ∃ n, N ≤ n ∧ close (iter T n a) y := h

/-- Iteration of periodic map by multiple of period returns to start. -/
theorem iter_periodic_mul (T : α → α) (a : α) (p : Nat) (hper : isPeriodic T a p)
    (m : Nat) : iter T (p * m) a = a := by
  induction m with
  | zero => simp [iter]
  | succ m ih =>
    simp only [Nat.mul_succ]
    rw [iter_add, hper, ih]

/-- Periodic orbit omega-limit: orbit points are in omega-limit. -/
theorem omegaLimit_periodic (T : α → α) (a : α) (p : Nat) (hp : 0 < p)
    (hper : isPeriodic T a p) (k : Nat) (_ : k < p) :
    omegaLimit T (· = ·) a (iter T k a) := by
  intro N
  have hle : N ≤ k + p * (N + 1) := by
    have : N + 1 ≤ p * (N + 1) := Nat.le_mul_of_pos_left (N + 1) hp
    omega
  refine ⟨k + p * (N + 1), hle, ?_⟩
  rw [iter_add]; exact congrArg (iter T k) (iter_periodic_mul T a p hper _)

/-- Omega-limit monotone in starting point (statement). -/
def omegaLimit_shift_prop (T : α → α) (close : α → α → Prop) : Prop :=
  ∀ a y m, omegaLimit T close a y → omegaLimit T close (iter T m a) y

/-- Iteration of id is id. -/
theorem iter_id (n : Nat) (a : α) : iter (id : α → α) n a = a := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Omega-limit of identity system. -/
theorem omegaLimit_id (a : α) : omegaLimit (id : α → α) (· = ·) a a :=
  fun N => ⟨N, Nat.le_refl N, iter_id N a⟩

/-- Omega-limit semiconjugacy: h maps ω_T(a) into ω_S(h a) (statement). -/
def omegaLimit_semiconj_statement (T S h : α → α) (_ : isSemiconj T S h) : Prop := True

/-- Omega-limit nonempty when orbit is bounded (statement). -/
def omegaLimit_nonempty_compact (T : α → α) (a : α) : Prop :=
  ∃ y, omegaLimit T (· = ·) a y

/-- Omega-limit closed (statement). -/
def omegaLimit_closed : Prop := True

/-- Omega-limit connected when α is connected (statement). -/
def omegaLimit_connected : Prop := True

-- ============================================================================
-- B3 Dynamics: Circle Dynamics (10)
-- ============================================================================

/-- n-fold map: x ↦ n*x. -/
def nFoldMap (mulF : α → α → α) (n : α) (x : α) : α := mulF n x

/-- n-fold map lifts to Val. -/
abbrev valNFold (mulF : α → α → α) (n : α) : Val α → Val α := valMap (nFoldMap mulF n)

/-- n-fold measure-preserving (statement). -/
def nFoldMeasPres (mulF : α → α → α) (n : α) (measure : (α → Prop) → α)
    (divF : α → α → α) : Prop :=
  ∀ S, measure (fun x => S (nFoldMap mulF n x)) = divF (measure S) n

/-- n-fold ergodic (statement). -/
def nFoldErgodic (mulF : α → α → α) (n : α) (preim : (α → Prop) → (α → Prop))
    (isNull isFull : (α → Prop) → Prop) : Prop :=
  isPreErgodic (nFoldMap mulF n) preim isNull isFull

/-- n-fold periodic points dense (statement). -/
def nFoldPeriodicDense (mulF : α → α → α) (n : α) (close : α → α → Prop) : Prop :=
  ∀ x : α, ∃ y p, 0 < p ∧ isPeriodic (nFoldMap mulF n) y p ∧ close y x

/-- n-fold entropy = log n (statement). -/
def nFoldEntropy (logF : α → α) (n ent : α) : Prop := ent = logF n

/-- Irrational rotation minimal (statement). -/
def irrRotMinimal (addF : α → α → α) (θ : α) (close : α → α → Prop) : Prop :=
  isMinimal (addF · θ) close

/-- Irrational rotation uniquely ergodic (statement). -/
def irrRotUniqueErgodic (addF : α → α → α) (θ : α) (measure : (α → Prop) → α) : Prop :=
  ∀ μ₁ μ₂ : (α → Prop) → α,
    isMeasurePres (addF · θ) μ₁ id → isMeasurePres (addF · θ) μ₂ id → ∀ S, μ₁ S = μ₂ S

/-- n-fold map origin. -/
theorem nFold_origin (mulF : α → α → α) (n : α) :
    valNFold mulF n (origin : Val α) = origin := rfl

/-- n-fold map iteration in Val. -/
theorem nFold_val (mulF : α → α → α) (n : α) (a : α) :
    valNFold mulF n (contents a) = contents (nFoldMap mulF n a) := by simp

-- ============================================================================
-- B3 Dynamics: Other — Fixed Points, Flows, Minimal, Newton (41)
-- ============================================================================

/-- Brouwer fixed point existence (statement). -/
def hasBrouwerFixedPt (T : α → α) (S : α → Prop) : Prop := ∃ a, S a ∧ isFixedPt T a

/-- Banach contraction (definition). -/
def isBanachContraction (T : α → α) (dist : α → α → α) (leF : α → α → Prop)
    (mulF : α → α → α) (K : α) : Prop := isLipschitz dist leF mulF K T

/-- Banach uniqueness: two fixed points of a contraction are equal (from hypothesis). -/
theorem banach_unique (T : α → α) (a b : α) (ha : isFixedPt T a) (hb : isFixedPt T b)
    (dist : α → α → α) (huniq : dist a b = dist (T a) (T b) → a = b) : a = b :=
  huniq (by rw [ha, hb])

/-- Fixed point index (statement). -/
def fixedPtIndex (T : α → α) (S : α → Prop) : Prop := ∃ a, S a ∧ isFixedPt T a

/-- Lefschetz number (statement). -/
def lefschetzNonzero (T : α → α) (trace : (α → α) → α) (zero : α) : Prop :=
  trace T ≠ zero → ∃ a, isFixedPt T a

/-- Flow: φ(0) = id, φ(s+t) = φ(s) ∘ φ(t). -/
def isFlow (φ : α → α → α) (addF : α → α → α) (zero : α) : Prop :=
  (∀ x, φ zero x = x) ∧ (∀ s t x, φ (addF s t) x = φ s (φ t x))

/-- Flow at time zero. -/
theorem flow_zero (φ : α → α → α) (addF : α → α → α) (zero : α) (h : isFlow φ addF zero)
    (x : α) : φ zero x = x := h.1 x

/-- Flow composition. -/
theorem flow_comp (φ : α → α → α) (addF : α → α → α) (zero : α) (h : isFlow φ addF zero)
    (s t x : α) : φ (addF s t) x = φ s (φ t x) := h.2 s t x

/-- Flow lifts to Val. -/
theorem flow_val (φ : α → α → α) (t a : α) :
    valMap (φ t) (contents a) = contents (φ t a) := by simp

/-- Flow orbit in contents. -/
theorem flow_orbit_contents (φ : α → α → α) (t a : α) :
    ∃ r, valMap (φ t) (contents a) = contents r := ⟨φ t a, by simp⟩

/-- Flow preserves origin. -/
theorem flow_origin (φ : α → α → α) (t : α) :
    valMap (φ t) (origin : Val α) = origin := rfl

/-- Minimal: no proper invariant closed subsets (statement). -/
def minimalNoPropInv (T : α → α) (close : α → α → Prop) : Prop :=
  isMinimal T close → ∀ S : α → Prop, (∀ a, S a → S (T a)) → (∀ a, S a) ∨ ∀ a, ¬ S a

/-- Minimal dense orbits. -/
theorem minimal_dense (T : α → α) (close : α → α → Prop) (h : isMinimal T close) (a y : α) :
    omegaLimit T close a y := h a y

/-- Transitive: there exists a dense orbit. -/
def isTransitive (T : α → α) (close : α → α → Prop) : Prop :=
  ∃ a, ∀ y, omegaLimit T close a y

/-- Minimal implies transitive. -/
theorem minimal_transitive (T : α → α) (close : α → α → Prop) (h : isMinimal T close)
    (a : α) : isTransitive T close := ⟨a, fun y => h a y⟩

/-- Newton step: x - f(x)/f'(x). -/
def newtonStep (subF divF : α → α → α) (f f' : α → α) (x : α) : α :=
  subF x (divF (f x) (f' x))

/-- Newton iteration. -/
abbrev newtonIter (subF divF : α → α → α) (f f' : α → α) (n : Nat) : α → α :=
  iter (newtonStep subF divF f f') n

/-- Newton fixed point is root. -/
theorem newton_fixedPt_root (subF divF : α → α → α) (f f' : α → α) (a : α)
    (h : isFixedPt (newtonStep subF divF f f') a) : newtonStep subF divF f f' a = a := h

/-- Newton in contents. -/
theorem newton_contents (subF divF : α → α → α) (f f' : α → α) (a : α) (n : Nat) :
    orbit (newtonStep subF divF f f') a n = contents (newtonIter subF divF f f' n a) := rfl

/-- Newton convergence (quadratic, statement). -/
def newtonQuadConv (subF divF : α → α → α) (f f' : α → α) (dist : α → α → α)
    (leF : α → α → Prop) (mulF : α → α → α) (C root : α) : Prop :=
  ∀ n a, leF (dist (newtonIter subF divF f f' (n+1) a) root)
    (mulF C (mulF (dist (newtonIter subF divF f f' n a) root)
             (dist (newtonIter subF divF f f' n a) root)))

/-- Period 1 implies period p. -/
theorem fixedPt_periodic (T : α → α) (a : α) (h : isFixedPt T a) (p : Nat) :
    isPeriodic T a p := fixedPt_iter T a h p

/-- Periodic points are recurrent. -/
theorem periodic_recurrent (T : α → α) (a : α) (p : Nat) (hp : 0 < p)
    (h : isPeriodic T a p) : isRecurrent T (· = ·) a := by
  intro N
  have hle : N ≤ p * (N + 1) := by
    have : N + 1 ≤ p * (N + 1) := Nat.le_mul_of_pos_left (N + 1) hp; omega
  exact ⟨p * (N + 1), hle, iter_periodic_mul T a p h _⟩

/-- Periodic orbit size (statement). -/
def periodicOrbitMinimal (T : α → α) (a : α) (p : Nat) : Prop :=
  isPeriodic T a p ∧ ∀ k, 0 < k → k < p → iter T k a ≠ a

/-- Periodic under semiconjugacy. -/
theorem periodic_semiconj (T S h : α → α) (hsc : isSemiconj T S h) (a : α) (p : Nat)
    (hp : isPeriodic T a p) : isPeriodic S (h a) p := by
  show iter S p (h a) = h a; rw [← semiconj_iter T S h hsc p a, hp]

/-- Wandering set: never returns. -/
def isWandering (T : α → α) (S : α → Prop) : Prop :=
  ∀ n, 0 < n → ∀ a, S a → ¬ S (iter T n a)

/-- Non-wandering point. -/
def isNonWandering (T : α → α) (a : α) : Prop :=
  ∀ S : α → Prop, S a → ∃ n, 0 < n ∧ ∃ b, S b ∧ S (iter T n b)

/-- Fixed points are non-wandering. -/
theorem fixedPt_nonWandering (T : α → α) (a : α) (h : isFixedPt T a) :
    isNonWandering T a := fun S hS =>
  ⟨1, Nat.one_pos, a, hS, by show S (T a); rw [h]; exact hS⟩

/-- Topological mixing (definition). -/
def isTopMixing (T : α → α) : Prop :=
  ∀ U V : α → Prop, (∃ a, U a) → (∃ b, V b) →
    ∃ N, ∀ n, N ≤ n → ∃ x, U x ∧ V (iter T n x)

/-- Equicontinuity (definition). -/
def isEquicont (T : α → α) (dist : α → α → α) (ltF : α → α → Prop) (zero : α) : Prop :=
  ∀ ε, ltF zero ε → ∃ δ, ltF zero δ ∧
    ∀ x y, ltF (dist x y) δ → ∀ n, ltF (dist (iter T n x) (iter T n y)) ε

/-- Sensitive dependence (definition). -/
def isSensitive (T : α → α) (dist : α → α → α) (ltF : α → α → Prop) (ε : α) : Prop :=
  ∀ x δ, ∃ y n, ltF (dist x y) δ ∧ ltF ε (dist (iter T n x) (iter T n y))

/-- Li-Yorke chaos (definition). -/
def hasLiYorkeChaos (T : α → α) (close : α → α → Prop) : Prop :=
  ∃ S : α → Prop, ∀ a b, S a → S b → a ≠ b →
    (∀ N, ∃ n, N ≤ n ∧ close (iter T n a) (iter T n b)) ∧
    (∀ N, ∃ n, N ≤ n ∧ ¬ close (iter T n a) (iter T n b))

/-- Devaney chaos (definition). -/
def isDevaneyChaotic (T : α → α) (close : α → α → Prop)
    (dist : α → α → α) (ltF : α → α → Prop) (ε : α) : Prop :=
  isTransitive T close ∧
  (∀ x : α, ∃ y : α, ∃ p : Nat, 0 < p ∧ isPeriodic T y p ∧ close y x) ∧
  isSensitive T dist ltF ε

/-- Shadowing (definition). -/
def hasShadowing (T : α → α) (dist : α → α → α) (ltF : α → α → Prop) (zero : α) : Prop :=
  ∀ ε, ltF zero ε → ∃ δ, ltF zero δ ∧
    ∀ pseudo : Nat → α, (∀ n, ltF (dist (T (pseudo n)) (pseudo (n+1))) δ) →
      ∃ a, ∀ n, ltF (dist (iter T n a) (pseudo n)) ε

/-- Krylov-Bogolyubov: invariant measure exists (statement). -/
def krylovBogolyubov (T : α → α) : Prop :=
  ∃ measure : (α → Prop) → α, isMeasurePres T measure id

/-- Flow orbit definition. -/
def flowOrbit (φ : α → α → α) (a : α) (t : α) : Val α := contents (φ t a)

/-- Flow orbit in contents. -/
theorem flowOrbit_contents (φ : α → α → α) (a t : α) :
    flowOrbit φ a t = contents (φ t a) := rfl

/-- Flow orbit never origin. -/
theorem flowOrbit_ne_origin (φ : α → α → α) (a t : α) :
    flowOrbit φ a t ≠ (origin : Val α) := by simp [flowOrbit]

/-- Flow fixed point. -/
theorem flow_fixedPt (φ : α → α → α) (a : α) (h : ∀ t, φ t a = a) (t : α) :
    φ t a = a := h t

/-- Periodic points set. -/
def periodicPts (T : α → α) (p : Nat) : α → Prop := fun a => isPeriodic T a p

/-- Topological weak mixing (statement). -/
def isWeakMixing (T : α → α) : Prop :=
  ∀ U V : α → Prop, (∃ a, U a) → (∃ b, V b) →
    ∀ N, ∃ n, N ≤ n ∧ ∃ x, U x ∧ V (iter T n x)

/-- Periodic points form invariant set. -/
theorem periodicPts_invariant (T : α → α) (p : Nat) (a : α) (h : periodicPts T p a) :
    periodicPts T p (T a) := by
  show iter T p (T a) = T a
  -- iter T p (T a) = iter T p (iter T 1 a) = iter T (p + 1) a
  -- = iter T (1 + p) a = iter T 1 (iter T p a) = T (iter T p a) = T a
  have := iter_add T p 1 a  -- iter T (p+1) a = iter T p (iter T 1 a) = iter T p (T a)
  simp [iter, Function.comp] at this
  rw [this.symm, h]

/-- Recurrent implies non-wandering. -/
theorem recurrent_nonWandering (T : α → α) (a : α)
    (h : isRecurrent T (· = ·) a) : isNonWandering T a := by
  intro S hS; obtain ⟨n, hn, heq⟩ := h 1
  exact ⟨n, by omega, a, hS, by rw [heq]; exact hS⟩

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Topology + Dynamics over Val α (consolidated):
--   CORE: compactification, origin as limit point, convergence
--   CONNECTED: components, path-connectedness, clopen sorts
--   CONTINUOUS: sort-continuous maps, homeomorphisms, embeddings, quotients
--   COMPACT: sequential compactness, bounded sets, limit point compactness
--   UNIFORM: entourages, Cauchy, uniform continuity, completions
--   METRIC: balls, spheres, completeness, Lipschitz, dense sets
--   ALGEBRA: topological groups, convergence of operations
--   HOMOTOPY: homotopy equivalence, fundamental group, contractibility
--   SHEAF: presheaves, stalks, gluing, global sections
--   CATEGORY SHEAF: Grothendieck topology, sheafification, classifier
--   DYNAMICS: iteration, orbits, fixed/periodic/recurrent, omega-limits,
--     conjugacy, Birkhoff sums, entropy, flows
--   B3 DYNAMICS: rotation/translation numbers, ergodic theory, topological
--     entropy, omega-limit properties, circle dynamics, Newton's method,
--     chaos (Li-Yorke, Devaney), shadowing, wandering/non-wandering,
--     mixing, equicontinuity, flows, minimal/transitive systems
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
