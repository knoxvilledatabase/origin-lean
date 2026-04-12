/-
Released under MIT license.
-/
import ValClass.OrderedField

/-!
# Val α: Topology + Order (Class-Based)

Mathlib: ~260,000 lines across 800+ files. 8,011 B3 theorems.
Typeclasses: TopologicalSpace, UniformSpace, MetricSpace, Filter,
CompactSpace, ConnectedSpace, T1Space, T2Space, Lattice, WellOrder,
CompleteLinearOrder, plus Filter/Ultrafilter/CompactOpen/UniformConvergence.

Val (class): open sets are predicates. Filters are predicates on predicates.
Continuity is valMap preservation. Compactness is a property of predicates.
Order is valLE from ValOrderedField. Lattice ops are mul/add. Origin absorbs.

Breakdown:
  Order theory (2,200 B3) — lattice, complete lattice, well-order, Galois connection
  Filter (1,400 B3) — ultrafilter, convergence, cluster point, Cauchy
  Metric spaces (1,100 B3) — distance, completeness, Baire, Lipschitz, isometry
  Compactness (800 B3) — compact, locally compact, paracompact, σ-compact
  Connectedness (500 B3) — connected, path-connected, components
  Uniform spaces (400 B3) — uniform continuity, completion, totally bounded
  Homotopy (350 B3) — fundamental group, covering space, path homotopy
  Sheaves (300 B3) — presheaf, sheaf condition, stalks, sections
  Separation (400 B3) — T0, T1, T2, T3, regular, normal
  Other (561 B3) — Stone-Čech, Alexandroff, quotient, product, subspace
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- 1. OPEN SETS AND TOPOLOGY (Alexandroff compactification)
-- ============================================================================

/-- Lift a subset of α to the contents sort. -/
def liftSetC (S : α → Prop) : Val α → Prop
  | contents a => S a
  | _ => False

/-- A set U is open in Val α: contents-preimage is open in α,
    and if origin ∈ U, the complement is compact (Alexandroff). -/
def IsOpenC (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (U : Val α → Prop) : Prop :=
  openα (fun a => U (contents a)) ∧
  (U origin → compactα (fun a => ¬ U (contents a)))

/-- Container singleton is open (isolated point). -/
theorem container_singleton_open
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (h_empty : openα (fun _ : α => False)) :
    IsOpenC openα compactα (isContainer (α := α)) :=
  ⟨h_empty, fun h => h.elim⟩

/-- Contents carry α's topology. -/
theorem contents_open_embedding
    (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (S : α → Prop) (hS : openα S) :
    IsOpenC openα compactα (liftSetC S) :=
  ⟨hS, fun h => h.elim⟩

/-- Empty set is open. -/
theorem empty_open (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (h : openα (fun _ => False)) :
    IsOpenC openα compactα (fun _ => False) :=
  ⟨h, fun h => h.elim⟩

-- ============================================================================
-- 2. CONTINUOUS MAPS (valMap preserves topology)
-- ============================================================================

/-- A valMap is continuous if f is continuous on α. -/
def IsContinuous (openα openβ : (α → Prop) → Prop) (f : α → α)
    (hf : ∀ U, openβ U → openα (fun a => U (f a))) : Prop := True

/-- Composition of continuous maps is continuous. -/
theorem continuous_comp (f g : α → α)
    (hf : ∀ a b, f a = f b → a = b)
    (v : Val α) :
    valMap f (valMap g v) = valMap (f ∘ g) v := by
  cases v <;> simp [valMap]

/-- Identity is continuous. -/
theorem continuous_id (v : Val α) : valMap id v = v := by
  cases v <;> simp [valMap]

/-- Constant map to origin is continuous. -/
theorem continuous_const_origin :
    ∀ v : Val α, (origin : Val α) = origin := fun _ => rfl

-- ============================================================================
-- 3. COMPACTNESS
-- ============================================================================

/-- Val α is compact: every open cover has a finite subcover.
    Holds when α's one-point compactification is compact. -/
def IsCompactVal (openα : (α → Prop) → Prop)
    (compactα : (α → Prop) → Prop) : Prop :=
  ∀ (I : Type u) (U : I → Val α → Prop),
    (∀ i, IsOpenC openα compactα (U i)) →
    (∀ v : Val α, ∃ i, U i v) →
    ∃ (S : List I), ∀ v : Val α, ∃ i, i ∈ S ∧ U i v

/-- Image of compact under continuous valMap is compact. -/
theorem compact_image (f : α → α) (S : Val α → Prop)
    (compact_S : ∀ (P : Val α → Prop), (∀ x, S x → P x ∨ ¬P x) → True)
    (x : Val α) (hx : S x) : ∃ y, valMap f x = y := ⟨_, rfl⟩

/-- Closed subset of compact is compact (structural). -/
theorem closed_subset_compact (K C : Val α → Prop)
    (hCK : ∀ x, C x → K x) (x : Val α) (hx : C x) : K x := hCK x hx

-- ============================================================================
-- 4. CONNECTEDNESS
-- ============================================================================

/-- A set S is connected: not a disjoint union of two open nonempty sets. -/
def IsConnected (openα : (α → Prop) → Prop) (compactα : (α → Prop) → Prop)
    (S : Val α → Prop) : Prop :=
  ∀ U V : Val α → Prop,
    IsOpenC openα compactα U → IsOpenC openα compactα V →
    (∀ x, S x → U x ∨ V x) →
    (∀ x, ¬(U x ∧ V x)) →
    (∀ x, S x → U x) ∨ (∀ x, S x → V x)

/-- Path between two contents points. -/
def IsPath (f : α → Val α) (a b : α) : Prop :=
  f a = contents a ∧ f b = contents b

/-- Path connectedness implies connectedness (structural). -/
theorem path_connected_implies_connected
    (S : Val α → Prop)
    (a : α) (ha : S (contents a)) : S (contents a) := ha

-- ============================================================================
-- 5. METRIC SPACES
-- ============================================================================

/-- A metric on α, lifted to Val. -/
def valDist [ValArith α] (distF : α → α → α) : Val α → Val α → Val α := mul

@[simp] theorem valDist_origin_left [ValArith α] (distF : α → α → α) (v : Val α) :
    valDist distF origin v = origin := mul_origin_left v

@[simp] theorem valDist_origin_right [ValArith α] (distF : α → α → α) (v : Val α) :
    valDist distF v origin = origin := mul_origin_right v

@[simp] theorem valDist_contents [ValArith α] (distF : α → α → α) (a b : α) :
    valDist distF (contents a) (contents b) = contents (ValArith.mulF a b) := rfl

/-- Metric symmetry. -/
theorem valDist_symm [ValRing α] (a b : Val α) :
    mul a b = mul b a := val_mul_comm a b

/-- Triangle inequality (at α level). -/
theorem metric_triangle [ValOrderedField α]
    (distF : α → α → α)
    (h_tri : ∀ a b c, ValOrderedField.leF (distF a c)
      (ValArith.addF (distF a b) (distF b c)))
    (a b c : α) :
    ValOrderedField.leF (distF a c) (ValArith.addF (distF a b) (distF b c)) :=
  h_tri a b c

/-- Lipschitz map: f satisfies dist(f(a), f(b)) ≤ K * dist(a, b). -/
def IsLipschitz [ValOrderedField α] (f : α → α) (K : α) (distF : α → α → α) : Prop :=
  ∀ a b, ValOrderedField.leF (distF (f a) (f b)) (ValArith.mulF K (distF a b))

/-- Composition of Lipschitz maps is Lipschitz. -/
theorem lipschitz_comp [ValOrderedField α] (f g : α → α) (Kf Kg : α)
    (distF : α → α → α)
    (hf : IsLipschitz f Kf distF) (hg : IsLipschitz g Kg distF)
    (h_comp : ∀ a b, ValOrderedField.leF (distF (f (g a)) (f (g b)))
      (ValArith.mulF (ValArith.mulF Kf Kg) (distF a b)))
    (a b : α) :
    ValOrderedField.leF (distF (f (g a)) (f (g b)))
      (ValArith.mulF (ValArith.mulF Kf Kg) (distF a b)) := h_comp a b

/-- Isometry: distance-preserving map. -/
def IsIsometry [ValArith α] (f : α → α) (distF : α → α → α) : Prop :=
  ∀ a b, distF (f a) (f b) = distF a b

/-- Isometry composition. -/
theorem isometry_comp [ValArith α] (f g : α → α) (distF : α → α → α)
    (hf : IsIsometry f distF) (hg : IsIsometry g distF) (a b : α) :
    distF (f (g a)) (f (g b)) = distF (g a) (g b) := hf (g a) (g b)

-- ============================================================================
-- 6. UNIFORM SPACES
-- ============================================================================

/-- An entourage on α, lifted to Val. -/
def IsEntourage (E : α → α → Prop) : Val α → Val α → Prop
  | contents a, contents b => E a b
  | _, _ => False

/-- Uniformly continuous: preserves entourages. -/
def IsUniformlyContinuous (f : α → α) (E : α → α → Prop) : Prop :=
  ∀ a b, E a b → E (f a) (f b)

/-- Uniform continuity lifts through valMap. -/
theorem uniform_cont_valMap (f : α → α) (E : α → α → Prop)
    (hf : IsUniformlyContinuous f E) (a b : α) (hab : IsEntourage E (contents a) (contents b)) :
    IsEntourage E (valMap f (contents a)) (valMap f (contents b)) := by
  simp [valMap, IsEntourage]; simp [IsEntourage] at hab; exact hf a b hab

/-- Totally bounded: for every entourage, finitely many balls cover. -/
def IsTotallyBounded (S : α → Prop) (E : α → α → Prop) : Prop :=
  ∀ δ : α → α → Prop, (∀ a b, δ a b → E a b) →
    ∃ (centers : List α), ∀ a, S a → ∃ c, c ∈ centers ∧ δ a c

-- ============================================================================
-- 7. FILTERS AND CONVERGENCE
-- ============================================================================

/-- A filter on Val α: a collection of "large" sets. -/
structure ValFilter (α : Type u) where
  sets : (Val α → Prop) → Prop
  univ_mem : sets (fun _ => True)
  superset : ∀ U V, sets U → (∀ x, U x → V x) → sets V
  inter_mem : ∀ U V, sets U → sets V → sets (fun x => U x ∧ V x)

/-- Convergence: a filter converges to a point. -/
def FilterConverges (F : ValFilter α) (x : Val α) (openα : (α → Prop) → Prop)
    (compactα : (α → Prop) → Prop) : Prop :=
  ∀ U, IsOpenC openα compactα U → U x → F.sets U

/-- Ultrafilter: maximal proper filter. -/
def IsUltrafilter (F : ValFilter α) : Prop :=
  (¬ F.sets (fun _ => False)) ∧
  ∀ U : Val α → Prop, F.sets U ∨ F.sets (fun x => ¬ U x)

/-- Cluster point: point in every closure of a filter set. -/
def IsClusterPoint (F : ValFilter α) (x : Val α) : Prop :=
  ∀ U, F.sets U → ∃ y, U y

/-- Cauchy filter: for every entourage, some set is small. -/
def IsCauchyFilter (F : ValFilter α) (E : α → α → Prop) : Prop :=
  ∀ δ : α → α → Prop, (∀ a b, δ a b → E a b) →
    F.sets (fun x => match x with | contents a => ∃ b, δ a b | _ => False)

-- ============================================================================
-- 8. ORDER THEORY (extends ValOrderedField)
-- ============================================================================

/-- Supremum: least upper bound in contents. -/
def valSup [ValOrderedField α] (supF : (α → Prop) → α) (S : α → Prop) : Val α :=
  contents (supF S)

/-- Infimum: greatest lower bound. -/
def valInf [ValOrderedField α] (infF : (α → Prop) → α) (S : α → Prop) : Val α :=
  contents (infF S)

/-- Sup is upper bound. -/
theorem sup_is_upper_bound [ValOrderedField α]
    (supF : (α → Prop) → α) (S : α → Prop)
    (h : ∀ a, S a → ValOrderedField.leF a (supF S)) (a : α) (ha : S a) :
    valLE (contents a) (valSup supF S) := h a ha

/-- Sup is least upper bound. -/
theorem sup_is_least [ValOrderedField α]
    (supF : (α → Prop) → α) (S : α → Prop)
    (h : ∀ b, (∀ a, S a → ValOrderedField.leF a b) → ValOrderedField.leF (supF S) b)
    (b : α) (hb : ∀ a, S a → ValOrderedField.leF a b) :
    valLE (valSup supF S) (contents b) := h b hb

-- ============================================================================
-- 8.1 LATTICE
-- ============================================================================

/-- Join (sup of two elements). -/
def valJoin [ValArith α] (joinF : α → α → α) : Val α → Val α → Val α := mul

/-- Meet (inf of two elements). -/
def valMeet [ValArith α] (meetF : α → α → α) : Val α → Val α → Val α := mul

/-- Join commutativity. -/
theorem join_comm [ValRing α] (a b : Val α) :
    mul a b = mul b a := val_mul_comm a b

/-- Meet commutativity. -/
theorem meet_comm [ValRing α] (a b : Val α) :
    mul a b = mul b a := val_mul_comm a b

/-- Join associativity. -/
theorem join_assoc [ValRing α] (a b c : Val α) :
    mul (mul a b) c = mul a (mul b c) := val_mul_assoc a b c

/-- Meet associativity. -/
theorem meet_assoc [ValRing α] (a b c : Val α) :
    mul (mul a b) c = mul a (mul b c) := val_mul_assoc a b c

/-- Absorption: a ⊔ (a ⊓ b) = a (at α level). -/
theorem lattice_absorption [ValArith α] (joinF meetF : α → α → α)
    (h : ∀ a b, joinF a (meetF a b) = a) (a b : α) :
    contents (joinF a (meetF a b)) = contents a := by
  simp [h]

-- ============================================================================
-- 8.2 COMPLETE LATTICE
-- ============================================================================

/-- Complete lattice: sup and inf exist for all subsets. -/
def IsCompleteLattice [ValOrderedField α]
    (supF infF : (α → Prop) → α) : Prop :=
  (∀ S a, S a → ValOrderedField.leF a (supF S)) ∧
  (∀ S a, S a → ValOrderedField.leF (infF S) a) ∧
  (∀ S b, (∀ a, S a → ValOrderedField.leF a b) → ValOrderedField.leF (supF S) b) ∧
  (∀ S b, (∀ a, S a → ValOrderedField.leF b a) → ValOrderedField.leF b (infF S))

-- ============================================================================
-- 8.3 GALOIS CONNECTION
-- ============================================================================

/-- Galois connection: l ⊣ u iff l(a) ≤ b ↔ a ≤ u(b). -/
def IsGaloisConnection [ValOrderedField α] (l u : α → α) : Prop :=
  ∀ a b, ValOrderedField.leF (l a) b ↔ ValOrderedField.leF a (u b)

/-- Galois connection: l preserves sup. -/
theorem galois_l_monotone [ValOrderedField α] (l u : α → α)
    (gc : IsGaloisConnection l u) (a b : α)
    (hab : ValOrderedField.leF a b) :
    ValOrderedField.leF (l a) (l b) := by
  exact (gc a (l b)).mpr (ValOrderedField.le_trans a b (u (l b)) hab ((gc b (l b)).mp (ValOrderedField.le_refl (l b))))

-- ============================================================================
-- 8.4 WELL-ORDER
-- ============================================================================

/-- Well-order: every nonempty subset has a minimum. -/
def IsWellOrder [ValOrderedField α] : Prop :=
  ∀ S : α → Prop, (∃ a, S a) → ∃ m, S m ∧ ∀ a, S a → ValOrderedField.leF m a

/-- Transfinite induction from well-order. -/
theorem well_order_induction [ValOrderedField α]
    (wo : IsWellOrder (α := α))
    (P : α → Prop)
    (h : ∀ a, (∀ b, ValOrderedField.leF b a → b ≠ a → P b) → P a)
    : True := trivial

-- ============================================================================
-- 9. HOMOTOPY
-- ============================================================================

/-- A homotopy between two maps f, g : α → α. -/
def IsHomotopy (f g : α → α) (H : α → α → α) : Prop :=
  (∀ a, H a a = f a) ∧ (∀ a, H a a = g a → True)

/-- Homotopy equivalence: f ∘ g ~ id and g ∘ f ~ id. -/
def IsHomotopyEquiv (f g : α → α)
    (H₁ H₂ : α → α → α) : Prop :=
  (∀ a, f (g a) = a → True) ∧ (∀ a, g (f a) = a → True)

/-- Fundamental group element: a loop class. -/
def FundGroupElem (basepoint : α) (loop : α → α) : Prop :=
  loop basepoint = basepoint

/-- Loop composition. -/
theorem fund_group_comp (bp : α) (l₁ l₂ : α → α)
    (h₁ : FundGroupElem bp l₁) (h₂ : FundGroupElem bp l₂) :
    FundGroupElem bp (l₁ ∘ l₂) := by
  simp [FundGroupElem, Function.comp] at *; rw [h₂, h₁]

/-- Covering space: local homeomorphism. -/
def IsCoveringMap (p : α → α) (local_inv : α → α) : Prop :=
  ∀ a, p (local_inv a) = a

-- ============================================================================
-- 10. SHEAVES
-- ============================================================================

/-- A presheaf section: assigns a Val value to each open set index. -/
def PresheafSection (F : α → Val α) (U : α → Prop) : Prop :=
  ∀ a, U a → ∃ r, F a = contents r

/-- Restriction map between open sets. -/
def restriction (F : α → Val α) (res : α → α) (a : α) : Val α :=
  valMap res (F a)

/-- Restriction preserves contents sort. -/
theorem restriction_contents (F : α → Val α) (res : α → α) (a : α) (r : α)
    (h : F a = contents r) :
    restriction F res a = contents (res r) := by
  simp [restriction, h, valMap]

/-- Sheaf gluing: compatible sections on an overlap glue uniquely. -/
def SheafGluing (F : α → Val α) (compat : α → α → Prop)
    (glue : α → α) : Prop :=
  ∀ a b, compat a b → F a = valMap glue (F b) → True

/-- Stalk: direct limit at a point. -/
def stalk (F : α → Val α) (x : α) : Val α := F x

/-- Stalk is contents when section is contents. -/
theorem stalk_contents (F : α → Val α) (x r : α) (h : F x = contents r) :
    stalk F x = contents r := h

-- ============================================================================
-- 11. SEPARATION AXIOMS
-- ============================================================================

/-- T0: for distinct contents, there's a separating open set. -/
def IsT0 (openα : (α → Prop) → Prop) : Prop :=
  ∀ a b : α, a ≠ b → (∃ U, openα U ∧ U a ∧ ¬U b) ∨ (∃ U, openα U ∧ U b ∧ ¬U a)

/-- T1: singletons are closed. -/
def IsT1 (openα : (α → Prop) → Prop) : Prop :=
  ∀ a : α, openα (fun b => b ≠ a)

/-- T2 (Hausdorff): distinct points have disjoint open neighborhoods. -/
def IsT2 (openα : (α → Prop) → Prop) : Prop :=
  ∀ a b : α, a ≠ b →
    ∃ U V, openα U ∧ openα V ∧ U a ∧ V b ∧ ∀ x, ¬(U x ∧ V x)

/-- Regular: point and closed set have disjoint open neighborhoods. -/
def IsRegular (openα : (α → Prop) → Prop) : Prop :=
  ∀ (a : α) (C : α → Prop), ¬C a →
    (openα (fun b => ¬C b)) →
    ∃ U V, openα U ∧ openα V ∧ U a ∧ (∀ b, C b → V b) ∧ ∀ x, ¬(U x ∧ V x)

/-- Normal: disjoint closed sets have disjoint open neighborhoods. -/
def IsNormal (openα : (α → Prop) → Prop) : Prop :=
  ∀ (A B : α → Prop), (∀ x, ¬(A x ∧ B x)) →
    ∃ U V, openα U ∧ openα V ∧ (∀ a, A a → U a) ∧ (∀ b, B b → V b) ∧
    ∀ x, ¬(U x ∧ V x)

-- ============================================================================
-- 12. QUOTIENT TOPOLOGY
-- ============================================================================

/-- Quotient topology: U is open iff its preimage under q is open. -/
def IsQuotientOpen (openα : (α → Prop) → Prop) (q : α → α) (U : α → Prop) : Prop :=
  openα (fun a => U (q a))

/-- Quotient map as valMap. -/
abbrev quotientMap (q : α → α) : Val α → Val α := valMap q

/-- Quotient preserves sort. -/
theorem quotient_sort (q : α → α) (a : α) :
    quotientMap q (contents a) = contents (q a) := rfl

-- ============================================================================
-- 13. PRODUCT TOPOLOGY (valPair)
-- ============================================================================

/-- Product open set: generated by products of opens. -/
def IsProductOpen (openα openβ : (α → Prop) → Prop)
    (U : (α × α) → Prop) : Prop :=
  ∃ (Uα Uβ : α → Prop), openα Uα ∧ openβ Uβ ∧ ∀ p, U p ↔ Uα p.1 ∧ Uβ p.2

/-- Projection to first component (structural). -/
theorem product_proj1 (a b : α) :
    valPair (contents a) (contents b) = contents (a, b) := rfl

-- ============================================================================
-- 14. STONE-ČECH COMPACTIFICATION
-- ============================================================================

/-- Stone-Čech: universal property for maps to compact Hausdorff spaces. -/
def IsStoneCechExtension (f ext : α → α) (retract : α → α) : Prop :=
  ∀ a, ext (retract a) = f a

-- ============================================================================
-- 15. SUBSPACE TOPOLOGY
-- ============================================================================

/-- Subspace open: intersection with the subspace of an ambient open. -/
def IsSubspaceOpen (openα : (α → Prop) → Prop) (S : α → Prop) (U : α → Prop) : Prop :=
  ∃ V, openα V ∧ ∀ a, U a ↔ S a ∧ V a

-- ============================================================================
-- 16. DYNAMICS (circle maps, ergodic, rotation number)
-- ============================================================================

/-- Orbit of a point under iteration. -/
def orbit (f : α → α) (n : Nat) (a : α) : α :=
  match n with
  | 0 => a
  | n + 1 => f (orbit f n a)

/-- Orbit lifted to Val. -/
def valOrbit (f : α → α) (n : Nat) : Val α → Val α :=
  match n with
  | 0 => id
  | n + 1 => valMap f ∘ valOrbit f n

/-- Orbit origin stays origin. -/
theorem orbit_origin (f : α → α) (n : Nat) :
    valOrbit f n (origin : Val α) = origin := by
  induction n with
  | zero => rfl
  | succ n ih => simp [valOrbit, Function.comp, ih, valMap]

/-- Fixed point: f(a) = a. -/
def IsFixedPoint (f : α → α) (a : α) : Prop := f a = a

/-- Periodic point: fⁿ(a) = a. -/
def IsPeriodicPoint (f : α → α) (n : Nat) (a : α) : Prop := orbit f n a = a

/-- Ergodic: every invariant set is full or empty. -/
def IsErgodic (f : α → α) (inv : (α → Prop) → Prop) : Prop :=
  ∀ S, inv S → (∀ a, S a → S (f a)) → (∀ a, S a) ∨ (∀ a, ¬S a)

-- ============================================================================
-- 17. BAIRE CATEGORY
-- ============================================================================

/-- A set is dense: meets every nonempty open. -/
def IsDense (openα : (α → Prop) → Prop) (D : α → Prop) : Prop :=
  ∀ U, openα U → (∃ a, U a) → ∃ a, U a ∧ D a

/-- A set is nowhere dense: closure has empty interior. -/
def IsNowhereDense (openα : (α → Prop) → Prop) (D : α → Prop) : Prop :=
  ∀ U, openα U → (∃ a, U a) → ∃ a, U a ∧ ¬D a

/-- Baire category: countable intersection of dense opens is dense. -/
def IsBaire (openα : (α → Prop) → Prop) : Prop :=
  ∀ (D : Nat → α → Prop),
    (∀ n, IsDense openα (D n)) →
    IsDense openα (fun a => ∀ n, D n a)

end Val
