/-
Extracted from Topology/Defs/Basic.lean
Genuine: 19 of 19 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FunProp

/-!
# Basic definitions about topological spaces

This file contains definitions about topology that do not require imports
other than `Mathlib.Data.Set.Lattice`.

## Main definitions

* `TopologicalSpace X`: a typeclass endowing `X` with a topology.
  By definition, a topology is a collection of sets called *open sets* such that

  - `isOpen_univ`: the whole space is open;
  - `IsOpen.inter`: the intersection of two open sets is an open set;
  - `isOpen_sUnion`: the union of a family of open sets is an open set.

* `IsOpen s`: predicate saying that `s` is an open set, same as `TopologicalSpace.IsOpen`.

* `IsClosed s`: a set is called *closed*, if its complement is an open set.
  For technical reasons, this is a typeclass.

* `IsClopen s`: a set is *clopen* if it is both closed and open.

* `interior s`: the *interior* of a set `s` is the maximal open set that is included in `s`.

* `closure s`: the *closure* of a set `s` is the minimal closed set that includes `s`.

* `frontier s`: the *frontier* of a set is the set difference `closure s \ interior s`.
  A point `x` belongs to `frontier s`, if any neighborhood of `x`
  contains points both from `s` and `sᶜ`.

* `Dense s`: a set is *dense* if its closure is the whole space.
  We define it as `∀ x, x ∈ closure s` so that one can write `(h : Dense s) x`.

* `DenseRange f`: a function has *dense range*, if `Set.range f` is a dense set.

* `Continuous f`: a map is *continuous*, if the preimage of any open set is an open set.

* `IsOpenMap f`: a map is an *open map*, if the image of any open set is an open set.

* `IsClosedMap f`: a map is a *closed map*, if the image of any closed set is a closed set.

** Notation

We introduce notation `IsOpen[t]`, `IsClosed[t]`, `closure[t]`, `Continuous[t₁, t₂]`
that allow passing custom topologies to these predicates and functions without using `@`.
-/

universe u v

open Set

@[to_additive existing TopologicalSpace]
class TopologicalSpace (X : Type u) where
  /-- A predicate saying that a set is an open set. Use `IsOpen` in the root namespace instead. -/
  protected IsOpen : Set X → Prop
  /-- The set representing the whole space is an open set.
  Use `isOpen_univ` in the root namespace instead. -/
  protected isOpen_univ : IsOpen univ
  /-- The intersection of two open sets is an open set. Use `IsOpen.inter` instead. -/
  protected isOpen_inter : ∀ s t, IsOpen s → IsOpen t → IsOpen (s ∩ t)
  /-- The union of a family of open sets is an open set.
  Use `isOpen_sUnion` in the root namespace instead. -/
  protected isOpen_sUnion : ∀ s, (∀ t ∈ s, IsOpen t) → IsOpen (⋃₀ s)

variable {X : Type u} {Y : Type v}

/-! ### Predicates on sets -/

section Defs

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

def IsOpen : Set X → Prop := TopologicalSpace.IsOpen

@[simp] theorem isOpen_univ : IsOpen (univ : Set X) := TopologicalSpace.isOpen_univ

theorem IsOpen.inter (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) :=
  TopologicalSpace.isOpen_inter s t hs ht

theorem isOpen_sUnion {s : Set (Set X)} (h : ∀ t ∈ s, IsOpen t) : IsOpen (⋃₀ s) :=
  TopologicalSpace.isOpen_sUnion s h

class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ

def IsClopen (s : Set X) : Prop :=
  IsClosed s ∧ IsOpen s

def IsLocallyClosed (s : Set X) : Prop := ∃ (U Z : Set X), IsOpen U ∧ IsClosed Z ∧ s = U ∩ Z

def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }

def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }

def frontier (s : Set X) : Set X :=
  closure s \ interior s

def coborder (s : Set X) : Set X :=
  (closure s \ s)ᶜ

def Dense (s : Set X) : Prop :=
  ∀ x, x ∈ closure s

def DenseRange {α : Type*} (f : α → X) := Dense (range f)

@[fun_prop]
structure Continuous (f : X → Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : ∀ s, IsOpen s → IsOpen (f ⁻¹' s)

def IsOpenMap (f : X → Y) : Prop := ∀ U : Set X, IsOpen U → IsOpen (f '' U)

def IsClosedMap (f : X → Y) : Prop := ∀ U : Set X, IsClosed U → IsClosed (f '' U)

@[mk_iff]
structure IsOpenQuotientMap (f : X → Y) : Prop where
  /-- An open quotient map is surjective. -/
  surjective : Function.Surjective f
  /-- An open quotient map is continuous. -/
  continuous : Continuous f
  /-- An open quotient map is an open map. -/
  isOpenMap : IsOpenMap f

end Defs

/-! ### Notation for non-standard topologies -/

scoped[Topology] notation (name := IsOpen_of) "IsOpen[" t "]" => @IsOpen _ t

scoped[Topology] notation (name := IsClosed_of) "IsClosed[" t "]" => @IsClosed _ t

scoped[Topology] notation (name := closure_of) "closure[" t "]" => @closure _ t

scoped[Topology] notation (name := Continuous_of) "Continuous[" t₁ ", " t₂ "]" =>

  @Continuous _ _ t₁ t₂

class BaireSpace (X : Type*) [TopologicalSpace X] : Prop where
  baire_property : ∀ f : ℕ → Set X, (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Dense (⋂ n, f n)
