/-
Extracted from Order/Filter/Defs.lean
Genuine: 38 | Conflates: 1 | Dissolved: 0 | Infrastructure: 21
-/
import Origin.Core
import Mathlib.Order.SetNotation
import Mathlib.Order.Bounds.Defs
import Mathlib.Data.Set.Basic

noncomputable section

/-!
# Definitions about filters

A *filter* on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. Filters are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

## Main definitions

* `Filter` : filters on a set;
* `Filter.principal`, `𝓟 s` : filter of all sets containing a given set;
* `Filter.map`, `Filter.comap` : operations on filters;
* `Filter.Tendsto` : limit with respect to filters;
* `Filter.Eventually` : `f.Eventually p` means `{x | p x} ∈ f`;
* `Filter.Frequently` : `f.Frequently p` means `{x | ¬p x} ∉ f`;
* `filter_upwards [h₁, ..., hₙ]` :
  a tactic that takes a list of proofs `hᵢ : sᵢ ∈ f`,
  and replaces a goal `s ∈ f` with `∀ x, x ∈ s₁ → ... → x ∈ sₙ → x ∈ s`;
* `Filter.NeBot f` : a utility class stating that `f` is a non-trivial filter.
* `Filter.IsBounded r f`: the filter `f` is eventually bounded w.r.t. the relation `r`,
  i.e. eventually, it is bounded by some uniform bound.
  `r` will be usually instantiated with `(· ≤ ·)` or `(· ≥ ·)`.
* `Filter.IsCobounded r f` states that the filter `f` does not tend to infinity w.r.t. `r`.
  This is also called frequently bounded. Will be usually instantiated with `(· ≤ ·)` or `(· ≥ ·)`.

## Notations

* `∀ᶠ x in f, p x` : `f.Eventually p`;
* `∃ᶠ x in f, p x` : `f.Frequently p`;
* `f =ᶠ[l] g` : `∀ᶠ x in l, f x = g x`;
* `f ≤ᶠ[l] g` : `∀ᶠ x in l, f x ≤ g x`;
* `𝓟 s` : `Filter.Principal s`, localized in `Filter`.

## Implementation Notes

Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`,
which we do *not* require.
This gives `Filter X` better formal properties,
in particular a bottom element `⊥` for its lattice structure,
at the cost of including the assumption `[NeBot f]` in a number of lemmas and definitions.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]
-/

open Set

structure Filter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ ∈ sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets

namespace Filter

variable {α β : Type*} {f g : Filter α} {s t : Set α}

theorem filter_eq : ∀ {f g : Filter α}, f.sets = g.sets → f = g
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

instance instMembership : Membership (Set α) (Filter α) := ⟨fun F U => U ∈ F.sets⟩

@[ext]
protected theorem ext (h : ∀ s, s ∈ f ↔ s ∈ g) : f = g := filter_eq <| Set.ext h

@[simp]
theorem univ_mem : univ ∈ f :=
  f.univ_sets

theorem mem_of_superset {x y : Set α} (hx : x ∈ f) (hxy : x ⊆ y) : y ∈ f :=
  f.sets_of_superset hx hxy

theorem univ_mem' (h : ∀ a, a ∈ s) : s ∈ f :=
  mem_of_superset univ_mem fun x _ => h x

theorem inter_mem (hs : s ∈ f) (ht : t ∈ f) : s ∩ t ∈ f :=
  f.inter_sets hs ht

theorem mp_mem (hs : s ∈ f) (h : { x | x ∈ s → x ∈ t } ∈ f) : t ∈ f :=
  mem_of_superset (inter_mem hs h) fun _ ⟨h₁, h₂⟩ => h₂ h₁

protected def copy (f : Filter α) (S : Set (Set α)) (hmem : ∀ s, s ∈ S ↔ s ∈ f) : Filter α where
  sets := S
  univ_sets := (hmem _).2 univ_mem
  sets_of_superset h hsub := (hmem _).2 <| mem_of_superset ((hmem _).1 h) hsub
  inter_sets h₁ h₂ := (hmem _).2 <| inter_mem ((hmem _).1 h₁) ((hmem _).1 h₂)

def comk (p : Set α → Prop) (he : p ∅) (hmono : ∀ t, p t → ∀ s ⊆ t, p s)
    (hunion : ∀ s, p s → ∀ t, p t → p (s ∪ t)) : Filter α where
  sets := {t | p tᶜ}
  univ_sets := by simpa
  sets_of_superset := fun ht₁ ht => hmono _ ht₁ _ (compl_subset_compl.2 ht)
  inter_sets := fun ht₁ ht₂ => by simp [compl_inter, hunion _ ht₁ _ ht₂]

@[simp]
lemma mem_comk {p : Set α → Prop} {he hmono hunion s} :
    s ∈ comk p he hmono hunion ↔ p sᶜ :=
  .rfl

def principal (s : Set α) : Filter α where
  sets := { t | s ⊆ t }
  univ_sets := subset_univ s
  sets_of_superset hx := Subset.trans hx
  inter_sets := subset_inter

scoped notation "𝓟" => Filter.principal

instance : Pure Filter where
  pure x := .copy (𝓟 {x}) {s | x ∈ s} fun _ ↦ by simp

def ker (f : Filter α) : Set α := ⋂₀ f.sets

def join (f : Filter (Filter α)) : Filter α where
  sets := { s | { t : Filter α | s ∈ t } ∈ f }
  univ_sets := by simp only [mem_setOf_eq, univ_mem, setOf_true]
  sets_of_superset hx xy := mem_of_superset hx fun f h => mem_of_superset h xy
  inter_sets hx hy := mem_of_superset (inter_mem hx hy) fun f ⟨h₁, h₂⟩ => inter_mem h₁ h₂

instance : PartialOrder (Filter α) where
  le f g := ∀ ⦃U : Set α⦄, U ∈ g → U ∈ f
  le_antisymm a b h₁ h₂ := filter_eq <| Subset.antisymm h₂ h₁
  le_refl a := Subset.rfl
  le_trans a b c h₁ h₂ := Subset.trans h₂ h₁

instance instSupSet : SupSet (Filter α) where
  sSup S := join (𝓟 S)

@[simp] theorem mem_sSup {S : Set (Filter α)} : s ∈ sSup S ↔ ∀ f ∈ S, s ∈ f := .rfl

@[irreducible]
protected def sInf (s : Set (Filter α)) : Filter α := sSup (lowerBounds s)

instance instInfSet : InfSet (Filter α) where
  sInf := Filter.sInf

protected theorem sSup_lowerBounds (s : Set (Filter α)) : sSup (lowerBounds s) = sInf s := by
  simp [sInf, Filter.sInf]

instance : Top (Filter α) where
  top := .copy (sSup (Set.range pure)) {s | ∀ x, x ∈ s} <| by simp

theorem mem_top_iff_forall {s : Set α} : s ∈ (⊤ : Filter α) ↔ ∀ x, x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_top {s : Set α} : s ∈ (⊤ : Filter α) ↔ s = univ := by
  rw [mem_top_iff_forall, eq_univ_iff_forall]

instance : Bot (Filter α) where
  bot := .copy (sSup ∅) univ <| by simp

@[simp]
theorem mem_bot {s : Set α} : s ∈ (⊥ : Filter α) :=
  trivial

instance instInf : Min (Filter α) :=
  ⟨fun f g : Filter α =>
    { sets := { s | ∃ a ∈ f, ∃ b ∈ g, s = a ∩ b }
      univ_sets := ⟨_, univ_mem, _, univ_mem, by simp⟩
      sets_of_superset := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ xy
        refine ⟨a ∪ y, mem_of_superset ha subset_union_left, b ∪ y,
          mem_of_superset hb subset_union_left, ?_⟩
        rw [← inter_union_distrib_right, union_eq_self_of_subset_left xy]
      inter_sets := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
        refine ⟨a ∩ c, inter_mem ha hc, b ∩ d, inter_mem hb hd, ?_⟩
        ac_rfl }⟩

instance instSup : Max (Filter α) where
  max f g := .copy (sSup {f, g}) {s | s ∈ f ∧ s ∈ g} <| by simp

-- CONFLATES (assumes ground = zero): NeBot
class NeBot (f : Filter α) : Prop where
  /-- The filter is nontrivial: `f ≠ ⊥` or equivalently, `∅ ∉ f`. -/
  ne' : f ≠ ⊥

theorem neBot_iff {f : Filter α} : NeBot f ↔ f ≠ ⊥ :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

protected def Eventually (p : α → Prop) (f : Filter α) : Prop :=
  { x | p x } ∈ f

notation3 "∀ᶠ "(...)" in "f", "r:(scoped p => Filter.Eventually p f) => r

@[inherit_doc Filter.Eventually]
protected def Frequently (p : α → Prop) (f : Filter α) : Prop :=
  ¬∀ᶠ x in f, ¬p x

notation3 "∃ᶠ "(...)" in "f", "r:(scoped p => Filter.Frequently p f) => r

@[inherit_doc Filter.Frequently]
def EventuallyEq (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x = g x

notation:50 f " =ᶠ[" l:50 "] " g:50 => EventuallyEq l f g

def EventuallyLE [LE β] (l : Filter α) (f g : α → β) : Prop :=
  ∀ᶠ x in l, f x ≤ g x

notation:50 f " ≤ᶠ[" l:50 "] " g:50 => EventuallyLE l f g

def map (m : α → β) (f : Filter α) : Filter β where
  sets := preimage m ⁻¹' f.sets
  univ_sets := univ_mem
  sets_of_superset hs st := mem_of_superset hs fun _x hx ↦ st hx
  inter_sets hs ht := inter_mem hs ht

def Tendsto (f : α → β) (l₁ : Filter α) (l₂ : Filter β) :=
  l₁.map f ≤ l₂

def comap (m : α → β) (f : Filter β) : Filter α where
  sets := { s | ∃ t ∈ f, m ⁻¹' t ⊆ s }
  univ_sets := ⟨univ, univ_mem, subset_univ _⟩
  sets_of_superset := fun ⟨a', ha', ma'a⟩ ab => ⟨a', ha', ma'a.trans ab⟩
  inter_sets := fun ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩ =>
    ⟨a' ∩ b', inter_mem ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩

protected def coprod (f : Filter α) (g : Filter β) : Filter (α × β) :=
  f.comap Prod.fst ⊔ g.comap Prod.snd

instance instSProd : SProd (Filter α) (Filter β) (Filter (α × β)) where
  sprod f g := f.comap Prod.fst ⊓ g.comap Prod.snd

protected def prod (f : Filter α) (g : Filter β) : Filter (α × β) := f ×ˢ g

def bind (f : Filter α) (m : α → Filter β) : Filter β :=
  join (map m f)

def seq (f : Filter (α → β)) (g : Filter α) : Filter β where
  sets := { s | ∃ u ∈ f, ∃ t ∈ g, ∀ m ∈ u, ∀ x ∈ t, (m : α → β) x ∈ s }
  univ_sets := ⟨univ, univ_mem, univ, univ_mem, fun _ _ _ _ => trivial⟩
  sets_of_superset := fun ⟨t₀, t₁, h₀, h₁, h⟩ hst =>
    ⟨t₀, t₁, h₀, h₁, fun _ hx _ hy => hst <| h _ hx _ hy⟩
  inter_sets := fun ⟨t₀, ht₀, t₁, ht₁, ht⟩ ⟨u₀, hu₀, u₁, hu₁, hu⟩ =>
    ⟨t₀ ∩ u₀, inter_mem ht₀ hu₀, t₁ ∩ u₁, inter_mem ht₁ hu₁, fun _ ⟨hx₀, hx₁⟩ _ ⟨hy₀, hy₁⟩ =>
      ⟨ht _ hx₀ _ hy₀, hu _ hx₁ _ hy₁⟩⟩

def curry (f : Filter α) (g : Filter β) : Filter (α × β) :=
  bind f fun a ↦ map (a, ·) g

instance : Bind Filter :=
  ⟨@Filter.bind⟩

instance : Functor Filter where map := @Filter.map

protected def lift (f : Filter α) (g : Set α → Filter β) :=
  ⨅ s ∈ f, g s

protected def lift' (f : Filter α) (h : Set α → Set β) :=
  f.lift (𝓟 ∘ h)

def IsBounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ᶠ x in f, r x b

def IsBoundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (map u f).IsBounded r

def IsCobounded (r : α → α → Prop) (f : Filter α) :=
  ∃ b, ∀ a, (∀ᶠ x in f, r x a) → r b a

def IsCoboundedUnder (r : α → α → Prop) (f : Filter β) (u : β → α) :=
  (map u f).IsCobounded r

end Filter

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

syntax (name := filterUpwards) "filter_upwards" (" [" term,* "]")?
  (" with" (ppSpace colGt term:max)*)? (" using " term)? : tactic

elab_rules : tactic

| `(tactic| filter_upwards $[[$[$args],*]]? $[with $wth*]? $[using $usingArg]?) => do

  let config : ApplyConfig := {newGoals := ApplyNewGoals.nonDependentOnly}

  for e in args.getD #[] |>.reverse do

    let goal ← getMainGoal

    replaceMainGoal <| ← goal.withContext <| runTermElab do

      let m ← mkFreshExprMVar none

      let lem ← Term.elabTermEnsuringType

        (← ``(Filter.mp_mem $e $(← Term.exprToSyntax m))) (← goal.getType)

      goal.assign lem

      return [m.mvarId!]

  liftMetaTactic fun goal => do

    goal.apply (← mkConstWithFreshMVarLevels ``Filter.univ_mem') config

  evalTactic <|← `(tactic| dsimp (config := {zeta := false}) only [Set.mem_setOf_eq])

  if let some l := wth then

    evalTactic <|← `(tactic| intro $[$l]*)

  if let some e := usingArg then

    evalTactic <|← `(tactic| exact $e)

end Mathlib.Tactic
