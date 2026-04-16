/-
Extracted from Data/Set/Operations.lean
Genuine: 39 | Conflates: 0 | Dissolved: 0 | Infrastructure: 18
-/
import Origin.Core
import Mathlib.Data.SProd
import Mathlib.Data.Subtype
import Mathlib.Order.Notation
import Mathlib.Util.CompileInductive

noncomputable section

/-!
# Basic definitions about sets

In this file we define various operations on sets.
We also provide basic lemmas needed to unfold the definitions.
More advanced theorems about these definitions are located in other files in `Mathlib/Data/Set`.

## Main definitions

- complement of a set and set difference;
- `Set.Elem`: coercion of a set to a type; it is reducibly equal to `{x // x ∈ s}`;
- `Set.preimage f s`, a.k.a. `f ⁻¹' s`: preimage of a set;
- `Set.range f`: the range of a function;
  it is more general than `f '' univ` because it allows functions from `Sort*`;
- `s ×ˢ t`: product of `s : Set α` and `t : Set β` as a set in `α × β`;
- `Set.diagonal`: the diagonal in `α × α`;
- `Set.offDiag s`: the part of `s ×ˢ s` that is off the diagonal;
- `Set.pi`: indexed product of a family of sets `∀ i, Set (α i)`,
  as a set in `∀ i, α i`;
- `Set.EqOn f g s`: the predicate saying that two functions are equal on a set;
- `Set.MapsTo f s t`: the predicate syaing that `f` sends all points of `s` to `t;
- `Set.MapsTo.restrict`: restrict `f : α → β` to `f' : s → t` provided that `Set.MapsTo f s t`;
- `Set.restrictPreimage`: restrict `f : α → β` to `f' : (f ⁻¹' t) → t`;
- `Set.InjOn`: the predicate saying that `f` is injective on a set;
- `Set.SurjOn f s t`: the prediate saying that `t ⊆ f '' s`;
- `Set.BijOn f s t`: the predicate saying that `f` is injective on `s` and `f '' s = t`;
- `Set.graphOn`: the graph of a function on a set;
- `Set.LeftInvOn`, `Set.RightInvOn`, `Set.InvOn`:
  the predicates saying that `f'` is a left, right or two-sided inverse of `f` on `s`, `t`, or both;
- `Set.image2`: the image of a pair of sets under a binary operation,
  mostly useful to define pointwise algebraic operations on sets;
- `Set.seq`: monadic `seq` operation on sets;
  we don't use monadic notation to ensure support for maps between different universes;

## Notations

- `f '' s`: image of a set;
- `f ⁻¹' s`: preimage of a set;
- `s ×ˢ t`: the product of sets;
- `s ∪ t`: the union of two sets;
- `s ∩ t`: the intersection of two sets;
- `sᶜ`: the complement of a set;
- `s \ t`: the difference of two sets.

## Keywords

set, image, preimage
-/

compile_def% Union.union

compile_def% Inter.inter

compile_def% SDiff.sdiff

compile_def% HasCompl.compl

compile_def% EmptyCollection.emptyCollection

compile_def% Insert.insert

compile_def% Singleton.singleton

attribute [ext] Set.ext

universe u v w

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w}

@[simp, mfld_simps] theorem mem_setOf_eq {x : α} {p : α → Prop} : (x ∈ {y | p y}) = p x := rfl

@[simp, mfld_simps] theorem mem_univ (x : α) : x ∈ @univ α := trivial

instance : HasCompl (Set α) := ⟨fun s ↦ {x | x ∉ s}⟩

@[simp] theorem mem_compl_iff (s : Set α) (x : α) : x ∈ sᶜ ↔ x ∉ s := Iff.rfl

@[simp] theorem mem_diff {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := Iff.rfl

theorem mem_diff_of_mem {s t : Set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t := ⟨h1, h2⟩

@[coe, reducible] def Elem (s : Set α) : Type u := {x // x ∈ s}

instance : CoeSort (Set α) (Type u) := ⟨Elem⟩

def preimage (f : α → β) (s : Set β) : Set α := {x | f x ∈ s}

infixl:80 " ⁻¹' " => preimage

@[simp, mfld_simps]
theorem mem_preimage {f : α → β} {s : Set β} {a : α} : a ∈ f ⁻¹' s ↔ f a ∈ s := Iff.rfl

infixl:80 " '' " => image

@[simp]
theorem mem_image (f : α → β) (s : Set α) (y : β) : y ∈ f '' s ↔ ∃ x ∈ s, f x = y :=
  Iff.rfl

@[mfld_simps]
theorem mem_image_of_mem (f : α → β) {x : α} {a : Set α} (h : x ∈ a) : f x ∈ f '' a :=
  ⟨_, h, rfl⟩

def imageFactorization (f : α → β) (s : Set α) : s → f '' s := fun p =>
  ⟨f p.1, mem_image_of_mem f p.2⟩

def kernImage (f : α → β) (s : Set α) : Set β := {y | ∀ ⦃x⦄, f x = y → x ∈ s}

lemma subset_kernImage_iff {s : Set β} {t : Set α} {f : α → β} : s ⊆ kernImage f t ↔ f ⁻¹' s ⊆ t :=
  ⟨fun h _ hx ↦ h hx rfl,
    fun h _ hx y hy ↦ h (show f y ∈ s from hy.symm ▸ hx)⟩

section Range

variable {ι : Sort*} {f : ι → α}

def range (f : ι → α) : Set α := {x | ∃ y, f y = x}

@[simp] theorem mem_range {x : α} : x ∈ range f ↔ ∃ y, f y = x := Iff.rfl

@[mfld_simps] theorem mem_range_self (i : ι) : f i ∈ range f := ⟨i, rfl⟩

def rangeFactorization (f : ι → α) : ι → range f := fun i => ⟨f i, mem_range_self i⟩

end Range

noncomputable def rangeSplitting (f : α → β) : range f → α := fun x => x.2.choose

theorem apply_rangeSplitting (f : α → β) (x : range f) : f (rangeSplitting f x) = x :=
  x.2.choose_spec

@[simp]
theorem comp_rangeSplitting (f : α → β) : f ∘ rangeSplitting f = Subtype.val := by
  ext
  simp only [Function.comp_apply]
  apply apply_rangeSplitting

section Prod

def prod (s : Set α) (t : Set β) : Set (α × β) := {p | p.1 ∈ s ∧ p.2 ∈ t}

@[default_instance]
instance instSProd : SProd (Set α) (Set β) (Set (α × β)) where
  sprod := Set.prod

variable {a : α} {b : β} {s : Set α} {t : Set β} {p : α × β}

@[simp, mfld_simps]
theorem mem_prod : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t := .rfl

theorem mk_mem_prod (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t := ⟨ha, hb⟩

end Prod

section Diagonal

def diagonal (α : Type*) : Set (α × α) := {p | p.1 = p.2}

@[simp] theorem mem_diagonal_iff {x : α × α} : x ∈ diagonal α ↔ x.1 = x.2 := .rfl

def offDiag (s : Set α) : Set (α × α) := {x | x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2}

@[simp]
theorem mem_offDiag {x : α × α} {s : Set α} : x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 :=
  Iff.rfl

end Diagonal

section Pi

variable {ι : Type*} {α : ι → Type*}

def pi (s : Set ι) (t : ∀ i, Set (α i)) : Set (∀ i, α i) := {f | ∀ i ∈ s, f i ∈ t i}

variable {s : Set ι} {t : ∀ i, Set (α i)} {f : ∀ i, α i}

@[simp] theorem mem_pi : f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i := .rfl

end Pi

def EqOn (f₁ f₂ : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → f₁ x = f₂ x

def MapsTo (f : α → β) (s : Set α) (t : Set β) : Prop := ∀ ⦃x⦄, x ∈ s → f x ∈ t

theorem mapsTo_image (f : α → β) (s : Set α) : MapsTo f s (f '' s) := fun _ ↦ mem_image_of_mem f

theorem mapsTo_preimage (f : α → β) (t : Set β) : MapsTo f (f ⁻¹' t) t := fun _ ↦ id

def MapsTo.restrict (f : α → β) (s : Set α) (t : Set β) (h : MapsTo f s t) : s → t :=
  Subtype.map f h

@[simps!]
def restrictPreimage (t : Set β) (f : α → β) : f ⁻¹' t → t :=
  (Set.mapsTo_preimage f t).restrict _ _ _

def InjOn (f : α → β) (s : Set α) : Prop :=
  ∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂

def graphOn (f : α → β) (s : Set α) : Set (α × β) := (fun x ↦ (x, f x)) '' s

def SurjOn (f : α → β) (s : Set α) (t : Set β) : Prop := t ⊆ f '' s

def BijOn (f : α → β) (s : Set α) (t : Set β) : Prop := MapsTo f s t ∧ InjOn f s ∧ SurjOn f s t

def LeftInvOn (f' : β → α) (f : α → β) (s : Set α) : Prop := ∀ ⦃x⦄, x ∈ s → f' (f x) = x

abbrev RightInvOn (f' : β → α) (f : α → β) (t : Set β) : Prop := LeftInvOn f f' t

def InvOn (g : β → α) (f : α → β) (s : Set α) (t : Set β) : Prop :=
  LeftInvOn g f s ∧ RightInvOn g f t

section image2

def image2 (f : α → β → γ) (s : Set α) (t : Set β) : Set γ := {c | ∃ a ∈ s, ∃ b ∈ t, f a b = c}

variable {f : α → β → γ} {s : Set α} {t : Set β} {a : α} {b : β} {c : γ}

@[simp] theorem mem_image2 : c ∈ image2 f s t ↔ ∃ a ∈ s, ∃ b ∈ t, f a b = c := .rfl

theorem mem_image2_of_mem (ha : a ∈ s) (hb : b ∈ t) : f a b ∈ image2 f s t :=
  ⟨a, ha, b, hb, rfl⟩

end image2

def seq (s : Set (α → β)) (t : Set α) : Set β := image2 (fun f ↦ f) s t

@[simp]
theorem mem_seq_iff {s : Set (α → β)} {t : Set α} {b : β} :
    b ∈ seq s t ↔ ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b :=
  Iff.rfl

end Set
