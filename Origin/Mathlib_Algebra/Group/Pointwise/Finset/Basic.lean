/-
Extracted from Algebra/Group/Pointwise/Finset/Basic.lean
Genuine: 306 | Conflates: 4 | Dissolved: 0 | Infrastructure: 46
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn
import Mathlib.Data.Finset.Density
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Set.Pointwise.SMul

noncomputable section

/-!
# Pointwise operations of finsets

This file defines pointwise algebraic operations on finsets.

## Main declarations

For finsets `s` and `t`:
* `0` (`Finset.zero`): The singleton `{0}`.
* `1` (`Finset.one`): The singleton `{1}`.
* `-s` (`Finset.neg`): Negation, finset of all `-x` where `x ∈ s`.
* `s⁻¹` (`Finset.inv`): Inversion, finset of all `x⁻¹` where `x ∈ s`.
* `s + t` (`Finset.add`): Addition, finset of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s * t` (`Finset.mul`): Multiplication, finset of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s - t` (`Finset.sub`): Subtraction, finset of all `x - y` where `x ∈ s` and `y ∈ t`.
* `s / t` (`Finset.div`): Division, finset of all `x / y` where `x ∈ s` and `y ∈ t`.
* `s +ᵥ t` (`Finset.vadd`): Scalar addition, finset of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s • t` (`Finset.smul`): Scalar multiplication, finset of all `x • y` where `x ∈ s` and
  `y ∈ t`.
* `s -ᵥ t` (`Finset.vsub`): Scalar subtraction, finset of all `x -ᵥ y` where `x ∈ s` and
  `y ∈ t`.
* `a • s` (`Finset.smulFinset`): Scaling, finset of all `a • x` where `x ∈ s`.
* `a +ᵥ s` (`Finset.vaddFinset`): Translation, finset of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `Finset α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

## Implementation notes

We put all instances in the locale `Pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the locale to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`.

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

open Function MulOpposite

open scoped Pointwise

variable {F α β γ : Type*}

namespace Finset

/-! ### `0`/`1` as finsets -/

section One

variable [One α] {s : Finset α} {a : α}

@[to_additive "The finset `0 : Finset α` is defined as `{0}` in locale `Pointwise`."]
protected def one : One (Finset α) :=
  ⟨{1}⟩

scoped[Pointwise] attribute [instance] Finset.one Finset.zero

@[to_additive (attr := simp)]
theorem mem_one : a ∈ (1 : Finset α) ↔ a = 1 :=
  mem_singleton

@[to_additive (attr := simp, norm_cast)]
theorem coe_one : ↑(1 : Finset α) = (1 : Set α) :=
  coe_singleton 1

@[to_additive (attr := simp, norm_cast)]
lemma coe_eq_one : (s : Set α) = 1 ↔ s = 1 := coe_eq_singleton

@[to_additive (attr := simp)]
theorem one_subset : (1 : Finset α) ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff

@[to_additive]
theorem singleton_one : ({1} : Finset α) = 1 :=
  rfl

@[to_additive]
theorem one_mem_one : (1 : α) ∈ (1 : Finset α) :=
  mem_singleton_self _

@[to_additive (attr := simp, aesop safe apply (rule_sets := [finsetNonempty]))]
theorem one_nonempty : (1 : Finset α).Nonempty :=
  ⟨1, one_mem_one⟩

@[to_additive (attr := simp)]
protected theorem map_one {f : α ↪ β} : map f 1 = {f 1} :=
  map_singleton f 1

@[to_additive (attr := simp)]
theorem image_one [DecidableEq β] {f : α → β} : image f 1 = {f 1} :=
  image_singleton _ _

@[to_additive]
theorem subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff

@[to_additive]
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s ⊆ 1 ↔ s = 1 :=
  h.subset_singleton_iff

@[to_additive (attr := simp)]
theorem card_one : (1 : Finset α).card = 1 :=
  card_singleton _

@[to_additive "The singleton operation as a `ZeroHom`."]
def singletonOneHom : OneHom α (Finset α) where
  toFun := singleton; map_one' := singleton_one

@[to_additive (attr := simps) "Lift a `ZeroHom` to `Finset` via `image`"]
def imageOneHom [DecidableEq β] [One β] [FunLike F α β] [OneHomClass F α β] (f : F) :
    OneHom (Finset α) (Finset β) where
  toFun := Finset.image f
  map_one' := by rw [image_one, map_one, singleton_one]

@[to_additive (attr := simp)]
lemma sup_one [SemilatticeSup β] [OrderBot β] (f : α → β) : sup 1 f = f 1 := sup_singleton

@[to_additive (attr := simp)]
lemma inf_one [SemilatticeInf β] [OrderTop β] (f : α → β) : inf 1 f = f 1 := inf_singleton

end One

/-! ### Finset negation/inversion -/

section Inv

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

@[to_additive
      "The pointwise negation of finset `-s` is defined as `{-x | x ∈ s}` in locale `Pointwise`."]
protected def inv : Inv (Finset α) :=
  ⟨image Inv.inv⟩

scoped[Pointwise] attribute [instance] Finset.inv Finset.neg

@[to_additive] lemma image_inv_eq_inv (s : Finset α) : s.image (·⁻¹) = s⁻¹ := rfl

@[to_additive]
theorem mem_inv {x : α} : x ∈ s⁻¹ ↔ ∃ y ∈ s, y⁻¹ = x :=
  mem_image

@[to_additive]
theorem inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ :=
  mem_image_of_mem _ ha

@[to_additive]
theorem card_inv_le : s⁻¹.card ≤ s.card :=
  card_image_le

@[to_additive (attr := simp)]
theorem inv_empty : (∅ : Finset α)⁻¹ = ∅ :=
  image_empty _

@[to_additive (attr := simp)]
theorem inv_nonempty_iff : s⁻¹.Nonempty ↔ s.Nonempty := image_nonempty

alias ⟨Nonempty.of_inv, Nonempty.inv⟩ := inv_nonempty_iff

attribute [to_additive] Nonempty.inv Nonempty.of_inv

attribute [aesop safe apply (rule_sets := [finsetNonempty])] Nonempty.inv Nonempty.neg

@[to_additive (attr := simp)]
theorem inv_eq_empty : s⁻¹ = ∅ ↔ s = ∅ := image_eq_empty

@[to_additive (attr := mono, gcongr)]
theorem inv_subset_inv (h : s ⊆ t) : s⁻¹ ⊆ t⁻¹ :=
  image_subset_image h

@[to_additive (attr := simp)]
theorem inv_singleton (a : α) : ({a} : Finset α)⁻¹ = {a⁻¹} :=
  image_singleton _ _

@[to_additive (attr := simp)]
theorem inv_insert (a : α) (s : Finset α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ :=
  image_insert _ _ _

@[to_additive (attr := simp)]
lemma sup_inv [SemilatticeSup β] [OrderBot β] (s : Finset α) (f : α → β) :
    sup s⁻¹ f = sup s (f ·⁻¹) :=
  sup_image ..

@[to_additive (attr := simp)]
lemma sup'_inv [SemilatticeSup β] {s : Finset α} (hs : s⁻¹.Nonempty) (f : α → β) :
    sup' s⁻¹ hs f = sup' s hs.of_inv (f ·⁻¹) :=
  sup'_image ..

@[to_additive (attr := simp)]
lemma inf_inv [SemilatticeInf β] [OrderTop β] (s : Finset α) (f : α → β) :
    inf s⁻¹ f = inf s (f ·⁻¹) :=
  inf_image ..

@[to_additive (attr := simp)]
lemma inf'_inv [SemilatticeInf β] {s : Finset α} (hs : s⁻¹.Nonempty) (f : α → β) :
    inf' s⁻¹ hs f = inf' s hs.of_inv (f ·⁻¹) :=
  inf'_image ..

@[to_additive] lemma image_op_inv (s : Finset α) : s⁻¹.image op = (s.image op)⁻¹ :=
  image_comm op_inv

@[to_additive]
lemma map_op_inv (s : Finset α) : s⁻¹.map opEquiv.toEmbedding = (s.map opEquiv.toEmbedding)⁻¹ := by
  simp [map_eq_image, image_op_inv]

end Inv

open Pointwise

section InvolutiveInv

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

@[to_additive (attr := simp)]
lemma mem_inv' : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := by simp [mem_inv, inv_eq_iff_eq_inv]

@[to_additive (attr := simp, norm_cast)]
theorem coe_inv (s : Finset α) : ↑s⁻¹ = (s : Set α)⁻¹ := coe_image.trans Set.image_inv_eq_inv

@[to_additive (attr := simp)]
theorem card_inv (s : Finset α) : s⁻¹.card = s.card := card_image_of_injective _ inv_injective

@[to_additive (attr := simp)]
lemma dens_inv [Fintype α] (s : Finset α) : s⁻¹.dens = s.dens := by simp [dens]

@[to_additive (attr := simp)]
theorem preimage_inv (s : Finset α) : s.preimage (·⁻¹) inv_injective.injOn = s⁻¹ :=
  coe_injective <| by rw [coe_preimage, Set.inv_preimage, coe_inv]

@[to_additive (attr := simp)]
lemma inv_univ [Fintype α] : (univ : Finset α)⁻¹ = univ := by ext; simp

@[to_additive (attr := simp)]
lemma inv_inter (s t : Finset α) : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ := coe_injective <| by simp

end InvolutiveInv

/-! ### Scalar addition/multiplication of finsets -/

section SMul

variable [DecidableEq β] [SMul α β] {s s₁ s₂ : Finset α} {t t₁ t₂ u : Finset β} {a : α} {b : β}

@[to_additive "The pointwise sum of two finsets `s` and `t`: `s +ᵥ t = {x +ᵥ y | x ∈ s, y ∈ t}`."]
protected def smul : SMul (Finset α) (Finset β) := ⟨image₂ (· • ·)⟩

scoped[Pointwise] attribute [instance] Finset.smul Finset.vadd

@[to_additive] lemma mem_smul {x : β} : x ∈ s • t ↔ ∃ y ∈ s, ∃ z ∈ t, y • z = x := mem_image₂

@[to_additive (attr := simp, norm_cast)]
lemma coe_smul (s : Finset α) (t : Finset β) : ↑(s • t) = (s : Set α) • (t : Set β) := coe_image₂ ..

@[to_additive] lemma smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t := mem_image₂_of_mem

@[to_additive] lemma card_smul_le : #(s • t) ≤ #s * #t := card_image₂_le ..

@[to_additive (attr := simp)]
lemma empty_smul (t : Finset β) : (∅ : Finset α) • t = ∅ := image₂_empty_left

@[to_additive (attr := simp)]
lemma smul_empty (s : Finset α) : s • (∅ : Finset β) = ∅ := image₂_empty_right

@[to_additive (attr := simp)]
lemma smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff

@[to_additive (attr := simp)]
lemma smul_nonempty_iff : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
lemma Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty := .image₂

@[to_additive] lemma Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty := .of_image₂_left

@[to_additive] lemma Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty := .of_image₂_right

@[to_additive]
lemma smul_singleton (b : β) : s • ({b} : Finset β) = s.image (· • b) := image₂_singleton_right

@[to_additive]
lemma singleton_smul_singleton (a : α) (b : β) : ({a} : Finset α) • ({b} : Finset β) = {a • b} :=
  image₂_singleton

@[to_additive (attr := mono, gcongr)]
lemma smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ := image₂_subset

@[to_additive] lemma smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ := image₂_subset_left

@[to_additive] lemma smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t := image₂_subset_right

@[to_additive] lemma smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u := image₂_subset_iff

@[to_additive]
lemma union_smul [DecidableEq α] : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t := image₂_union_left

@[to_additive]
lemma smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ := image₂_union_right

@[to_additive]
lemma inter_smul_subset [DecidableEq α] : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image₂_inter_subset_left

@[to_additive]
lemma smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ := image₂_inter_subset_right

@[to_additive]
lemma inter_smul_union_subset_union [DecidableEq α] : (s₁ ∩ s₂) • (t₁ ∪ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image₂_inter_union_subset_union

@[to_additive]
lemma union_smul_inter_subset_union [DecidableEq α] : (s₁ ∪ s₂) • (t₁ ∩ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image₂_union_inter_subset_union

@[to_additive
"If a finset `u` is contained in the scalar sum of two sets `s +ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' +ᵥ t'`."]
lemma subset_smul {s : Set α} {t : Set β} :
    ↑u ⊆ s • t → ∃ (s' : Finset α) (t' : Finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' • t' :=
  subset_set_image₂

end SMul

/-! ### Translation/scaling of finsets -/

section SMul

variable [DecidableEq β] [SMul α β] {s s₁ s₂ t : Finset β} {a : α} {b : β}

@[to_additive "The translation of a finset `s` by a vector `a`: `a +ᵥ s = {a +ᵥ x | x ∈ s}`."]
protected def smulFinset : SMul α (Finset β) where smul a := image <| (a • ·)

scoped[Pointwise] attribute [instance] Finset.smulFinset Finset.vaddFinset

@[to_additive] lemma smul_finset_def : a • s = s.image (a • ·) := rfl

@[to_additive] lemma image_smul : s.image (a • ·) = a • s := rfl

@[to_additive]
lemma mem_smul_finset {x : β} : x ∈ a • s ↔ ∃ y, y ∈ s ∧ a • y = x := by
  simp only [Finset.smul_finset_def, and_assoc, mem_image, exists_prop, Prod.exists, mem_product]

@[to_additive (attr := simp, norm_cast)]
lemma coe_smul_finset (a : α) (s : Finset β) : ↑(a • s) = a • (↑s : Set β) := coe_image

@[to_additive] lemma smul_mem_smul_finset : b ∈ s → a • b ∈ a • s := mem_image_of_mem _

@[to_additive] lemma smul_finset_card_le : (a • s).card ≤ s.card := card_image_le

@[to_additive (attr := simp)]
lemma smul_finset_empty (a : α) : a • (∅ : Finset β) = ∅ := image_empty _

@[to_additive (attr := simp)]
lemma smul_finset_eq_empty : a • s = ∅ ↔ s = ∅ := image_eq_empty

@[to_additive (attr := simp)]
lemma smul_finset_nonempty : (a • s).Nonempty ↔ s.Nonempty := image_nonempty

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
lemma Nonempty.smul_finset (hs : s.Nonempty) : (a • s).Nonempty :=
  hs.image _

@[to_additive (attr := simp)]
lemma singleton_smul (a : α) : ({a} : Finset α) • t = a • t := image₂_singleton_left

@[to_additive (attr := mono, gcongr)]
lemma smul_finset_subset_smul_finset : s ⊆ t → a • s ⊆ a • t := image_subset_image

@[to_additive (attr := simp)]
lemma smul_finset_singleton (b : β) : a • ({b} : Finset β) = {a • b} := image_singleton ..

@[to_additive]
lemma smul_finset_union : a • (s₁ ∪ s₂) = a • s₁ ∪ a • s₂ := image_union _ _

@[to_additive]
lemma smul_finset_insert (a : α) (b : β) (s : Finset β) : a • insert b s = insert (a • b) (a • s) :=
  image_insert ..

@[to_additive]
lemma smul_finset_inter_subset : a • (s₁ ∩ s₂) ⊆ a • s₁ ∩ a • s₂ := image_inter_subset _ _ _

@[to_additive]
lemma smul_finset_subset_smul {s : Finset α} : a ∈ s → a • t ⊆ s • t := image_subset_image₂_right

@[to_additive (attr := simp)]
lemma biUnion_smul_finset (s : Finset α) (t : Finset β) : s.biUnion (· • t) = s • t :=
  biUnion_image_left

end SMul

open scoped Pointwise

/-! ### Finset addition/multiplication -/

section Mul

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

@[to_additive
      "The pointwise addition of finsets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in
      locale `Pointwise`."]
protected def mul : Mul (Finset α) :=
  ⟨image₂ (· * ·)⟩

scoped[Pointwise] attribute [instance] Finset.mul Finset.add

@[to_additive]
theorem mem_mul {x : α} : x ∈ s * t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := mem_image₂

@[to_additive (attr := simp, norm_cast)]
theorem coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t :=
  coe_image₂ _ _ _

@[to_additive]
theorem mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t :=
  mem_image₂_of_mem

@[to_additive]
theorem card_mul_le : (s * t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _

@[to_additive]
theorem card_mul_iff :
    (s * t).card = s.card * t.card ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 :=
  card_image₂_iff

@[to_additive (attr := simp)]
theorem empty_mul (s : Finset α) : ∅ * s = ∅ :=
  image₂_empty_left

@[to_additive (attr := simp)]
theorem mul_empty (s : Finset α) : s * ∅ = ∅ :=
  image₂_empty_right

@[to_additive (attr := simp)]
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

@[to_additive (attr := simp)]
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
  Nonempty.image₂

@[to_additive]
theorem Nonempty.of_mul_left : (s * t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left

@[to_additive]
theorem Nonempty.of_mul_right : (s * t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right

open scoped RightActions in

@[to_additive] lemma mul_singleton (a : α) : s * {a} = s <• a := image₂_singleton_right

@[to_additive] lemma singleton_mul (a : α) : {a} * s = a • s := image₂_singleton_left

@[to_additive (attr := simp)]
theorem singleton_mul_singleton (a b : α) : ({a} : Finset α) * {b} = {a * b} :=
  image₂_singleton

@[to_additive (attr := mono, gcongr)]
theorem mul_subset_mul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ * t₁ ⊆ s₂ * t₂ :=
  image₂_subset

@[to_additive (attr := gcongr)]
theorem mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ :=
  image₂_subset_left

@[to_additive (attr := gcongr)]
theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t :=
  image₂_subset_right

@[to_additive] instance : MulLeftMono (Finset α) where elim _s _t₁ _t₂ := mul_subset_mul_left

@[to_additive] instance : MulRightMono (Finset α) where elim _t _s₁ _s₂ := mul_subset_mul_right

@[to_additive]
theorem mul_subset_iff : s * t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x * y ∈ u :=
  image₂_subset_iff

@[to_additive]
theorem union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t :=
  image₂_union_left

@[to_additive]
theorem mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ :=
  image₂_union_right

@[to_additive]
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image₂_inter_subset_left

@[to_additive]
theorem mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
  image₂_inter_subset_right

@[to_additive]
theorem inter_mul_union_subset_union : s₁ ∩ s₂ * (t₁ ∪ t₂) ⊆ s₁ * t₁ ∪ s₂ * t₂ :=
  image₂_inter_union_subset_union

@[to_additive]
theorem union_mul_inter_subset_union : (s₁ ∪ s₂) * (t₁ ∩ t₂) ⊆ s₁ * t₁ ∪ s₂ * t₂ :=
  image₂_union_inter_subset_union

@[to_additive
      "If a finset `u` is contained in the sum of two sets `s + t`, we can find two finsets
      `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' + t'`."]
theorem subset_mul {s t : Set α} :
    ↑u ⊆ s * t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' * t' :=
  subset_set_image₂

@[to_additive]
theorem image_mul [DecidableEq β] : (s * t).image (f : α → β) = s.image f * t.image f :=
  image_image₂_distrib <| map_mul f

@[to_additive]
lemma image_op_mul (s t : Finset α) : (s * t).image op = t.image op * s.image op :=
  image_image₂_antidistrib op_mul

@[to_additive]
lemma map_op_mul (s t : Finset α) :
    (s * t).map opEquiv.toEmbedding = t.map opEquiv.toEmbedding * s.map opEquiv.toEmbedding := by
  simp [map_eq_image, image_op_mul]

@[to_additive "The singleton operation as an `AddHom`."]
def singletonMulHom : α →ₙ* Finset α where
  toFun := singleton; map_mul' _ _ := (singleton_mul_singleton _ _).symm

@[to_additive (attr := simps) "Lift an `AddHom` to `Finset` via `image`"]
def imageMulHom [DecidableEq β] : Finset α →ₙ* Finset β where
  toFun := Finset.image f
  map_mul' _ _ := image_mul _

@[to_additive (attr := simp (default + 1))]
lemma sup_mul_le {β} [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α → β} {a : β} :
    sup (s * t) f ≤ a ↔ ∀ x ∈ s, ∀ y ∈ t, f (x * y) ≤ a :=
  sup_image₂_le

@[to_additive]
lemma sup_mul_left {β} [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s * t) f = sup s fun x ↦ sup t (f <| x * ·) :=
  sup_image₂_left ..

@[to_additive]
lemma sup_mul_right {β} [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s * t) f = sup t fun y ↦ sup s (f <| · * y) :=
  sup_image₂_right ..

@[to_additive (attr := simp (default + 1))]
lemma le_inf_mul {β} [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α → β} {a : β} :
    a ≤ inf (s * t) f ↔ ∀ x ∈ s, ∀ y ∈ t, a ≤ f (x * y) :=
  le_inf_image₂

@[to_additive]
lemma inf_mul_left {β} [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s * t) f = inf s fun x ↦ inf t (f <| x * ·) :=
  inf_image₂_left ..

@[to_additive]
lemma inf_mul_right {β} [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s * t) f = inf t fun y ↦ inf s (f <| · * y) :=
  inf_image₂_right ..

end Mul

/-! ### Finset subtraction/division -/

section Div

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

@[to_additive
      "The pointwise subtraction of finsets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}`
      in locale `Pointwise`."]
protected def div : Div (Finset α) :=
  ⟨image₂ (· / ·)⟩

scoped[Pointwise] attribute [instance] Finset.div Finset.sub

@[to_additive]
theorem mem_div : a ∈ s / t ↔ ∃ b ∈ s, ∃ c ∈ t, b / c = a :=
  mem_image₂

@[to_additive (attr := simp, norm_cast)]
theorem coe_div (s t : Finset α) : (↑(s / t) : Set α) = ↑s / ↑t :=
  coe_image₂ _ _ _

@[to_additive]
theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t :=
  mem_image₂_of_mem

@[to_additive]
theorem div_card_le : (s / t).card ≤ s.card * t.card :=
  card_image₂_le _ _ _

@[to_additive (attr := simp)]
theorem empty_div (s : Finset α) : ∅ / s = ∅ :=
  image₂_empty_left

@[to_additive (attr := simp)]
theorem div_empty (s : Finset α) : s / ∅ = ∅ :=
  image₂_empty_right

@[to_additive (attr := simp)]
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

@[to_additive (attr := simp)]
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
theorem Nonempty.div : s.Nonempty → t.Nonempty → (s / t).Nonempty :=
  Nonempty.image₂

@[to_additive]
theorem Nonempty.of_div_left : (s / t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left

@[to_additive]
theorem Nonempty.of_div_right : (s / t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right

@[to_additive (attr := simp)]
theorem div_singleton (a : α) : s / {a} = s.image (· / a) :=
  image₂_singleton_right

@[to_additive (attr := simp)]
theorem singleton_div (a : α) : {a} / s = s.image (a / ·) :=
  image₂_singleton_left

@[to_additive]
theorem singleton_div_singleton (a b : α) : ({a} : Finset α) / {b} = {a / b} :=
  image₂_singleton

@[to_additive (attr := mono, gcongr)]
theorem div_subset_div : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ / t₁ ⊆ s₂ / t₂ :=
  image₂_subset

@[to_additive]
theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ :=
  image₂_subset_left

@[to_additive]
theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t :=
  image₂_subset_right

@[to_additive]
theorem div_subset_iff : s / t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x / y ∈ u :=
  image₂_subset_iff

@[to_additive]
theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t :=
  image₂_union_left

@[to_additive]
theorem div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ :=
  image₂_union_right

@[to_additive]
theorem inter_div_subset : s₁ ∩ s₂ / t ⊆ s₁ / t ∩ (s₂ / t) :=
  image₂_inter_subset_left

@[to_additive]
theorem div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
  image₂_inter_subset_right

@[to_additive]
theorem inter_div_union_subset_union : s₁ ∩ s₂ / (t₁ ∪ t₂) ⊆ s₁ / t₁ ∪ s₂ / t₂ :=
  image₂_inter_union_subset_union

@[to_additive]
theorem union_div_inter_subset_union : (s₁ ∪ s₂) / (t₁ ∩ t₂) ⊆ s₁ / t₁ ∪ s₂ / t₂ :=
  image₂_union_inter_subset_union

@[to_additive
      "If a finset `u` is contained in the sum of two sets `s - t`, we can find two finsets
      `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' - t'`."]
theorem subset_div {s t : Set α} :
    ↑u ⊆ s / t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' / t' :=
  subset_set_image₂

@[to_additive (attr := simp (default + 1))]
lemma sup_div_le [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α → β} {a : β} :
    sup (s / t) f ≤ a ↔ ∀ x ∈ s, ∀ y ∈ t, f (x /  y) ≤ a :=
  sup_image₂_le

@[to_additive]
lemma sup_div_left [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s / t) f = sup s fun x ↦ sup t (f <| x / ·) :=
  sup_image₂_left ..

@[to_additive]
lemma sup_div_right [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s / t) f = sup t fun y ↦ sup s (f <| · / y) :=
  sup_image₂_right ..

@[to_additive (attr := simp (default + 1))]
lemma le_inf_div [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α → β} {a : β} :
    a ≤ inf (s / t) f ↔ ∀ x ∈ s, ∀ y ∈ t, a ≤ f (x / y) :=
  le_inf_image₂

@[to_additive]
lemma inf_div_left [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s / t) f = inf s fun x ↦ inf t (f <| x / ·) :=
  inf_image₂_left ..

@[to_additive]
lemma inf_div_right [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s / t) f = inf t fun y ↦ inf s (f <| · / y) :=
  inf_image₂_right ..

end Div

/-! ### Instances -/

open Pointwise

section Instances

variable [DecidableEq α] [DecidableEq β]

protected def nsmul [Zero α] [Add α] : SMul ℕ (Finset α) :=
  ⟨nsmulRec⟩

protected def npow [One α] [Mul α] : Pow (Finset α) ℕ :=
  ⟨fun s n => npowRec n s⟩

attribute [to_additive existing] Finset.npow

protected def zsmul [Zero α] [Add α] [Neg α] : SMul ℤ (Finset α) :=
  ⟨zsmulRec⟩

@[to_additive existing]
protected def zpow [One α] [Mul α] [Inv α] : Pow (Finset α) ℤ :=
  ⟨fun s n => zpowRec npowRec n s⟩

scoped[Pointwise] attribute [instance] Finset.nsmul Finset.npow Finset.zsmul Finset.zpow

@[to_additive "`Finset α` is an `AddSemigroup` under pointwise operations if `α` is. "]
protected def semigroup [Semigroup α] : Semigroup (Finset α) :=
  coe_injective.semigroup _ coe_mul

section CommSemigroup

variable [CommSemigroup α] {s t : Finset α}

@[to_additive "`Finset α` is an `AddCommSemigroup` under pointwise operations if `α` is. "]
protected def commSemigroup : CommSemigroup (Finset α) :=
  coe_injective.commSemigroup _ coe_mul

@[to_additive]
theorem inter_mul_union_subset : s ∩ t * (s ∪ t) ⊆ s * t :=
  image₂_inter_union_subset mul_comm

@[to_additive]
theorem union_mul_inter_subset : (s ∪ t) * (s ∩ t) ⊆ s * t :=
  image₂_union_inter_subset mul_comm

end CommSemigroup

section MulOneClass

variable [MulOneClass α]

@[to_additive "`Finset α` is an `AddZeroClass` under pointwise operations if `α` is."]
protected def mulOneClass : MulOneClass (Finset α) :=
  coe_injective.mulOneClass _ (coe_singleton 1) coe_mul

scoped[Pointwise] attribute [instance] Finset.semigroup Finset.addSemigroup Finset.commSemigroup

  Finset.addCommSemigroup Finset.mulOneClass Finset.addZeroClass

@[to_additive]
theorem subset_mul_left (s : Finset α) {t : Finset α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun a ha =>
  mem_mul.2 ⟨a, ha, 1, ht, mul_one _⟩

@[to_additive]
theorem subset_mul_right {s : Finset α} (t : Finset α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun a ha =>
  mem_mul.2 ⟨1, hs, a, ha, one_mul _⟩

@[to_additive "The singleton operation as an `AddMonoidHom`."]
def singletonMonoidHom : α →* Finset α :=
  { singletonMulHom, singletonOneHom with }

@[to_additive "The coercion from `Finset` to `set` as an `AddMonoidHom`."]
noncomputable def coeMonoidHom : Finset α →* Set α where
  toFun := CoeTC.coe
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive (attr := simps) "Lift an `add_monoid_hom` to `Finset` via `image`"]
def imageMonoidHom [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β] (f : F) :
    Finset α →* Finset β :=
  { imageMulHom f, imageOneHom f with }

end MulOneClass

section Monoid

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

@[to_additive (attr := simp, norm_cast)]
theorem coe_pow (s : Finset α) (n : ℕ) : ↑(s ^ n) = (s : Set α) ^ n := by
  change ↑(npowRec n s) = (s : Set α) ^ n
  induction' n with n ih
  · rw [npowRec, pow_zero, coe_one]
  · rw [npowRec, pow_succ, coe_mul, ih]

@[to_additive "`Finset α` is an `AddMonoid` under pointwise operations if `α` is. "]
protected def monoid : Monoid (Finset α) :=
  coe_injective.monoid _ coe_one coe_mul coe_pow

scoped[Pointwise] attribute [instance] Finset.monoid Finset.addMonoid

@[to_additive]
protected lemma pow_right_monotone (hs : 1 ∈ s) : Monotone (s ^ ·) :=
  pow_right_monotone <| one_subset.2 hs

@[to_additive (attr := gcongr)]
lemma pow_subset_pow_left (hst : s ⊆ t) : s ^ n ⊆ t ^ n := pow_left_mono _ hst

@[to_additive (attr := gcongr)]
lemma pow_subset_pow_right (hs : 1 ∈ s) (hmn : m ≤ n) : s ^ m ⊆ s ^ n :=
  Finset.pow_right_monotone hs hmn

@[to_additive (attr := gcongr)]
lemma pow_subset_pow (hst : s ⊆ t) (ht : 1 ∈ t) (hmn : m ≤ n) : s ^ m ⊆ t ^ n :=
  (pow_subset_pow_left hst).trans (pow_subset_pow_right ht hmn)

@[to_additive]
lemma subset_pow (hs : 1 ∈ s) (hn : n ≠ 0) : s ⊆ s ^ n := by
  simpa using pow_subset_pow_right hs <| Nat.one_le_iff_ne_zero.2 hn

alias nsmul_subset_nsmul_of_zero_mem := nsmul_subset_nsmul_right

@[to_additive]
lemma pow_subset_pow_mul_of_sq_subset_mul (hst : s ^ 2 ⊆ t * s) (hn : n ≠ 0) :
    s ^ n ⊆ t ^ (n - 1) * s := pow_le_pow_mul_of_sq_le_mul hst hn

@[to_additive (attr := simp) nsmul_empty]
lemma empty_pow (hn : n ≠ 0) : (∅ : Finset α) ^ n = ∅ := match n with | n + 1 => by simp [pow_succ]

@[to_additive]
lemma Nonempty.pow (hs : s.Nonempty) : ∀ {n}, (s ^ n).Nonempty
  | 0 => by simp
  | n + 1 => by rw [pow_succ]; exact hs.pow.mul hs

set_option push_neg.use_distrib true in
@[to_additive (attr := simp)] lemma pow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n ≠ 0 := by
  constructor
  · contrapose!
    rintro (hs | rfl)
    -- TODO: The `nonempty_iff_ne_empty` would be unnecessary if `push_neg` knew how to simplify
    -- `s ≠ ∅` to `s.Nonempty` when `s : Finset α`.
    -- See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/push_neg.20extensibility
    · exact nonempty_iff_ne_empty.1 (nonempty_iff_ne_empty.2 hs).pow
    · rw [← nonempty_iff_ne_empty]
      simp
  · rintro ⟨rfl, hn⟩
    exact empty_pow hn

@[to_additive (attr := simp) nsmul_singleton]
lemma singleton_pow (a : α) : ∀ n, ({a} : Finset α) ^ n = {a ^ n}
  | 0 => by simp [singleton_one]
  | n + 1 => by simp [pow_succ, singleton_pow _ n]

@[to_additive] lemma pow_mem_pow (ha : a ∈ s) : a ^ n ∈ s ^ n := by
  simpa using pow_subset_pow_left (singleton_subset_iff.2 ha)

@[to_additive] lemma one_mem_pow (hs : 1 ∈ s) : 1 ∈ s ^ n := by simpa using pow_mem_pow hs

@[to_additive]
lemma inter_pow_subset : (s ∩ t) ^ n ⊆ s ^ n ∩ t ^ n := by apply subset_inter <;> gcongr <;> simp

@[to_additive (attr := simp, norm_cast)]
theorem coe_list_prod (s : List (Finset α)) : (↑s.prod : Set α) = (s.map (↑)).prod :=
  map_list_prod (coeMonoidHom : Finset α →* Set α) _

@[to_additive]
theorem mem_prod_list_ofFn {a : α} {s : Fin n → Finset α} :
    a ∈ (List.ofFn s).prod ↔ ∃ f : ∀ i : Fin n, s i, (List.ofFn fun i => (f i : α)).prod = a := by
  rw [← mem_coe, coe_list_prod, List.map_ofFn, Set.mem_prod_list_ofFn]
  rfl

@[to_additive]
theorem mem_pow {a : α} {n : ℕ} :
    a ∈ s ^ n ↔ ∃ f : Fin n → s, (List.ofFn fun i => ↑(f i)).prod = a := by
  simp [← mem_coe, coe_pow, Set.mem_pow]

@[to_additive]
lemma card_pow_le : ∀ {n}, (s ^ n).card ≤ s.card ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ, pow_succ]; refine card_mul_le.trans (by gcongr; exact card_pow_le)

@[to_additive]
theorem mul_univ_of_one_mem [Fintype α] (hs : (1 : α) ∈ s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, hs, _, mem_univ _, one_mul _⟩

@[to_additive]
theorem univ_mul_of_one_mem [Fintype α] (ht : (1 : α) ∈ t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, mem_univ _, _, ht, mul_one _⟩

@[to_additive (attr := simp)]
theorem univ_mul_univ [Fintype α] : (univ : Finset α) * univ = univ :=
  mul_univ_of_one_mem <| mem_univ _

@[to_additive (attr := simp) nsmul_univ]
theorem univ_pow [Fintype α] (hn : n ≠ 0) : (univ : Finset α) ^ n = univ :=
  coe_injective <| by rw [coe_pow, coe_univ, Set.univ_pow hn]

@[to_additive]
protected theorem _root_.IsUnit.finset : IsUnit a → IsUnit ({a} : Finset α) :=
  IsUnit.map (singletonMonoidHom : α →* Finset α)

@[to_additive]
lemma image_op_pow (s : Finset α) : ∀ n : ℕ, (s ^ n).image op = s.image op ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => by rw [pow_succ, pow_succ', image_op_mul, image_op_pow]

@[to_additive]
lemma map_op_pow (s : Finset α) :
    ∀ n : ℕ, (s ^ n).map opEquiv.toEmbedding = s.map opEquiv.toEmbedding ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => by rw [pow_succ, pow_succ', map_op_mul, map_op_pow]

end Monoid

section CommMonoid

variable [CommMonoid α]

@[to_additive "`Finset α` is an `AddCommMonoid` under pointwise operations if `α` is. "]
protected def commMonoid : CommMonoid (Finset α) :=
  coe_injective.commMonoid _ coe_one coe_mul coe_pow

scoped[Pointwise] attribute [instance] Finset.commMonoid Finset.addCommMonoid

@[to_additive (attr := simp, norm_cast)]
theorem coe_prod {ι : Type*} (s : Finset ι) (f : ι → Finset α) :
    ↑(∏ i ∈ s, f i) = ∏ i ∈ s, (f i : Set α) :=
  map_prod ((coeMonoidHom) : Finset α →* Set α) _ _

end CommMonoid

open Pointwise

section DivisionMonoid

variable [DivisionMonoid α] {s t : Finset α} {n : ℤ}

@[to_additive (attr := simp)]
theorem coe_zpow (s : Finset α) : ∀ n : ℤ, ↑(s ^ n) = (s : Set α) ^ n
  | Int.ofNat _ => coe_pow _ _
  | Int.negSucc n => by
    refine (coe_inv _).trans ?_
    exact congr_arg Inv.inv (coe_pow _ _)

@[to_additive]
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  simp_rw [← coe_inj, coe_mul, coe_one, Set.mul_eq_one_iff, coe_singleton]

@[to_additive
  "`Finset α` is a subtraction monoid under pointwise operations if `α` is."]
protected def divisionMonoid : DivisionMonoid (Finset α) :=
  coe_injective.divisionMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

scoped[Pointwise] attribute [instance] Finset.divisionMonoid Finset.subtractionMonoid

@[to_additive (attr := simp)]
theorem isUnit_iff : IsUnit s ↔ ∃ a, s = {a} ∧ IsUnit a := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Finset.mul_eq_one_iff.1 u.mul_inv
    refine ⟨a, ha, ⟨a, b, h, singleton_injective ?_⟩, rfl⟩
    rw [← singleton_mul_singleton, ← ha, ← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.finset

@[to_additive (attr := simp)]
theorem isUnit_coe : IsUnit (s : Set α) ↔ IsUnit s := by
  simp_rw [isUnit_iff, Set.isUnit_iff, coe_eq_singleton]

@[to_additive (attr := simp)]
lemma univ_div_univ [Fintype α] : (univ / univ : Finset α) = univ := by simp [div_eq_mul_inv]

@[to_additive] lemma subset_div_left (ht : 1 ∈ t) : s ⊆ s / t := by
  rw [div_eq_mul_inv]; exact subset_mul_left _ <| by simpa

@[to_additive] lemma inv_subset_div_right (hs : 1 ∈ s) : t⁻¹ ⊆ s / t := by
  rw [div_eq_mul_inv]; exact subset_mul_right _ hs

@[to_additive (attr := simp) zsmul_empty]
lemma empty_zpow (hn : n ≠ 0) : (∅ : Finset α) ^ n = ∅ := by cases n <;> aesop

@[to_additive]
lemma Nonempty.zpow (hs : s.Nonempty) : ∀ {n : ℤ}, (s ^ n).Nonempty
  | (n : ℕ) => hs.pow
  | .negSucc n => by simpa using hs.pow

set_option push_neg.use_distrib true in
@[to_additive (attr := simp)] lemma zpow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n ≠ 0 := by
  constructor
  · contrapose!
    rintro (hs | rfl)
    · exact nonempty_iff_ne_empty.1 (nonempty_iff_ne_empty.2 hs).zpow
    · rw [← nonempty_iff_ne_empty]
      simp
  · rintro ⟨rfl, hn⟩
    exact empty_zpow hn

@[to_additive (attr := simp) zsmul_singleton]
lemma singleton_zpow (a : α) (n : ℤ) : ({a} : Finset α) ^ n = {a ^ n} := by cases n <;> simp

end DivisionMonoid

@[to_additive subtractionCommMonoid
      "`Finset α` is a commutative subtraction monoid under pointwise operations if `α` is."]
protected def divisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (Finset α) :=
  coe_injective.divisionCommMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

scoped[Pointwise] attribute [instance] Finset.divisionCommMonoid Finset.subtractionCommMonoid

section Group

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]

variable (f : F) {s t : Finset α} {a b : α}

/-! Note that `Finset` is not a `Group` because `s / s ≠ 1` in general. -/

@[to_additive (attr := simp)]
theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  rw [← mem_coe, ← disjoint_coe, coe_div, Set.one_mem_div_iff]

@[to_additive (attr := simp)]
lemma one_mem_inv_mul_iff : (1 : α) ∈ t⁻¹ * s ↔ ¬Disjoint s t := by
  aesop (add simp [not_disjoint_iff_nonempty_inter, mem_mul, mul_eq_one_iff_eq_inv,
    Finset.Nonempty])

@[to_additive]
theorem not_one_mem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left

@[to_additive]
lemma not_one_mem_inv_mul_iff : (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t := one_mem_inv_mul_iff.not_left

@[to_additive]
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, ha, a, ha, div_self' _⟩

@[to_additive]
theorem isUnit_singleton (a : α) : IsUnit ({a} : Finset α) :=
  (Group.isUnit a).finset

theorem isUnit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  simp only [isUnit_iff, Group.isUnit, and_true]

@[simp]
theorem isUnit_iff_singleton_aux {α} [Group α] {s : Finset α} :
    (∃ a, s = {a} ∧ IsUnit a) ↔ ∃ a, s = {a} := by
  simp only [Group.isUnit, and_true]

@[to_additive (attr := simp)]
theorem image_mul_left :
    image (fun b => a * b) t = preimage t (fun b => a⁻¹ * b) (mul_right_injective _).injOn :=
  coe_injective <| by simp

@[to_additive (attr := simp)]
theorem image_mul_right : image (· * b) t = preimage t (· * b⁻¹) (mul_left_injective _).injOn :=
  coe_injective <| by simp

@[to_additive]
lemma image_inv (f : F) (s : Finset α) : s⁻¹.image f = (s.image f)⁻¹ := image_comm (map_inv _)

theorem image_div : (s / t).image (f : α → β) = s.image f / t.image f :=
  image_image₂_distrib <| map_div f

end Group

end Instances

section Group

variable [Group α] {a b : α}

@[to_additive (attr := simp)]
theorem preimage_mul_left_singleton :
    preimage {b} (a * ·) (mul_right_injective _).injOn = {a⁻¹ * b} := by
  classical rw [← image_mul_left', image_singleton]

@[to_additive (attr := simp)]
theorem preimage_mul_right_singleton :
    preimage {b} (· * a) (mul_left_injective _).injOn = {b * a⁻¹} := by
  classical rw [← image_mul_right', image_singleton]

@[to_additive (attr := simp)]
theorem preimage_mul_left_one : preimage 1 (a * ·) (mul_right_injective _).injOn = {a⁻¹} := by
  classical rw [← image_mul_left', image_one, mul_one]

@[to_additive (attr := simp)]
theorem preimage_mul_right_one : preimage 1 (· * b) (mul_left_injective _).injOn = {b⁻¹} := by
  classical rw [← image_mul_right', image_one, one_mul]

@[to_additive]
theorem preimage_mul_left_one' : preimage 1 (a⁻¹ * ·) (mul_right_injective _).injOn = {a} := by
  rw [preimage_mul_left_one, inv_inv]

@[to_additive]
theorem preimage_mul_right_one' : preimage 1 (· * b⁻¹) (mul_left_injective _).injOn = {b} := by
  rw [preimage_mul_right_one, inv_inv]

end Group

/-! ### Scalar subtraction of finsets -/

section VSub

variable [VSub α β] [DecidableEq α] {s s₁ s₂ t t₁ t₂ : Finset β} {u : Finset α} {a : α} {b c : β}

protected def vsub : VSub (Finset α) (Finset β) :=
  ⟨image₂ (· -ᵥ ·)⟩

scoped[Pointwise] attribute [instance] Finset.vsub

theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ b ∈ s, ∃ c ∈ t, b -ᵥ c = a :=
  mem_image₂

@[simp, norm_cast]
theorem coe_vsub (s t : Finset β) : (↑(s -ᵥ t) : Set α) = (s : Set β) -ᵥ t :=
  coe_image₂ _ _ _

theorem vsub_mem_vsub : b ∈ s → c ∈ t → b -ᵥ c ∈ s -ᵥ t :=
  mem_image₂_of_mem

theorem vsub_card_le : (s -ᵥ t : Finset α).card ≤ s.card * t.card :=
  card_image₂_le _ _ _

@[simp]
theorem empty_vsub (t : Finset β) : (∅ : Finset β) -ᵥ t = ∅ :=
  image₂_empty_left

@[simp]
theorem vsub_empty (s : Finset β) : s -ᵥ (∅ : Finset β) = ∅ :=
  image₂_empty_right

@[simp]
theorem vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

@[simp]
theorem vsub_nonempty : (s -ᵥ t : Finset α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
theorem Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Finset α).Nonempty :=
  Nonempty.image₂

theorem Nonempty.of_vsub_left : (s -ᵥ t : Finset α).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left

theorem Nonempty.of_vsub_right : (s -ᵥ t : Finset α).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right

@[simp]
theorem vsub_singleton (b : β) : s -ᵥ ({b} : Finset β) = s.image (· -ᵥ b) :=
  image₂_singleton_right

theorem singleton_vsub (a : β) : ({a} : Finset β) -ᵥ t = t.image (a -ᵥ ·) :=
  image₂_singleton_left

theorem singleton_vsub_singleton (a b : β) : ({a} : Finset β) -ᵥ {b} = {a -ᵥ b} :=
  image₂_singleton

@[mono, gcongr]
theorem vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image₂_subset

theorem vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ :=
  image₂_subset_left

theorem vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t :=
  image₂_subset_right

theorem vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x -ᵥ y ∈ u :=
  image₂_subset_iff

section

variable [DecidableEq β]

theorem union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) :=
  image₂_union_left

theorem vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) :=
  image₂_union_right

theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) :=
  image₂_inter_subset_left

theorem vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) :=
  image₂_inter_subset_right

end

theorem subset_vsub {s t : Set β} :
    ↑u ⊆ s -ᵥ t → ∃ s' t' : Finset β, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' -ᵥ t' :=
  subset_set_image₂

end VSub

section Instances

variable [DecidableEq γ]

@[to_additive]
instance smulCommClass_finset [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Finset γ) :=
  ⟨fun _ _ => Commute.finset_image <| smul_comm _ _⟩

@[to_additive]
instance smulCommClass_finset' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_comm]⟩

@[to_additive]
instance smulCommClass_finset'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Finset α) β (Finset γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _

@[to_additive]
instance smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Finset α) (Finset β) (Finset γ) :=
  ⟨fun s t u => coe_injective <| by simp_rw [coe_smul, smul_comm]⟩

@[to_additive vaddAssocClass]
instance isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Finset γ) :=
  ⟨fun a b s => by simp only [← image_smul, image_image, smul_assoc, Function.comp_def]⟩

variable [DecidableEq β]

@[to_additive vaddAssocClass']
instance isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩

@[to_additive vaddAssocClass'']
instance isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Finset α) (Finset β) (Finset γ) :=
  ⟨fun a s t => coe_injective <| by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩

@[to_additive]
instance isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Finset β) :=
  ⟨fun a s => coe_injective <| by simp only [coe_smul_finset, coe_smul, op_smul_eq_smul]⟩

@[to_additive
      "An additive action of an additive monoid `α` on a type `β` gives an additive action
      of `Finset α` on `Finset β`"]
protected def mulAction [DecidableEq α] [Monoid α] [MulAction α β] :
    MulAction (Finset α) (Finset β) where
  mul_smul _ _ _ := image₂_assoc mul_smul
  one_smul s := image₂_singleton_left.trans <| by simp_rw [one_smul, image_id']

@[to_additive
      "An additive action of an additive monoid on a type `β` gives an additive action
      on `Finset β`."]
protected def mulActionFinset [Monoid α] [MulAction α β] : MulAction α (Finset β) :=
  coe_injective.mulAction _ coe_smul_finset

scoped[Pointwise]

  attribute [instance]
    Finset.mulActionFinset Finset.addActionFinset Finset.mulAction Finset.addAction

end Instances

section SMul

variable [DecidableEq β] [DecidableEq γ] [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

@[to_additive]
theorem op_smul_finset_smul_eq_smul_smul_finset (a : α) (s : Finset β) (t : Finset γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext
  simp [mem_smul, mem_smul_finset, h]

end SMul

section Mul

variable [Mul α] [DecidableEq α] {s t u : Finset α} {a : α}

@[to_additive]
theorem op_smul_finset_subset_mul : a ∈ t → op a • s ⊆ s * t :=
  image_subset_image₂_left

@[to_additive (attr := simp)]
theorem biUnion_op_smul_finset (s t : Finset α) : (t.biUnion fun a => op a • s) = s * t :=
  biUnion_image_right

@[to_additive]
theorem mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u :=
  image₂_subset_iff_left

@[to_additive]
theorem mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u :=
  image₂_subset_iff_right

end Mul

section Monoid

variable [DecidableEq α] [DecidableEq β] [Monoid α] [Monoid β] [FunLike F α β]

@[to_additive]
lemma image_pow_of_ne_zero [MulHomClass F α β] :
    ∀ {n}, n ≠ 0 → ∀ (f : F) (s : Finset α), (s ^ n).image f = s.image f ^ n
  | 1, _ => by simp
  | n + 2, _ => by simp [image_mul, pow_succ _ n.succ, image_pow_of_ne_zero]

@[to_additive]
lemma image_pow [MonoidHomClass F α β] (f : F) (s : Finset α) : ∀ n, (s ^ n).image f = s.image f ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => image_pow_of_ne_zero n.succ_ne_zero ..

end Monoid

section Semigroup

variable [Semigroup α] [DecidableEq α]

@[to_additive]
theorem op_smul_finset_mul_eq_mul_smul_finset (a : α) (s : Finset α) (t : Finset α) :
    op a • s * t = s * a • t :=
  op_smul_finset_smul_eq_smul_smul_finset _ _ _ fun _ _ _ => mul_assoc _ _ _

end Semigroup

section IsLeftCancelMul

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

-- CONFLATES (assumes ground = zero): Nontrivial.mul_left
@[to_additive]
lemma Nontrivial.mul_left : t.Nontrivial → s.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, mul_mem_mul hc ha, c * b, mul_mem_mul hc hb, by simpa⟩

-- CONFLATES (assumes ground = zero): Nontrivial.mul
@[to_additive]
lemma Nontrivial.mul (hs : s.Nontrivial) (ht : t.Nontrivial) : (s * t).Nontrivial :=
  ht.mul_left hs.nonempty

@[to_additive]
theorem pairwiseDisjoint_smul_iff {s : Set α} {t : Finset α} :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 := by
  simp_rw [← pairwiseDisjoint_coe, coe_smul_finset, Set.pairwiseDisjoint_smul_iff]

@[to_additive (attr := simp)]
theorem card_singleton_mul (a : α) (t : Finset α) : ({a} * t).card = t.card :=
  card_image₂_singleton_left _ <| mul_right_injective _

@[to_additive]
theorem singleton_mul_inter (a : α) (s t : Finset α) : {a} * (s ∩ t) = {a} * s ∩ ({a} * t) :=
  image₂_singleton_inter _ _ <| mul_right_injective _

@[to_additive]
theorem card_le_card_mul_left {s : Finset α} (hs : s.Nonempty) : t.card ≤ (s * t).card :=
  card_le_card_image₂_left _ hs mul_right_injective

@[to_additive
"The size of `s + s` is at least the size of `s`, version with left-cancellative addition.
See `card_le_card_add_self'` for the version with right-cancellative addition."
]
theorem card_le_card_mul_self {s : Finset α} : s.card ≤ (s * s).card := by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_mul_left, *]

end IsLeftCancelMul

section IsRightCancelMul

variable [Mul α] [IsRightCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

-- CONFLATES (assumes ground = zero): Nontrivial.mul_right
@[to_additive]
lemma Nontrivial.mul_right : s.Nontrivial → t.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨a * c, mul_mem_mul ha hc, b * c, mul_mem_mul hb hc, by simpa⟩

@[to_additive (attr := simp)]
theorem card_mul_singleton (s : Finset α) (a : α) : (s * {a}).card = s.card :=
  card_image₂_singleton_right _ <| mul_left_injective _

@[to_additive]
theorem inter_mul_singleton (s t : Finset α) (a : α) : s ∩ t * {a} = s * {a} ∩ (t * {a}) :=
  image₂_inter_singleton _ _ <| mul_left_injective _

@[to_additive]
theorem card_le_card_mul_right (ht : t.Nonempty) : s.card ≤ (s * t).card :=
  card_le_card_image₂_right _ ht mul_left_injective

@[to_additive
"The size of `s + s` is at least the size of `s`, version with right-cancellative addition.
See `card_le_card_add_self` for the version with left-cancellative addition."
]
theorem card_le_card_mul_self' : s.card ≤ (s * s).card := by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_mul_right, *]

end IsRightCancelMul

section CancelMonoid

variable [DecidableEq α] [CancelMonoid α] {s : Finset α} {m n : ℕ}

-- CONFLATES (assumes ground = zero): Nontrivial.pow
@[to_additive]
lemma Nontrivial.pow (hs : s.Nontrivial) : ∀ {n}, n ≠ 0 → (s ^ n).Nontrivial
  | 1, _ => by simpa
  | n + 2, _ => by simpa [pow_succ] using (hs.pow n.succ_ne_zero).mul hs

@[to_additive "See `Finset.card_nsmul_mono` for a version that works for the empty set."]
protected lemma Nonempty.card_pow_mono (hs : s.Nonempty) : Monotone fun n : ℕ ↦ (s ^ n).card :=
  monotone_nat_of_le_succ fun n ↦ by rw [pow_succ]; exact card_le_card_mul_right hs

@[to_additive "See `Finset.Nonempty.card_nsmul_mono` for a version that works for zero scalars."]
lemma card_pow_mono (hm : m ≠ 0) (hmn : m ≤ n) : (s ^ m).card ≤ (s ^ n).card := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [hm]
  · exact hs.card_pow_mono hmn

@[to_additive]
lemma card_le_card_pow (hn : n ≠ 0) : s.card ≤ (s ^ n).card := by
  simpa using card_pow_mono (s := s) one_ne_zero (Nat.one_le_iff_ne_zero.2 hn)

end CancelMonoid

section Group

variable [Group α] [DecidableEq α] {s t : Finset α}

@[to_additive] lemma card_le_card_div_left (hs : s.Nonempty) : t.card ≤ (s / t).card :=
  card_le_card_image₂_left _ hs fun _ ↦ div_right_injective

@[to_additive] lemma card_le_card_div_right (ht : t.Nonempty) : s.card ≤ (s / t).card :=
  card_le_card_image₂_right _ ht fun _ ↦ div_left_injective

@[to_additive] lemma card_le_card_div_self : s.card ≤ (s / s).card := by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_div_left, *]

end Group

open Pointwise

@[to_additive]
theorem image_smul_comm [DecidableEq β] [DecidableEq γ] [SMul α β] [SMul α γ] (f : β → γ) (a : α)
    (s : Finset β) : (∀ b, f (a • b) = a • f b) → (a • s).image f = a • s.image f :=
  image_comm

@[to_additive]
theorem image_smul_distrib [DecidableEq α] [DecidableEq β] [Monoid α] [Monoid β] [FunLike F α β]
    [MonoidHomClass F α β] (f : F) (a : α) (s : Finset α) : (a • s).image f = f a • s.image f :=
  image_comm <| map_mul _ _

section Group

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β}

@[to_additive (attr := simp)]
theorem smul_mem_smul_finset_iff (a : α) : a • b ∈ a • s ↔ b ∈ s :=
  (MulAction.injective _).mem_finset_image

@[to_additive]
theorem inv_smul_mem_iff : a⁻¹ • b ∈ s ↔ b ∈ a • s := by
  rw [← smul_mem_smul_finset_iff a, smul_inv_smul]

@[to_additive]
theorem mem_inv_smul_finset_iff : b ∈ a⁻¹ • s ↔ a • b ∈ s := by
  rw [← smul_mem_smul_finset_iff a, smul_inv_smul]

@[to_additive (attr := simp)]
theorem smul_finset_subset_smul_finset_iff : a • s ⊆ a • t ↔ s ⊆ t :=
  image_subset_image_iff <| MulAction.injective _

@[to_additive]
theorem smul_finset_subset_iff : a • s ⊆ t ↔ s ⊆ a⁻¹ • t := by
  simp_rw [← coe_subset]
  push_cast
  exact Set.set_smul_subset_iff

@[to_additive]
theorem subset_smul_finset_iff : s ⊆ a • t ↔ a⁻¹ • s ⊆ t := by
  simp_rw [← coe_subset]
  push_cast
  exact Set.subset_set_smul_iff

@[to_additive]
theorem smul_finset_inter : a • (s ∩ t) = a • s ∩ a • t :=
  image_inter _ _ <| MulAction.injective a

@[to_additive]
theorem smul_finset_sdiff : a • (s \ t) = a • s \ a • t :=
  image_sdiff _ _ <| MulAction.injective a

open scoped symmDiff in

@[to_additive]
theorem smul_finset_symmDiff : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff _ _ <| MulAction.injective a

@[to_additive (attr := simp)]
theorem smul_finset_univ [Fintype β] : a • (univ : Finset β) = univ :=
  image_univ_of_surjective <| MulAction.surjective a

@[to_additive (attr := simp)]
theorem smul_univ [Fintype β] {s : Finset α} (hs : s.Nonempty) : s • (univ : Finset β) = univ :=
  coe_injective <| by
    push_cast
    exact Set.smul_univ hs

@[to_additive (attr := simp)]
theorem card_smul_finset (a : α) (s : Finset β) : (a • s).card = s.card :=
  card_image_of_injective _ <| MulAction.injective _

@[to_additive (attr := simp)]
lemma dens_smul_finset [Fintype β] (a : α) (s : Finset β) : (a • s).dens = s.dens := by simp [dens]

@[to_additive "If the left cosets of `t` by elements of `s` are disjoint (but not necessarily
distinct!), then the size of `t` divides the size of `s +ᵥ t`."]
theorem card_dvd_card_smul_right {s : Finset α} :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id → t.card ∣ (s • t).card :=
  card_dvd_card_image₂_right fun _ _ => MulAction.injective _

variable [DecidableEq α]

@[to_additive "If the right cosets of `s` by elements of `t` are disjoint (but not necessarily
distinct!), then the size of `s` divides the size of `s + t`."]
theorem card_dvd_card_mul_left {s t : Finset α} :
    ((fun b => s.image fun a => a * b) '' (t : Set α)).PairwiseDisjoint id →
      s.card ∣ (s * t).card :=
  card_dvd_card_image₂_left fun _ _ => mul_left_injective _

@[to_additive "If the left cosets of `t` by elements of `s` are disjoint (but not necessarily
distinct!), then the size of `t` divides the size of `s + t`."]
theorem card_dvd_card_mul_right {s t : Finset α} :
    ((· • t) '' (s : Set α)).PairwiseDisjoint id → t.card ∣ (s * t).card :=
  card_dvd_card_image₂_right fun _ _ => mul_right_injective _

@[to_additive (attr := simp)]
lemma inv_smul_finset_distrib (a : α) (s : Finset α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  ext; simp [← inv_smul_mem_iff]

@[to_additive (attr := simp)]
lemma inv_op_smul_finset_distrib (a : α) (s : Finset α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹ := by
  ext; simp [← inv_smul_mem_iff]

end Group

section BigOps

section CommMonoid

variable [CommMonoid α] {ι : Type*} [DecidableEq ι]

@[to_additive (attr := simp)] lemma prod_inv_index [InvolutiveInv ι] (s : Finset ι) (f : ι → α) :
    ∏ i ∈ s⁻¹, f i = ∏ i ∈ s, f i⁻¹ := prod_image inv_injective.injOn

@[to_additive existing, simp] lemma prod_neg_index [InvolutiveNeg ι] (s : Finset ι) (f : ι → α) :
    ∏ i ∈ -s, f i = ∏ i ∈ s, f (-i) := prod_image neg_injective.injOn

end CommMonoid

section AddCommMonoid

variable [AddCommMonoid α] {ι : Type*} [DecidableEq ι]

@[to_additive existing, simp] lemma sum_inv_index [InvolutiveInv ι] (s : Finset ι) (f : ι → α) :
    ∑ i ∈ s⁻¹, f i = ∑ i ∈ s, f i⁻¹ := sum_image inv_injective.injOn

end AddCommMonoid

end BigOps

end Finset

namespace Fintype

variable {ι : Type*} {α β : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (β i)]

@[to_additive]
lemma piFinset_smul [∀ i, SMul (α i) (β i)] (s : ∀ i, Finset (α i)) (t : ∀ i, Finset (β i)) :
    piFinset (fun i ↦ s i • t i) = piFinset s • piFinset t := piFinset_image₂ _ _ _

@[to_additive]
lemma piFinset_smul_finset [∀ i, SMul (α i) (β i)] (a : ∀ i, α i) (s : ∀ i, Finset (β i)) :
    piFinset (fun i ↦ a i • s i) = a • piFinset s := piFinset_image _ _

variable [∀ i, DecidableEq (α i)]

@[to_additive]
lemma piFinset_mul [∀ i, Mul (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ s i * t i) = piFinset s * piFinset t := piFinset_image₂ _ _ _

@[to_additive]
lemma piFinset_div [∀ i, Div (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ s i / t i) = piFinset s / piFinset t := piFinset_image₂ _ _ _

@[to_additive (attr := simp)]
lemma piFinset_inv [∀ i, Inv (α i)] (s : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ (s i)⁻¹) = (piFinset s)⁻¹ := piFinset_image _ _

end Fintype

open Pointwise

namespace Set

section One

@[to_additive]
instance instFintypeOne [One α] : Fintype (1 : Set α) := Set.fintypeSingleton _

variable [One α]

@[to_additive (attr := simp)]
theorem toFinset_one : (1 : Set α).toFinset = 1 :=
  rfl

@[to_additive (attr := simp high)]
theorem Finite.toFinset_one (h : (1 : Set α).Finite := finite_one) : h.toFinset = 1 :=
  Finite.toFinset_singleton _

end One

section Mul

variable [DecidableEq α] [Mul α] {s t : Set α}

@[to_additive (attr := simp)]
theorem toFinset_mul (s t : Set α) [Fintype s] [Fintype t] [Fintype ↑(s * t)] :
    (s * t).toFinset = s.toFinset * t.toFinset :=
  toFinset_image2 _ _ _

@[to_additive]
theorem Finite.toFinset_mul (hs : s.Finite) (ht : t.Finite) (hf := hs.mul ht) :
    hf.toFinset = hs.toFinset * ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end Mul

section SMul

variable [SMul α β] [DecidableEq β] {s : Set α} {t : Set β}

@[to_additive (attr := simp)]
theorem toFinset_smul (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s • t)] :
    (s • t).toFinset = s.toFinset • t.toFinset :=
  toFinset_image2 _ _ _

@[to_additive]
theorem Finite.toFinset_smul (hs : s.Finite) (ht : t.Finite) (hf := hs.smul ht) :
    hf.toFinset = hs.toFinset • ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end SMul

section SMul

variable [DecidableEq β] [SMul α β] {a : α} {s : Set β}

@[to_additive (attr := simp)]
theorem toFinset_smul_set (a : α) (s : Set β) [Fintype s] [Fintype ↑(a • s)] :
    (a • s).toFinset = a • s.toFinset :=
  toFinset_image _ _

@[to_additive]
theorem Finite.toFinset_smul_set (hs : s.Finite) (hf : (a • s).Finite := hs.smul_set) :
    hf.toFinset = a • hs.toFinset :=
  Finite.toFinset_image _ _ _

end SMul

section VSub

variable [DecidableEq α] [VSub α β] {s t : Set β}

@[simp]
theorem toFinset_vsub (s t : Set β) [Fintype s] [Fintype t] [Fintype ↑(s -ᵥ t)] :
    (s -ᵥ t : Set α).toFinset = s.toFinset -ᵥ t.toFinset :=
  toFinset_image2 _ _ _

theorem Finite.toFinset_vsub (hs : s.Finite) (ht : t.Finite) (hf := hs.vsub ht) :
    hf.toFinset = hs.toFinset -ᵥ ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end VSub

end Set

instance Nat.decidablePred_mem_vadd_set {s : Set ℕ} [DecidablePred (· ∈ s)] (a : ℕ) :
    DecidablePred (· ∈ a +ᵥ s) :=
  fun n ↦ decidable_of_iff' (a ≤ n ∧ n - a ∈ s) <| by
    simp only [Set.mem_vadd_set, vadd_eq_add]; aesop

set_option linter.style.longFile 2000
