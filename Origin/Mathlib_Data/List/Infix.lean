/-
Extracted from Data/List/Infix.lean
Genuine: 33 of 46 | Dissolved: 0 | Infrastructure: 13
-/
import Origin.Core
import Mathlib.Data.List.Basic

/-!
# Prefixes, suffixes, infixes

This file proves properties about
* `List.isPrefix`: `l₁` is a prefix of `l₂` if `l₂` starts with `l₁`.
* `List.isSuffix`: `l₁` is a suffix of `l₂` if `l₂` ends with `l₁`.
* `List.isInfix`: `l₁` is an infix of `l₂` if `l₁` is a prefix of some suffix of `l₂`.
* `List.inits`: The list of prefixes of a list.
* `List.tails`: The list of prefixes of a list.
* `insert` on lists

All those (except `insert`) are defined in `Mathlib.Data.List.Defs`.

## Notation

* `l₁ <+: l₂`: `l₁` is a prefix of `l₂`.
* `l₁ <:+ l₂`: `l₁` is a suffix of `l₂`.
* `l₁ <:+: l₂`: `l₁` is an infix of `l₂`.
-/

variable {α : Type*}

namespace List

variable {l l₁ l₂ l₃ : List α} {a b : α}

/-! ### prefix, suffix, infix -/

section Fix

theorem eq_of_infix_of_length_eq (h : l₁ <:+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.eq_of_length

theorem eq_of_prefix_of_length_eq (h : l₁ <+: l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.eq_of_length

theorem eq_of_suffix_of_length_eq (h : l₁ <:+ l₂) : l₁.length = l₂.length → l₁ = l₂ :=
  h.eq_of_length

@[gcongr] lemma IsPrefix.take (h : l₁ <+: l₂) (n : ℕ) : l₁.take n <+: l₂.take n := by
  simpa [prefix_take_iff, Nat.min_le_left] using (take_prefix n l₁).trans h

@[gcongr] lemma IsPrefix.drop (h : l₁ <+: l₂) (n : ℕ) : l₁.drop n <+: l₂.drop n := by
  rw [prefix_iff_eq_take.mp h, drop_take]; apply take_prefix

attribute [gcongr] take_prefix_take_left

lemma isPrefix_append_of_length (h : l₁.length ≤ l₂.length) : l₁ <+: l₂ ++ l₃ ↔ l₁ <+: l₂ :=
  ⟨fun h ↦ by rw [prefix_iff_eq_take] at *; nth_rw 1 [h, take_eq_left_iff]; tauto,
   fun h ↦ h.trans <| l₂.prefix_append l₃⟩

@[simp] lemma take_isPrefix_take {m n : ℕ} : l.take m <+: l.take n ↔ m ≤ n ∨ l.length ≤ n := by
  simp [prefix_take_iff, take_prefix]; omega

lemma dropSlice_sublist (n m : ℕ) (l : List α) : l.dropSlice n m <+ l :=
  calc
    l.dropSlice n m = take n l ++ drop m (drop n l) := by rw [dropSlice_eq, drop_drop, Nat.add_comm]
  _ <+ take n l ++ drop n l := (Sublist.refl _).append (drop_sublist _ _)
  _ = _ := take_append_drop _ _

lemma dropSlice_subset (n m : ℕ) (l : List α) : l.dropSlice n m ⊆ l :=
  (dropSlice_sublist n m l).subset

lemma mem_of_mem_dropSlice {n m : ℕ} {l : List α} {a : α} (h : a ∈ l.dropSlice n m) : a ∈ l :=
  dropSlice_subset n m l h

theorem tail_subset (l : List α) : tail l ⊆ l :=
  (tail_sublist l).subset

theorem mem_of_mem_dropLast (h : a ∈ l.dropLast) : a ∈ l :=
  dropLast_subset l h

attribute [gcongr] Sublist.drop

attribute [refl] prefix_refl suffix_refl infix_refl

theorem concat_get_prefix {x y : List α} (h : x <+: y) (hl : x.length < y.length) :
    x ++ [y.get ⟨x.length, hl⟩] <+: y := by
  use y.drop (x.length + 1)
  nth_rw 1 [List.prefix_iff_eq_take.mp h]
  convert List.take_append_drop (x.length + 1) y using 2
  rw [← List.take_concat_get, List.concat_eq_append]; rfl

instance decidableInfix [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <:+: l₂)
  | [], l₂ => isTrue ⟨[], l₂, rfl⟩
  | a :: l₁, [] => isFalse fun ⟨s, t, te⟩ => by simp at te
  | l₁, b :: l₂ =>
    letI := l₁.decidableInfix l₂
    @decidable_of_decidable_of_iff (l₁ <+: b :: l₂ ∨ l₁ <:+: l₂) _ _
      infix_cons_iff.symm

theorem cons_prefix_iff : a :: l₁ <+: b :: l₂ ↔ a = b ∧ l₁ <+: l₂ := by
  simp

protected theorem IsPrefix.reduceOption {l₁ l₂ : List (Option α)} (h : l₁ <+: l₂) :
    l₁.reduceOption <+: l₂.reduceOption :=
  h.filterMap id

instance : IsPartialOrder (List α) (· <+: ·) where
  refl _ := prefix_rfl
  trans _ _ _ := IsPrefix.trans
  antisymm _ _ h₁ h₂ := h₁.eq_of_length <| h₁.length_le.antisymm h₂.length_le

instance : IsPartialOrder (List α) (· <:+ ·) where
  refl _ := suffix_rfl
  trans _ _ _ := IsSuffix.trans
  antisymm _ _ h₁ h₂ := h₁.eq_of_length <| h₁.length_le.antisymm h₂.length_le

instance : IsPartialOrder (List α) (· <:+: ·) where
  refl _ := infix_rfl
  trans _ _ _ := IsInfix.trans
  antisymm _ _ h₁ h₂ := h₁.eq_of_length <| h₁.length_le.antisymm h₂.length_le

end Fix

section InitsTails

@[simp]
theorem mem_inits : ∀ s t : List α, s ∈ inits t ↔ s <+: t
  | s, [] =>
    suffices s = nil ↔ s <+: nil by simpa only [inits, mem_singleton]
    ⟨fun h => h.symm ▸ prefix_rfl, eq_nil_of_prefix_nil⟩
  | s, a :: t =>
    suffices (s = nil ∨ ∃ l ∈ inits t, a :: l = s) ↔ s <+: a :: t by simpa
    ⟨fun o =>
      match s, o with
      | _, Or.inl rfl => ⟨_, rfl⟩
      | s, Or.inr ⟨r, hr, hs⟩ => by
        let ⟨s, ht⟩ := (mem_inits _ _).1 hr
        rw [← hs, ← ht]; exact ⟨s, rfl⟩,
      fun mi =>
      match s, mi with
      | [], ⟨_, rfl⟩ => Or.inl rfl
      | b :: s, ⟨r, hr⟩ =>
        (List.noConfusion hr) fun ba (st : s ++ r = t) =>
          Or.inr <| by rw [ba]; exact ⟨_, (mem_inits _ _).2 ⟨_, st⟩, rfl⟩⟩

@[simp]
theorem mem_tails : ∀ s t : List α, s ∈ tails t ↔ s <:+ t
  | s, [] => by
    simp only [tails, mem_singleton, suffix_nil]
  | s, a :: t => by
    simp only [tails, mem_cons, mem_tails s t]
    exact
      show s = a :: t ∨ s <:+ t ↔ s <:+ a :: t from
        ⟨fun o =>
          match s, t, o with
          | _, t, Or.inl rfl => suffix_rfl
          | s, _, Or.inr ⟨l, rfl⟩ => ⟨a :: l, rfl⟩,
          fun e =>
          match s, t, e with
          | _, t, ⟨[], rfl⟩ => Or.inl rfl
          | s, t, ⟨b :: l, he⟩ => List.noConfusion he fun _ lt => Or.inr ⟨l, lt⟩⟩

theorem inits_cons (a : α) (l : List α) : inits (a :: l) = [] :: l.inits.map fun t => a :: t := by
  simp

theorem tails_cons (a : α) (l : List α) : tails (a :: l) = (a :: l) :: l.tails := by simp

@[simp]
theorem inits_append : ∀ s t : List α, inits (s ++ t) = s.inits ++ t.inits.tail.map fun l => s ++ l
  | [], [] => by simp
  | [], a :: t => by simp
  | a :: s, t => by simp [inits_append s t, Function.comp_def]

@[simp]
theorem tails_append :
    ∀ s t : List α, tails (s ++ t) = (s.tails.map fun l => l ++ t) ++ t.tails.tail
  | [], [] => by simp
  | [], a :: t => by simp
  | a :: s, t => by simp [tails_append s t]

theorem inits_eq_tails : ∀ l : List α, l.inits = (reverse <| map reverse <| tails <| reverse l)
  | [] => by simp
  | a :: l => by simp [inits_eq_tails l, map_inj_left, ← map_reverse]

theorem tails_eq_inits : ∀ l : List α, l.tails = (reverse <| map reverse <| inits <| reverse l)
  | [] => by simp
  | a :: l => by simp [tails_eq_inits l, append_left_inj]

theorem inits_reverse (l : List α) : inits (reverse l) = reverse (map reverse l.tails) := by
  rw [tails_eq_inits l]
  simp [reverse_involutive.comp_self, ← map_reverse]

theorem tails_reverse (l : List α) : tails (reverse l) = reverse (map reverse l.inits) := by
  rw [inits_eq_tails l]
  simp [reverse_involutive.comp_self, ← map_reverse]

theorem map_reverse_inits (l : List α) : map reverse l.inits = (reverse <| tails <| reverse l) := by
  rw [inits_eq_tails l]
  simp [reverse_involutive.comp_self, ← map_reverse]

theorem map_reverse_tails (l : List α) : map reverse l.tails = (reverse <| inits <| reverse l) := by
  rw [tails_eq_inits l]
  simp [reverse_involutive.comp_self, ← map_reverse]

@[simp]
theorem length_tails (l : List α) : length (tails l) = length l + 1 := by
  induction' l with x l IH
  · simp
  · simpa using IH

@[simp]
theorem length_inits (l : List α) : length (inits l) = length l + 1 := by simp [inits_eq_tails]

@[simp]
theorem getElem_tails (l : List α) (n : Nat) (h : n < (tails l).length) :
    (tails l)[n] = l.drop n := by
  induction l generalizing n with
  | nil => simp
  | cons a l ihl =>
    cases n with
    | zero => simp
    | succ n => simp [ihl]

theorem get_tails (l : List α) (n : Fin (length (tails l))) : (tails l).get n = l.drop n := by
  simp

@[simp]
theorem getElem_inits (l : List α) (n : Nat) (h : n < length (inits l)) :
    (inits l)[n] = l.take n := by
  induction l generalizing n with
  | nil => simp
  | cons a l ihl =>
    cases n with
    | zero => simp
    | succ n => simp [ihl]

theorem get_inits (l : List α) (n : Fin (length (inits l))) : (inits l).get n = l.take n := by
  simp

lemma map_inits {β : Type*} (g : α → β) : (l.map g).inits = l.inits.map (map g) := by
  induction' l using reverseRecOn <;> simp [*]

lemma map_tails {β : Type*} (g : α → β) : (l.map g).tails = l.tails.map (map g) := by
  induction' l using reverseRecOn <;> simp [*]

lemma take_inits {n} : (l.take n).inits = l.inits.take (n + 1) := by
  apply ext_getElem <;> (simp [take_take]; omega)

end InitsTails

/-! ### insert -/

section Insert

variable [DecidableEq α]

theorem insert_eq_ite (a : α) (l : List α) : insert a l = if a ∈ l then l else a :: l := by
  simp only [← elem_iff]
  rfl

@[simp]
theorem suffix_insert (a : α) (l : List α) : l <:+ l.insert a := by
  by_cases h : a ∈ l
  · simp only [insert_of_mem h, insert, suffix_refl]
  · simp only [insert_of_not_mem h, suffix_cons, insert]

theorem infix_insert (a : α) (l : List α) : l <:+: l.insert a :=
  (suffix_insert a l).isInfix

theorem sublist_insert (a : α) (l : List α) : l <+ l.insert a :=
  (suffix_insert a l).sublist

theorem subset_insert (a : α) (l : List α) : l ⊆ l.insert a :=
  (sublist_insert a l).subset

end Insert

theorem IsPrefix.get_eq {x y : List α} (h : x <+: y) {n} (hn : n < x.length) :
    x.get ⟨n, hn⟩ = y.get ⟨n, hn.trans_le h.length_le⟩ := by
  simp only [get_eq_getElem, IsPrefix.getElem h hn]

end List
