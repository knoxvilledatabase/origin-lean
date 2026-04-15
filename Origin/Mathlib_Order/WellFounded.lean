/-
Extracted from Order/WellFounded.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Well-founded relations

A relation is well-founded if it can be used for induction: for each `x`, `(∀ y, r y x → P y) → P x`
implies `P x`. Well-founded relations can be used for induction and recursion, including
construction of fixed points in the space of dependent functions `Π x : α, β x`.

The predicate `WellFounded` is defined in the core library. In this file we prove some extra lemmas
and provide a few new definitions: `WellFounded.min`, `WellFounded.sup`, and `WellFounded.succ`,
and an induction principle `WellFounded.induction_bot`.
-/

theorem exists_not_acc_lt_of_not_acc {α} {a : α} {r} (h : ¬Acc r a) : ∃ b, ¬Acc r b ∧ r b a := by
  rw [acc_def] at h
  push Not at h
  simpa only [and_comm]

theorem not_acc_iff_exists_descending_chain {α} {r : α → α → Prop} {x : α} :
    ¬Acc r x ↔ ∃ f : ℕ → α, f 0 = x ∧ ∀ n, r (f (n + 1)) (f n) where
  mp hx := let f : ℕ → {a : α // ¬Acc r a} :=
      Nat.rec ⟨x, hx⟩ fun _ a ↦ ⟨_, (exists_not_acc_lt_of_not_acc a.2).choose_spec.1⟩
    ⟨(f · |>.1), rfl, fun n ↦ (exists_not_acc_lt_of_not_acc (f n).2).choose_spec.2⟩
  mpr h acc := acc.rec
    (fun _x _ ih ⟨f, hf⟩ ↦ ih (f 1) (hf.1 ▸ hf.2 0) ⟨(f <| · + 1), rfl, fun _ ↦ hf.2 _⟩) h

theorem acc_iff_isEmpty_descending_chain {α} {r : α → α → Prop} {x : α} :
    Acc r x ↔ IsEmpty { f : ℕ → α // f 0 = x ∧ ∀ n, r (f (n + 1)) (f n) } := by
  contrapose!
  rw [nonempty_subtype]
  exact not_acc_iff_exists_descending_chain

theorem wellFounded_iff_isEmpty_descending_chain {α} {r : α → α → Prop} :
    WellFounded r ↔ IsEmpty { f : ℕ → α // ∀ n, r (f (n + 1)) (f n) } where
  mp := fun ⟨h⟩ ↦ ⟨fun ⟨f, hf⟩ ↦ (acc_iff_isEmpty_descending_chain.mp (h (f 0))).false ⟨f, rfl, hf⟩⟩
  mpr h := ⟨fun _ ↦ acc_iff_isEmpty_descending_chain.mpr ⟨fun ⟨f, hf⟩ ↦ h.false ⟨f, hf.2⟩⟩⟩

variable {α β γ : Type*}

namespace WellFounded

variable {r r' : α → α → Prop}

protected theorem asymm (h : WellFounded r) : Std.Asymm r := ⟨h.asymmetric⟩
