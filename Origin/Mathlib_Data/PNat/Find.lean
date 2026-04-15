/-
Extracted from Data/PNat/Find.lean
Genuine: 6 of 7 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Explicit least witnesses to existentials on positive natural numbers

Implemented via calling out to `Nat.find`.

-/

namespace PNat

variable {p q : ℕ+ → Prop} [DecidablePred p] [DecidablePred q] (h : ∃ n, p n)

-- INSTANCE (free from Core): decidablePredExistsNat

protected def findX : { n // p n ∧ ∀ m : ℕ+, m < n → ¬p m } := by
  have : ∃ (n' : ℕ) (n : ℕ+) (_ : n' = n), p n := Exists.elim h fun n hn => ⟨n, n, rfl, hn⟩
  have n := Nat.findX this
  refine ⟨⟨n, ?_⟩, ?_, fun m hm pm => ?_⟩
  · obtain ⟨n', hn', -⟩ := n.prop.1
    rw [hn']
    exact n'.prop
  · obtain ⟨n', hn', pn'⟩ := n.prop.1
    simpa [hn', Subtype.coe_eta] using pn'
  · exact n.prop.2 m hm ⟨m, rfl, pm⟩

protected def find : ℕ+ :=
  PNat.findX h

protected theorem find_spec : p (PNat.find h) :=
  (PNat.findX h).prop.left

protected theorem find_min : ∀ {m : ℕ+}, m < PNat.find h → ¬p m :=
  @(PNat.findX h).prop.right

protected theorem find_min' {m : ℕ+} (hm : p m) : PNat.find h ≤ m :=
  le_of_not_gt fun l => PNat.find_min h l hm

variable {n m : ℕ+}

theorem find_eq_iff : PNat.find h = m ↔ p m ∧ ∀ n < m, ¬p n := by
  constructor
  · rintro rfl
    exact ⟨PNat.find_spec h, fun _ => PNat.find_min h⟩
  · rintro ⟨hm, hlt⟩
    exact le_antisymm (PNat.find_min' h hm) (not_lt.1 <| imp_not_comm.1 (hlt _) <| PNat.find_spec h)
