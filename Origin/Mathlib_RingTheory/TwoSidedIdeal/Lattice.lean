/-
Extracted from RingTheory/TwoSidedIdeal/Lattice.lean
Genuine: 7 of 20 | Dissolved: 0 | Infrastructure: 13
-/
import Origin.Core

/-!
# The complete lattice structure on two-sided ideals
-/

namespace TwoSidedIdeal

variable (R : Type*) [NonUnitalNonAssocRing R]

-- INSTANCE (free from Core): :

section sup

variable {R}

lemma mem_sup_left {I J : TwoSidedIdeal R} {x : R} (h : x ∈ I) :
    x ∈ I ⊔ J :=
  (show I ≤ I ⊔ J from le_sup_left) h

lemma mem_sup_right {I J : TwoSidedIdeal R} {x : R} (h : x ∈ J) :
    x ∈ I ⊔ J :=
  (show J ≤ I ⊔ J from le_sup_right) h

lemma mem_sup {I J : TwoSidedIdeal R} {x : R} :
    x ∈ I ⊔ J ↔ ∃ y ∈ I, ∃ z ∈ J, y + z = x := by
  constructor
  · let s : TwoSidedIdeal R := .mk'
      {x | ∃ y ∈ I, ∃ z ∈ J, y + z = x}
      ⟨0, ⟨zero_mem _, ⟨0, ⟨zero_mem _, zero_add _⟩⟩⟩⟩
      (by rintro _ _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩ ⟨a, ⟨ha, ⟨b, ⟨hb, rfl⟩⟩⟩⟩;
          exact ⟨x + a, ⟨add_mem _ hx ha, ⟨y + b, ⟨add_mem _ hy hb, by abel⟩⟩⟩⟩)
      (by rintro _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩
          exact ⟨-x, ⟨neg_mem _ hx, ⟨-y, ⟨neg_mem _ hy, by abel⟩⟩⟩⟩)
      (by rintro r _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩
          exact ⟨_, ⟨mul_mem_left _ _ _ hx, ⟨_, ⟨mul_mem_left _ _ _ hy, mul_add _ _ _ |>.symm⟩⟩⟩⟩)
      (by rintro r _ ⟨x, ⟨hx, ⟨y, ⟨hy, rfl⟩⟩⟩⟩
          exact ⟨_, ⟨mul_mem_right _ _ _ hx, ⟨_, ⟨mul_mem_right _ _ _ hy, add_mul _ _ _ |>.symm⟩⟩⟩⟩)
    suffices (I.ringCon ⊔ J.ringCon) ≤ s.ringCon by
      intro h; convert this h; rw [rel_iff, sub_zero, mem_mk']; rfl
    refine sup_le (fun x y h => ?_) (fun x y h => ?_) <;> rw [rel_iff] at h ⊢ <;> rw [mem_mk']
    exacts [⟨_, ⟨h, ⟨0, ⟨zero_mem _, add_zero _⟩⟩⟩⟩, ⟨0, ⟨zero_mem _, ⟨_, ⟨h, zero_add _⟩⟩⟩⟩]
  · rintro ⟨y, ⟨hy, ⟨z, ⟨hz, rfl⟩⟩⟩⟩; exact add_mem _ (mem_sup_left hy) (mem_sup_right hz)

end sup

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

lemma iSup_ringCon {ι : Type*} (I : ι → TwoSidedIdeal R) :
    (⨆ i, I i).ringCon = ⨆ i, (I i).ringCon := by
  simp only [iSup, sSup_ringCon]; congr; ext; simp

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

lemma iInf_ringCon {ι : Type*} (I : ι → TwoSidedIdeal R) :
    (⨅ i, I i).ringCon = ⨅ i, (I i).ringCon := by
  simp only [iInf, sInf_ringCon]; congr!; ext; simp

-- INSTANCE (free from Core): :

lemma mem_iInf {ι : Type*} {I : ι → TwoSidedIdeal R} {x : R} :
    x ∈ iInf I ↔ ∀ i, x ∈ I i :=
  show (∀ _, _) ↔ _ by simp [mem_iff]

lemma mem_sInf {S : Set (TwoSidedIdeal R)} {x : R} :
    x ∈ sInf S ↔ ∀ I ∈ S, x ∈ I :=
  show (∀ _, _) ↔ _ by simp [mem_iff]

-- INSTANCE (free from Core): :
