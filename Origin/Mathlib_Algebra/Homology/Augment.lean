/-
Extracted from Algebra/Homology/Augment.lean
Genuine: 15 | Conflates: 0 | Dissolved: 0 | Infrastructure: 19
-/
import Origin.Core
import Mathlib.Algebra.Homology.Single

noncomputable section

/-!
# Augmentation and truncation of `ℕ`-indexed (co)chain complexes.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe v u

variable {V : Type u} [Category.{v} V]

namespace ChainComplex

@[simps]
def truncate [HasZeroMorphisms V] : ChainComplex V ℕ ⥤ ChainComplex V ℕ where
  obj C :=
    { X := fun i => C.X (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
      shape := fun i j w => C.shape _ _ <| by simpa }
  map f := { f := fun i => f.f (i + 1) }

def truncateTo [HasZeroObject V] [HasZeroMorphisms V] (C : ChainComplex V ℕ) :
    truncate.obj C ⟶ (single₀ V).obj (C.X 0) :=
  (toSingle₀Equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 1 0, by aesop⟩

variable [HasZeroMorphisms V]

def augment (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    ChainComplex V ℕ where
  X | 0 => X
    | i + 1 => C.X i
  d | 1, 0 => f
    | i + 1, j + 1 => C.d i j
    | _, _ => 0
  shape
    | 1, 0, h => absurd rfl h
    | _ + 2, 0, _ => rfl
    | 0, _, _ => rfl
    | i + 1, j + 1, h => by
      simp only; exact C.shape i j (Nat.succ_ne_succ.1 h)
  d_comp_d'
    | _, _, 0, rfl, rfl => w
    | _, _, k + 1, rfl, rfl => C.d_comp_d _ _ _

def truncateAugment (C : ChainComplex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
    truncate.obj (augment C f w) ≅ C where
  hom := { f := fun _ => 𝟙 _ }
  inv :=
    { f := fun _ => 𝟙 _
      comm' := fun i j => by
        cases j <;>
          · dsimp
            simp }
  hom_inv_id := by
    ext (_ | i) <;>
      · dsimp
        simp
  inv_hom_id := by
    ext (_ | i) <;>
      · dsimp
        simp

@[simp]
theorem chainComplex_d_succ_succ_zero (C : ChainComplex V ℕ) (i : ℕ) : C.d (i + 2) 0 = 0 := by
  rw [C.shape]
  exact i.succ_succ_ne_one.symm

def augmentTruncate (C : ChainComplex V ℕ) :
    augment (truncate.obj C) (C.d 1 0) (C.d_comp_d _ _ _) ≅ C where
  hom :=
    { f := fun | 0 => 𝟙 _ | _+1 => 𝟙 _
      comm' := fun i j => by
        -- Porting note: was an rcases n with (_|_|n) but that was causing issues
        match i with
        | 0 | 1 | n+2 =>
          cases' j with j <;> dsimp [augment, truncate] <;> simp
    }
  inv :=
    { f := fun | 0 => 𝟙 _ | _+1 => 𝟙 _
      comm' := fun i j => by
        -- Porting note: was an rcases n with (_|_|n) but that was causing issues
        match i with
          | 0 | 1 | n+2 =>
          cases' j with j <;> dsimp [augment, truncate] <;> simp
    }
  hom_inv_id := by
    ext i
    cases i <;>
      · dsimp
        simp
  inv_hom_id := by
    ext i
    cases i <;>
      · dsimp
        simp

def toSingle₀AsComplex [HasZeroObject V] (C : ChainComplex V ℕ) (X : V)
    (f : C ⟶ (single₀ V).obj X) : ChainComplex V ℕ :=
  let ⟨f, w⟩ := toSingle₀Equiv C X f
  augment C f w

end ChainComplex

namespace CochainComplex

@[simps]
def truncate [HasZeroMorphisms V] : CochainComplex V ℕ ⥤ CochainComplex V ℕ where
  obj C :=
    { X := fun i => C.X (i + 1)
      d := fun i j => C.d (i + 1) (j + 1)
      shape := fun i j w => by
        apply C.shape
        simpa }
  map f := { f := fun i => f.f (i + 1) }

def toTruncate [HasZeroObject V] [HasZeroMorphisms V] (C : CochainComplex V ℕ) :
    (single₀ V).obj (C.X 0) ⟶ truncate.obj C :=
  (fromSingle₀Equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 0 1, by aesop⟩

variable [HasZeroMorphisms V]

def augment (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    CochainComplex V ℕ where
  X | 0 => X
    | i + 1 => C.X i
  d | 0, 1 => f
    | i + 1, j + 1 => C.d i j
    | _, _ => 0
  shape i j s := by
    simp? at s says simp only [ComplexShape.up_Rel] at s
    rcases j with (_ | _ | j) <;> cases i <;> try simp
    · contradiction
    · rw [C.shape]
      simp only [ComplexShape.up_Rel]
      contrapose! s
      rw [← s]
  d_comp_d' i j k hij hjk := by
    rcases k with (_ | _ | k) <;> rcases j with (_ | _ | j) <;> cases i <;> try simp
    cases k
    · exact w
    · rw [C.shape, comp_zero]
      simp only [ComplexShape.up_Rel, zero_add]
      exact (Nat.one_lt_succ_succ _).ne

def truncateAugment (C : CochainComplex V ℕ) {X : V} (f : X ⟶ C.X 0) (w : f ≫ C.d 0 1 = 0) :
    truncate.obj (augment C f w) ≅ C where
  hom := { f := fun _ => 𝟙 _ }
  inv :=
    { f := fun _ => 𝟙 _
      comm' := fun i j => by
        cases j <;>
          · dsimp
            simp }
  hom_inv_id := by
    ext i
    cases i <;>
      · dsimp
        simp
  inv_hom_id := by
    ext i
    cases i <;>
      · dsimp
        simp

@[simp]
theorem cochainComplex_d_succ_succ_zero (C : CochainComplex V ℕ) (i : ℕ) : C.d 0 (i + 2) = 0 := by
  rw [C.shape]
  simp only [ComplexShape.up_Rel, zero_add]
  exact (Nat.one_lt_succ_succ _).ne

def augmentTruncate (C : CochainComplex V ℕ) :
    augment (truncate.obj C) (C.d 0 1) (C.d_comp_d _ _ _) ≅ C where
  hom :=
    { f := fun | 0 => 𝟙 _ | _+1 => 𝟙 _
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;> cases i <;>
          · dsimp
            -- Porting note https://github.com/leanprover-community/mathlib4/issues/10959
            -- simp can't handle this now but aesop does
            aesop }
  inv :=
    { f := fun | 0 => 𝟙 _ | _+1 => 𝟙 _
      comm' := fun i j => by
        rcases j with (_ | _ | j) <;> cases' i with i <;>
          · dsimp
            -- Porting note https://github.com/leanprover-community/mathlib4/issues/10959
            -- simp can't handle this now but aesop does
            aesop }
  hom_inv_id := by
    ext i
    cases i <;>
      · dsimp
        simp
  inv_hom_id := by
    ext i
    cases i <;>
      · dsimp
        simp

def fromSingle₀AsComplex [HasZeroObject V] (C : CochainComplex V ℕ) (X : V)
    (f : (single₀ V).obj X ⟶ C) : CochainComplex V ℕ :=
  let ⟨f, w⟩ := fromSingle₀Equiv C X f
  augment C f w

end CochainComplex
