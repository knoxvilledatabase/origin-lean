/-
Extracted from CategoryTheory/Triangulated/TStructure/TruncLEGT.lean
Genuine: 7 of 12 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Truncations for a t-structure

Let `t` be a t-structure on a (pre)triangulated category `C`.
In this file, for any `n : ℤ`, we introduce the truncation functors
`t.truncLE n : C ⥤ C` and `t.truncGT n : C ⥤ C`, as variants of the functors
`t.truncLT n : C ⥤ C` and `t.truncGE n : C ⥤ C` introduced in the file
`Mathlib/CategoryTheory/Triangulated/TStructure/TruncLTGE.lean`.

-/

namespace CategoryTheory

open Limits Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

noncomputable def truncLE (n : ℤ) : C ⥤ C := t.truncLT (n + 1)

-- INSTANCE (free from Core): (n

lemma isLE_truncLE_obj (X : C) (a b : ℤ) (hn : a ≤ b := by lia) :
    t.IsLE ((t.truncLE a).obj X) b :=
  t.isLE_truncLT_obj ..

-- INSTANCE (free from Core): (n

noncomputable def truncGT (n : ℤ) : C ⥤ C := t.truncGE (n + 1)

-- INSTANCE (free from Core): (n

lemma isGE_truncGT_obj (X : C) (a b : ℤ) (hn : b ≤ a + 1 := by lia) :
    t.IsGE ((t.truncGT a).obj X) b :=
  t.isGE_truncGE_obj ..

-- INSTANCE (free from Core): (n

-- INSTANCE (free from Core): (n

noncomputable def truncLEIsoTruncLT (a b : ℤ) (h : a + 1 = b) :
    t.truncLE a ≅ t.truncLT b :=
  eqToIso (by rw [← h]; rfl)

noncomputable def truncGTIsoTruncGE (a b : ℤ) (h : a + 1 = b) :
    t.truncGT a ≅ t.truncGE b :=
  eqToIso (by rw [← h]; rfl)

noncomputable def truncLEι (n : ℤ) : t.truncLE n ⟶ 𝟭 C := t.truncLTι (n + 1)

set_option backward.isDefEq.respectTransparency false in
