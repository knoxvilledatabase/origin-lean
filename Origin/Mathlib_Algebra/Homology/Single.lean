/-
Extracted from Algebra/Homology/Single.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homological complexes supported in a single degree

We define `single V j c : V ⥤ HomologicalComplex V c`,
which constructs complexes in `V` of shape `c`, supported in degree `j`.

In `ChainComplex.toSingle₀Equiv` we characterize chain maps to an
`ℕ`-indexed complex concentrated in degree 0; they are equivalent to
`{ f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 }`.
(This is useful translating between a projective resolution and
an augmented exact complex of projectives.)

-/

open CategoryTheory Category Limits ZeroObject

universe v u

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V] [HasZeroObject V]

namespace HomologicalComplex

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

noncomputable def single (j : ι) : V ⥤ HomologicalComplex V c where
  obj A :=
    { X := fun i => if i = j then A else 0
      d := fun _ _ => 0 }
  map f :=
    { f := fun i => if h : i = j then eqToHom (by dsimp; rw [if_pos h]) ≫ f ≫
              eqToHom (by dsimp; rw [if_pos h]) else 0 }
  map_id A := by
    ext
    dsimp
    split_ifs with h
    · subst h
      simp
    · #adaptation_note /-- nightly-2024-03-07
      previously was `rw [if_neg h]; simp`, but that fails with "motive not type correct"
      This is because dsimp does not simplify numerals;
      this note should be removable once https://github.com/leanprover/lean4/pull/8433 lands. -/
      convert (id_zero (C := V)).symm
      all_goals simp [if_neg h]
  map_comp f g := by
    ext
    dsimp
    split_ifs with h
    · subst h
      simp
    · simp

variable {V}
