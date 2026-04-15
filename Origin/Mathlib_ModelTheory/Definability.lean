/-
Extracted from ModelTheory/Definability.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Definable Sets

This file defines what it means for a set over a first-order structure to be definable.

## Main Definitions

- `Set.Definable` is defined so that `A.Definable L s` indicates that the
  set `s` of a finite Cartesian power of `M` is definable with parameters in `A`.
- `Set.Definable₁` is defined so that `A.Definable₁ L s` indicates that
  `(s : Set M)` is definable with parameters in `A`.
- `Set.Definable₂` is defined so that `A.Definable₂ L s` indicates that
  `(s : Set (M × M))` is definable with parameters in `A`.
- A `FirstOrder.Language.DefinableSet` is defined so that `L.DefinableSet A α` is the Boolean
  algebra of subsets of `α → M` defined by formulas with parameters in `A`.
- `Set.TermDefinable` functions are those equivalent to some term expressible in the language.
- `Set.TermDefinable₁` specialize this to case of unary functions.

## Main Results

- `L.DefinableSet A α` forms a `BooleanAlgebra`
- `Set.Definable.image_comp` shows that definability is closed under projections in finite
  dimensions.
- The `Set.TermDefinable` property is transitive, and `TermDefinable` functions are closed under
  composition.

-/

universe u v w u₁

namespace Set

variable {M : Type w} (A : Set M) (L : FirstOrder.Language.{u, v}) [L.Structure M]

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

variable {α : Type u₁} {β : Type*}

def Definable (s : Set (α → M)) : Prop :=
  ∃ φ : L[[A]].Formula α, s = setOf φ.Realize

variable {L} {A} {B : Set M} {s : Set (α → M)}

theorem definable_iff_exists_formula_sum :
    A.Definable L s ↔ ∃ φ : L.Formula (A ⊕ α), s = {v | φ.Realize (Sum.elim (↑) v)} := by
  rw [Definable, Equiv.exists_congr_left (BoundedFormula.constantsVarsEquiv)]
  refine exists_congr (fun φ => iff_iff_eq.2 (congr_arg (s = ·) ?_))
  ext
  simp only [BoundedFormula.constantsVarsEquiv, constantsOn,
    BoundedFormula.mapTermRelEquiv_symm_apply, mem_setOf_eq, Formula.Realize]
  refine BoundedFormula.realize_mapTermRel_id ?_ (fun _ _ _ => rfl)
  intros
  simp only [Term.constantsVarsEquivLeft_symm_apply, Term.realize_varsToConstants,
    coe_con, Term.realize_relabel]
  congr 1 with a
  rcases a with (_ | _) | _ <;> rfl

set_option backward.isDefEq.respectTransparency false in

theorem empty_definable_iff :
    (∅ : Set M).Definable L s ↔ ∃ φ : L.Formula α, s = setOf φ.Realize := by
  rw [Definable, Equiv.exists_congr_left (LEquiv.addEmptyConstants L (∅ : Set M)).onFormula]
  simp

theorem definable_iff_empty_definable_with_params :
    A.Definable L s ↔ (∅ : Set M).Definable L[[A]] s :=
  empty_definable_iff.symm

theorem Definable.mono (hAs : A.Definable L s) (hAB : A ⊆ B) : B.Definable L s := by
  rw [definable_iff_empty_definable_with_params] at *
  exact hAs.map_expansion (L.lhomWithConstantsMap (Set.inclusion hAB))
