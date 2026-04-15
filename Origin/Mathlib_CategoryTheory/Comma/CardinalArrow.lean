/-
Extracted from CategoryTheory/Comma/CardinalArrow.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Cardinal of Arrow

We obtain various results about the cardinality of `Arrow C`. For example,
if `C` is a (small) category, `Arrow C` is finite iff `FinCategory C` holds.

-/

universe w w' v u

namespace CategoryTheory

lemma Arrow.finite_iff (C : Type u) [SmallCategory C] :
    Finite (Arrow C) ↔ Nonempty (FinCategory C) := by
  constructor
  · intro
    refine ⟨?_, fun a b ↦ ?_⟩
    · have := Finite.of_injective (fun (a : C) ↦ Arrow.mk (𝟙 a))
        (fun _ _ ↦ congr_arg Comma.left)
      apply Fintype.ofFinite
    · have := Finite.of_injective (fun (f : a ⟶ b) ↦ Arrow.mk f)
        (fun f g h ↦ by
          change (Arrow.mk f).hom = (Arrow.mk g).hom
          congr)
      apply Fintype.ofFinite
  · rintro ⟨_⟩
    have := Fintype.ofEquiv _ (Arrow.equivSigma C).symm
    infer_instance

-- INSTANCE (free from Core): Arrow.finite

def Arrow.opEquiv (C : Type u) [Category.{v} C] : Arrow Cᵒᵖ ≃ Arrow C where
  toFun f := Arrow.mk f.hom.unop
  invFun g := Arrow.mk g.hom.op
