/-
Extracted from MeasureTheory/Function/LpOrder.lean
Genuine: 8 of 13 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Order related properties of Lp spaces

## Results

- `Lp E p μ` is an `OrderedAddCommGroup` when `E` is a `NormedLatticeAddCommGroup`.

## TODO

- move definitions of `Lp.posPart` and `Lp.negPart` to this file, and define them as
  `PosPart.pos` and `NegPart.neg` given by the lattice structure.

-/

open TopologicalSpace MeasureTheory

open scoped ENNReal

variable {α E : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

namespace MeasureTheory

namespace Lp

section Order

variable [NormedAddCommGroup E]

section PartialOrder

variable [PartialOrder E]

theorem coeFn_le (f g : Lp E p μ) : f ≤ᵐ[μ] g ↔ f ≤ g := by
  rw [← Subtype.coe_le_coe, ← AEEqFun.coeFn_le]

theorem coeFn_nonneg (f : Lp E p μ) : 0 ≤ᵐ[μ] f ↔ 0 ≤ f := by
  rw [← coeFn_le]
  have h0 := Lp.coeFn_zero E p μ
  constructor <;> intro h <;> filter_upwards [h, h0] with _ _ h2
  · rwa [h2]
  · rwa [← h2]

variable [IsOrderedAddMonoid E]

-- INSTANCE (free from Core): instAddLeftMono

-- INSTANCE (free from Core): instIsOrderedAddMonoid

-- INSTANCE (free from Core): [Fact

end PartialOrder

section Lattice

variable [Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E]

theorem _root_.MeasureTheory.MemLp.sup {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (f ⊔ g) p μ :=
  MemLp.mono' (hf.norm.add hg.norm) (hf.1.sup hg.1)
    (Filter.Eventually.of_forall fun x => norm_sup_le_add (f x) (g x))

theorem _root_.MeasureTheory.MemLp.inf {f g : α → E} (hf : MemLp f p μ) (hg : MemLp g p μ) :
    MemLp (f ⊓ g) p μ :=
  MemLp.mono' (hf.norm.add hg.norm) (hf.1.inf hg.1)
    (Filter.Eventually.of_forall fun x => norm_inf_le_add (f x) (g x))

theorem _root_.MeasureTheory.MemLp.abs {f : α → E} (hf : MemLp f p μ) : MemLp |f| p μ :=
  hf.sup hf.neg

-- INSTANCE (free from Core): instLattice

theorem coeFn_sup (f g : Lp E p μ) : ⇑(f ⊔ g) =ᵐ[μ] ⇑f ⊔ ⇑g :=
  AEEqFun.coeFn_sup _ _

theorem coeFn_inf (f g : Lp E p μ) : ⇑(f ⊓ g) =ᵐ[μ] ⇑f ⊓ ⇑g :=
  AEEqFun.coeFn_inf _ _

theorem coeFn_abs (f : Lp E p μ) : ⇑|f| =ᵐ[μ] fun x => |f x| :=
  AEEqFun.coeFn_abs _

-- INSTANCE (free from Core): instHasSolidNorm

end Lattice

end Order

end Lp

end MeasureTheory
