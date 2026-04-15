/-
Extracted from MeasureTheory/Group/MeasurableEquiv.lean
Genuine: 12 | Conflates: 0 | Dissolved: 14 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# (Scalar) multiplication and (vector) addition as measurable equivalences

In this file we define the following measurable equivalences:

* `MeasurableEquiv.smul`: if a group `G` acts on `α` by measurable maps, then each element `c : G`
  defines a measurable automorphism of `α`;
* `MeasurableEquiv.vadd`: additive version of `MeasurableEquiv.smul`;
* `MeasurableEquiv.smul₀`: if a group with zero `G` acts on `α` by measurable maps, then each
  nonzero element `c : G` defines a measurable automorphism of `α`;
* `MeasurableEquiv.mulLeft`: if `G` is a group with measurable multiplication, then left
  multiplication by `g : G` is a measurable automorphism of `G`;
* `MeasurableEquiv.addLeft`: additive version of `MeasurableEquiv.mulLeft`;
* `MeasurableEquiv.mulRight`: if `G` is a group with measurable multiplication, then right
  multiplication by `g : G` is a measurable automorphism of `G`;
* `MeasurableEquiv.addRight`: additive version of `MeasurableEquiv.mulRight`;
* `MeasurableEquiv.mulLeft₀`, `MeasurableEquiv.mulRight₀`: versions of
  `MeasurableEquiv.mulLeft` and `MeasurableEquiv.mulRight` for groups with zero;
* `MeasurableEquiv.inv`: `Inv.inv` as a measurable automorphism
  of a group (or a group with zero);
* `MeasurableEquiv.neg`: negation as a measurable automorphism of an additive group.

We also deduce that the corresponding maps are measurable embeddings.

## Tags

measurable, equivalence, group action
-/

namespace MeasurableEquiv

variable {G G₀ α : Type*} [MeasurableSpace G] [MeasurableSpace G₀] [MeasurableSpace α] [Group G]
  [GroupWithZero G₀] [MulAction G α] [MulAction G₀ α] [MeasurableSMul G α] [MeasurableSMul G₀ α]

@[to_additive (attr := simps! (config := .asFn) toEquiv apply)
      "If an additive group `G` acts on `α` by measurable maps, then each element `c : G`
      defines a measurable automorphism of `α`." ]
def smul (c : G) : α ≃ᵐ α where
  toEquiv := MulAction.toPerm c
  measurable_toFun := measurable_const_smul c
  measurable_invFun := measurable_const_smul c⁻¹

@[to_additive]
theorem _root_.measurableEmbedding_const_smul (c : G) : MeasurableEmbedding (c • · : α → α) :=
  (smul c).measurableEmbedding

@[to_additive (attr := simp)]
theorem symm_smul (c : G) : (smul c : α ≃ᵐ α).symm = smul c⁻¹ :=
  ext rfl

-- DISSOLVED: smul₀

-- DISSOLVED: coe_smul₀

-- DISSOLVED: symm_smul₀

-- DISSOLVED: _root_.measurableEmbedding_const_smul₀

section Mul

variable [MeasurableMul G] [MeasurableMul G₀]

@[to_additive
      "If `G` is an additive group with measurable addition, then addition of `g : G`
      on the left is a measurable automorphism of `G`."]
def mulLeft (g : G) : G ≃ᵐ G :=
  smul g

@[to_additive (attr := simp)]
theorem coe_mulLeft (g : G) : ⇑(mulLeft g) = (g * ·) :=
  rfl

@[to_additive (attr := simp)]
theorem symm_mulLeft (g : G) : (mulLeft g).symm = mulLeft g⁻¹ :=
  ext rfl

@[to_additive (attr := simp)]
theorem toEquiv_mulLeft (g : G) : (mulLeft g).toEquiv = Equiv.mulLeft g :=
  rfl

@[to_additive]
theorem _root_.measurableEmbedding_mulLeft (g : G) : MeasurableEmbedding (g * ·) :=
  (mulLeft g).measurableEmbedding

@[to_additive
      "If `G` is an additive group with measurable addition, then addition of `g : G`
      on the right is a measurable automorphism of `G`."]
def mulRight (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.mulRight g
  measurable_toFun := measurable_mul_const g
  measurable_invFun := measurable_mul_const g⁻¹

@[to_additive]
theorem _root_.measurableEmbedding_mulRight (g : G) : MeasurableEmbedding fun x => x * g :=
  (mulRight g).measurableEmbedding

@[to_additive (attr := simp)]
theorem coe_mulRight (g : G) : ⇑(mulRight g) = fun x => x * g :=
  rfl

@[to_additive (attr := simp)]
theorem symm_mulRight (g : G) : (mulRight g).symm = mulRight g⁻¹ :=
  ext rfl

@[to_additive (attr := simp)]
theorem toEquiv_mulRight (g : G) : (mulRight g).toEquiv = Equiv.mulRight g :=
  rfl

-- DISSOLVED: mulLeft₀

-- DISSOLVED: _root_.measurableEmbedding_mulLeft₀

-- DISSOLVED: coe_mulLeft₀

-- DISSOLVED: symm_mulLeft₀

-- DISSOLVED: toEquiv_mulLeft₀

-- DISSOLVED: mulRight₀

-- DISSOLVED: _root_.measurableEmbedding_mulRight₀

-- DISSOLVED: coe_mulRight₀

-- DISSOLVED: symm_mulRight₀

-- DISSOLVED: toEquiv_mulRight₀

end Mul

@[to_additive (attr := simps! (config := .asFn) toEquiv apply)
    "Negation as a measurable automorphism of an additive group."]
def inv (G) [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] : G ≃ᵐ G where
  toEquiv := Equiv.inv G
  measurable_toFun := measurable_inv
  measurable_invFun := measurable_inv

@[to_additive (attr := simp)]
theorem symm_inv {G} [MeasurableSpace G] [InvolutiveInv G] [MeasurableInv G] :
    (inv G).symm = inv G :=
  rfl

@[to_additive " `equiv.subRight` as a `MeasurableEquiv` "]
def divRight [MeasurableMul G] (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.divRight g
  measurable_toFun := measurable_div_const' g
  measurable_invFun := measurable_mul_const g

@[to_additive " `equiv.subLeft` as a `MeasurableEquiv` "]
def divLeft [MeasurableMul G] [MeasurableInv G] (g : G) : G ≃ᵐ G where
  toEquiv := Equiv.divLeft g
  measurable_toFun := measurable_id.const_div g
  measurable_invFun := measurable_inv.mul_const g

end MeasurableEquiv
