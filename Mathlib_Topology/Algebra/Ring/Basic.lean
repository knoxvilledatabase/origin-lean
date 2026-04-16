/-
Extracted from Topology/Algebra/Ring/Basic.lean
Genuine: 37 | Conflates: 0 | Dissolved: 0 | Infrastructure: 27
-/
import Origin.Core
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Topology.Algebra.Group.Basic

noncomputable section

/-!

# Topological (semi)rings

A topological (semi)ring is a (semi)ring equipped with a topology such that all operations are
continuous. Besides this definition, this file proves that the topological closure of a subring
(resp. an ideal) is a subring (resp. an ideal) and defines products and quotients
of topological (semi)rings.

## Main Results

- `Subring.topologicalClosure`/`Subsemiring.topologicalClosure`: the topological closure of a
  `Subring`/`Subsemiring` is itself a `Sub(semi)ring`.
- The product of two topological (semi)rings is a topological (semi)ring.
- The indexed product of topological (semi)rings is a topological (semi)ring.
-/

open Set Filter TopologicalSpace Function Topology Filter

section TopologicalSemiring

variable (α : Type*)

class TopologicalSemiring [TopologicalSpace α] [NonUnitalNonAssocSemiring α] extends
  ContinuousAdd α, ContinuousMul α : Prop

class TopologicalRing [TopologicalSpace α] [NonUnitalNonAssocRing α] extends TopologicalSemiring α,
  ContinuousNeg α : Prop

variable {α}

theorem TopologicalSemiring.continuousNeg_of_mul [TopologicalSpace α] [NonAssocRing α]
    [ContinuousMul α] : ContinuousNeg α where
  continuous_neg := by
    simpa using (continuous_const.mul continuous_id : Continuous fun x : α => -1 * x)

theorem TopologicalSemiring.toTopologicalRing [TopologicalSpace α] [NonAssocRing α]
    (_ : TopologicalSemiring α) : TopologicalRing α where
  toContinuousNeg := TopologicalSemiring.continuousNeg_of_mul

instance (priority := 100) TopologicalRing.to_topologicalAddGroup [NonUnitalNonAssocRing α]
    [TopologicalSpace α] [TopologicalRing α] : TopologicalAddGroup α := ⟨⟩

instance (priority := 50) DiscreteTopology.topologicalSemiring [TopologicalSpace α]
    [NonUnitalNonAssocSemiring α] [DiscreteTopology α] : TopologicalSemiring α := ⟨⟩

instance (priority := 50) DiscreteTopology.topologicalRing [TopologicalSpace α]
    [NonUnitalNonAssocRing α] [DiscreteTopology α] : TopologicalRing α := ⟨⟩

section

namespace NonUnitalSubsemiring

variable [TopologicalSpace α] [NonUnitalSemiring α] [TopologicalSemiring α]

instance instTopologicalSemiring (S : NonUnitalSubsemiring α) : TopologicalSemiring S :=
  { S.toSubsemigroup.continuousMul, S.toAddSubmonoid.continuousAdd with }

def topologicalClosure (s : NonUnitalSubsemiring α) : NonUnitalSubsemiring α :=
  { s.toSubsemigroup.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set α) }

@[simp]
theorem topologicalClosure_coe (s : NonUnitalSubsemiring α) :
    (s.topologicalClosure : Set α) = _root_.closure (s : Set α) :=
  rfl

theorem le_topologicalClosure (s : NonUnitalSubsemiring α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem isClosed_topologicalClosure (s : NonUnitalSubsemiring α) :
    IsClosed (s.topologicalClosure : Set α) := isClosed_closure

theorem topologicalClosure_minimal (s : NonUnitalSubsemiring α) {t : NonUnitalSubsemiring α}
    (h : s ≤ t) (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

abbrev nonUnitalCommSemiringTopologicalClosure [T2Space α] (s : NonUnitalSubsemiring α)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommSemiring s.topologicalClosure :=
  { NonUnitalSubsemiringClass.toNonUnitalSemiring s.topologicalClosure,
    s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end NonUnitalSubsemiring

variable [TopologicalSpace α] [Semiring α] [TopologicalSemiring α]

instance : TopologicalSemiring (ULift α) where

namespace Subsemiring

instance topologicalSemiring (S : Subsemiring α) : TopologicalSemiring S :=
  { S.toSubmonoid.continuousMul, S.toAddSubmonoid.continuousAdd with }

end Subsemiring

def Subsemiring.topologicalClosure (s : Subsemiring α) : Subsemiring α :=
  { s.toSubmonoid.topologicalClosure, s.toAddSubmonoid.topologicalClosure with
    carrier := _root_.closure (s : Set α) }

@[simp]
theorem Subsemiring.topologicalClosure_coe (s : Subsemiring α) :
    (s.topologicalClosure : Set α) = _root_.closure (s : Set α) :=
  rfl

theorem Subsemiring.le_topologicalClosure (s : Subsemiring α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem Subsemiring.isClosed_topologicalClosure (s : Subsemiring α) :
    IsClosed (s.topologicalClosure : Set α) := isClosed_closure

theorem Subsemiring.topologicalClosure_minimal (s : Subsemiring α) {t : Subsemiring α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

abbrev Subsemiring.commSemiringTopologicalClosure [T2Space α] (s : Subsemiring α)
    (hs : ∀ x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

end

section

variable {β : Type*} [TopologicalSpace α] [TopologicalSpace β]

instance [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] [TopologicalSemiring α]
    [TopologicalSemiring β] : TopologicalSemiring (α × β) where

instance [NonUnitalNonAssocRing α] [NonUnitalNonAssocRing β] [TopologicalRing α]
    [TopologicalRing β] : TopologicalRing (α × β) where

end

instance {β : Type*} {C : β → Type*} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocSemiring (C b)] [∀ b, TopologicalSemiring (C b)] :
    ContinuousAdd ((b : β) → C b) :=
  inferInstance

instance Pi.instTopologicalSemiring {β : Type*} {C : β → Type*} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocSemiring (C b)] [∀ b, TopologicalSemiring (C b)] :
    TopologicalSemiring (∀ b, C b) where

instance Pi.instTopologicalRing {β : Type*} {C : β → Type*} [∀ b, TopologicalSpace (C b)]
    [∀ b, NonUnitalNonAssocRing (C b)] [∀ b, TopologicalRing (C b)] :
    TopologicalRing (∀ b, C b) := ⟨⟩

section MulOpposite

open MulOpposite

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [ContinuousAdd α] :
    ContinuousAdd αᵐᵒᵖ :=
  continuousAdd_induced opAddEquiv.symm

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [TopologicalSemiring α] :
    TopologicalSemiring αᵐᵒᵖ := ⟨⟩

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [ContinuousNeg α] : ContinuousNeg αᵐᵒᵖ :=
  opHomeomorph.symm.isInducing.continuousNeg fun _ => rfl

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [TopologicalRing α] :
    TopologicalRing αᵐᵒᵖ := ⟨⟩

end MulOpposite

section AddOpposite

open AddOpposite

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [ContinuousMul α] :
    ContinuousMul αᵃᵒᵖ :=
  continuousMul_induced opMulEquiv.symm

instance [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [TopologicalSemiring α] :
    TopologicalSemiring αᵃᵒᵖ := ⟨⟩

instance [NonUnitalNonAssocRing α] [TopologicalSpace α] [TopologicalRing α] :
    TopologicalRing αᵃᵒᵖ := ⟨⟩

end AddOpposite

section

variable {R : Type*} [NonUnitalNonAssocRing R] [TopologicalSpace R]

theorem TopologicalRing.of_addGroup_of_nhds_zero [TopologicalAddGroup R]
    (hmul : Tendsto (uncurry ((· * ·) : R → R → R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hmul_left : ∀ x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : ∀ x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0) : TopologicalRing R where
  continuous_mul := by
    refine continuous_of_continuousAt_zero₂ (AddMonoidHom.mul (R := R)) ?_ ?_ ?_ <;>
      simpa only [ContinuousAt, mul_zero, zero_mul, nhds_prod_eq, AddMonoidHom.mul_apply]

theorem TopologicalRing.of_nhds_zero
    (hadd : Tendsto (uncurry ((· + ·) : R → R → R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hneg : Tendsto (fun x => -x : R → R) (𝓝 0) (𝓝 0))
    (hmul : Tendsto (uncurry ((· * ·) : R → R → R)) (𝓝 0 ×ˢ 𝓝 0) <| 𝓝 0)
    (hmul_left : ∀ x₀ : R, Tendsto (fun x : R => x₀ * x) (𝓝 0) <| 𝓝 0)
    (hmul_right : ∀ x₀ : R, Tendsto (fun x : R => x * x₀) (𝓝 0) <| 𝓝 0)
    (hleft : ∀ x₀ : R, 𝓝 x₀ = map (fun x => x₀ + x) (𝓝 0)) : TopologicalRing R :=
  have := TopologicalAddGroup.of_comm_of_nhds_zero hadd hneg hleft
  TopologicalRing.of_addGroup_of_nhds_zero hmul hmul_left hmul_right

end

variable [TopologicalSpace α]

section

variable [NonUnitalNonAssocRing α] [TopologicalRing α]

instance : TopologicalRing (ULift α) where

theorem mulLeft_continuous (x : α) : Continuous (AddMonoidHom.mulLeft x) :=
  continuous_const.mul continuous_id

theorem mulRight_continuous (x : α) : Continuous (AddMonoidHom.mulRight x) :=
  continuous_id.mul continuous_const

end

namespace NonUnitalSubring

variable [NonUnitalRing α] [TopologicalRing α]

instance instTopologicalRing (S : NonUnitalSubring α) : TopologicalRing S :=
  { S.toSubsemigroup.continuousMul, inferInstanceAs (TopologicalAddGroup S.toAddSubgroup) with }

def topologicalClosure (S : NonUnitalSubring α) : NonUnitalSubring α :=
  { S.toSubsemigroup.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set α) }

theorem le_topologicalClosure (s : NonUnitalSubring α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem isClosed_topologicalClosure (s : NonUnitalSubring α) :
    IsClosed (s.topologicalClosure : Set α) := isClosed_closure

theorem topologicalClosure_minimal (s : NonUnitalSubring α) {t : NonUnitalSubring α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

abbrev nonUnitalCommRingTopologicalClosure [T2Space α] (s : NonUnitalSubring α)
    (hs : ∀ x y : s, x * y = y * x) : NonUnitalCommRing s.topologicalClosure :=
  { s.topologicalClosure.toNonUnitalRing, s.toSubsemigroup.commSemigroupTopologicalClosure hs with }

end NonUnitalSubring

variable [Ring α] [TopologicalRing α]

instance Subring.instTopologicalRing (S : Subring α) : TopologicalRing S :=
  { S.toSubmonoid.continuousMul, inferInstanceAs (TopologicalAddGroup S.toAddSubgroup) with }

def Subring.topologicalClosure (S : Subring α) : Subring α :=
  { S.toSubmonoid.topologicalClosure, S.toAddSubgroup.topologicalClosure with
    carrier := _root_.closure (S : Set α) }

theorem Subring.le_topologicalClosure (s : Subring α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem Subring.isClosed_topologicalClosure (s : Subring α) :
    IsClosed (s.topologicalClosure : Set α) := isClosed_closure

theorem Subring.topologicalClosure_minimal (s : Subring α) {t : Subring α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

abbrev Subring.commRingTopologicalClosure [T2Space α] (s : Subring α)
    (hs : ∀ x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }

end TopologicalSemiring

/-!
### Lattice of ring topologies
We define a type class `RingTopology α` which endows a ring `α` with a topology such that all ring
operations are continuous.

Ring topologies on a fixed ring `α` are ordered, by reverse inclusion. They form a complete lattice,
with `⊥` the discrete topology and `⊤` the indiscrete topology.

Any function `f : α → β` induces `coinduced f : TopologicalSpace α → RingTopology β`. -/

universe u v

structure RingTopology (α : Type u) [Ring α] extends TopologicalSpace α, TopologicalRing α : Type u

namespace RingTopology

variable {α : Type*} [Ring α]

instance inhabited {α : Type u} [Ring α] : Inhabited (RingTopology α) :=
  ⟨let _ : TopologicalSpace α := ⊤;
    { continuous_add := continuous_top
      continuous_mul := continuous_top
      continuous_neg := continuous_top }⟩

theorem toTopologicalSpace_injective :
    Injective (toTopologicalSpace : RingTopology α → TopologicalSpace α) := by
  intro f g _; cases f; cases g; congr

@[ext]
theorem ext {f g : RingTopology α} (h : f.IsOpen = g.IsOpen) : f = g :=
  toTopologicalSpace_injective <| TopologicalSpace.ext h

instance : PartialOrder (RingTopology α) :=
  PartialOrder.lift RingTopology.toTopologicalSpace toTopologicalSpace_injective

private def def_sInf (S : Set (RingTopology α)) : RingTopology α :=
  let _ := sInf (toTopologicalSpace '' S)
  { toContinuousAdd := continuousAdd_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousAdd
    toContinuousMul := continuousMul_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousMul
    toContinuousNeg := continuousNeg_sInf <| forall_mem_image.2 fun t _ =>
      let _ := t.1; t.toContinuousNeg }

instance : CompleteSemilatticeInf (RingTopology α) where
  sInf := def_sInf
  sInf_le := fun _ a haS => sInf_le (α := TopologicalSpace α) ⟨a, ⟨haS, rfl⟩⟩
  le_sInf := fun _ _ h => le_sInf (α := TopologicalSpace α) <| forall_mem_image.2 h

instance : CompleteLattice (RingTopology α) :=
  completeLatticeOfCompleteSemilatticeInf _

def coinduced {α β : Type*} [t : TopologicalSpace α] [Ring β] (f : α → β) : RingTopology β :=
  sInf { b : RingTopology β | t.coinduced f ≤ b.toTopologicalSpace }

theorem coinduced_continuous {α β : Type*} [t : TopologicalSpace α] [Ring β] (f : α → β) :
    Continuous[t, (coinduced f).toTopologicalSpace] f :=
  continuous_sInf_rng.2 <| forall_mem_image.2 fun _ => continuous_iff_coinduced_le.2

def toAddGroupTopology (t : RingTopology α) : AddGroupTopology α where
  toTopologicalSpace := t.toTopologicalSpace
  toTopologicalAddGroup :=
    @TopologicalRing.to_topologicalAddGroup _ _ t.toTopologicalSpace t.toTopologicalRing

def toAddGroupTopology.orderEmbedding : OrderEmbedding (RingTopology α) (AddGroupTopology α) :=
  OrderEmbedding.ofMapLEIff toAddGroupTopology fun _ _ => Iff.rfl

end RingTopology

section AbsoluteValue

def AbsoluteValue.comp {R S T : Type*} [Semiring T] [Semiring R] [OrderedSemiring S]
    (v : AbsoluteValue R S) {f : T →+* R} (hf : Function.Injective f) : AbsoluteValue T S where
  toMulHom := v.1.comp f
  nonneg' _ := v.nonneg _
  eq_zero' _ := v.eq_zero.trans (map_eq_zero_iff f hf)
  add_le' _ _ := (congr_arg v (map_add f _ _)).trans_le (v.add_le _ _)

end AbsoluteValue
