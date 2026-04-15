/-
Extracted from LinearAlgebra/CliffordAlgebra/SpinGroup.lean
Genuine: 13 of 14 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The Pin group and the Spin group

In this file we define `lipschitzGroup`, `pinGroup` and `spinGroup` and show they form a group.

## Main definitions

* `lipschitzGroup`: the Lipschitz group with a quadratic form.
* `pinGroup`: the Pin group defined as the infimum of `lipschitzGroup` and `unitary`.
* `spinGroup`: the Spin group defined as the infimum of `pinGroup` and `CliffordAlgebra.even`.

## Implementation Notes

The definition of the Lipschitz group
$\{ x \in \mathop{\mathcal{C}\ell} | x \text{ is invertible and } x v x^{-1} ∈ V \}$ is given by:

* [fulton2004][], Chapter 20
* https://en.wikipedia.org/wiki/Clifford_algebra#Lipschitz_group

But they presumably form a group only in finite dimensions. So we define `lipschitzGroup` with
closure of all the invertible elements in the form of `ι Q m`, and we show this definition is
at least as large as the other definition (See `lipschitzGroup.conjAct_smul_range_ι` and
`lipschitzGroup.involute_act_ι_mem_range_ι`).
The reverse statement presumably is true only in finite dimensions.

Here are some discussions about the latent ambiguity of definition :
https://mathoverflow.net/q/427881/172242 and https://mathoverflow.net/q/251288/172242

## TODO

Try to show the reverse statement is true in finite dimensions.
-/

variable {R : Type*} [CommRing R]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {Q : QuadraticForm R M}

section Pin

open CliffordAlgebra MulAction

open scoped Pointwise

def lipschitzGroup (Q : QuadraticForm R M) : Subgroup (CliffordAlgebra Q)ˣ :=
  Subgroup.closure ((↑) ⁻¹' Set.range (ι Q) : Set (CliffordAlgebra Q)ˣ)

namespace lipschitzGroup

theorem conjAct_smul_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q)
    [Invertible (2 : R)] (m : M) :
    ConjAct.toConjAct x • ι Q m ∈ LinearMap.range (ι Q) := by
  unfold lipschitzGroup at hx
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  induction hx using Subgroup.closure_induction'' generalizing m with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    letI := x.invertible
    letI : Invertible (ι Q a) := by rwa [ha]
    letI : Invertible (Q a) := invertibleOfInvertibleι Q a
    simp_rw [← invOf_units x, ← ha, ι_mul_ι_mul_invOf_ι, LinearMap.mem_range_self]
  | inv_mem x hx =>
    obtain ⟨a, ha⟩ := hx
    letI := x.invertible
    letI : Invertible (ι Q a) := by rwa [ha]
    letI : Invertible (Q a) := invertibleOfInvertibleι Q a
    simp_rw [← invOf_units x, inv_inv, ← ha, invOf_ι_mul_ι_mul_ι, LinearMap.mem_range_self]
  | one => simp_rw [inv_one, Units.val_one, one_mul, mul_one, LinearMap.mem_range_self]
  | mul y z _ _ hy hz =>
    simp_rw [mul_inv_rev, Units.val_mul]
    suffices ↑y * (↑z * ι Q m * ↑z⁻¹) * ↑y⁻¹ ∈ _ by
      simpa only [mul_assoc] using this
    obtain ⟨z', hz'⟩ := hz m
    obtain ⟨y', hy'⟩ := hy z'
    simp_rw [← hz', ← hy', LinearMap.mem_range_self]

theorem involute_act_ι_mem_range_ι [Invertible (2 : R)]
    {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q) (b : M) :
      involute (Q := Q) ↑x * ι Q b * ↑x⁻¹ ∈ LinearMap.range (ι Q) := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' generalizing b with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    letI := x.invertible
    letI : Invertible (ι Q a) := by rwa [ha]
    letI : Invertible (Q a) := invertibleOfInvertibleι Q a
    simp_rw [← invOf_units x, ← ha, involute_ι, neg_mul, ι_mul_ι_mul_invOf_ι Q a b, ← map_neg,
      LinearMap.mem_range_self]
  | inv_mem x hx =>
    obtain ⟨a, ha⟩ := hx
    letI := x.invertible
    letI : Invertible (ι Q a) := by rwa [ha]
    letI : Invertible (Q a) := invertibleOfInvertibleι Q a
    letI := invertibleNeg (ι Q a)
    letI := Invertible.map involute (ι Q a)
    simp_rw [← invOf_units x, inv_inv, ← ha, map_invOf, involute_ι, invOf_neg, neg_mul,
      invOf_ι_mul_ι_mul_ι, ← map_neg, LinearMap.mem_range_self]
  | one => simp_rw [inv_one, Units.val_one, map_one, one_mul, mul_one, LinearMap.mem_range_self]
  | mul y z _ _ hy hz =>
    simp_rw [mul_inv_rev, Units.val_mul, map_mul]
    suffices involute (Q := Q) ↑y * (involute (Q := Q) ↑z * ι Q b * ↑z⁻¹) * ↑y⁻¹ ∈ _ by
      simpa only [mul_assoc] using this
    obtain ⟨z', hz'⟩ := hz b
    obtain ⟨y', hy'⟩ := hy z'
    simp_rw [← hz', ← hy', LinearMap.mem_range_self]

theorem conjAct_smul_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q)
    [Invertible (2 : R)] :
    ConjAct.toConjAct x • LinearMap.range (ι Q) = LinearMap.range (ι Q) := by
  suffices ∀ x ∈ lipschitzGroup Q,
      ConjAct.toConjAct x • LinearMap.range (ι Q) ≤ LinearMap.range (ι Q) by
    apply le_antisymm
    · exact this _ hx
    · have := smul_mono_right (ConjAct.toConjAct x) <| this _ (inv_mem hx)
      refine Eq.trans_le ?_ this
      simp only [map_inv, smul_inv_smul]
  intro x hx
  erw [Submodule.map_le_iff_le_comap]
  rintro _ ⟨m, rfl⟩
  exact conjAct_smul_ι_mem_range_ι hx _

theorem coe_mem_iff_mem {x : (CliffordAlgebra Q)ˣ} :
    ↑x ∈ (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ↔
    x ∈ lipschitzGroup Q := by
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply]
  norm_cast
  exact exists_eq_right

end lipschitzGroup

def pinGroup (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q) :=
  (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ⊓ unitary _

namespace pinGroup

theorem mem_lipschitzGroup {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) :
    x ∈ (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) :=
  hx.1

theorem mem_unitary {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) :
    x ∈ unitary (CliffordAlgebra Q) :=
  hx.2

theorem units_mem_iff {x : (CliffordAlgebra Q)ˣ} :
    ↑x ∈ pinGroup Q ↔ x ∈ lipschitzGroup Q ∧ ↑x ∈ unitary (CliffordAlgebra Q) := by
  rw [mem_iff, lipschitzGroup.coe_mem_iff_mem]

theorem units_mem_lipschitzGroup {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q) :
    x ∈ lipschitzGroup Q :=
  (units_mem_iff.1 hx).1

theorem conjAct_smul_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q)
    [Invertible (2 : R)] (y : M) : ConjAct.toConjAct x • ι Q y ∈ LinearMap.range (ι Q) :=
  lipschitzGroup.conjAct_smul_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

theorem involute_act_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q)
    [Invertible (2 : R)] (y : M) : involute (Q := Q) ↑x * ι Q y * ↑x⁻¹ ∈ LinearMap.range (ι Q) :=
  lipschitzGroup.involute_act_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

theorem conjAct_smul_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q)
    [Invertible (2 : R)] : ConjAct.toConjAct x • LinearMap.range (ι Q) = LinearMap.range (ι Q) :=
  lipschitzGroup.conjAct_smul_range_ι (units_mem_lipschitzGroup hx)
