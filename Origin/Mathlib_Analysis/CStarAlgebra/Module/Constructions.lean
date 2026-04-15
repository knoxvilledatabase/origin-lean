/-
Extracted from Analysis/CStarAlgebra/Module/Constructions.lean
Genuine: 19 of 34 | Dissolved: 0 | Infrastructure: 15
-/
import Origin.Core
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.CStarAlgebra.Module.Synonym
import Mathlib.Topology.MetricSpace.Bilipschitz

/-! # Constructions of Hilbert C⋆-modules

In this file we define the following constructions of `CStarModule`s where `A` denotes a C⋆-algebra.
For some of the types listed below, the instance is declared on the type synonym `WithCStarModule E`
(with the notation `C⋆ᵐᵒᵈ E`), instead of on `E` itself; we explain the reasoning behind each
decision below.

1. `A` as a `CStarModule` over itself.
2. `C⋆ᵐᵒᵈ (E × F)` as a `CStarModule` over `A`, when `E` and `F` are themselves `CStarModule`s over
  `A`.
3. `C⋆ᵐᵒᵈ (Π i : ι, E i)` as a `CStarModule` over `A`, when each `E i` is a `CStarModule` over `A`
  and `ι` is a `Fintype`.
4. `E` as a `CStarModule` over `ℂ`, when `E` is an `InnerProductSpace` over `ℂ`.

For `E × F` and `Π i : ι, E i`, we are required to declare the instance on a type synonym rather
than on the product or pi-type itself because the existing norm on these types does not agree with
the one induced by the C⋆-module structure. Moreover, the norm induced by the C⋆-module structure
doesn't agree with any other natural norm on these types (e.g., `WithLp 2 (E × F)` unless `A := ℂ`),
so we need a new synonym.

On `A` (a C⋆-algebra) and `E` (an inner product space), we declare the instances on the types
themselves to ease the use of the C⋆-module structure. This does have the potential to cause
inconvenience (as sometimes Lean will see terms of type `A` and apply lemmas pertaining to
C⋆-modules to those terms, when the lemmas were actually intended for terms of some other
C⋆-module in context, say `F`, in which case the arguments must be provided explicitly; see for
instance the application of `CStarModule.norm_eq_sqrt_norm_inner_self` in the proof of
`WithCStarModule.max_le_prod_norm` below). However, we believe that this, hopefully rare,
inconvenience is outweighed by avoiding translating between type synonyms where possible.

For more details on the importance of the `WithCStarModule` type synonym, see the module
documentation for `Analysis.CStarAlgebra.Module.Synonym`.

## Implementation notes

When `A := ℂ` and `E := ℂ`, then `ℂ` is both a C⋆-algebra (so it inherits a `CStarModule` instance
via (1) above) and an inner product space (so it inherits a `CStarModule` instance via (4) above).
We provide a sanity check ensuring that these two instances are definitionally equal. We also ensure
that the `Inner ℂ ℂ` instance from `InnerProductSpace` is definitionally equal to the one inherited
from the `CStarModule` instances.

Note that `C⋆ᵐᵒᵈ E` is *already* equipped with a bornology and uniformity whenever `E` is (namely,
the pullback of the respective structures through `WithCStarModule.equiv`), so in each of the above
cases, it is necessary to temporarily instantiate `C⋆ᵐᵒᵈ E` with `CStarModule.normedAddCommGroup`,
show the resulting type is bilipschitz equivalent to `E` via `WithCStarModule.equiv` (in the first
and last case, this map is actually trivially an isometry), and then replace the uniformity and
bornology with the correct ones.

-/

open CStarModule CStarRing

namespace WithCStarModule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-! ## A C⋆-algebra as a C⋆-module over itself -/

section Self

variable [StarOrderedRing A]

instance : CStarModule A A where
  inner x y := star x * y
  inner_add_right := mul_add ..
  inner_self_nonneg := star_mul_self_nonneg _
  inner_self := CStarRing.star_mul_self_eq_zero_iff _
  inner_op_smul_right := mul_assoc .. |>.symm
  inner_smul_right_complex := mul_smul_comm ..
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity)]
    simpa [sq] using Eq.symm <| CStarRing.norm_star_mul_self

open scoped InnerProductSpace in

lemma inner_def (x y : A) : ⟪x, y⟫_A = star x * y := rfl

end Self

/-! ## Products of C⋆-modules -/

section Prod

open scoped InnerProductSpace

variable {E F : Type*}

variable [NormedAddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E]

variable [NormedAddCommGroup F] [Module ℂ F] [SMul Aᵐᵒᵖ F]

variable [CStarModule A E] [CStarModule A F]

noncomputable instance : Norm (C⋆ᵐᵒᵈ (E × F)) where
  norm x := √‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖

lemma prod_norm (x : C⋆ᵐᵒᵈ (E × F)) : ‖x‖ = √‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖ := rfl

lemma prod_norm_sq (x : C⋆ᵐᵒᵈ (E × F)) : ‖x‖ ^ 2 = ‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖ := by
  simp [prod_norm]

lemma prod_norm_le_norm_add (x : C⋆ᵐᵒᵈ (E × F)) : ‖x‖ ≤ ‖x.1‖ + ‖x.2‖ := by
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  calc ‖x‖ ^ 2 ≤ ‖⟪x.1, x.1⟫_A‖ + ‖⟪x.2, x.2⟫_A‖ := prod_norm_sq x ▸ norm_add_le _ _
    _ = ‖x.1‖ ^ 2 + 0 + ‖x.2‖ ^ 2 := by simp [norm_sq_eq]
    _ ≤ ‖x.1‖ ^ 2 + 2 * ‖x.1‖ * ‖x.2‖ + ‖x.2‖ ^ 2 := by gcongr; positivity
    _ = (‖x.1‖ + ‖x.2‖) ^ 2 := by ring

variable [StarOrderedRing A]

noncomputable instance : CStarModule A (C⋆ᵐᵒᵈ (E × F)) where
  inner x y := inner x.1 y.1 + inner x.2 y.2
  inner_add_right {x y z} := by simpa using add_add_add_comm ..
  inner_self_nonneg := add_nonneg CStarModule.inner_self_nonneg CStarModule.inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h, CStarModule.inner_zero_left]⟩
    apply equiv (E × F) |>.injective
    ext
    · refine inner_self.mp <| le_antisymm ?_ inner_self_nonneg
      exact le_add_of_nonneg_right CStarModule.inner_self_nonneg |>.trans_eq h
    · refine inner_self.mp <| le_antisymm ?_ inner_self_nonneg
      exact le_add_of_nonneg_left CStarModule.inner_self_nonneg |>.trans_eq h
  inner_op_smul_right := by simp [add_mul]
  inner_smul_right_complex := by simp [smul_add]
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by with_reducible_and_instances rfl

lemma prod_inner (x y : C⋆ᵐᵒᵈ (E × F)) : ⟪x, y⟫_A = ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A := rfl

lemma max_le_prod_norm (x : C⋆ᵐᵒᵈ (E × F)) : max ‖x.1‖ ‖x.2‖ ≤ ‖x‖ := by
  rw [prod_norm]
  simp only [equiv_fst, norm_eq_sqrt_norm_inner_self (E := E),
    norm_eq_sqrt_norm_inner_self (E := F), equiv_snd, max_le_iff, norm_nonneg,
    Real.sqrt_le_sqrt_iff]
  constructor
  all_goals
    apply CStarAlgebra.norm_le_norm_of_nonneg_of_le
    all_goals
      aesop (add safe apply CStarModule.inner_self_nonneg)

lemma norm_equiv_le_norm_prod (x : C⋆ᵐᵒᵈ (E × F)) : ‖equiv (E × F) x‖ ≤ ‖x‖ :=
  max_le_prod_norm x

section Aux

attribute [-instance] WithCStarModule.instUniformSpace WithCStarModule.instBornology

attribute [local instance] CStarModule.normedAddCommGroup

open Filter Uniformity Bornology

private lemma antilipschitzWith_two_equiv_prod_aux : AntilipschitzWith 2 (equiv (E × F)) :=
  AddMonoidHomClass.antilipschitz_of_bound (linearEquiv ℂ (E × F)) fun x ↦ by
    apply prod_norm_le_norm_add x |>.trans
    simp only [NNReal.coe_ofNat, linearEquiv_apply, two_mul]
    gcongr
    · exact norm_fst_le x
    · exact norm_snd_le x

private lemma lipschitzWith_one_equiv_prod_aux : LipschitzWith 1 (equiv (E × F)) :=
  AddMonoidHomClass.lipschitz_of_bound_nnnorm (linearEquiv ℂ (E × F)) 1 <| by
    simpa using norm_equiv_le_norm_prod

private lemma uniformity_prod_eq_aux :
    𝓤[(inferInstance : UniformSpace (E × F)).comap <| equiv _] = 𝓤 (C⋆ᵐᵒᵈ (E × F)) :=
  uniformity_eq_of_bilipschitz antilipschitzWith_two_equiv_prod_aux lipschitzWith_one_equiv_prod_aux

private lemma isBounded_prod_iff_aux (s : Set (C⋆ᵐᵒᵈ (E × F))) :
    @IsBounded _ (induced <| equiv (E × F)) s ↔ IsBounded s :=
  isBounded_iff_of_bilipschitz antilipschitzWith_two_equiv_prod_aux
    lipschitzWith_one_equiv_prod_aux s

end Aux

noncomputable instance : NormedAddCommGroup (C⋆ᵐᵒᵈ (E × F)) :=
  .ofCoreReplaceAll normedSpaceCore uniformity_prod_eq_aux isBounded_prod_iff_aux

instance : NormedSpace ℂ (C⋆ᵐᵒᵈ (E × F)) := .ofCore normedSpaceCore

end Prod

/-! ## Pi-types of C⋆-modules -/

section Pi

open scoped InnerProductSpace

variable {ι : Type*} {E : ι → Type*} [Fintype ι]

variable [∀ i, NormedAddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, SMul Aᵐᵒᵖ (E i)]

variable [∀ i, CStarModule A (E i)]

noncomputable instance : Norm (C⋆ᵐᵒᵈ (Π i, E i)) where
  norm x := √‖∑ i, ⟪x i, x i⟫_A‖

lemma pi_norm (x : C⋆ᵐᵒᵈ (Π i, E i)) : ‖x‖ = √‖∑ i, ⟪x i, x i⟫_A‖ := by
  with_reducible_and_instances rfl

lemma pi_norm_sq (x : C⋆ᵐᵒᵈ (Π i, E i)) : ‖x‖ ^ 2 = ‖∑ i, ⟪x i, x i⟫_A‖ := by
  simp [pi_norm]

open Finset in

lemma pi_norm_le_sum_norm (x : C⋆ᵐᵒᵈ (Π i, E i)) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  calc ‖x‖ ^ 2 ≤ ∑ i, ‖⟪x i, x i⟫_A‖ := pi_norm_sq x ▸ norm_sum_le _ _
    _ = ∑ i, ‖x i‖ ^ 2 := by simp only [norm_sq_eq]
    _ ≤ (∑ i, ‖x i‖) ^ 2 := sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)

variable [StarOrderedRing A]

open Finset in

noncomputable instance : CStarModule A (C⋆ᵐᵒᵈ (Π i, E i)) where
  inner x y := ∑ i, inner (x i) (y i)
  inner_add_right {x y z} := by simp [inner_sum_right, sum_add_distrib]
  inner_self_nonneg := sum_nonneg <| fun _ _ ↦ CStarModule.inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h, CStarModule.inner_zero_left]⟩
    ext i
    refine inner_self.mp <| le_antisymm (le_of_le_of_eq ?_ h) inner_self_nonneg
    exact single_le_sum (fun i _ ↦ CStarModule.inner_self_nonneg (x := x i)) (mem_univ _)
  inner_op_smul_right := by simp [sum_mul]
  inner_smul_right_complex := by simp [smul_sum]
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by with_reducible_and_instances rfl

lemma pi_inner (x y : C⋆ᵐᵒᵈ (Π i, E i)) : ⟪x, y⟫_A = ∑ i, ⟪x i, y i⟫_A := rfl

@[simp]
lemma inner_single_left [DecidableEq ι] (x : C⋆ᵐᵒᵈ (Π i, E i)) {i : ι} (y : E i) :
    ⟪equiv _ |>.symm <| Pi.single i y, x⟫_A = ⟪y, x i⟫_A := by
  simp only [pi_inner, equiv_symm_pi_apply]
  rw [Finset.sum_eq_single i]
  all_goals simp_all

@[simp]
lemma inner_single_right [DecidableEq ι] (x : C⋆ᵐᵒᵈ (Π i, E i)) {i : ι} (y : E i) :
    ⟪x, equiv _ |>.symm <| Pi.single i y⟫_A = ⟪x i, y⟫_A := by
  simp only [pi_inner, equiv_symm_pi_apply]
  rw [Finset.sum_eq_single i]
  all_goals simp_all

@[simp]
lemma norm_single [DecidableEq ι] (i : ι) (y : E i) :
    ‖equiv _ |>.symm <| Pi.single i y‖ = ‖y‖ := by
  let _ : NormedAddCommGroup (C⋆ᵐᵒᵈ (Π i, E i)) := normedAddCommGroup
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  simp [norm_sq_eq]

lemma norm_apply_le_norm (x : C⋆ᵐᵒᵈ (Π i, E i)) (i : ι) : ‖x i‖ ≤ ‖x‖ := by
  let _ : NormedAddCommGroup (C⋆ᵐᵒᵈ (Π i, E i)) := normedAddCommGroup
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [pi_norm_sq, norm_sq_eq]
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le inner_self_nonneg ?_
  exact Finset.single_le_sum (fun j _ ↦ inner_self_nonneg (x := x j)) (Finset.mem_univ i)

open Finset in

lemma norm_equiv_le_norm_pi (x : C⋆ᵐᵒᵈ (Π i, E i)) : ‖equiv _ x‖ ≤ ‖x‖ := by
  let _ : NormedAddCommGroup (C⋆ᵐᵒᵈ (Π i, E i)) := normedAddCommGroup
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  simpa using norm_apply_le_norm x

section Aux

attribute [-instance] WithCStarModule.instUniformSpace WithCStarModule.instBornology

attribute [local instance] CStarModule.normedAddCommGroup

open Uniformity Bornology

private lemma antilipschitzWith_card_equiv_pi_aux :
    AntilipschitzWith (Fintype.card ι) (equiv (Π i, E i)) :=
  AddMonoidHomClass.antilipschitz_of_bound (linearEquiv ℂ (Π i, E i)) fun x ↦ by
    simp only [NNReal.coe_natCast, linearEquiv_apply]
    calc ‖x‖ ≤ ∑ i, ‖x i‖ := pi_norm_le_sum_norm x
      _ ≤ ∑ _, ‖⇑x‖ := Finset.sum_le_sum fun _ _ ↦ norm_le_pi_norm ..
      _ ≤ Fintype.card ι * ‖⇑x‖ := by simp

private lemma lipschitzWith_one_equiv_pi_aux : LipschitzWith 1 (equiv (Π i, E i)) :=
  AddMonoidHomClass.lipschitz_of_bound_nnnorm (linearEquiv ℂ (Π i, E i)) 1 <| by
    simpa using norm_equiv_le_norm_pi

private lemma uniformity_pi_eq_aux :
    𝓤[(inferInstance : UniformSpace (Π i, E i)).comap <| equiv _] = 𝓤 (C⋆ᵐᵒᵈ (Π i, E i)) :=
  uniformity_eq_of_bilipschitz antilipschitzWith_card_equiv_pi_aux lipschitzWith_one_equiv_pi_aux

private lemma isBounded_pi_iff_aux (s : Set (C⋆ᵐᵒᵈ (Π i, E i))) :
    @IsBounded _ (induced <| equiv (Π i, E i)) s ↔ IsBounded s :=
  isBounded_iff_of_bilipschitz antilipschitzWith_card_equiv_pi_aux lipschitzWith_one_equiv_pi_aux s

end Aux

noncomputable instance : NormedAddCommGroup (C⋆ᵐᵒᵈ (Π i, E i)) :=
  .ofCoreReplaceAll normedSpaceCore uniformity_pi_eq_aux isBounded_pi_iff_aux

instance : NormedSpace ℂ (C⋆ᵐᵒᵈ (Π i, E i)) := .ofCore normedSpaceCore

end Pi

/-! ## Inner product spaces as C⋆-modules -/

section InnerProductSpace

open ComplexOrder

variable {E : Type*}

variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable [instSMulOp : SMul ℂᵐᵒᵖ E] [instCentral : IsCentralScalar ℂ E]

open scoped InnerProductSpace in

instance instCStarModuleComplex : CStarModule ℂ E where
  inner x y := ⟪x, y⟫_ℂ
  inner_add_right := _root_.inner_add_right ..
  inner_self_nonneg {x} := by
    simp only
    rw [← inner_self_ofReal_re, RCLike.ofReal_nonneg]
    exact inner_self_nonneg
  inner_self := inner_self_eq_zero
  inner_op_smul_right := by simp [inner_smul_right, mul_comm]
  inner_smul_right_complex := inner_smul_right ..
  star_inner _ _ := inner_conj_symm ..
  norm_eq_sqrt_norm_inner_self {x} := by
    simpa only [← inner_self_re_eq_norm] using norm_eq_sqrt_inner x

example : instCStarModule (A := ℂ) = instCStarModuleComplex := by with_reducible_and_instances rfl

example : (toInner : Inner ℂ ℂ) = WithCStarModule.instCStarModule.toInner := rfl

end InnerProductSpace

end WithCStarModule
