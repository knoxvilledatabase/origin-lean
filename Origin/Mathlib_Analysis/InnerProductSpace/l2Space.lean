/-
Extracted from Analysis/InnerProductSpace/l2Space.lean
Genuine: 7 of 10 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Hilbert sum of a family of inner product spaces

Given a family `(G : ι → Type*) [Π i, InnerProductSpace 𝕜 (G i)]` of inner product spaces, this
file equips `lp G 2` with an inner product space structure, where `lp G 2` consists of those
dependent functions `f : Π i, G i` for which `∑' i, ‖f i‖ ^ 2`, the sum of the norms-squared, is
summable.  This construction is sometimes called the *Hilbert sum* of the family `G`.  By choosing
`G` to be `ι → 𝕜`, the Hilbert space `ℓ²(ι, 𝕜)` may be seen as a special case of this construction.

We also define a *predicate* `IsHilbertSum 𝕜 G V`, where `V : Π i, G i →ₗᵢ[𝕜] E`, expressing that
`V` is an `OrthogonalFamily` and that the associated map `lp G 2 →ₗᵢ[𝕜] E` is surjective.

## Main definitions

* `OrthogonalFamily.linearIsometry`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E` with
  mutually-orthogonal images, there is an induced isometric embedding of the Hilbert sum of `G`
  into `E`.

* `IsHilbertSum`: Given a Hilbert space `E`, a family `G` of inner product
  spaces and a family `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E`,
  `IsHilbertSum 𝕜 G V` means that `V` is an `OrthogonalFamily` and that the above
  linear isometry is surjective.

* `IsHilbertSum.linearIsometryEquiv`: If a Hilbert space `E` is a Hilbert sum of the
  inner product spaces `G i` with respect to the family `V : Π i, G i →ₗᵢ[𝕜] E`, then the
  corresponding `OrthogonalFamily.linearIsometry` can be upgraded to a `LinearIsometryEquiv`.

* `HilbertBasis`: We define a *Hilbert basis* of a Hilbert space `E` to be a structure whose single
  field `HilbertBasis.repr` is an isometric isomorphism of `E` with `ℓ²(ι, 𝕜)` (i.e., the Hilbert
  sum of `ι` copies of `𝕜`).  This parallels the definition of `Basis`, in `LinearAlgebra.Basis`,
  as an isomorphism of an `R`-module with `ι →₀ R`.

* `HilbertBasis.instCoeFun`: More conventionally a Hilbert basis is thought of as a family
  `ι → E` of vectors in `E` satisfying certain properties (orthonormality, completeness).  We obtain
  this interpretation of a Hilbert basis `b` by defining `⇑b`, of type `ι → E`, to be the image
  under `b.repr` of `lp.single 2 i (1:𝕜)`.  This parallels the definition `Basis.coeFun` in
  `LinearAlgebra.Basis`.

* `HilbertBasis.mk`: Make a Hilbert basis of `E` from an orthonormal family `v : ι → E` of vectors
  in `E` whose span is dense.  This parallels the definition `Basis.mk` in `LinearAlgebra.Basis`.

* `HilbertBasis.mkOfOrthogonalEqBot`: Make a Hilbert basis of `E` from an orthonormal family
  `v : ι → E` of vectors in `E` whose span has trivial orthogonal complement.

## Main results

* `lp.instInnerProductSpace`: Construction of the inner product space instance on the Hilbert sum
  `lp G 2`. Note that from the file `Mathlib/Analysis/Normed/Lp/lpSpace.lean`, the space `lp G 2`
  already held a normed space instance (`lp.normedSpace`), and if each `G i` is a Hilbert space
  (i.e., complete), then `lp G 2` was already known to be complete (`lp.completeSpace`). So the work
  here is to define the inner product and show it is compatible.

* `OrthogonalFamily.range_linearIsometry`: Given a family `G` of inner product spaces and a family
  `V : Π i, G i →ₗᵢ[𝕜] E` of isometric embeddings of the `G i` into `E` with mutually-orthogonal
  images, the image of the embedding `OrthogonalFamily.linearIsometry` of the Hilbert sum of `G`
  into `E` is the closure of the span of the images of the `G i`.

* `HilbertBasis.repr_apply_apply`: Given a Hilbert basis `b` of `E`, the entry `b.repr x i` of
  `x`'s representation in `ℓ²(ι, 𝕜)` is the inner product `⟪b i, x⟫`.

* `HilbertBasis.hasSum_repr`: Given a Hilbert basis `b` of `E`, a vector `x` in `E` can be
  expressed as the "infinite linear combination" `∑' i, b.repr x i • b i` of the basis vectors
  `b i`, with coefficients given by the entries `b.repr x i` of `x`'s representation in `ℓ²(ι, 𝕜)`.

* `exists_hilbertBasis`: A Hilbert space admits a Hilbert basis.

## Keywords

Hilbert space, Hilbert sum, l2, Hilbert basis, unitary equivalence, isometric isomorphism
-/

open RCLike Submodule Filter

open scoped NNReal ENNReal ComplexConjugate Topology lp

noncomputable section

variable {ι 𝕜 : Type*} [RCLike 𝕜] {E : Type*}

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Inner product space structure on `lp G 2` -/

namespace lp

theorem summable_inner (f g : lp G 2) : Summable fun i => ⟪f i, g i⟫ := by
  -- Apply the Direct Comparison Test, comparing with ∑' i, ‖f i‖ * ‖g i‖ (summable by Hölder)
  refine .of_norm_bounded (lp.summable_mul ?_ f g) ?_
  · rw [Real.holderConjugate_iff]; norm_num
  intro i
  -- Then apply Cauchy-Schwarz pointwise
  exact norm_inner_le_norm (𝕜 := 𝕜) _ _

-- INSTANCE (free from Core): instInnerProductSpace

theorem hasSum_inner (f g : lp G 2) : HasSum (fun i => ⟪f i, g i⟫) ⟪f, g⟫ :=
  (summable_inner f g).hasSum

theorem inner_single_left [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2) :
    ⟪lp.single 2 i a, f⟫ = ⟪a, f i⟫ := by
  refine (hasSum_inner (lp.single 2 i a) f).unique ?_
  simp_rw [lp.coeFn_single]
  convert hasSum_ite_eq i ⟪a, f i⟫ using 1
  ext j
  split_ifs with h
  · subst h; rw [Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

theorem inner_single_right [DecidableEq ι] (i : ι) (a : G i) (f : lp G 2) :
    ⟪f, lp.single 2 i a⟫ = ⟪f i, a⟫ := by
  simpa [inner_conj_symm] using congr_arg conj (inner_single_left (𝕜 := 𝕜) i a f)

end lp

/-! ### Identification of a general Hilbert space `E` with a Hilbert sum -/

namespace OrthogonalFamily

variable [CompleteSpace E] {V : ∀ i, G i →ₗᵢ[𝕜] E} (hV : OrthogonalFamily 𝕜 G V)

include hV

protected theorem summable_of_lp (f : lp G 2) :
    Summable fun i => V i (f i) := by
  rw [hV.summable_iff_norm_sq_summable]
  convert (lp.memℓp f).summable _
  · norm_cast
  · norm_num

protected def linearIsometry (hV : OrthogonalFamily 𝕜 G V) : lp G 2 →ₗᵢ[𝕜] E where
  toFun f := ∑' i, V i (f i)
  map_add' f g := by
    simp only [(hV.summable_of_lp f).tsum_add (hV.summable_of_lp g), lp.coeFn_add, Pi.add_apply,
      LinearIsometry.map_add]
  map_smul' c f := by
    simpa only [LinearIsometry.map_smul, Pi.smul_apply, lp.coeFn_smul] using
      (hV.summable_of_lp f).tsum_const_smul c
  norm_map' f := by
    classical
      -- needed for lattice instance on `Finset ι`, for `Filter.atTop_neBot`
      have H : 0 < (2 : ℝ≥0∞).toReal := by simp
      suffices ‖∑' i : ι, V i (f i)‖ ^ (2 : ℝ≥0∞).toReal = ‖f‖ ^ (2 : ℝ≥0∞).toReal by
        exact Real.rpow_left_injOn H.ne' (norm_nonneg _) (norm_nonneg _) this
      refine tendsto_nhds_unique ?_ (lp.hasSum_norm H f)
      convert (hV.summable_of_lp f).hasSum.norm.rpow_const (Or.inr H.le) using 1
      ext s
      exact mod_cast (hV.norm_sum f s).symm

protected theorem hasSum_linearIsometry (f : lp G 2) :
    HasSum (fun i => V i (f i)) (hV.linearIsometry f) :=
  (hV.summable_of_lp f).hasSum
