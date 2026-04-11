/-
Released under MIT license.
-/
import Val.RingTheory
import Val.Category
import Val.Analysis

/-!
# Val α: Geometry — Algebraic Geometry + Differential Geometry

Two domains consolidated. Both stay in contents throughout.
Algebraic Geometry: Spec, Zariski topology, schemes, stalks, residue fields.
Differential Geometry: tangent vectors, derivatives, smooth maps, charts, forms.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- ALGEBRAIC GEOMETRY
-- ============================================================================

-- ============================================================================
-- Spec: Prime Ideals as Points
-- ============================================================================

/-- A point of Spec: a prime ideal predicate on α with the prime property. -/
structure SpecPoint (α : Type u) where
  ideal : α → Prop
  prime : ∀ (mulF : α → α → α) (a b : α), ideal (mulF a b) → ideal a ∨ ideal b

/-- Origin is outside every Spec point. -/
theorem spec_point_excludes_origin (p : SpecPoint α) :
    ¬ inIdeal p.ideal (origin : Val α) := id

/-- Container is outside every Spec point. -/
theorem spec_point_excludes_container (p : SpecPoint α) (c : α) :
    ¬ inIdeal p.ideal (container c : Val α) := id

-- ============================================================================
-- Structure Sheaf: Sections Are Contents-Valued
-- ============================================================================


-- ============================================================================
-- Affine Schemes
-- ============================================================================

/-- Ring operations on global sections stay in contents. -/
theorem global_sections_mul (mulF : α → α → α) (r s : α) :
    mul mulF (contents r) (contents s) = contents (mulF r s) := rfl

theorem global_sections_add (addF : α → α → α) (r s : α) :
    add addF (contents r) (contents s) = contents (addF r s) := rfl

-- ============================================================================
-- Scheme Morphisms
-- ============================================================================

/-- Scheme morphisms send contents to contents via valMap. -/
theorem scheme_morphism_contents (f : α → α) (a : α) :
    valMap f (contents a) = contents (f a) := rfl

/-- Composition of scheme morphisms. -/
theorem scheme_morphism_comp (f g : α → α) :
    valMap (g ∘ f) = valMap g ∘ valMap f := valMap_comp f g

-- ============================================================================
-- Local Rings: Localization at Primes
-- ============================================================================

/-- Local ring element a/s: always contents. No s ≠ 0 sort-level hypothesis. -/
theorem local_ring_element (mulF : α → α → α) (invF : α → α)
    (P : α → Prop) (a s : α) (_ : ¬ P s) :
    ∃ r, mul mulF (contents a) (inv invF (contents s)) = contents r :=
  ⟨mulF a (invF s), rfl⟩

/-- Addition of fractions stays in contents. -/
theorem local_ring_add (mulF addF : α → α → α) (invF : α → α) (a b s t : α) :
    ∃ r, add addF (mul mulF (contents a) (inv invF (contents s)))
                  (mul mulF (contents b) (inv invF (contents t))) = contents r :=
  ⟨addF (mulF a (invF s)) (mulF b (invF t)), rfl⟩

-- ============================================================================
-- Stalks
-- ============================================================================

/-- Stalk operations: multiplication stays in contents. -/
theorem stalk_mul (mulF : α → α → α) (a b : α) :
    mul mulF (contents a) (contents b) = contents (mulF a b) := rfl

-- ============================================================================
-- Residue Field
-- ============================================================================

/-- Residue field element: quotient map sends contents to contents. -/
theorem residue_field_contents (proj : α → α) (a : α) :
    quotientMap proj (contents a) = contents (proj a) := rfl

-- ============================================================================
-- Separatedness
-- ============================================================================

/-- Distinct contents values are distinguishable. -/
theorem separated_diagonal (a b : α) (h : a ≠ b) :
    (contents a : Val α) ≠ contents b :=
  fun heq => h (contents_injective a b heq)

-- ============================================================================
-- DIFFERENTIAL GEOMETRY
-- ============================================================================

-- ============================================================================
-- Tangent Vectors
-- ============================================================================

/-- Addition of tangent vectors stays in contents. -/
theorem tangent_add (addF : α → α → α) (v w : α) :
    add addF (contents v) (contents w) = contents (addF v w) := rfl

/-- Scalar multiplication of tangent vectors stays in contents. -/
theorem tangent_scalar_mul (mulF : α → α → α) (c v : α) :
    mul mulF (contents c) (contents v) = contents (mulF c v) := rfl

-- ============================================================================
-- Derivatives
-- ============================================================================

/-- The quotient rule: (f/g)'. No g(a) ≠ 0 sort-level hypothesis. -/
theorem quotient_rule_contents (mulF addF : α → α → α) (invF negF : α → α)
    (f g f' g' : α → α) (a : α) :
    ∃ r, mul mulF
             (add addF (mul mulF (contents (f' a)) (contents (g a)))
                       (mul mulF (contents (negF (f a))) (contents (g' a))))
             (inv invF (mul mulF (contents (g a)) (contents (g a)))) = contents r :=
  ⟨mulF (addF (mulF (f' a) (g a)) (mulF (negF (f a)) (g' a)))
        (invF (mulF (g a) (g a))), rfl⟩

-- ============================================================================
-- Smooth Maps
-- ============================================================================

/-- Smooth maps preserve sort via valMap. -/
theorem smooth_map_contents (f : α → α) (a : α) :
    valMap f (contents a) = contents (f a) := rfl

/-- Composition of smooth maps preserves sort. -/
theorem smooth_comp (f g : α → α) :
    valMap (g ∘ f) = valMap g ∘ valMap f := valMap_comp f g

-- ============================================================================
-- Manifold Charts
-- ============================================================================

/-- A chart: homeomorphism between a manifold patch and α. -/
structure Chart (α : Type u) where
  toFun : α → α
  invFun : α → α
  left_inv : ∀ a, invFun (toFun a) = a

/-- Chart round-trip: φ⁻¹ ∘ φ = id on contents. -/
theorem chart_roundtrip (φ : Chart α) (a : α) :
    valMap φ.invFun (valMap φ.toFun (contents a)) = contents a := by
  simp [φ.left_inv]

/-- Transition maps between charts preserve contents. -/
theorem transition_map_contents (φ ψ : Chart α) (a : α) :
    valMap (ψ.toFun ∘ φ.invFun) (contents a) =
    contents (ψ.toFun (φ.invFun a)) := rfl

-- ============================================================================
-- Vector Fields
-- ============================================================================

/-- Addition of vector fields: pointwise, stays in contents. -/
theorem vectorField_add (addF : α → α → α) (X Y : α → α) (p : α) :
    add addF (contents (X p)) (contents (Y p)) = contents (addF (X p) (Y p)) := rfl

/-- Lie bracket: [X, Y](f) = X(Y(f)) - Y(X(f)). Both terms contents. -/
theorem lie_bracket_contents (addF : α → α → α) (negF : α → α) (XYf YXf : α) :
    add addF (contents XYf) (contents (negF YXf)) = contents (addF XYf (negF YXf)) := rfl

-- ============================================================================
-- Connections
-- ============================================================================


-- ============================================================================
-- Differential Forms
-- ============================================================================

/-- Wedge product of forms: contents × contents = contents. -/
theorem wedge_product_contents (mulF : α → α → α) (ω₁ ω₂ : α) :
    mul mulF (contents ω₁) (contents ω₂) = contents (mulF ω₁ ω₂) := rfl

/-- Exterior derivative: d(ω) is contents when ω is contents. -/
theorem exterior_derivative_contents (dω : α → α) (a : α) :
    valMap dω (contents a) = contents (dω a) := rfl

/-- Stokes' theorem: ∫_M dω = ∫_∂M ω. Both sides contents. -/
theorem stokes_contents (lhs rhs : α) (h : lhs = rhs) :
    (contents lhs : Val α) = contents rhs := by rw [h]

-- ============================================================================
-- Riemannian Metric
-- ============================================================================

end Val
