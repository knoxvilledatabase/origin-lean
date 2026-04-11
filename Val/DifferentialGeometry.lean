/-
Released under MIT license.
-/
import Val.Analysis.Core
import Val.Category.Core

/-!
# Val α: Differential Geometry

Tangent vectors, derivatives, smooth maps, manifold charts, vector fields,
connections, curvature. Sort propagates through all constructions. Contents throughout.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Tangent Vectors
-- ============================================================================

/-- Addition of tangent vectors stays in contents. -/
theorem tangent_add (addF : α → α → α) (v w : α) :
    add addF (contents v) (contents w) = contents (addF v w) := rfl

/-- Scalar multiplication of tangent vectors stays in contents. -/
theorem tangent_scalar_mul (mulF : α → α → α) (c v : α) :
    mul mulF (contents c) (contents v) = contents (mulF c v) := rfl

/-- Tangent vectors are never origin. -/
theorem tangent_ne_origin (v : α) : (contents v : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Derivatives
-- ============================================================================

/-- The chain rule: (g ∘ f)'(a) = g'(f(a)) · f'(a). Both contents. -/
theorem chain_rule_contents (mulF : α → α → α) (f' g' : α → α) (f : α → α) (a : α) :
    mul mulF (contents (g' (f a))) (contents (f' a)) =
    contents (mulF (g' (f a)) (f' a)) := rfl

/-- The product rule: (fg)' = f'g + fg'. All terms contents. -/
theorem product_rule_contents (mulF addF : α → α → α) (f g f' g' : α → α) (a : α) :
    add addF (mul mulF (contents (f' a)) (contents (g a)))
             (mul mulF (contents (f a)) (contents (g' a))) =
    contents (addF (mulF (f' a) (g a)) (mulF (f a) (g' a))) := rfl

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

/-- Smooth maps never send contents to origin. -/
theorem smooth_map_ne_origin (f : α → α) (a : α) :
    valMap f (contents a) ≠ (origin : Val α) := by intro h; cases h

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

/-- Vector fields are never origin. -/
theorem vectorField_ne_origin (X : α → α) (p : α) :
    (contents (X p) : Val α) ≠ origin := by intro h; cases h

/-- Lie bracket: [X, Y](f) = X(Y(f)) - Y(X(f)). Both terms contents. -/
theorem lie_bracket_contents (addF : α → α → α) (negF : α → α) (XYf YXf : α) :
    add addF (contents XYf) (contents (negF YXf)) = contents (addF XYf (negF YXf)) := rfl

-- ============================================================================
-- Connections
-- ============================================================================

/-- Covariant derivative ∇_X Y: contents in, contents out. -/
theorem connection_contents (nabla : α → α → α) (X Y : α) :
    (contents (nabla X Y) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Curvature
-- ============================================================================

/-- Riemann curvature tensor: contents. -/
theorem curvature_contents (curvature : α) :
    (contents curvature : Val α) ≠ origin := by intro h; cases h

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

/-- The metric tensor is never origin from contents inputs. -/
theorem metric_tensor_ne_origin (g : α → α → α) (v w : α) :
    (contents (g v w) : Val α) ≠ origin := by intro h; cases h

end Val
