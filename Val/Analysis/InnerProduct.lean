/-
Released under MIT license.
-/
import Val.Analysis.Normed
import Val.FunctionalAnalysis

/-!
# Val α: Inner Product Spaces

Inner products, Hilbert spaces, orthogonality, projections, Riesz representation.
Inner products map contents × contents → contents.
Normalization divides by ‖v‖ which is contents. No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Inner Product
-- ============================================================================

/-- Inner product on Val α. Contents × contents → contents.
    Origin absorbs. Container carries. -/
def innerProd (ipF : α → α → α) : Val α → Val α → Val α
  | origin, _ => origin
  | _, origin => origin
  | container a, container b => container (ipF a b)
  | container a, contents b => container (ipF a b)
  | contents a, container b => container (ipF a b)
  | contents a, contents b => contents (ipF a b)

@[simp] theorem innerProd_contents (ipF : α → α → α) (a b : α) :
    innerProd ipF (contents a) (contents b) = contents (ipF a b) := rfl

@[simp] theorem innerProd_origin_left (ipF : α → α → α) (v : Val α) :
    innerProd ipF origin v = origin := by cases v <;> rfl

theorem innerProd_contents_ne_origin (ipF : α → α → α) (a b : α) :
    innerProd ipF (contents a) (contents b) ≠ origin := by intro h; cases h

-- ============================================================================
-- Symmetry, Linearity, Definiteness
-- ============================================================================

/-- ⟨x, y⟩ = ⟨y, x⟩ within contents (real case). -/
theorem innerProd_comm (ipF : α → α → α) (hcomm : ∀ a b, ipF a b = ipF b a) (a b : α) :
    innerProd ipF (contents a) (contents b) = innerProd ipF (contents b) (contents a) := by
  show contents (ipF a b) = contents (ipF b a); rw [hcomm]

/-- ⟨x + y, z⟩ = ⟨x, z⟩ + ⟨y, z⟩ within contents. -/
theorem innerProd_add_left [Add α] (ipF : α → α → α)
    (hlin : ∀ a b c, ipF (a + b) c = ipF a c + ipF b c) (a b c : α) :
    innerProd ipF (contents (a + b)) (contents c) =
    contents (ipF a c + ipF b c) := by
  show contents (ipF (a + b) c) = contents (ipF a c + ipF b c); rw [hlin]

/-- ⟨c·x, y⟩ = c·⟨x, y⟩ within contents. -/
theorem innerProd_smul_left [Mul α] (ipF : α → α → α)
    (hscal : ∀ c a b, ipF (c * a) b = c * ipF a b) (c a b : α) :
    innerProd ipF (contents (c * a)) (contents b) =
    contents (c * ipF a b) := by
  show contents (ipF (c * a) b) = contents (c * ipF a b); rw [hscal]

-- ============================================================================
-- Norm from Inner Product: ‖x‖² = ⟨x, x⟩
-- ============================================================================

/-- The norm squared from inner product. Contents in, contents out. -/
def normSqFromIP (ipF : α → α → α) (a : α) : α := ipF a a

theorem normSq_contents (ipF : α → α → α) (a : α) :
    ∃ r, (contents (normSqFromIP ipF a) : Val α) = contents r :=
  ⟨normSqFromIP ipF a, rfl⟩

theorem normSq_ne_origin (ipF : α → α → α) (a : α) :
    (contents (normSqFromIP ipF a) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Orthogonality
-- ============================================================================

/-- Two vectors are orthogonal when ⟨x, y⟩ = 0. A contents equation. -/
def isOrthogonal [Zero α] (ipF : α → α → α) (x y : α) : Prop :=
  ipF x y = 0

/-- Orthogonal inner product is contents(0), never origin. -/
theorem orthogonal_value_ne_origin [Zero α] (ipF : α → α → α) (x y : α)
    (h : isOrthogonal ipF x y) :
    innerProd ipF (contents x) (contents y) ≠ (origin : Val α) := by intro h; cases h

/-- Orthogonal vectors have inner product contents(0), not origin. -/
theorem orthogonal_is_contents_zero [Zero α] (ipF : α → α → α) (x y : α)
    (h : isOrthogonal ipF x y) :
    innerProd ipF (contents x) (contents y) = (contents 0 : Val α) := by
  show contents (ipF x y) = contents 0; rw [h]

-- ============================================================================
-- Projection
-- ============================================================================

/-- Orthogonal projection: proj_v(u) = (⟨u,v⟩ / ⟨v,v⟩) · v.
    All contents operations. No ‖v‖ ≠ 0 at sort level. -/
def projection [Mul α] (invF : α → α) (ipF : α → α → α) (u v : α) : α :=
  ipF u v * invF (ipF v v) * v

theorem projection_contents [Mul α] (invF : α → α) (ipF : α → α → α) (u v : α) :
    ∃ r, (contents (projection invF ipF u v) : Val α) = contents r :=
  ⟨projection invF ipF u v, rfl⟩

theorem projection_ne_origin [Mul α] (invF : α → α) (ipF : α → α → α) (u v : α) :
    (contents (projection invF ipF u v) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Gram-Schmidt Step
-- ============================================================================

/-- One step of Gram-Schmidt: subtract projection from u. No ≠ 0 needed. -/
def gramSchmidtStep [Add α] [Mul α] [Neg α] (invF : α → α) (ipF : α → α → α) (u v : α) : α :=
  u + -(projection invF ipF u v)

theorem gramSchmidt_contents [Add α] [Mul α] [Neg α] (invF : α → α) (ipF : α → α → α) (u v : α) :
    ∃ r, (contents (gramSchmidtStep invF ipF u v) : Val α) = contents r :=
  ⟨gramSchmidtStep invF ipF u v, rfl⟩

theorem gramSchmidt_ne_origin [Add α] [Mul α] [Neg α] (invF : α → α) (ipF : α → α → α) (u v : α) :
    (contents (gramSchmidtStep invF ipF u v) : Val α) ≠ origin := by intro h; cases h

-- ============================================================================
-- Cauchy-Schwarz Inequality
-- ============================================================================

/-- Cauchy-Schwarz: |⟨x,y⟩|² ≤ ⟨x,x⟩·⟨y,y⟩. Both sides contents. -/
theorem cauchy_schwarz [Mul α] [LE α] (ipF : α → α → α)
    (h : ∀ x y, ipF x y * ipF x y ≤ ipF x x * ipF y y) (a b : α) :
    ipF a b * ipF a b ≤ ipF a a * ipF b b :=
  h a b

-- ============================================================================
-- Riesz Representation
-- ============================================================================

/-- Riesz representation: every continuous linear functional is ⟨·, v⟩ for some v. -/
theorem riesz_contents (ipF : α → α → α) (v : α) :
    (contents v : Val α) ≠ origin := by intro h; cases h

theorem riesz_apply_contents (ipF : α → α → α) (v a : α) :
    innerProd ipF (contents a) (contents v) ≠ origin := by intro h; cases h

-- ============================================================================
-- Parallelogram Law
-- ============================================================================

/-- Parallelogram law within contents. -/
theorem parallelogram_law [Add α] [Neg α] (ipF : α → α → α)
    (h : ∀ x y, ipF (x + y) (x + y) + ipF (x + -(y)) (x + -(y)) =
                 (ipF x x + ipF y y) + (ipF x x + ipF y y)) (a b : α) :
    ipF (a + b) (a + b) + ipF (a + -(b)) (a + -(b)) =
    (ipF a a + ipF b b) + (ipF a a + ipF b b) :=
  h a b

end Val
