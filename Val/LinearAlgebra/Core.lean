/-
Released under MIT license.
-/
import Val.Algebra

/-!
# Linear Algebra over Val α: The 2×2 Case

The key result: `det A ≠ 0` dissolves. If entries are contents, det is contents —
structurally not origin. No proof obligation at each call site.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- 2×2 Matrix
-- ============================================================================

/-- A 2×2 matrix of Val α entries. -/
structure Mat2 (β : Type u) where
  e₁₁ : β
  e₁₂ : β
  e₂₁ : β
  e₂₂ : β

-- ============================================================================
-- Determinant
-- ============================================================================

/-- det([[a,b],[c,d]]) = a·d - b·c via add subF (mul mulF ...) -/
def det2 (mulF subF : α → α → α) (m : Mat2 (Val α)) : Val α :=
  add subF (mul mulF m.e₁₁ m.e₂₂) (mul mulF m.e₁₂ m.e₂₁)

/-- Det of a contents matrix is contents. -/
theorem det2_contents (mulF subF : α → α → α) (a b c d : α) :
    det2 mulF subF ⟨contents a, contents b, contents c, contents d⟩ =
    contents (subF (mulF a d) (mulF b c)) := by rfl

/-- Det of a contents matrix is never origin. THIS IS THE THEOREM.
    `det A ≠ 0` dissolves — the sort carries the invariant. -/
theorem det2_contents_ne_origin (mulF subF : α → α → α) (a b c d : α) :
    det2 mulF subF ⟨contents a, contents b, contents c, contents d⟩ ≠ origin := by
  simp [det2]

theorem det2_contents_ne_container (mulF subF : α → α → α) (a b c d e : α) :
    det2 mulF subF ⟨contents a, contents b, contents c, contents d⟩ ≠ container e := by
  simp [det2]

-- ============================================================================
-- Origin Propagation
-- ============================================================================

theorem det2_origin_e11 (mulF subF : α → α → α) (e₁₂ e₂₁ e₂₂ : Val α) :
    det2 mulF subF ⟨origin, e₁₂, e₂₁, e₂₂⟩ = origin := by simp [det2]

theorem det2_origin_e12 (mulF subF : α → α → α) (e₁₁ e₂₁ e₂₂ : Val α) :
    det2 mulF subF ⟨e₁₁, origin, e₂₁, e₂₂⟩ = origin := by simp [det2]

theorem det2_origin_e21 (mulF subF : α → α → α) (e₁₁ e₁₂ e₂₂ : Val α) :
    det2 mulF subF ⟨e₁₁, e₁₂, origin, e₂₂⟩ = origin := by simp [det2]

theorem det2_origin_e22 (mulF subF : α → α → α) (e₁₁ e₁₂ e₂₁ : Val α) :
    det2 mulF subF ⟨e₁₁, e₁₂, e₂₁, origin⟩ = origin := by simp [det2]

-- ============================================================================
-- Matrix Multiplication
-- ============================================================================

/-- 2×2 matrix multiplication over Val α. -/
def matMul2 (addF mulF : α → α → α) (a b : Mat2 (Val α)) : Mat2 (Val α) :=
  { e₁₁ := add addF (mul mulF a.e₁₁ b.e₁₁) (mul mulF a.e₁₂ b.e₂₁)
    e₁₂ := add addF (mul mulF a.e₁₁ b.e₁₂) (mul mulF a.e₁₂ b.e₂₂)
    e₂₁ := add addF (mul mulF a.e₂₁ b.e₁₁) (mul mulF a.e₂₂ b.e₂₁)
    e₂₂ := add addF (mul mulF a.e₂₁ b.e₁₂) (mul mulF a.e₂₂ b.e₂₂) }

/-- Product of two contents matrices has all contents entries. -/
theorem matMul2_contents (addF mulF : α → α → α) (a b c d e f g h : α) :
    matMul2 addF mulF
      ⟨contents a, contents b, contents c, contents d⟩
      ⟨contents e, contents f, contents g, contents h⟩ =
    ⟨contents (addF (mulF a e) (mulF b g)),
     contents (addF (mulF a f) (mulF b h)),
     contents (addF (mulF c e) (mulF d g)),
     contents (addF (mulF c f) (mulF d h))⟩ := by rfl

/-- No entry of a contents matrix product is origin. -/
theorem matMul2_contents_e11_ne_origin (addF mulF : α → α → α) (a b c d e f g h : α) :
    (matMul2 addF mulF
      ⟨contents a, contents b, contents c, contents d⟩
      ⟨contents e, contents f, contents g, contents h⟩).e₁₁ ≠ origin := by
  simp [matMul2]

theorem matMul2_contents_e22_ne_origin (addF mulF : α → α → α) (a b c d e f g h : α) :
    (matMul2 addF mulF
      ⟨contents a, contents b, contents c, contents d⟩
      ⟨contents e, contents f, contents g, contents h⟩).e₂₂ ≠ origin := by
  simp [matMul2]

-- ============================================================================
-- Adjugate
-- ============================================================================

/-- adj([[a,b],[c,d]]) = [[d,-b],[-c,a]] -/
def adj2 (negF : α → α) (m : Mat2 (Val α)) : Mat2 (Val α) :=
  { e₁₁ := m.e₂₂
    e₁₂ := neg negF m.e₁₂
    e₂₁ := neg negF m.e₂₁
    e₂₂ := m.e₁₁ }

/-- Adjugate of a contents matrix has all contents entries. -/
theorem adj2_contents (negF : α → α) (a b c d : α) :
    adj2 negF ⟨contents a, contents b, contents c, contents d⟩ =
    ⟨contents d, contents (negF b), contents (negF c), contents a⟩ := by rfl

-- ============================================================================
-- Cayley-Hamilton (2×2 diagonal)
-- ============================================================================

/-- The (1,1) entry of A·adj(A) equals det(A) within contents. -/
theorem cayley_hamilton_diag_11 (addF mulF subF : α → α → α) (negF : α → α)
    (hmn : ∀ x y : α, mulF x (negF y) = negF (mulF x y))
    (hsub : ∀ x y : α, addF x (negF y) = subF x y)
    (a b c d : α) :
    let m : Mat2 (Val α) := ⟨contents a, contents b, contents c, contents d⟩
    (matMul2 addF mulF m (adj2 negF m)).e₁₁ = det2 mulF subF m := by
  simp [matMul2, adj2, neg, mul, add, det2, hmn, hsub]

end Val
