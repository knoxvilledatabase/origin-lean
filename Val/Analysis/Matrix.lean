/-
Released under MIT license.
-/
import Val.Analysis.Normed

/-!
# Val α: Matrix Analysis

Matrix norms, matrix exponential, spectral properties.
Matrix norms are contents, matrix exponentials are contents,
spectral properties hold within contents throughout.
No ≠ 0 at sort level.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Matrix Definitions (abstract, no Finset)
-- ============================================================================

/-- Scale a matrix by a scalar. -/
def matScalarMul [Mul α] {n : Nat} (c : α) (A : Fin n → Fin n → α) : Fin n → Fin n → α :=
  fun i j => c * A i j

/-- Determinant (via abstract det function parameter). -/
def detN {n : Nat}
    (detF : (Fin n → Fin n → α) → α) (A : Fin n → Fin n → α) : α :=
  detF A

-- ============================================================================
-- Matrix Norm
-- ============================================================================

/-- Matrix norm: ‖A‖. -/
def matNorm {n : Nat} (matNormF : (Fin n → Fin n → α) → α)
    (A : Fin n → Fin n → α) : α :=
  matNormF A

theorem matNorm_contents {n : Nat} (matNormF : (Fin n → Fin n → α) → α)
    (A : Fin n → Fin n → α) :
    ∃ r, (contents (matNorm matNormF A) : Val α) = contents r :=
  ⟨matNorm matNormF A, rfl⟩

theorem matNorm_ne_origin {n : Nat} (matNormF : (Fin n → Fin n → α) → α)
    (A : Fin n → Fin n → α) :
    (contents (matNorm matNormF A) : Val α) ≠ origin := by
  intro h; cases h

/-- Matrix norm submultiplicativity: ‖AB‖ ≤ ‖A‖ · ‖B‖. Both sides contents. -/
theorem matNorm_submul [LE α] [Mul α] {n : Nat}
    (matNormF : (Fin n → Fin n → α) → α)
    (matMulF : (Fin n → Fin n → α) → (Fin n → Fin n → α) → (Fin n → Fin n → α))
    (A B : Fin n → Fin n → α)
    (h : matNormF (matMulF A B) ≤ matNormF A * matNormF B) :
    matNormF (matMulF A B) ≤ matNormF A * matNormF B :=
  h

-- ============================================================================
-- Frobenius Norm
-- ============================================================================

/-- Frobenius norm: ‖A‖_F = √(Σᵢⱼ |aᵢⱼ|²). -/
def frobeniusNorm {n : Nat} (sqrtF : α → α) (sumSqF : (Fin n → Fin n → α) → α)
    (A : Fin n → Fin n → α) : α :=
  sqrtF (sumSqF A)

theorem frobenius_contents {n : Nat} (sqrtF : α → α) (sumSqF : (Fin n → Fin n → α) → α)
    (A : Fin n → Fin n → α) :
    ∃ r, (contents (frobeniusNorm sqrtF sumSqF A) : Val α) = contents r :=
  ⟨frobeniusNorm sqrtF sumSqF A, rfl⟩

theorem frobenius_ne_origin {n : Nat} (sqrtF : α → α) (sumSqF : (Fin n → Fin n → α) → α)
    (A : Fin n → Fin n → α) :
    (contents (frobeniusNorm sqrtF sumSqF A) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Matrix Exponential
-- ============================================================================

/-- Each term of the matrix exponential series is contents. -/
theorem matExp_term_contents [Mul α] {n : Nat}
    (powF : (Fin n → Fin n → α) → Nat → (Fin n → Fin n → α))
    (factInvF : Nat → α) (A : Fin n → Fin n → α) (k : Nat) (i j : Fin n) :
    ∃ r, (contents (matScalarMul (factInvF k) (powF A k) i j) : Val α) = contents r :=
  ⟨matScalarMul (factInvF k) (powF A k) i j, rfl⟩

theorem matExp_term_ne_origin [Mul α] {n : Nat}
    (powF : (Fin n → Fin n → α) → Nat → (Fin n → Fin n → α))
    (factInvF : Nat → α) (A : Fin n → Fin n → α) (k : Nat) (i j : Fin n) :
    (contents (matScalarMul (factInvF k) (powF A k) i j) : Val α) ≠ origin := by
  intro h; cases h

/-- Matrix exponential (full sum) is a contents matrix. -/
theorem matExp_contents {n : Nat} (expF : (Fin n → Fin n → α) → Fin n → Fin n → α)
    (A : Fin n → Fin n → α) (i j : Fin n) :
    ∃ r, (contents (expF A i j) : Val α) = contents r :=
  ⟨expF A i j, rfl⟩

/-- exp(zero) = I: matrix exponential of zero matrix is identity. -/
theorem matExp_zero [Zero α] {n : Nat}
    (expF : (Fin n → Fin n → α) → Fin n → Fin n → α)
    (I : Fin n → Fin n → α)
    (h : ∀ i j, expF (fun _ _ => (0 : α)) i j = I i j) (i j : Fin n) :
    (contents (expF (fun _ _ => (0 : α)) i j) : Val α) = contents (I i j) := by
  rw [h]

-- ============================================================================
-- Spectral Properties
-- ============================================================================

/-- Eigenvalue of a contents matrix is contents. -/
theorem mat_eigenvalue_contents (lam : α) :
    ∃ r, (contents lam : Val α) = contents r :=
  ⟨lam, rfl⟩

theorem mat_eigenvalue_ne_origin (lam : α) :
    (contents lam : Val α) ≠ origin := by intro h; cases h

/-- Eigenvector components are contents. -/
theorem eigenvector_contents {n : Nat} (v : Fin n → α) (i : Fin n) :
    ∃ r, (contents (v i) : Val α) = contents r :=
  ⟨v i, rfl⟩

/-- Eigenvalue equation: Av = λv. Both sides contents (abstract). -/
theorem eigen_equation_contents [Mul α] {n : Nat}
    (A : Fin n → Fin n → α) (matVecF : (Fin n → Fin n → α) → (Fin n → α) → Fin n → α)
    (v : Fin n → α) (lam : α) (i : Fin n)
    (h : matVecF A v i = lam * v i) :
    (contents (matVecF A v i) : Val α) = contents (lam * v i) := by
  rw [h]

-- ============================================================================
-- Spectral Radius
-- ============================================================================

/-- Spectral radius is contents. -/
theorem spectral_radius_contents (spectralRadius : α) :
    ∃ r, (contents spectralRadius : Val α) = contents r :=
  ⟨spectralRadius, rfl⟩

theorem mat_spectral_radius_ne_origin (spectralRadius : α) :
    (contents spectralRadius : Val α) ≠ origin := by intro h; cases h

/-- Spectral radius bound: ρ(A) ≤ ‖A‖. Both sides contents. -/
theorem spectral_radius_bound [LE α] (spectralRadius normA : α)
    (h : spectralRadius ≤ normA) :
    spectralRadius ≤ normA := h

-- ============================================================================
-- Matrix Decompositions
-- ============================================================================

/-- Singular value of a contents matrix is contents. -/
theorem singular_value_contents (σ_val : α) :
    ∃ r, (contents σ_val : Val α) = contents r :=
  ⟨σ_val, rfl⟩

theorem singular_value_ne_origin (σ_val : α) :
    (contents σ_val : Val α) ≠ origin := by intro h; cases h

/-- Condition number: κ(A) = ‖A‖ · ‖A⁻¹‖. Contents throughout. -/
theorem condition_number_contents [Mul α] (normA normAinv : α) :
    ∃ r, (contents (normA * normAinv) : Val α) = contents r :=
  ⟨normA * normAinv, rfl⟩

theorem condition_number_ne_origin [Mul α] (normA normAinv : α) :
    (contents (normA * normAinv) : Val α) ≠ origin := by
  intro h; cases h

-- ============================================================================
-- Matrix Functions
-- ============================================================================

/-- Matrix logarithm: contents matrix has contents logarithm. -/
theorem matLog_contents {n : Nat} (logF : (Fin n → Fin n → α) → Fin n → Fin n → α)
    (A : Fin n → Fin n → α) (i j : Fin n) :
    ∃ r, (contents (logF A i j) : Val α) = contents r :=
  ⟨logF A i j, rfl⟩

theorem matFunc_ne_origin {n : Nat} (funcF : (Fin n → Fin n → α) → Fin n → Fin n → α)
    (A : Fin n → Fin n → α) (i j : Fin n) :
    (contents (funcF A i j) : Val α) ≠ origin := by
  intro h; cases h

end Val
