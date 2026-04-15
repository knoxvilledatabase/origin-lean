/-
Extracted from Algebra/Lie/Subalgebra.lean
Genuine: 6 of 22 | Dissolved: 0 | Infrastructure: 16
-/
import Origin.Core

/-!
# Lie subalgebras

This file defines Lie subalgebras of a Lie algebra and provides basic related definitions and
results.

## Main definitions

  * `LieSubalgebra`
  * `LieSubalgebra.incl`
  * `LieSubalgebra.map`
  * `LieHom.range`
  * `LieEquiv.ofInjective`
  * `LieEquiv.ofEq`
  * `LieEquiv.ofSubalgebras`

## Tags

lie algebra, lie subalgebra
-/

universe u v w w₁ w₂

section LieSubalgebra

open Set

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

structure LieSubalgebra extends Submodule R L where
  /-- A Lie subalgebra is closed under Lie bracket. -/
  lie_mem' : ∀ {x y}, x ∈ carrier → y ∈ carrier → ⁅x, y⁆ ∈ carrier

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

namespace LieSubalgebra

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): lieRing

variable {R₁ : Type*} [Semiring R₁]

-- INSTANCE (free from Core): [SMul

-- INSTANCE (free from Core): [SMul

-- INSTANCE (free from Core): [SMul

-- INSTANCE (free from Core): (L'

-- INSTANCE (free from Core): (L'

end

-- INSTANCE (free from Core): lieAlgebra

variable {R L}

variable (L' : LieSubalgebra R L)

protected theorem zero_mem : (0 : L) ∈ L' :=
  zero_mem L'

protected theorem add_mem {x y : L} : x ∈ L' → y ∈ L' → (x + y : L) ∈ L' :=
  add_mem

protected theorem sub_mem {x y : L} : x ∈ L' → y ∈ L' → (x - y : L) ∈ L' :=
  sub_mem

protected theorem smul_mem (t : R) {x : L} (h : x ∈ L') : t • x ∈ L' :=
  SMulMemClass.smul_mem _ h

theorem lie_mem {x y : L} (hx : x ∈ L') (hy : y ∈ L') : (⁅x, y⁆ : L) ∈ L' :=
  L'.lie_mem' hx hy
