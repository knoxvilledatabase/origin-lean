/-
Extracted from Data/Matrix/Block.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Block Matrices

## Main definitions

* `Matrix.fromBlocks`: build a block matrix out of 4 blocks
* `Matrix.toBlocks₁₁`, `Matrix.toBlocks₁₂`, `Matrix.toBlocks₂₁`, `Matrix.toBlocks₂₂`:
  extract each of the four blocks from `Matrix.fromBlocks`.
* `Matrix.blockDiagonal`: block diagonal of equally sized blocks. On square blocks, this is a
  ring homomorphisms, `Matrix.blockDiagonalRingHom`.
* `Matrix.blockDiag`: extract the blocks from the diagonal of a block diagonal matrix.
* `Matrix.blockDiagonal'`: block diagonal of unequally sized blocks. On square blocks, this is a
  ring homomorphisms, `Matrix.blockDiagonal'RingHom`.
* `Matrix.blockDiag'`: extract the blocks from the diagonal of a block diagonal matrix.
-/

variable {l m n o p q : Type*} {m' n' p' : o → Type*}

variable {R : Type*} {S : Type*} {α : Type*} {β : Type*}

open Matrix

namespace Matrix

theorem dotProduct_block [Fintype m] [Fintype n] [Mul α] [AddCommMonoid α] (v w : m ⊕ n → α) :
    v ⬝ᵥ w = v ∘ Sum.inl ⬝ᵥ w ∘ Sum.inl + v ∘ Sum.inr ⬝ᵥ w ∘ Sum.inr :=
  Fintype.sum_sum_type _

section BlockMatrices
