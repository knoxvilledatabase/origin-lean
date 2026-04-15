/-
Extracted from Computability/Encoding.lean
Genuine: 6 of 8 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Encodings

This file contains the definition of a (finite) encoding, a map from a type to
strings in an alphabet, used in defining computability by Turing machines.
It also contains several examples:

## Examples

- `finEncodingNatBool`  : a binary encoding of `ℕ` in a simple alphabet.
- `finEncodingNatΓ'`    : a binary encoding of `ℕ` in the alphabet used for TM's.
- `unaryFinEncodingNat` : a unary encoding of `ℕ`
- `finEncodingBoolBool` : an encoding of `Bool`.
- `finEncodingList`     : an encoding of `List α` in the alphabet `α`.
- `finEncodingPair`     : an encoding of `α × β` from encodings of `α` and `β`.
-/

universe u v

open Cardinal

namespace Computability

structure Encoding (α : Type u) where
  /-- The alphabet of the encoding -/
  Γ : Type v
  /-- The encoding function -/
  encode : α → List Γ
  /-- The decoding function -/
  decode : List Γ → Option α
  /-- Decoding and encoding are inverses of each other. -/
  decode_encode : ∀ x, decode (encode x) = some x

attribute [simp] Encoding.decode_encode

theorem Encoding.encode_injective {α : Type u} (e : Encoding α) : Function.Injective e.encode := by
  refine fun _ _ h => Option.some_injective _ ?_
  rw [← e.decode_encode, ← e.decode_encode, h]

structure FinEncoding (α : Type u) extends Encoding.{u, 0} α where
  /-- The alphabet of the encoding is finite -/
  ΓFin : Fintype Γ

-- INSTANCE (free from Core): Γ.fintype

inductive Γ'
  | blank
  | bit (b : Bool)
  | bra
  | ket
  | comma
  deriving DecidableEq, Fintype

-- INSTANCE (free from Core): inhabitedΓ'

def inclusionBoolΓ' : Bool → Γ' :=
  Γ'.bit

def sectionΓ'Bool : Γ' → Bool
  | Γ'.bit b => b
  | _ => Inhabited.default
