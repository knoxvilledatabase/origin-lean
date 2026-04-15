/-
Extracted from Algebra/Notation/Defs.lean
Genuine: 6 of 6 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Typeclasses for algebraic operations

Notation typeclass for `Inv`, the multiplicative analogue of `Neg`.

We also introduce notation classes `SMul` and `VAdd` for multiplicative and additive
actions.

We introduce the notation typeclass `Star` for algebraic structures with a star operation. Note: to
accommodate diverse notational preferences, no default notation is provided for `Star.star`.

`SMul` is typically, but not exclusively, used for scalar multiplication-like operators.
See the module `Algebra.AddTorsor` for a motivating example for the name `VAdd` (vector addition).

Note `Zero` has already been defined in core Lean.

## Notation

- `a • b` is used as notation for `HSMul.hSMul a b`.
- `a +ᵥ b` is used as notation for `HVAdd.hVAdd a b`.

-/

assert_not_exists Function.Bijective

universe u v w

class HVAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- `a +ᵥ b` computes the sum of `a` and `b`.
  The meaning of this notation is type-dependent. -/
  hVAdd : α → β → γ

attribute [notation_class smul Simps.copySecond] HSMul

attribute [notation_class nsmul Simps.nsmulArgs] HSMul

attribute [notation_class zsmul Simps.zsmulArgs] HSMul

class VAdd (G : Type u) (P : Type v) where
  /-- `a +ᵥ b` computes the sum of `a` and `b`. The meaning of this notation is type-dependent,
  but it is intended to be used for left actions. -/
  vadd : G → P → P

class VSub (G : outParam Type*) (P : Type*) where
  /-- `a -ᵥ b` computes the difference of `a` and `b`. The meaning of this notation is
  type-dependent, but it is intended to be used for additive torsors. -/
  vsub : P → P → G

attribute [to_additive existing] SMul HSMul

attribute [to_additive (attr := default_instance)] instHSMul

attribute [ext] SMul VAdd
