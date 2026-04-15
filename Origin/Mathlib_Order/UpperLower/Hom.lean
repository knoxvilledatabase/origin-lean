/-
Extracted from Order/UpperLower/Hom.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `UpperSet.Ici` etc. as `Sup`/`sSup`/`Inf`/`sInf`-homomorphisms

In this file we define `UpperSet.iciSupHom` etc. These functions are `UpperSet.Ici` and
`LowerSet.Iic` bundled as `SupHom`s, `InfHom`s, `sSupHom`s, or `sInfHom`s.
-/

variable {α : Type*}

open OrderDual

namespace UpperSet

section SemilatticeSup

variable [SemilatticeSup α]

def iciSupHom : SupHom α (UpperSet α) :=
  ⟨Ici, Ici_sup⟩
