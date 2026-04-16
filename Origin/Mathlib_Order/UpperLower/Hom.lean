/-
Extracted from Order/UpperLower/Hom.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Hom.CompleteLattice

noncomputable section

/-!
# `UpperSet.Ici` etc as `Sup`/`sSup`/`Inf`/`sInf`-homomorphisms

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

end SemilatticeSup

variable [CompleteLattice α]

def icisSupHom : sSupHom α (UpperSet α) :=
  ⟨Ici, fun s => (Ici_sSup s).trans sSup_image.symm⟩

end UpperSet

namespace LowerSet

section SemilatticeInf

variable [SemilatticeInf α]

def iicInfHom : InfHom α (LowerSet α) :=
  ⟨Iic, Iic_inf⟩

end SemilatticeInf

variable [CompleteLattice α]

def iicsInfHom : sInfHom α (LowerSet α) :=
  ⟨Iic, fun s => (Iic_sInf s).trans sInf_image.symm⟩

end LowerSet
