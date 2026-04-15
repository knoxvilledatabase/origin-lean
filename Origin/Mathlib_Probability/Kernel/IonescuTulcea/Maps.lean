/-
Extracted from Probability/Kernel/IonescuTulcea/Maps.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Auxiliary maps for Ionescu-Tulcea theorem

This file contains auxiliary maps which are used to prove the Ionescu-Tulcea theorem.
-/

open Finset Preorder

section Definitions

section LinearOrder

variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [DecidableLE ι] {X : ι → Type*}

def IocProdIoc (a b c : ι) (x : (Π i : Ioc a b, X i) × (Π i : Ioc b c, X i)) (i : Ioc a c) : X i :=
  if h : i ≤ b
    then x.1 ⟨i, mem_Ioc.2 ⟨(mem_Ioc.1 i.2).1, h⟩⟩
    else x.2 ⟨i, mem_Ioc.2 ⟨not_le.1 h, (mem_Ioc.1 i.2).2⟩⟩
