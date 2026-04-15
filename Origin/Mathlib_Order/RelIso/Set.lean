/-
Extracted from Order/RelIso/Set.lean
Genuine: 5 of 6 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Interactions between relation homomorphisms and sets

It is likely that there are better homes for many of these statement,
in files further down the import graph.
-/

open Function

universe u v w

variable {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}

namespace RelHomClass

variable {F : Type*}

theorem map_inf [SemilatticeInf α] [LinearOrder β] [FunLike F β α]
    [RelHomClass F (· < ·) (· < ·)] (a : F) (m n : β) :
    a (m ⊓ n) = a m ⊓ a n :=
  (StrictMono.monotone fun _ _ => map_rel a).map_inf m n

theorem map_sup [SemilatticeSup α] [LinearOrder β] [FunLike F β α]
    [RelHomClass F (· > ·) (· > ·)] (a : F) (m n : β) :
    a (m ⊔ n) = a m ⊔ a n :=
  map_inf (α := αᵒᵈ) (β := βᵒᵈ) _ _ _

theorem directed [FunLike F α β] [RelHomClass F r s] {ι : Sort*} {a : ι → α} {f : F}
    (ha : Directed r a) : Directed s (f ∘ a) :=
  ha.mono_comp _ fun _ _ h ↦ map_rel f h

theorem directedOn [FunLike F α β] [RelHomClass F r s] {f : F}
    {t : Set α} (hs : DirectedOn r t) : DirectedOn s (f '' t) :=
  hs.mono_comp fun _ _ h ↦ map_rel f h

end RelHomClass

namespace RelIso

end RelIso

def Subrel (r : α → α → Prop) (p : α → Prop) : Subtype p → Subtype p → Prop :=
  Subtype.val ⁻¹'o r
