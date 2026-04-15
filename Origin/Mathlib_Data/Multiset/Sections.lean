/-
Extracted from Data/Multiset/Sections.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Sections of a multiset
-/

assert_not_exists Ring

namespace Multiset

variable {α : Type*}

section Sections

def Sections (s : Multiset (Multiset α)) : Multiset (Multiset α) :=
  Multiset.recOn s {0} (fun s _ c => s.bind fun a => c.map (Multiset.cons a)) fun a₀ a₁ _ pi => by
    simp [map_bind, bind_bind a₀ a₁, cons_swap]
