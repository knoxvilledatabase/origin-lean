/-
Extracted from CategoryTheory/Filtered/Connected.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Filtered categories are connected
-/

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

theorem IsFilteredOrEmpty.isPreconnected [IsFilteredOrEmpty C] : IsPreconnected C :=
  zigzag_isPreconnected fun j j' => .trans
    (.single <| .inl <| .intro <| IsFiltered.leftToMax j j')
    (.single <| .inr <| .intro <| IsFiltered.rightToMax j j')

theorem IsCofilteredOrEmpty.isPreconnected [IsCofilteredOrEmpty C] : IsPreconnected C :=
  zigzag_isPreconnected fun j j' => .trans
    (.single <| .inr <| .intro <| IsCofiltered.minToLeft j j')
    (.single <| .inl <| .intro <| IsCofiltered.minToRight j j')

attribute [local instance] IsFiltered.nonempty in

theorem IsFiltered.isConnected [IsFiltered C] : IsConnected C :=
  { IsFilteredOrEmpty.isPreconnected C with }

attribute [local instance] IsCofiltered.nonempty in

theorem IsCofiltered.isConnected [IsCofiltered C] : IsConnected C :=
  { IsCofilteredOrEmpty.isPreconnected C with }

end CategoryTheory
