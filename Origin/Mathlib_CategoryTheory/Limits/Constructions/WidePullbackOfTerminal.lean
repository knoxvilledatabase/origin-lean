/-
Extracted from CategoryTheory/Limits/Constructions/WidePullbackOfTerminal.lean
Genuine: 4 of 4 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Existence of wide pullbacks when the target object is terminal

In this file, we show that the wide pullback of a family of arrows `objs j ⟶ B`
exists when `B` is terminal and the product of the objects `objs j` exists.

-/

universe w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
  {ι : Type w} {B : C} {objs : ι → C}
  (arrows : (j : ι) → objs j ⟶ B)

namespace WidePullbackCone

abbrev toFan (s : WidePullbackCone arrows) : Fan objs :=
  Fan.mk _ s.π

variable (c : Fan objs)

abbrev ofFan (hB : IsTerminal B) : WidePullbackCone arrows :=
  WidePullbackCone.mk (hB.from _) c.proj (fun _ ↦ hB.hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in

variable {c} in

def isLimitOfFan (hc : IsLimit c) (hB : IsTerminal B) :
    IsLimit (ofFan arrows c hB) :=
  IsLimit.mk _
    (fun s ↦ hc.lift s.toFan)
    (fun s ↦ hB.hom_ext _ _)
    (fun s i ↦ hc.fac s.toFan (.mk i))
    (fun s m _ hm ↦ hc.hom_ext (fun ⟨i⟩ ↦ by simpa using hm i))

end WidePullbackCone

lemma hasWidePullback_of_isTerminal
    [HasProduct objs] (hB : IsTerminal B) :
    HasWidePullback B objs arrows where
  exists_limit :=
    ⟨_, WidePullbackCone.isLimitOfFan (arrows := arrows) (limit.isLimit _) hB⟩

end CategoryTheory.Limits
