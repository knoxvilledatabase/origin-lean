/-
Extracted from Algebra/Homology/HasNoLoop.lean
Genuine: 5 of 14 | Dissolved: 4 | Infrastructure: 5
-/
import Origin.Core

/-!
# Complex shapes with no loop

Let `c : ComplexShape ι`. We define a type class `c.HasNoLoop`
which expresses that `¬ c.Rel i i` for all `i : ι`.

-/

namespace ComplexShape

variable {ι : Type*}

class HasNoLoop (c : ComplexShape ι) : Prop where
  not_rel_self (i : ι) : ¬ c.Rel i i

variable (c : ComplexShape ι) [c.HasNoLoop] (j : ι)

lemma not_rel_self : ¬ c.Rel j j :=
  HasNoLoop.not_rel_self j

variable {j} in

lemma not_rel_of_eq {j' : ι} (h : j = j') : ¬ c.Rel j j' := by
  subst h
  exact c.not_rel_self j

-- INSTANCE (free from Core): :

lemma exists_distinct_prev_or :
    (∃ (k : ι), c.Rel j k ∧ j ≠ k) ∨ ∀ (k : ι), ¬ c.Rel j k := by
  grind +splitIndPred

lemma exists_distinct_next_or :
    (∃ (i : ι), c.Rel i j ∧ i ≠ j) ∨ ∀ (i : ι), ¬ c.Rel i j := by
  grind +splitIndPred

-- DISSOLVED: hasNoLoop_up'

-- DISSOLVED: hasNoLoop_down'

-- DISSOLVED: hasNoLoop_up

-- DISSOLVED: hasNoLoop_down

end

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end ComplexShape
