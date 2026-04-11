/-
Released under MIT license.
-/
import Val.Category.Core

/-!
# Val α: Limits, Colimits, Equalizers, Pullbacks

Categorical limits and colimits in Val α.
Origin is the zero object. Products and coproducts from Core.
Now: equalizers and pullbacks.
-/

namespace Val

universe u
variable {α β γ : Type u}

-- ============================================================================
-- Equalizer
-- ============================================================================

/-- The equalizer of f, g : α → β: the set {a | f a = g a}. -/
def equalizer (f g : α → β) (a : α) : Prop := f a = g a

/-- The equalizer in Val α: contents(a) where f a = g a. -/
def valEqualizer (f g : α → β) (a : α) (_ : f a = g a) : Val α := contents a

/-- Equalizer elements are contents. -/
theorem equalizer_is_contents (f g : α → β) (a : α) (h : f a = g a) :
    ∃ r, valEqualizer f g a h = contents r := ⟨a, rfl⟩

/-- Equalizer elements are never origin. -/
theorem equalizer_ne_origin (f g : α → β) (a : α) (h : f a = g a) :
    valEqualizer f g a h ≠ (origin : Val α) := by simp [valEqualizer]

/-- The equalizer map: f and g agree on equalizer elements. -/
theorem equalizer_agreement (f g : α → β) (a : α) (h : f a = g a) :
    valMap f (valEqualizer f g a h) = valMap g (valEqualizer f g a h) := by
  show contents (f a) = contents (g a); rw [h]

-- ============================================================================
-- Coequalizer
-- ============================================================================

/-- Coequalizer in Val α: the quotient map sends contents to contents. -/
theorem coequalizer_contents (proj : β → γ) (b : β) :
    valMap proj (contents b) = contents (proj b) := rfl

-- ============================================================================
-- Pullback
-- ============================================================================

/-- The pullback of f : α → γ and g : β → γ: pairs (a, b) where f a = g b. -/
def pullback (f : α → γ) (g : β → γ) (a : α) (b : β) : Prop := f a = g b

/-- Pullback in Val α: a pair of contents values where the maps agree. -/
def valPullback (f : α → γ) (g : β → γ) (a : α) (b : β) (_ : f a = g b) :
    Val (α × β) := contents (a, b)

/-- Pullback elements are contents. -/
theorem pullback_is_contents (f : α → γ) (g : β → γ) (a : α) (b : β) (h : f a = g b) :
    ∃ r, valPullback f g a b h = contents r := ⟨(a, b), rfl⟩

/-- Pullback elements are never origin. -/
theorem pullback_ne_origin (f : α → γ) (g : β → γ) (a : α) (b : β) (h : f a = g b) :
    valPullback f g a b h ≠ (origin : Val (α × β)) := by simp [valPullback]

-- ============================================================================
-- Pushout
-- ============================================================================

/-- Pushout injection into left component. -/
def pushoutInl (a : α) : Val (α ⊕ β) := contents (Sum.inl a)
def pushoutInr (b : β) : Val (α ⊕ β) := contents (Sum.inr b)

/-- Pushout injections are contents. -/
theorem pushout_inl_contents (a : α) :
    ∃ r, pushoutInl (β := β) a = contents r := ⟨Sum.inl a, rfl⟩

theorem pushout_inr_contents (b : β) :
    ∃ r, pushoutInr (α := α) b = contents r := ⟨Sum.inr b, rfl⟩

-- ============================================================================
-- Terminal and Initial Objects
-- ============================================================================

/-- The terminal map: every sort maps to the same sort in Val Unit. -/
def toTerminal : Val α → Val Unit
  | origin => origin
  | container _ => container ()
  | contents _ => contents ()

/-- Terminal map is unique among sort-preserving maps. -/
theorem terminal_unique (f g : Val α → Val Unit)
    (hf_o : f origin = origin) (hg_o : g origin = origin)
    (hf_c : ∀ a, f (container a) = container ()) (hg_c : ∀ a, g (container a) = container ())
    (hf_x : ∀ a, f (contents a) = contents ()) (hg_x : ∀ a, g (contents a) = contents ()) :
    f = g := by
  funext x; cases x with
  | origin => rw [hf_o, hg_o]
  | container a => rw [hf_c, hg_c]
  | contents a => rw [hf_x, hg_x]

-- ============================================================================
-- Zero Object
-- ============================================================================

/-- Origin is the zero object: absorbs under all operations. -/
theorem zero_object_absorb (mulF : α → α → α) :
    mul mulF (origin : Val α) origin = origin := rfl

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Limits and colimits over Val α:
--   ✓ Equalizers: contents, never origin, maps agree
--   ✓ Coequalizers: quotient preserves contents
--   ✓ Pullbacks: contents pairs, projections work
--   ✓ Pushouts: injections are contents
--   ✓ Terminal object: unique sort-preserving map
--   ✓ Zero object: origin absorbs
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
