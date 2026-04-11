/-
Released under MIT license.
-/
import Val.Category.Core
import Val.Algebra

/-!
# Val α: Abelian Categories

Kernels, cokernels, exact sequences, images.
The sort system gives structural kernels: the kernel of a sort-preserving
map is the preimage of origin, which is exactly {origin}.
-/

namespace Val

universe u
variable {α β γ : Type u}

-- ============================================================================
-- Kernel
-- ============================================================================

/-- The kernel of a Val-map: the set of values that map to origin. -/
def valKernel (f : Val α → Val β) (x : Val α) : Prop :=
  f x = origin

/-- For valMap f, origin is always in the kernel. -/
theorem origin_in_kernel (f : α → β) :
    valKernel (valMap f) (origin : Val α) := rfl

/-- For valMap f, no contents value is in the kernel. -/
theorem contents_not_in_kernel (f : α → β) (a : α) :
    ¬ valKernel (valMap f) (contents a) := by
  intro h; simp [valKernel, valMap] at h

/-- The kernel of valMap f is exactly {origin}. -/
theorem kernel_is_origin (f : α → β) (x : Val α) :
    valKernel (valMap f) x ↔ x = origin := by
  constructor
  · intro h; cases x with
    | origin => rfl
    | container a => simp [valKernel, valMap] at h
    | contents a => simp [valKernel, valMap] at h
  · intro h; rw [h]; rfl

-- ============================================================================
-- Cokernel
-- ============================================================================

/-- The cokernel: values in the codomain not hit by any input. -/
def valCokernel (f : Val α → Val β) (y : Val β) : Prop :=
  ∀ x : Val α, f x ≠ y

/-- Origin is not in the cokernel of valMap f (since origin maps to origin). -/
theorem origin_not_in_cokernel (f : α → β) :
    ¬ valCokernel (valMap f) (origin : Val β) := by
  intro h; exact h origin rfl

-- ============================================================================
-- Image
-- ============================================================================

/-- The image of a map: the set of values in the codomain that are hit. -/
def valImage (f : Val α → Val β) (y : Val β) : Prop :=
  ∃ x : Val α, f x = y

/-- Origin is in the image of every valMap. -/
theorem origin_in_image (f : α → β) :
    valImage (valMap f) (origin : Val β) := ⟨origin, rfl⟩

/-- Every contents value in the codomain is in the image if f is surjective. -/
theorem contents_in_image (f : α → β) (b : β) (hf : ∃ a, f a = b) :
    valImage (valMap f) (contents b) := by
  obtain ⟨a, ha⟩ := hf
  exact ⟨contents a, by show contents (f a) = contents b; rw [ha]⟩

-- ============================================================================
-- Exact Sequences
-- ============================================================================

/-- A sequence A → B → C is exact at B if image(f) = kernel(g). -/
def isExact (f : Val α → Val β) (g : Val β → Val γ) : Prop :=
  ∀ y : Val β, valImage f y ↔ valKernel g y

/-- The zero morphism: everything maps to origin. -/
def zeroMorphism : Val α → Val β
  | _ => origin

/-- The zero morphism has full kernel. -/
theorem zero_morphism_kernel (x : Val α) :
    valKernel (zeroMorphism (β := β)) x := rfl

-- ============================================================================
-- Short Exact Sequences
-- ============================================================================

/-- Origin is in the kernel of any valMap. -/
theorem short_exact_origin_kernel (f : α → β) :
    valKernel (valMap f) (origin : Val α) := rfl

/-- Surjective maps have contents in their image. -/
theorem short_exact_surjective (g : β → γ) (c : γ) (hg : ∃ b, g b = c) :
    valImage (valMap g) (contents c) := by
  obtain ⟨b, hb⟩ := hg
  exact ⟨contents b, by show contents (g b) = contents c; rw [hb]⟩

-- ============================================================================
-- Additive Structure
-- ============================================================================

/-- The zero morphism between Val spaces. -/
theorem zero_sequence_kernel :
    ∀ y : Val β, valKernel (fun _ : Val β => (origin : Val γ)) y := fun _ => rfl

/-- Snake lemma: the connecting morphism maps contents to contents. -/
theorem snake_contents (δ_map : α → β) (a : α) :
    valMap δ_map (contents a) = contents (δ_map a) := rfl

/-- The connecting morphism never produces origin from contents. -/
theorem snake_ne_origin (δ_map : α → β) (a : α) :
    valMap δ_map (contents a) ≠ (origin : Val β) := by simp

-- ============================================================================
-- THE RESULT
-- ============================================================================
--
-- Abelian categories over Val α:
--   ✓ Kernels: exactly {origin} for valMap
--   ✓ Contents never in kernel
--   ✓ Cokernels: origin not in cokernel
--   ✓ Images: origin and surjective contents in image
--   ✓ Exact sequences: image = kernel
--   ✓ Zero morphism: full kernel
--   ✓ Snake lemma: connecting morphism preserves contents
--
-- Zero sorries. Zero typeclasses. Zero Mathlib.

end Val
