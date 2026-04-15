/-
Extracted from Analysis/Convex/Function.lean
Genuine: 102 of 102 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Convex and concave functions

This file defines convex and concave functions in vector spaces and proves the finite Jensen
inequality. The integral version can be found in `Analysis.Convex.Integral`.

A function `f : E → β` is `ConvexOn` a set `s` if `s` is itself a convex set, and for any two
points `x y ∈ s`, the segment joining `(x, f x)` to `(y, f y)` is above the graph of `f`.
Equivalently, `ConvexOn 𝕜 f s` means that the epigraph `{p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}` is
a convex set.

## Main declarations

* `ConvexOn 𝕜 s f`: The function `f` is convex on `s` with scalars `𝕜`.
* `ConcaveOn 𝕜 s f`: The function `f` is concave on `s` with scalars `𝕜`.
* `StrictConvexOn 𝕜 s f`: The function `f` is strictly convex on `s` with scalars `𝕜`.
* `StrictConcaveOn 𝕜 s f`: The function `f` is strictly concave on `s` with scalars `𝕜`.
-/

open LinearMap Set Convex Pointwise

variable {𝕜 E F α β ι : Type*}

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable [AddCommMonoid E] [AddCommMonoid F]

section OrderedAddCommMonoid

variable [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]

section SMul

variable (𝕜) [SMul 𝕜 E] [SMul 𝕜 α] [SMul 𝕜 β] (s : Set E) (f : E → β) {g : β → α}

def ConvexOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y

def ConcaveOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y ≤ f (a • x + b • y)

def StrictConvexOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) < a • f x + b • f y

def StrictConcaveOn : Prop :=
  Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
    a • f x + b • f y < f (a • x + b • y)

variable {𝕜 s f}

open OrderDual (toDual ofDual)

theorem ConvexOn.dual (hf : ConvexOn 𝕜 s f) : ConcaveOn 𝕜 s (toDual ∘ f) := hf

theorem ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (toDual ∘ f) := hf

theorem StrictConvexOn.dual (hf : StrictConvexOn 𝕜 s f) : StrictConcaveOn 𝕜 s (toDual ∘ f) := hf

theorem StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) : StrictConvexOn 𝕜 s (toDual ∘ f) := hf

theorem convexOn_id {s : Set β} (hs : Convex 𝕜 s) : ConvexOn 𝕜 s _root_.id :=
  ⟨hs, by
    intros
    rfl⟩

theorem concaveOn_id {s : Set β} (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s _root_.id :=
  ⟨hs, by
    intros
    rfl⟩

section congr

variable {g : E → β}

theorem ConvexOn.congr (hf : ConvexOn 𝕜 s f) (hfg : EqOn f g s) : ConvexOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab⟩

theorem ConcaveOn.congr (hf : ConcaveOn 𝕜 s f) (hfg : EqOn f g s) : ConcaveOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha hb hab)] using hf.2 hx hy ha hb hab⟩

theorem StrictConvexOn.congr (hf : StrictConvexOn 𝕜 s f) (hfg : EqOn f g s) :
    StrictConvexOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha.le hb.le hab)] using
      hf.2 hx hy hxy ha hb hab⟩

theorem StrictConcaveOn.congr (hf : StrictConcaveOn 𝕜 s f) (hfg : EqOn f g s) :
    StrictConcaveOn 𝕜 s g :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab => by
    simpa only [← hfg hx, ← hfg hy, ← hfg (hf.1 hx hy ha.le hb.le hab)] using
      hf.2 hx hy hxy ha hb hab⟩

end congr

theorem ConvexOn.subset {t : Set E} (hf : ConvexOn 𝕜 t f) (hst : s ⊆ t) (hs : Convex 𝕜 s) :
    ConvexOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

theorem ConcaveOn.subset {t : Set E} (hf : ConcaveOn 𝕜 t f) (hst : s ⊆ t) (hs : Convex 𝕜 s) :
    ConcaveOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

theorem StrictConvexOn.subset {t : Set E} (hf : StrictConvexOn 𝕜 t f) (hst : s ⊆ t)
    (hs : Convex 𝕜 s) : StrictConvexOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

theorem StrictConcaveOn.subset {t : Set E} (hf : StrictConcaveOn 𝕜 t f) (hst : s ⊆ t)
    (hs : Convex 𝕜 s) : StrictConcaveOn 𝕜 s f :=
  ⟨hs, fun _ hx _ hy => hf.2 (hst hx) (hst hy)⟩

theorem ConvexOn.comp (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
    (hg' : MonotoneOn g (f '' s)) : ConvexOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy _ _ ha hb hab =>
    (hg' (mem_image_of_mem f <| hf.1 hx hy ha hb hab)
            (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab) <|
          hf.2 hx hy ha hb hab).trans <|
      hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab⟩

theorem ConcaveOn.comp (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
    (hg' : MonotoneOn g (f '' s)) : ConcaveOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy _ _ ha hb hab =>
    (hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab).trans <|
      hg' (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha hb hab)
          (mem_image_of_mem f <| hf.1 hx hy ha hb hab) <|
        hf.2 hx hy ha hb hab⟩

theorem ConvexOn.comp_concaveOn (hg : ConvexOn 𝕜 (f '' s) g) (hf : ConcaveOn 𝕜 s f)
    (hg' : AntitoneOn g (f '' s)) : ConvexOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg'

theorem ConcaveOn.comp_convexOn (hg : ConcaveOn 𝕜 (f '' s) g) (hf : ConvexOn 𝕜 s f)
    (hg' : AntitoneOn g (f '' s)) : ConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg'

theorem StrictConvexOn.comp (hg : StrictConvexOn 𝕜 (f '' s) g) (hf : StrictConvexOn 𝕜 s f)
    (hg' : StrictMonoOn g (f '' s)) (hf' : s.InjOn f) : StrictConvexOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab =>
    (hg' (mem_image_of_mem f <| hf.1 hx hy ha.le hb.le hab)
            (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab) <|
          hf.2 hx hy hxy ha hb hab).trans <|
      hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) (mt (hf' hx hy) hxy) ha hb hab⟩

theorem StrictConcaveOn.comp (hg : StrictConcaveOn 𝕜 (f '' s) g) (hf : StrictConcaveOn 𝕜 s f)
    (hg' : StrictMonoOn g (f '' s)) (hf' : s.InjOn f) : StrictConcaveOn 𝕜 s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab =>
    (hg.2 (mem_image_of_mem f hx) (mem_image_of_mem f hy) (mt (hf' hx hy) hxy) ha hb hab).trans <|
      hg' (hg.1 (mem_image_of_mem f hx) (mem_image_of_mem f hy) ha.le hb.le hab)
          (mem_image_of_mem f <| hf.1 hx hy ha.le hb.le hab) <|
        hf.2 hx hy hxy ha hb hab⟩

theorem StrictConvexOn.comp_strictConcaveOn (hg : StrictConvexOn 𝕜 (f '' s) g)
    (hf : StrictConcaveOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) (hf' : s.InjOn f) :
    StrictConvexOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg' hf'

theorem StrictConcaveOn.comp_strictConvexOn (hg : StrictConcaveOn 𝕜 (f '' s) g)
    (hf : StrictConvexOn 𝕜 s f) (hg' : StrictAntiOn g (f '' s)) (hf' : s.InjOn f) :
    StrictConcaveOn 𝕜 s (g ∘ f) :=
  hg.dual.comp hf hg' hf'

end SMul

section DistribMulAction

variable [IsOrderedAddMonoid β] [SMul 𝕜 E] [DistribMulAction 𝕜 β] {s : Set E} {f g : E → β}

theorem ConvexOn.add (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x hx y hy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) ≤ a • f x + b • f y + (a • g x + b • g y) :=
        add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]
      ⟩

theorem ConcaveOn.add (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 s (f + g) :=
  hf.dual.add hg

end DistribMulAction

section Module

variable [SMul 𝕜 E] [Module 𝕜 β] {s : Set E} {f : E → β}

theorem convexOn_const (c : β) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s fun _ : E => c :=
  ⟨hs, fun _ _ _ _ _ _ _ _ hab => (Convex.combo_self hab c).ge⟩

theorem concaveOn_const (c : β) (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s fun _ => c :=
  convexOn_const (β := βᵒᵈ) _ hs

theorem ConvexOn.add_const [IsOrderedAddMonoid β] (hf : ConvexOn 𝕜 s f) (b : β) :
    ConvexOn 𝕜 s (f + fun _ => b) :=
  hf.add (convexOn_const _ hf.1)

theorem ConcaveOn.add_const [IsOrderedAddMonoid β] (hf : ConcaveOn 𝕜 s f) (b : β) :
    ConcaveOn 𝕜 s (f + fun _ => b) :=
  hf.add (concaveOn_const _ hf.1)

theorem convexOn_of_convex_epigraph (h : Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 }) :
    ConvexOn 𝕜 s f :=
  ⟨fun x hx y hy a b ha hb hab => (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).1,
    fun x hx y hy a b ha hb hab => (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a b ha hb hab).2⟩

theorem concaveOn_of_convex_hypograph (h : Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1 }) :
    ConcaveOn 𝕜 s f :=
  convexOn_of_convex_epigraph (β := βᵒᵈ) h

end Module

section PosSMulMono

variable [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β] [PosSMulMono 𝕜 β] {s : Set E} {f : E → β}

theorem ConvexOn.convex_le (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | f x ≤ r }) :=
  fun x hx y hy a b ha hb hab =>
  ⟨hf.1 hx.1 hy.1 ha hb hab,
    calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx.1 hy.1 ha hb hab
      _ ≤ a • r + b • r := by
        gcongr
        · exact hx.2
        · exact hy.2
      _ = r := Convex.combo_self hab r
      ⟩

theorem ConcaveOn.convex_ge (hf : ConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  hf.dual.convex_le r

theorem ConvexOn.convex_epigraph (hf : ConvexOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 } := by
  rintro ⟨x, r⟩ ⟨hx, hr⟩ ⟨y, t⟩ ⟨hy, ht⟩ a b ha hb hab
  refine ⟨hf.1 hx hy ha hb hab, ?_⟩
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
    _ ≤ a • r + b • t := by gcongr

theorem ConcaveOn.convex_hypograph (hf : ConcaveOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1 } :=
  hf.dual.convex_epigraph

theorem convexOn_iff_convex_epigraph :
    ConvexOn 𝕜 s f ↔ Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 } :=
  ⟨ConvexOn.convex_epigraph, convexOn_of_convex_epigraph⟩

theorem concaveOn_iff_convex_hypograph :
    ConcaveOn 𝕜 s f ↔ Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1 } :=
  convexOn_iff_convex_epigraph (β := βᵒᵈ)

end PosSMulMono

section Module

variable [Module 𝕜 E] [SMul 𝕜 β] {s : Set E} {f : E → β}

theorem ConvexOn.translate_right (hf : ConvexOn 𝕜 s f) (c : E) :
    ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  ⟨hf.1.translate_preimage_right _, fun x hx y hy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add, smul_add, add_add_add_comm, Convex.combo_self hab]
      _ ≤ a • f (c + x) + b • f (c + y) := hf.2 hx hy ha hb hab
      ⟩

theorem ConcaveOn.translate_right (hf : ConcaveOn 𝕜 s f) (c : E) :
    ConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  hf.dual.translate_right _

theorem ConvexOn.translate_left (hf : ConvexOn 𝕜 s f) (c : E) :
    ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [add_comm c] using hf.translate_right c

theorem ConcaveOn.translate_left (hf : ConcaveOn 𝕜 s f) (c : E) :
    ConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) :=
  hf.dual.translate_left _

end Module

section Module

variable [Module 𝕜 E] [Module 𝕜 β]

theorem convexOn_iff_forall_pos {s : Set E} {f : E → β} :
    ConvexOn 𝕜 s f ↔ Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b →
      a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y := by
  refine and_congr_right'
    ⟨fun h x hx y hy a b ha hb hab => h hx hy ha.le hb.le hab, fun h x hx y hy a b ha hb hab => ?_⟩
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_add] at hab
    subst b
    simp_rw [zero_smul, zero_add, one_smul, le_rfl]
  obtain rfl | hb' := hb.eq_or_lt
  · rw [add_zero] at hab
    subst a
    simp_rw [zero_smul, add_zero, one_smul, le_rfl]
  exact h hx hy ha' hb' hab

theorem concaveOn_iff_forall_pos {s : Set E} {f : E → β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
        a • f x + b • f y ≤ f (a • x + b • y) :=
  convexOn_iff_forall_pos (β := βᵒᵈ)

theorem convexOn_iff_pairwise_pos {s : Set E} {f : E → β} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        s.Pairwise fun x y =>
          ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y := by
  rw [convexOn_iff_forall_pos]
  refine
    and_congr_right'
      ⟨fun h x hx y hy _ a b ha hb hab => h hx hy ha hb hab, fun h x hx y hy a b ha hb hab => ?_⟩
  obtain rfl | hxy := eq_or_ne x y
  · rw [Convex.combo_self hab, Convex.combo_self hab]
  exact h hx hy hxy ha hb hab

theorem concaveOn_iff_pairwise_pos {s : Set E} {f : E → β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        s.Pairwise fun x y =>
          ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • f x + b • f y ≤ f (a • x + b • y) :=
  convexOn_iff_pairwise_pos (β := βᵒᵈ)

theorem LinearMap.convexOn (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f :=
  ⟨hs, fun _ _ _ _ _ _ _ _ _ => by rw [f.map_add, f.map_smul, f.map_smul]⟩

theorem LinearMap.concaveOn (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s f :=
  ⟨hs, fun _ _ _ _ _ _ _ _ _ => by rw [f.map_add, f.map_smul, f.map_smul]⟩

theorem StrictConvexOn.convexOn {s : Set E} {f : E → β} (hf : StrictConvexOn 𝕜 s f) :
    ConvexOn 𝕜 s f :=
  convexOn_iff_pairwise_pos.mpr
    ⟨hf.1, fun _ hx _ hy hxy _ _ ha hb hab => (hf.2 hx hy hxy ha hb hab).le⟩

theorem StrictConcaveOn.concaveOn {s : Set E} {f : E → β} (hf : StrictConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 s f :=
  hf.dual.convexOn

section PosSMulMono

variable [IsOrderedAddMonoid β] [PosSMulMono 𝕜 β] {s : Set E} {f : E → β}

theorem StrictConvexOn.convex_lt (hf : StrictConvexOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x ∈ s | f x < r }) :=
  convex_iff_pairwise_pos.2 fun x hx y hy hxy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx.1 hy.1 hxy ha hb hab
        _ ≤ a • r + b • r := by
          gcongr
          · exact hx.2.le
          · exact hy.2.le
        _ = r := Convex.combo_self hab r
        ⟩

theorem StrictConcaveOn.convex_gt (hf : StrictConcaveOn 𝕜 s f) (r : β) :
    Convex 𝕜 ({ x ∈ s | r < f x }) :=
  hf.dual.convex_lt r

end PosSMulMono

section LinearOrder

variable [LinearOrder E] {s : Set E} {f : E → β}

theorem LinearOrder.convexOn_of_lt (hs : Convex 𝕜 s)
    (hf : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) ≤ a • f x + b • f y) :
    ConvexOn 𝕜 s f := by
  refine convexOn_iff_pairwise_pos.2 ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  wlog h : x < y
  · rw [add_comm (a • x), add_comm (a • f x)]
    rw [add_comm] at hab
    exact this hs hf y hy x hx hxy.symm b a hb ha hab (hxy.lt_or_gt.resolve_left h)
  exact hf hx hy h ha hb hab

theorem LinearOrder.concaveOn_of_lt (hs : Convex 𝕜 s)
    (hf : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
      a • f x + b • f y ≤ f (a • x + b • y)) :
    ConcaveOn 𝕜 s f :=
  LinearOrder.convexOn_of_lt (β := βᵒᵈ) hs hf

theorem LinearOrder.strictConvexOn_of_lt (hs : Convex 𝕜 s)
    (hf : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
      f (a • x + b • y) < a • f x + b • f y) :
    StrictConvexOn 𝕜 s f := by
  refine ⟨hs, fun x hx y hy hxy a b ha hb hab => ?_⟩
  wlog h : x < y
  · rw [add_comm (a • x), add_comm (a • f x)]
    rw [add_comm] at hab
    exact this hs hf y hy x hx hxy.symm b a hb ha hab (hxy.lt_or_gt.resolve_left h)
  exact hf hx hy h ha hb hab

theorem LinearOrder.strictConcaveOn_of_lt (hs : Convex 𝕜 s)
    (hf : ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 →
      a • f x + b • f y < f (a • x + b • y)) :
    StrictConcaveOn 𝕜 s f :=
  LinearOrder.strictConvexOn_of_lt (β := βᵒᵈ) hs hf

end LinearOrder

end Module

section Module

variable [Module 𝕜 E] [Module 𝕜 F] [SMul 𝕜 β]

theorem ConvexOn.comp_linearMap {f : F → β} {s : Set F} (hf : ConvexOn 𝕜 s f) (g : E →ₗ[𝕜] F) :
    ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  ⟨hf.1.linear_preimage _, fun x hx y hy a b ha hb hab =>
    calc
      f (g (a • x + b • y)) = f (a • g x + b • g y) := by rw [g.map_add, g.map_smul, g.map_smul]
      _ ≤ a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab⟩

theorem ConcaveOn.comp_linearMap {f : F → β} {s : Set F} (hf : ConcaveOn 𝕜 s f) (g : E →ₗ[𝕜] F) :
    ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  hf.dual.comp_linearMap g

end Module

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [AddCommMonoid β] [PartialOrder β] [IsOrderedCancelAddMonoid β]

section DistribMulAction

variable [SMul 𝕜 E] [DistribMulAction 𝕜 β] {s : Set E} {f g : E → β}

theorem StrictConvexOn.add_convexOn (hf : StrictConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add_of_lt_of_le (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy ha.le hb.le hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]⟩

theorem ConvexOn.add_strictConvexOn (hf : ConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f + g) :=
  add_comm g f ▸ hg.add_convexOn hf

theorem StrictConvexOn.add (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x hx y hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy hxy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by rw [smul_add, smul_add, add_add_add_comm]⟩

theorem StrictConcaveOn.add_concaveOn (hf : StrictConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add_convexOn hg.dual

theorem ConcaveOn.add_strictConcaveOn (hf : ConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add_strictConvexOn hg.dual

theorem StrictConcaveOn.add (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add hg

theorem StrictConvexOn.add_const {γ : Type*} {f : E → γ}
    [AddCommMonoid γ] [PartialOrder γ] [IsOrderedCancelAddMonoid γ]
    [Module 𝕜 γ] (hf : StrictConvexOn 𝕜 s f) (b : γ) : StrictConvexOn 𝕜 s (f + fun _ => b) :=
  hf.add_convexOn (convexOn_const _ hf.1)

theorem StrictConcaveOn.add_const {γ : Type*} {f : E → γ}
    [AddCommMonoid γ] [PartialOrder γ] [IsOrderedCancelAddMonoid γ]
    [Module 𝕜 γ] (hf : StrictConcaveOn 𝕜 s f) (b : γ) : StrictConcaveOn 𝕜 s (f + fun _ => b) :=
  hf.add_concaveOn (concaveOn_const _ hf.1)

end DistribMulAction

section Module

variable [Module 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E} {f : E → β}

theorem ConvexOn.convex_lt (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | f x < r }) :=
  convex_iff_forall_pos.2 fun x hx y hy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx.1 hy.1 ha.le hb.le hab
        _ < a • r + b • r :=
          (add_lt_add_of_lt_of_le (smul_lt_smul_of_pos_left hx.2 ha)
            (smul_le_smul_of_nonneg_left hy.2.le hb.le))
        _ = r := Convex.combo_self hab _⟩

theorem ConcaveOn.convex_gt (hf : ConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | r < f x }) :=
  hf.dual.convex_lt r

theorem ConvexOn.openSegment_subset_strict_epigraph (hf : ConvexOn 𝕜 s f) (p q : E × β)
    (hp : p.1 ∈ s ∧ f p.1 < p.2) (hq : q.1 ∈ s ∧ f q.1 ≤ q.2) :
    openSegment 𝕜 p q ⊆ { p : E × β | p.1 ∈ s ∧ f p.1 < p.2 } := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨hf.1 hp.1 hq.1 ha.le hb.le hab, ?_⟩
  calc
    f (a • p.1 + b • q.1) ≤ a • f p.1 + b • f q.1 := hf.2 hp.1 hq.1 ha.le hb.le hab
    _ < a • p.2 + b • q.2 := add_lt_add_of_lt_of_le
       (smul_lt_smul_of_pos_left hp.2 ha) (smul_le_smul_of_nonneg_left hq.2 hb.le)

theorem ConcaveOn.openSegment_subset_strict_hypograph (hf : ConcaveOn 𝕜 s f) (p q : E × β)
    (hp : p.1 ∈ s ∧ p.2 < f p.1) (hq : q.1 ∈ s ∧ q.2 ≤ f q.1) :
    openSegment 𝕜 p q ⊆ { p : E × β | p.1 ∈ s ∧ p.2 < f p.1 } :=
  hf.dual.openSegment_subset_strict_epigraph p q hp hq

theorem ConvexOn.convex_strict_epigraph [ZeroLEOneClass 𝕜] (hf : ConvexOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 < p.2 } :=
  convex_iff_openSegment_subset.mpr fun p hp q hq =>
    hf.openSegment_subset_strict_epigraph p q hp ⟨hq.1, hq.2.le⟩

theorem ConcaveOn.convex_strict_hypograph [ZeroLEOneClass 𝕜] (hf : ConcaveOn 𝕜 s f) :
    Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 < f p.1 } :=
  hf.dual.convex_strict_epigraph

end Module

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
  [SMul 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E}
  {f g : E → β}

theorem ConvexOn.sup (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f ⊔ g) := by
  refine ⟨hf.left, fun x hx y hy a b ha hb hab => sup_le ?_ ?_⟩
  · calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.right hx hy ha hb hab
      _ ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_left
  · calc
      g (a • x + b • y) ≤ a • g x + b • g y := hg.right hx hy ha hb hab
      _ ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_right

theorem ConcaveOn.inf (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 s (f ⊓ g) :=
  hf.dual.sup hg

theorem StrictConvexOn.sup (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f ⊔ g) :=
  ⟨hf.left, fun x hx y hy hxy a b ha hb hab =>
    max_lt
      (calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
        _ ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_left)
      (calc
        g (a • x + b • y) < a • g x + b • g y := hg.2 hx hy hxy ha hb hab
        _ ≤ a • (f x ⊔ g x) + b • (f y ⊔ g y) := by gcongr <;> apply le_sup_right)⟩

theorem StrictConcaveOn.inf (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f ⊓ g) :=
  hf.dual.sup hg

theorem ConvexOn.le_on_segment' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {a b : 𝕜}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : f (a • x + b • y) ≤ max (f x) (f y) :=
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
    _ ≤ a • max (f x) (f y) + b • max (f x) (f y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = max (f x) (f y) := Convex.combo_self hab _

theorem ConcaveOn.ge_on_segment' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : min (f x) (f y) ≤ f (a • x + b • y) :=
  hf.dual.le_on_segment' hx hy ha hb hab

theorem ConvexOn.le_on_segment (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ [x -[𝕜] y]) : f z ≤ max (f x) (f y) :=
  let ⟨_, _, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.le_on_segment' hx hy ha hb hab

theorem ConcaveOn.ge_on_segment (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ [x -[𝕜] y]) : min (f x) (f y) ≤ f z :=
  hf.dual.le_on_segment hx hy hz

theorem StrictConvexOn.lt_on_open_segment' (hf : StrictConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    f (a • x + b • y) < max (f x) (f y) :=
  calc
    f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
    _ ≤ a • max (f x) (f y) + b • max (f x) (f y) := by
      gcongr
      · apply le_max_left
      · apply le_max_right
    _ = max (f x) (f y) := Convex.combo_self hab _

theorem StrictConcaveOn.lt_on_open_segment' (hf : StrictConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    min (f x) (f y) < f (a • x + b • y) :=
  hf.dual.lt_on_open_segment' hx hy hxy ha hb hab

theorem StrictConvexOn.lt_on_openSegment (hf : StrictConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) (hz : z ∈ openSegment 𝕜 x y) : f z < max (f x) (f y) :=
  let ⟨_, _, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.lt_on_open_segment' hx hy hxy ha hb hab

theorem StrictConcaveOn.lt_on_openSegment (hf : StrictConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s)
    (hy : y ∈ s) (hxy : x ≠ y) (hz : z ∈ openSegment 𝕜 x y) : min (f x) (f y) < f z :=
  hf.dual.lt_on_openSegment hx hy hxy hz

end LinearOrderedAddCommMonoid

section LinearOrderedCancelAddCommMonoid

variable [AddCommMonoid β] [LinearOrder β] [IsOrderedCancelAddMonoid β]

section PosSMulStrictMono

variable [SMul 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E} {f g : E → β}

theorem ConvexOn.le_left_of_right_le' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) (hfy : f y ≤ f (a • x + b • y)) :
    f (a • x + b • y) ≤ f x :=
  le_of_not_gt fun h ↦ lt_irrefl (f (a • x + b • y)) <|
    calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha.le hb hab
      _ < a • f (a • x + b • y) + b • f (a • x + b • y) := add_lt_add_of_lt_of_le
          (smul_lt_smul_of_pos_left h ha) (smul_le_smul_of_nonneg_left hfy hb)
      _ = f (a • x + b • y) := Convex.combo_self hab _

theorem ConcaveOn.left_le_of_le_right' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) (hfy : f (a • x + b • y) ≤ f y) :
    f x ≤ f (a • x + b • y) :=
  hf.dual.le_left_of_right_le' hx hy ha hb hab hfy

theorem ConvexOn.le_right_of_left_le' (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s)
    (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) (hfx : f x ≤ f (a • x + b • y)) :
    f (a • x + b • y) ≤ f y := by
  rw [add_comm] at hab hfx ⊢
  exact hf.le_left_of_right_le' hy hx hb ha hab hfx

theorem ConcaveOn.right_le_of_le_left' (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s)
    (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) (hfx : f (a • x + b • y) ≤ f x) :
    f y ≤ f (a • x + b • y) :=
  hf.dual.le_right_of_left_le' hx hy ha hb hab hfx

theorem ConvexOn.le_left_of_right_le (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hyz : f y ≤ f z) : f z ≤ f x := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_left_of_right_le' hx hy ha hb.le hab hyz

theorem ConcaveOn.left_le_of_le_right (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hyz : f z ≤ f y) : f x ≤ f z :=
  hf.dual.le_left_of_right_le hx hy hz hyz

theorem ConvexOn.le_right_of_left_le (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hxz : f x ≤ f z) : f z ≤ f y := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_right_of_left_le' hx hy ha.le hb hab hxz

theorem ConcaveOn.right_le_of_le_left (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hxz : f z ≤ f x) : f y ≤ f z :=
  hf.dual.le_right_of_left_le hx hy hz hxz

end PosSMulStrictMono

section Module

variable [Module 𝕜 E] [Module 𝕜 β] [PosSMulStrictMono 𝕜 β] {s : Set E} {f g : E → β}

theorem ConvexOn.lt_left_of_right_lt' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f y < f (a • x + b • y)) :
    f (a • x + b • y) < f x :=
  not_le.1 fun h ↦ lt_irrefl (f (a • x + b • y)) <|
    calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha.le hb.le hab
      _ < a • f (a • x + b • y) + b • f (a • x + b • y) := add_lt_add_of_le_of_lt
          (smul_le_smul_of_nonneg_left h ha.le) (smul_lt_smul_of_pos_left hfy hb)
      _ = f (a • x + b • y) := Convex.combo_self hab _

theorem ConcaveOn.left_lt_of_lt_right' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f (a • x + b • y) < f y) :
    f x < f (a • x + b • y) :=
  hf.dual.lt_left_of_right_lt' hx hy ha hb hab hfy

theorem ConvexOn.lt_right_of_left_lt' (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s)
    (hy : y ∈ s) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f x < f (a • x + b • y)) :
    f (a • x + b • y) < f y := by
  rw [add_comm] at hab hfx ⊢
  exact hf.lt_left_of_right_lt' hy hx hb ha hab hfx

theorem ConcaveOn.lt_right_of_left_lt' (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s)
    (hy : y ∈ s) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f (a • x + b • y) < f x) :
    f y < f (a • x + b • y) :=
  hf.dual.lt_right_of_left_lt' hx hy ha hb hab hfx

theorem ConvexOn.lt_left_of_right_lt (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hyz : f y < f z) : f z < f x := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_left_of_right_lt' hx hy ha hb hab hyz

theorem ConcaveOn.left_lt_of_lt_right (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hyz : f z < f y) : f x < f z :=
  hf.dual.lt_left_of_right_lt hx hy hz hyz

theorem ConvexOn.lt_right_of_left_lt (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hxz : f x < f z) : f z < f y := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_right_of_left_lt' hx hy ha hb hab hxz

theorem ConcaveOn.lt_right_of_left_lt (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ openSegment 𝕜 x y) (hxz : f z < f x) : f y < f z :=
  hf.dual.lt_right_of_left_lt hx hy hz hxz

end Module

end LinearOrderedCancelAddCommMonoid

section OrderedAddCommGroup

variable [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β] [SMul 𝕜 E] [Module 𝕜 β]
  {s : Set E} {f g : E → β}
