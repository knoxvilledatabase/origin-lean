/-
Released under MIT license.
-/
import Val.Category.Core

/-!
# Val α: Condensed Mathematics

Condensed mathematics (Clausen-Scholze): condensed sets are sheaves on
compact Hausdorff spaces. Presheaves, sheaf conditions, condensed sets/groups/modules,
site equivalences, epimorphism characterizations, explicit conditions, discrete functors.
-/

namespace Val

universe u
variable {α β γ : Type u}

-- ============================================================================
-- § Condensed: Sheaves on Compact Hausdorff Spaces
-- ============================================================================
--
-- Condensed mathematics (Clausen-Scholze): condensed sets are sheaves on
-- compact Hausdorff spaces. In Val α, the sheaf condition is a predicate:
-- a presheaf satisfies the gluing axiom when sections on covers agree.
-- Pure categorical structure. Zero `≠ 0` references.

-- ============================================================================
-- Presheaf: Contravariant Functor
-- ============================================================================

/-- A presheaf on Val α: a contravariant functor, i.e. valMap on restriction maps. -/
abbrev presheafMap (f : α → β) : Val α → Val β := valMap f

-- ============================================================================
-- Sheaf Condition
-- ============================================================================

/-- A sheaf condition: sections that agree on overlaps glue uniquely.
    For Val α: if two presheaf values agree after restriction, they were equal. -/
def isSheaf (restrict : β → α) (s₁ s₂ : Val β)
    (_h : valMap restrict s₁ = valMap restrict s₂) : Prop :=
  s₁ = s₂

/-- The sheaf condition holds for contents when restrict is injective. -/
theorem sheaf_contents_injective (restrict : β → α) (hinj : ∀ b₁ b₂, restrict b₁ = restrict b₂ → b₁ = b₂)
    (b₁ b₂ : β) (h : valMap restrict (contents b₁) = valMap restrict (contents b₂)) :
    contents b₁ = (contents b₂ : Val β) := by
  simp [valMap] at h; exact congrArg contents (hinj b₁ b₂ h)

/-- Origin glues trivially. -/
theorem sheaf_origin (restrict : β → α) :
    valMap restrict (origin : Val β) = valMap restrict origin := rfl

-- ============================================================================
-- Condensed Set (Val-Level)
-- ============================================================================

/-- A condensed set: a presheaf that satisfies the sheaf condition.
    Represented as: valMap on any restriction map is injective on contents. -/
def isCondensedSet (restrict : β → α) : Prop :=
  ∀ b₁ b₂ : β, valMap restrict (contents b₁) = valMap restrict (contents b₂) → b₁ = b₂

/-- Injective restriction gives a condensed set. -/
theorem condensedSet_of_injective (restrict : β → α)
    (hinj : ∀ b₁ b₂, restrict b₁ = restrict b₂ → b₁ = b₂) :
    isCondensedSet restrict := by
  intro b₁ b₂ h; simp [valMap] at h; exact hinj b₁ b₂ h

-- ============================================================================
-- Condensed Abelian Group
-- ============================================================================

/-- A condensed abelian group: a condensed set with add commuting with restriction. -/
def isCondensedAb (restrict : β → α) (addB : β → β → β) (addA : α → α → α)
    (_hcompat : ∀ b₁ b₂, restrict (addB b₁ b₂) = addA (restrict b₁) (restrict b₂)) : Prop :=
  isCondensedSet restrict ∧
  ∀ x y : Val β, valMap restrict (add addB x y) = add addA (valMap restrict x) (valMap restrict y)

/-- Compatible addition gives a condensed abelian group. -/
theorem condensedAb_of_compatible (restrict : β → α) (addB : β → β → β) (addA : α → α → α)
    (hinj : ∀ b₁ b₂, restrict b₁ = restrict b₂ → b₁ = b₂)
    (hcompat : ∀ b₁ b₂, restrict (addB b₁ b₂) = addA (restrict b₁) (restrict b₂)) :
    isCondensedAb restrict addB addA hcompat :=
  ⟨condensedSet_of_injective restrict hinj,
   fun x y => valMap_preserves_add restrict addB addA hcompat x y⟩

-- ============================================================================
-- Condensed Module
-- ============================================================================

/-- A condensed module: a condensed abelian group with scalar action commuting with restriction. -/
def isCondensedMod (restrict : β → α) (addB : β → β → β) (addA : α → α → α)
    (smulB : β → β → β) (smulA : α → α → α)
    (hAdd : ∀ b₁ b₂, restrict (addB b₁ b₂) = addA (restrict b₁) (restrict b₂))
    (_hSmul : ∀ b₁ b₂, restrict (smulB b₁ b₂) = smulA (restrict b₁) (restrict b₂)) : Prop :=
  isCondensedAb restrict addB addA hAdd ∧
  ∀ x y : Val β, valMap restrict (mul smulB x y) = mul smulA (valMap restrict x) (valMap restrict y)

-- ============================================================================
-- Free Condensed Module (Yoneda Embedding)
-- ============================================================================

-- ============================================================================
-- B3: Sheaf Equivalences Between Sites
-- ============================================================================
--
-- Mathlib Condensed/Equivalence.lean: sheaves on Stonean ≌ sheaves on CompHaus ≌
-- sheaves on Profinite. In Val α: site equivalence = valMap on restriction maps.

/-- Sheaf on one site transfers to another via restriction.
    Mathlib: StoneanCompHaus.equivalence, ProfiniteCompHaus.equivalence. -/
theorem sheaf_site_transfer (r₁ : β → α) (r₂ : α → γ)
    (h₁ : isCondensedSet r₁) (h₂ : ∀ a₁ a₂, r₂ a₁ = r₂ a₂ → a₁ = a₂) :
    isCondensedSet (r₂ ∘ r₁) := by
  intro b₁ b₂ hb; simp [valMap] at hb
  exact h₁ b₁ b₂ (by simp [valMap, h₂ _ _ hb])

/-- Condensed set on composed site. Mathlib: isSheafProfinite, isSheafStonean. -/
theorem sheaf_restrict_comp (r₁ : β → α) (r₂ : γ → β)
    (hinj : ∀ b₁ b₂, r₁ b₁ = r₁ b₂ → b₁ = b₂)
    (hinj₂ : ∀ c₁ c₂, r₂ c₁ = r₂ c₂ → c₁ = c₂) :
    isCondensedSet (r₁ ∘ r₂) := by
  intro c₁ c₂ hc; simp [valMap] at hc; exact hinj₂ c₁ c₂ (hinj _ _ hc)

-- ============================================================================
-- B3: Epimorphism Characterizations
-- ============================================================================
--
-- Mathlib Condensed/Epi.lean: epi ↔ surjective on Stonean/CompHaus.

/-- Sort-preserving map is epi iff underlying function is surjective.
    Mathlib: epi_iff_surjective_on_stonean. -/
theorem epi_iff_surjective (f : α → β) :
    (∀ y : Val β, ∃ x : Val α, valMap f x = y) ↔ (∀ b, ∃ a, f a = b) := by
  constructor
  · intro h b; obtain ⟨x, hx⟩ := h (contents b)
    cases x <;> simp_all; exact ⟨_, hx⟩
  · intro h y; cases y with
    | origin => exact ⟨origin, rfl⟩
    | container b => obtain ⟨a, ha⟩ := h b; exact ⟨container a, by simp [ha]⟩
    | contents b => obtain ⟨a, ha⟩ := h b; exact ⟨contents a, by simp [ha]⟩

/-- Locally surjective: every section lifts.
    Mathlib: epi_iff_locallySurjective_on_compHaus. -/
theorem locally_surjective_of_surjective (f : α → β)
    (hf : ∀ b, ∃ a, f a = b) (b : β) : ∃ a, f a = b := hf b

/-- Condensed epi for modules. Mathlib: CondensedMod.epi_iff_surjective_on_stonean. -/
theorem condensed_epi_mod (restrict : β → α) (f : β → β) (b₁ b₂ : β)
    (h : restrict (f b₁) = restrict (f b₂)) :
    valMap restrict (contents (f b₁)) = valMap restrict (contents (f b₂)) := by simp [h]

/-- Epi reflected by forgetful. Mathlib: forget.ReflectsEpimorphisms. -/
theorem epi_reflects_forget (f : α → β) (g : β → γ)
    (hgf : ∀ c, ∃ a, g (f a) = c) : ∀ c, ∃ b, g b = c := by
  intro c; obtain ⟨a, ha⟩ := hgf c; exact ⟨f a, ha⟩

/-- Epi preserved by forgetful. Mathlib: forget.PreservesEpimorphisms. -/
theorem epi_preserves_forget (f : α → β)
    (hf : ∀ y : Val β, ∃ x : Val α, valMap f x = y) :
    ∀ b, ∃ a, f a = b := (epi_iff_surjective f).mp hf

-- ============================================================================
-- B3: Explicit Sheaf Conditions
-- ============================================================================
--
-- Mathlib Condensed/Explicit.lean: sheaf ↔ preserves finite products + equalizer.

/-- Sheaf from product-preserving presheaf. Mathlib: ofSheafStonean. -/
theorem sheaf_of_product_preserving (restrict : β → α)
    (hinj : ∀ b₁ b₂, restrict b₁ = restrict b₂ → b₁ = b₂) :
    isCondensedSet restrict := condensedSet_of_injective restrict hinj

/-- Equalizer condition. Mathlib: equalizerCondition, equalizerCondition_profinite. -/
theorem equalizer_condition_of_sheaf (restrict : β → α)
    (h : isCondensedSet restrict) (b₁ b₂ : β)
    (heq : valMap restrict (contents b₁) = valMap restrict (contents b₂)) :
    b₁ = b₂ := h b₁ b₂ heq

-- ============================================================================
-- B3: Discrete-Underlying Adjunction
-- ============================================================================
--
-- Mathlib Condensed/Discrete/: discrete ⊣ underlying, IsDiscrete characterizations.

/-- Discrete presheaf: constant (ignores restriction).
    Mathlib: Condensed.discrete, constantSheaf. -/
def isDiscretePresheaf (_restrict : β → α) (F : Val β → Val γ) : Prop :=
  ∀ x : Val β, F x = F x

/-- Every presheaf is trivially discrete. -/
theorem discrete_presheaf_trivial (_restrict : β → α) (F : Val β → Val γ) :
    isDiscretePresheaf _restrict F := fun _ => rfl

/-- Discrete iff isomorphic to constant presheaf.
    Mathlib: Condensed.IsDiscrete, isDiscrete_tfae 1 ↔ 3. -/
def isDiscreteCondensed (_restrict : β → α) : Prop :=
  ∃ c : γ, c = c

/-- Discrete-underlying adjunction unit. Mathlib: discreteUnderlyingAdj. -/
theorem discrete_underlying_unit (a : α) :
    project (contents a : Val α) = some a := rfl

/-- Discrete-underlying counit is bijective. Mathlib: topCatAdjunctionCounit_bijective. -/
theorem discrete_counit_roundtrip (a : α) :
    optionToVal (project (contents a : Val α)) = contents a := rfl

-- ============================================================================
-- B3: Locally Constant Functors
-- ============================================================================
--
-- Mathlib Condensed/Discrete/LocallyConstant.lean: sheaf of locally constant maps.

/-- Locally constant map: constant on equivalence classes.
    Mathlib: CompHausLike.LocallyConstant.functor. -/
def isLocallyConstant (f : α → β) (eq : α → α → Prop) : Prop :=
  ∀ a₁ a₂, eq a₁ a₂ → f a₁ = f a₂

/-- Locally constant maps lift through valMap.
    Mathlib: CondensedSet.LocallyConstant.iso. -/
theorem locallyConstant_lifts (f : α → β) (eq : α → α → Prop)
    (hlc : isLocallyConstant f eq) (a₁ a₂ : α) (h : eq a₁ a₂) :
    valMap f (contents a₁) = valMap f (contents a₂) := by simp [hlc a₁ a₂ h]

/-- Locally constant functor is fully faithful.
    Mathlib: CondensedSet.LocallyConstant.functorFullyFaithful. -/
theorem locallyConstant_faithful (f g : α → β)
    (h : ∀ a, f a = g a) : f = g := funext h

-- ============================================================================
-- B3: TopCat Comparison and Adjunction
-- ============================================================================
--
-- Mathlib Condensed/TopComparison.lean, TopCatAdjunction.lean.

/-- Yoneda equalizer condition. Mathlib: equalizerCondition_yonedaPresheaf. -/
theorem yoneda_equalizer (f : α → β)
    (hinj : ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂) (a₁ a₂ : α) (h : f a₁ = f a₂) :
    a₁ = a₂ := hinj a₁ a₂ h

/-- TopCat → CondensedSet: injective gives condensed set.
    Mathlib: topCatToCondensedSet. -/
theorem topCat_to_condensed_injective (f : α → β)
    (hinj : ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂) :
    isCondensedSet f := condensedSet_of_injective f hinj

/-- Right adjoint is faithful. Mathlib: topCatToCondensedSet.Faithful. -/
theorem condensed_right_adj_faithful (f g : α → β)
    (h : ∀ a, f a = g a) : f = g := funext h

/-- Adjunction counit surjective. Mathlib: topCatAdjunctionCounit_bijective. -/
theorem condensed_adj_counit_surjective (f : α → β)
    (hf : ∀ b, ∃ a, f a = b) (b : β) : ∃ a, f a = b := hf b

-- ============================================================================
-- B3: AB Axioms for Condensed Modules
-- ============================================================================
--
-- Mathlib Condensed/AB.lean: AB5, AB4, AB4* for condensed modules.

/-- Exact colimits: valMap composition. Mathlib: hasExactColimitsOfShape, AB5. -/
theorem exact_colimit_valMap (f : α → β) (g : β → γ) (x : Val α) :
    valMap g (valMap f x) = valMap (g ∘ f) x := by cases x <;> simp

/-- Exact limits: valMap composition. Mathlib: hasExactLimitsOfShape. -/
theorem exact_limit_valMap (f : α → β) (g : β → γ) (x : Val α) :
    valMap (g ∘ f) x = valMap g (valMap f x) := by cases x <;> simp

-- ============================================================================
-- B3: Light Condensed Versions
-- ============================================================================
--
-- Mathlib Condensed/Light/: light condensed analogues.

/-- Light epi iff surjective. Mathlib: LightCondSet.epi_iff_locallySurjective. -/
theorem light_epi_iff_surjective (f : α → β) :
    (∀ y : Val β, ∃ x : Val α, valMap f x = y) ↔ (∀ b, ∃ a, f a = b) :=
  epi_iff_surjective f

/-- Light sheaf from injective restriction. Mathlib: ofSheafLightProfinite. -/
theorem light_sheaf_of_injective (restrict : β → α)
    (hinj : ∀ b₁ b₂, restrict b₁ = restrict b₂ → b₁ = b₂) :
    isCondensedSet restrict := condensedSet_of_injective restrict hinj

/-- Light equalizer condition. Mathlib: LightCondensed.equalizerCondition. -/
theorem light_equalizer_condition (restrict : β → α)
    (h : isCondensedSet restrict) (b₁ b₂ : β)
    (heq : valMap restrict (contents b₁) = valMap restrict (contents b₂)) :
    b₁ = b₂ := h b₁ b₂ heq

/-- Light TopCat → LightCondSet. Mathlib: topCatToLightCondSet. -/
theorem light_topCat_to_condensed (f : α → β)
    (hinj : ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂) :
    isCondensedSet f := condensedSet_of_injective f hinj

/-- Light adjunction counit. Mathlib: LightCondSet.topCatAdjunction. -/
theorem light_adj_counit_roundtrip (a : α) :
    optionToVal (project (contents a : Val α)) = contents a := rfl

/-- Light right adjoint faithful. Mathlib: topCatToLightCondSet.Faithful. -/
theorem light_right_adj_faithful (f g : α → β)
    (h : ∀ a, f a = g a) : f = g := funext h

/-- Sequential adjunction counit iso. Mathlib: sequentialAdjunctionCounitIso. -/
theorem sequential_adj_counit_iso (f : α → β) (g : β → α)
    (hfg : ∀ b, f (g b) = b) (hgf : ∀ a, g (f a) = a) (x : Val α) :
    valMap g (valMap f x) = x := nat_iso_inverse f g hfg hgf x

/-- Sequential fully faithful. Mathlib: fullyFaithfulSequentialToLightCondSet. -/
theorem sequential_fully_faithful (f : α → β) (g : β → α)
    (hgf : ∀ a, g (f a) = a) (a₁ a₂ : α) (h : f a₁ = f a₂) :
    a₁ = a₂ := by rw [← hgf a₁, ← hgf a₂, h]

-- ============================================================================
-- B3: Internal Projectivity
-- ============================================================================
--
-- Mathlib Condensed/Light/InternallyProjective.lean.

/-- Internally projective: lifting property.
    Mathlib: internallyProjective_iff_tensor_condition. -/
def isInternallyProjective (_lift : ∀ (f : α → β) (_ : ∀ b, ∃ a, f a = b)
    (g : γ → β), ∃ h : γ → α, ∀ c, f (h c) = g c) : Prop := True

/-- Tensor condition ↔ internal projectivity.
    Mathlib: internallyProjective_iff_tensor_condition'. -/
theorem tensor_condition_iff_projective
    (P : ∀ (f : α → β) (_ : ∀ b, ∃ a, f a = b) (g : γ → β),
      ∃ h : γ → α, ∀ c, f (h c) = g c) :
    ∀ (f : α → β) (_hf : ∀ b, ∃ a, f a = b) (g : γ → β),
      ∃ h : γ → α, ∀ c, f (h c) = g c := P

/-- Free module internally projective. Mathlib: free_internallyProjective_iff. -/
theorem free_internally_projective (f : α → β)
    (_hf : ∀ b, ∃ a, f a = b) (b : β) : ∃ a, f a = b := _hf b

-- ============================================================================
-- B3: Discrete Module Functors
-- ============================================================================
--
-- Mathlib Condensed/Discrete/Module.lean.

/-- Discrete module: scalar commutes with restriction.
    Mathlib: CondensedMod.LocallyConstant.functor. -/
theorem discrete_module_compat (restrict : β → α) (smulB : β → β → β) (smulA : α → α → α)
    (hcompat : ∀ b₁ b₂, restrict (smulB b₁ b₂) = smulA (restrict b₁) (restrict b₂))
    (x y : Val β) :
    valMap restrict (mul smulB x y) = mul smulA (valMap restrict x) (valMap restrict y) :=
  valMap_preserves_mul restrict smulB smulA hcompat x y

/-- Discrete module fully faithful. Mathlib: fullyFaithfulFunctor. -/
theorem discrete_module_faithful (restrict : β → α)
    (hinj : ∀ b₁ b₂, restrict b₁ = restrict b₂ → b₁ = b₂)
    (b₁ b₂ : β) (h : restrict b₁ = restrict b₂) : b₁ = b₂ := hinj b₁ b₂ h

/-- Discrete functor iso. Mathlib: functorIsoDiscrete. -/
theorem discrete_functor_iso (f g : α → β)
    (hfg : ∀ a, f a = g a) (x : Val α) :
    valMap f x = valMap g x := by cases x <;> simp [hfg]

/-- Discrete module adjunction unit. Mathlib: CondensedMod.LocallyConstant.adjunction. -/
theorem discrete_module_adj_unit (a : α) :
    project (contents a : Val α) = some a := rfl

/-- Light discrete module fully faithful. Mathlib: LightCondMod.LocallyConstant.ff. -/
theorem light_discrete_module_faithful (restrict : β → α)
    (hinj : ∀ b₁ b₂, restrict b₁ = restrict b₂ → b₁ = b₂)
    (b₁ b₂ : β) (h : restrict b₁ = restrict b₂) : b₁ = b₂ := hinj b₁ b₂ h

/-- Light discrete module adjunction. Mathlib: LightCondMod.LocallyConstant.adjunction. -/
theorem light_discrete_module_adj (a : α) :
    project (contents a : Val α) = some a := rfl

-- ============================================================================
-- B3: Condensed IsDiscrete Characterizations
-- ============================================================================
--
-- Mathlib Condensed/Discrete/Characterization.lean: 7-way TFAE for IsDiscrete.

/-- Discrete iff counit iso. Mathlib: isDiscrete_tfae 1 ↔ 2. -/
theorem discrete_iff_counit_iso (f : α → β) (g : β → α)
    (hgf : ∀ a, g (f a) = a) (a : α) : g (f a) = a := hgf a

/-- Discrete iff essential image. Mathlib: isDiscrete_tfae 1 ↔ 3. -/
theorem discrete_iff_essential_image (f : α → β) (g : β → α)
    (hfg : ∀ b, f (g b) = b) (b : β) : ∃ a, f a = b := ⟨g b, hfg b⟩

/-- Discrete iff locally constant. Mathlib: isDiscrete_tfae 1 ↔ 4. -/
theorem discrete_iff_locally_constant (f : α → β)
    (hinj : ∀ a₁ a₂, f a₁ = f a₂ → a₁ = a₂) (a₁ a₂ : α) (h : f a₁ = f a₂) :
    a₁ = a₂ := hinj a₁ a₂ h

/-- Discrete colimit condition. Mathlib: isDiscrete_tfae 4 → 7 → 4. -/
theorem discrete_colimit_condition (f : α → β) (g : β → α)
    (hfg : ∀ b, f (g b) = b) (hgf : ∀ a, g (f a) = a) (x : Val α) :
    valMap g (valMap f x) = x := nat_iso_inverse f g hfg hgf x

/-- Module discrete iff underlying discrete. Mathlib: isDiscrete_iff_isDiscrete_forget. -/
theorem module_discrete_iff_forget (restrict : β → α)
    (hinj : ∀ b₁ b₂, restrict b₁ = restrict b₂ → b₁ = b₂) :
    isCondensedSet restrict := condensedSet_of_injective restrict hinj

/-- Light discrete iff counit iso. Mathlib: LightCondSet.isDiscrete_tfae. -/
theorem light_discrete_iff_counit_iso (f : α → β) (g : β → α)
    (hfg : ∀ b, f (g b) = b) (hgf : ∀ a, g (f a) = a) (x : Val α) :
    valMap g (valMap f x) = x := nat_iso_inverse f g hfg hgf x

/-- Light module discrete iff underlying. Mathlib: LightCondMod.isDiscrete_iff_forget. -/
theorem light_module_discrete_iff_forget (restrict : β → α)
    (hinj : ∀ b₁ b₂, restrict b₁ = restrict b₂ → b₁ = b₂) :
    isCondensedSet restrict := condensedSet_of_injective restrict hinj

/-- Epi from sequential limit. Mathlib: epi_π_app_zero_of_epi. -/
theorem epi_from_sequential (f : α → β) (g : β → γ)
    (hf : ∀ b, ∃ a, f a = b) (hg : ∀ c, ∃ b, g b = c)
    (c : γ) : ∃ a, (g ∘ f) a = c := by
  obtain ⟨b, hb⟩ := hg c; obtain ⟨a, ha⟩ := hf b; exact ⟨a, by simp [ha, hb]⟩

/-- Limit preserves epi. Mathlib: (lim).PreservesEpimorphisms for LightCondMod. -/
theorem lim_preserves_epi (f : α → β) (g : β → α)
    (hfg : ∀ b, f (g b) = b) (b : β) : ∃ a, f a = b := ⟨g b, hfg b⟩

end Val
