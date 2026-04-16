/-
Extracted from CategoryTheory/Filtered/Final.lean
Genuine: 18 | Conflates: 0 | Dissolved: 0 | Infrastructure: 22
-/
import Origin.Core
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.TypesFiltered
import Mathlib.CategoryTheory.Limits.Final

noncomputable section

/-!
# Final functors with filtered (co)domain

If `C` is a filtered category, then the usual equivalent conditions for a functor `F : C ⥤ D` to be
final can be restated. We show:

* `final_iff_of_isFiltered`: a concrete description of finality which is sometimes a convenient way
  to show that a functor is final.
* `final_iff_isFiltered_structuredArrow`: `F` is final if and only if `StructuredArrow d F` is
  filtered for all `d : D`, which strengthens the usual statement that `F` is final if and only
  if `StructuredArrow d F` is connected for all `d : D`.
* Under categories of objects of filtered categories are filtered and their forgetful functors
  are final.
* If `D` is a filtered category and `F : C ⥤ D` is fully faithful and satisfies the additional
  condition that for every `d : D` there is an object `c : D` and a morphism `d ⟶ F.obj c`, then
  `C` is filtered and `F` is final.
* Finality and initiality of diagonal functors `diag : C ⥤ C × C` and of projection functors
  of (co)structured arrow categories.

## References

* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Section 3.2

-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor Opposite

section ArbitraryUniverses

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

theorem Functor.final_of_isFiltered_structuredArrow [∀ d, IsFiltered (StructuredArrow d F)] :
    Final F where
  out _ := IsFiltered.isConnected _

theorem Functor.initial_of_isCofiltered_costructuredArrow
    [∀ d, IsCofiltered (CostructuredArrow F d)] : Initial F where
  out _ := IsCofiltered.isConnected _

theorem isFiltered_structuredArrow_of_isFiltered_of_exists [IsFilteredOrEmpty C]
    (h₁ : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) (h₂ : ∀ {d : D} {c : C} (s s' : d ⟶ F.obj c),
      ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) (d : D) :
    IsFiltered (StructuredArrow d F) := by
  have : Nonempty (StructuredArrow d F) := by
    obtain ⟨c, ⟨f⟩⟩ := h₁ d
    exact ⟨.mk f⟩
  suffices IsFilteredOrEmpty (StructuredArrow d F) from IsFiltered.mk
  refine ⟨fun f g => ?_, fun f g η μ => ?_⟩
  · obtain ⟨c, ⟨t, ht⟩⟩ := h₂ (f.hom ≫ F.map (IsFiltered.leftToMax f.right g.right))
        (g.hom ≫ F.map (IsFiltered.rightToMax f.right g.right))
    refine ⟨.mk (f.hom ≫ F.map (IsFiltered.leftToMax f.right g.right ≫ t)), ?_, ?_, trivial⟩
    · exact StructuredArrow.homMk (IsFiltered.leftToMax _ _ ≫ t) rfl
    · exact StructuredArrow.homMk (IsFiltered.rightToMax _ _ ≫ t) (by simpa using ht.symm)
  · refine ⟨.mk (f.hom ≫ F.map (η.right ≫ IsFiltered.coeqHom η.right μ.right)),
      StructuredArrow.homMk (IsFiltered.coeqHom η.right μ.right) (by simp), ?_⟩
    simpa using IsFiltered.coeq_condition _ _

theorem isCofiltered_costructuredArrow_of_isCofiltered_of_exists [IsCofilteredOrEmpty C]
    (h₁ : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) (h₂ : ∀ {d : D} {c : C} (s s' : F.obj c ⟶ d),
      ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') (d : D) :
    IsCofiltered (CostructuredArrow F d) := by
  suffices IsFiltered (CostructuredArrow F d)ᵒᵖ from isCofiltered_of_isFiltered_op _
  suffices IsFiltered (StructuredArrow (op d) F.op) from
    IsFiltered.of_equivalence (costructuredArrowOpEquivalence _ _).symm
  apply isFiltered_structuredArrow_of_isFiltered_of_exists
  · intro d
    obtain ⟨c, ⟨t⟩⟩ := h₁ d.unop
    exact ⟨op c, ⟨Quiver.Hom.op t⟩⟩
  · intro d c s s'
    obtain ⟨c', t, ht⟩ := h₂ s.unop s'.unop
    exact ⟨op c', Quiver.Hom.op t, Quiver.Hom.unop_inj ht⟩

theorem Functor.final_of_exists_of_isFiltered [IsFilteredOrEmpty C]
    (h₁ : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) (h₂ : ∀ {d : D} {c : C} (s s' : d ⟶ F.obj c),
      ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) : Functor.Final F := by
  suffices ∀ d, IsFiltered (StructuredArrow d F) from final_of_isFiltered_structuredArrow F
  exact isFiltered_structuredArrow_of_isFiltered_of_exists F h₁ h₂

theorem Functor.final_const_of_isTerminal [IsFiltered C] {X : D} (hX : IsTerminal X) :
    ((Functor.const C).obj X).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨IsFiltered.nonempty.some, ⟨hX.from _⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, hX.hom_ext _ _⟩)

theorem Functor.final_const_terminal [IsFiltered C] [HasTerminal D] :
    ((Functor.const C).obj (⊤_ D)).Final :=
  Functor.final_const_of_isTerminal terminalIsTerminal

theorem Functor.initial_of_exists_of_isCofiltered [IsCofilteredOrEmpty C]
    (h₁ : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) (h₂ : ∀ {d : D} {c : C} (s s' : F.obj c ⟶ d),
      ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') : Functor.Initial F := by
  suffices ∀ d, IsCofiltered (CostructuredArrow F d) from
    initial_of_isCofiltered_costructuredArrow F
  exact isCofiltered_costructuredArrow_of_isCofiltered_of_exists F h₁ h₂

theorem Functor.initial_const_of_isInitial [IsCofiltered C] {X : D} (hX : IsInitial X) :
    ((Functor.const C).obj X).Initial :=
  Functor.initial_of_exists_of_isCofiltered _ (fun _ => ⟨IsCofiltered.nonempty.some, ⟨hX.to _⟩⟩)
    (fun {_ c} _ _ => ⟨c, 𝟙 _, hX.hom_ext _ _⟩)

theorem Functor.initial_const_initial [IsCofiltered C] [HasInitial D] :
    ((Functor.const C).obj (⊥_ D)).Initial :=
  Functor.initial_const_of_isInitial initialIsInitial

theorem IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful [IsFilteredOrEmpty D] [F.Full]
    [F.Faithful] (h : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) : IsFilteredOrEmpty C where
  cocone_objs c c' := by
    obtain ⟨c₀, ⟨f⟩⟩ := h (IsFiltered.max (F.obj c) (F.obj c'))
    exact ⟨c₀, F.preimage (IsFiltered.leftToMax _ _ ≫ f),
      F.preimage (IsFiltered.rightToMax _ _ ≫ f), trivial⟩
  cocone_maps {c c'} f g := by
    obtain ⟨c₀, ⟨f₀⟩⟩ := h (IsFiltered.coeq (F.map f) (F.map g))
    refine ⟨_, F.preimage (IsFiltered.coeqHom (F.map f) (F.map g) ≫ f₀), F.map_injective ?_⟩
    simp [reassoc_of% (IsFiltered.coeq_condition (F.map f) (F.map g))]

theorem IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful [IsCofilteredOrEmpty D]
    [F.Full] [F.Faithful] (h : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) : IsCofilteredOrEmpty C := by
  suffices IsFilteredOrEmpty Cᵒᵖ from isCofilteredOrEmpty_of_isFilteredOrEmpty_op _
  refine IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F.op (fun d => ?_)
  obtain ⟨c, ⟨f⟩⟩ := h d.unop
  exact ⟨op c, ⟨f.op⟩⟩

theorem IsFiltered.of_exists_of_isFiltered_of_fullyFaithful [IsFiltered D] [F.Full] [F.Faithful]
    (h : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) : IsFiltered C :=
  { IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F h with
    nonempty := by
      have : Nonempty D := IsFiltered.nonempty
      obtain ⟨c, -⟩ := h (Classical.arbitrary D)
      exact ⟨c⟩ }

theorem IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful [IsCofiltered D] [F.Full]
    [F.Faithful] (h : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) : IsCofiltered C :=
  { IsCofilteredOrEmpty.of_exists_of_isCofiltered_of_fullyFaithful F h with
    nonempty := by
      have : Nonempty D := IsCofiltered.nonempty
      obtain ⟨c, -⟩ := h (Classical.arbitrary D)
      exact ⟨c⟩ }

theorem Functor.final_of_exists_of_isFiltered_of_fullyFaithful [IsFilteredOrEmpty D] [F.Full]
    [F.Faithful] (h : ∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) : Final F := by
  have := IsFilteredOrEmpty.of_exists_of_isFiltered_of_fullyFaithful F h
  refine Functor.final_of_exists_of_isFiltered F h (fun {d c} s s' => ?_)
  obtain ⟨c₀, ⟨f⟩⟩ := h (IsFiltered.coeq s s')
  refine ⟨c₀, F.preimage (IsFiltered.coeqHom s s' ≫ f), ?_⟩
  simp [reassoc_of% (IsFiltered.coeq_condition s s')]

theorem Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful [IsCofilteredOrEmpty D] [F.Full]
    [Faithful F] (h : ∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) : Initial F := by
  suffices Final F.op from initial_of_final_op _
  refine Functor.final_of_exists_of_isFiltered_of_fullyFaithful F.op (fun d => ?_)
  obtain ⟨c, ⟨f⟩⟩ := h d.unop
  exact ⟨op c, ⟨f.op⟩⟩

instance IsFiltered.under [IsFilteredOrEmpty C] (c : C) : IsFiltered (Under c) :=
  isFiltered_structuredArrow_of_isFiltered_of_exists _
    (fun c' => ⟨c', ⟨𝟙 _⟩⟩)
    (fun s s' => IsFilteredOrEmpty.cocone_maps s s') c

instance IsCofiltered.over [IsCofilteredOrEmpty C] (c : C) : IsCofiltered (Over c) :=
  isCofiltered_costructuredArrow_of_isCofiltered_of_exists _
    (fun c' => ⟨c', ⟨𝟙 _⟩⟩)
    (fun s s' => IsCofilteredOrEmpty.cone_maps s s') c

instance Under.final_forget [IsFilteredOrEmpty C] (c : C) : Final (Under.forget c) :=
  final_of_exists_of_isFiltered _
    (fun c' => ⟨mk (IsFiltered.leftToMax c c'), ⟨IsFiltered.rightToMax c c'⟩⟩)
    (fun {_} {x} s s' => by
      use mk (x.hom ≫ IsFiltered.coeqHom s s')
      use homMk (IsFiltered.coeqHom s s') (by simp)
      simp only [forget_obj, id_obj, mk_right, const_obj_obj, forget_map, homMk_right]
      rw [IsFiltered.coeq_condition])

instance Over.initial_forget [IsCofilteredOrEmpty C] (c : C) : Initial (Over.forget c) :=
  initial_of_exists_of_isCofiltered _
    (fun c' => ⟨mk (IsCofiltered.minToLeft c c'), ⟨IsCofiltered.minToRight c c'⟩⟩)
    (fun {_} {x} s s' => by
      use mk (IsCofiltered.eqHom s s' ≫ x.hom)
      use homMk (IsCofiltered.eqHom s s') (by simp)
      simp only [forget_obj, mk_left, forget_map, homMk_left]
      rw [IsCofiltered.eq_condition])

end ArbitraryUniverses

section LocallySmall

variable {C : Type v₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₁} D] (F : C ⥤ D)

theorem Functor.final_iff_of_isFiltered [IsFilteredOrEmpty C] :
    Final F ↔ (∀ d, ∃ c, Nonempty (d ⟶ F.obj c)) ∧ (∀ {d : D} {c : C} (s s' : d ⟶ F.obj c),
      ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t) := by
  refine ⟨fun hF => ⟨?_, ?_⟩, fun h => final_of_exists_of_isFiltered F h.1 h.2⟩
  · intro d
    obtain ⟨f⟩ : Nonempty (StructuredArrow d F) := IsConnected.is_nonempty
    exact ⟨_, ⟨f.hom⟩⟩
  · intro d c s s'
    have : colimit.ι (F ⋙ coyoneda.obj (op d)) c s = colimit.ι (F ⋙ coyoneda.obj (op d)) c s' := by
      apply (Final.colimitCompCoyonedaIso F d).toEquiv.injective
      subsingleton
    obtain ⟨c', t₁, t₂, h⟩ := (Types.FilteredColimit.colimit_eq_iff.{v₁, v₁, v₁} _).mp this
    refine ⟨IsFiltered.coeq t₁ t₂, t₁ ≫ IsFiltered.coeqHom t₁ t₂, ?_⟩
    conv_rhs => rw [IsFiltered.coeq_condition t₁ t₂]
    dsimp only [comp_obj, coyoneda_obj_obj, unop_op, Functor.comp_map, coyoneda_obj_map] at h
    simp [reassoc_of% h]

theorem Functor.initial_iff_of_isCofiltered [IsCofilteredOrEmpty C] :
    Initial F ↔ (∀ d, ∃ c, Nonempty (F.obj c ⟶ d)) ∧ (∀ {d : D} {c : C} (s s' : F.obj c ⟶ d),
      ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s') := by
  refine ⟨fun hF => ?_, fun h => initial_of_exists_of_isCofiltered F h.1 h.2⟩
  obtain ⟨h₁, h₂⟩ := F.op.final_iff_of_isFiltered.mp inferInstance
  refine ⟨?_, ?_⟩
  · intro d
    obtain ⟨c, ⟨t⟩⟩ := h₁ (op d)
    exact ⟨c.unop, ⟨t.unop⟩⟩
  · intro d c s s'
    obtain ⟨c', t, ht⟩ := h₂ (Quiver.Hom.op s) (Quiver.Hom.op s')
    exact ⟨c'.unop, t.unop, Quiver.Hom.op_inj ht⟩

theorem Functor.Final.exists_coeq [IsFilteredOrEmpty C] [Final F] {d : D} {c : C}
    (s s' : d ⟶ F.obj c) : ∃ (c' : C) (t : c ⟶ c'), s ≫ F.map t = s' ≫ F.map t :=
  ((final_iff_of_isFiltered F).1 inferInstance).2 s s'

theorem Functor.Initial.exists_eq [IsCofilteredOrEmpty C] [Initial F] {d : D} {c : C}
    (s s' : F.obj c ⟶ d) : ∃ (c' : C) (t : c' ⟶ c), F.map t ≫ s = F.map t ≫ s' :=
  ((initial_iff_of_isCofiltered F).1 inferInstance).2 s s'

theorem Functor.final_iff_isFiltered_structuredArrow [IsFilteredOrEmpty C] :
    Final F ↔ ∀ d, IsFiltered (StructuredArrow d F) := by
  refine ⟨?_, fun h => final_of_isFiltered_structuredArrow F⟩
  rw [final_iff_of_isFiltered]
  exact fun h => isFiltered_structuredArrow_of_isFiltered_of_exists F h.1 h.2

theorem Functor.initial_iff_isCofiltered_costructuredArrow [IsCofilteredOrEmpty C] :
    Initial F ↔ ∀ d, IsCofiltered (CostructuredArrow F d) := by
  refine ⟨?_, fun h => initial_of_isCofiltered_costructuredArrow F⟩
  rw [initial_iff_of_isCofiltered]
  exact fun h => isCofiltered_costructuredArrow_of_isCofiltered_of_exists F h.1 h.2

instance [IsFiltered C] (X : C × C) : IsFiltered (StructuredArrow X (diag C)) := by
  haveI : ∀ Y, IsFiltered (StructuredArrow Y (Under.forget X.1)) := by
    rw [← final_iff_isFiltered_structuredArrow (Under.forget X.1)]
    infer_instance
  apply IsFiltered.of_equivalence (StructuredArrow.ofDiagEquivalence X).symm

instance Functor.final_diag_of_isFiltered [IsFiltered C] : Final (Functor.diag C) :=
  final_of_isFiltered_structuredArrow _

instance [IsCofiltered C] (X : C × C) : IsCofiltered (CostructuredArrow (diag C) X) := by
  haveI : ∀ Y, IsCofiltered (CostructuredArrow (Over.forget X.1) Y) := by
    rw [← initial_iff_isCofiltered_costructuredArrow (Over.forget X.1)]
    infer_instance
  apply IsCofiltered.of_equivalence (CostructuredArrow.ofDiagEquivalence X).symm

instance Functor.initial_diag_of_isFiltered [IsCofiltered C] : Initial (Functor.diag C) :=
  initial_of_isCofiltered_costructuredArrow _

end LocallySmall

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

theorem Functor.final_of_isFiltered_of_pUnit [IsFiltered C] (F : C ⥤ Discrete PUnit) :
    Final F := by
  refine final_of_exists_of_isFiltered F (fun _ => ?_) (fun {_} {c} _ _ => ?_)
  · use Classical.choice IsFiltered.nonempty
    exact ⟨Discrete.eqToHom (by simp)⟩
  · use c; use 𝟙 c
    apply Subsingleton.elim

theorem Functor.initial_of_isCofiltered_pUnit [IsCofiltered C] (F : C ⥤ Discrete PUnit) :
    Initial F := by
  refine initial_of_exists_of_isCofiltered F (fun _ => ?_) (fun {_} {c} _ _ => ?_)
  · use Classical.choice IsCofiltered.nonempty
    exact ⟨Discrete.eqToHom (by simp)⟩
  · use c; use 𝟙 c
    apply Subsingleton.elim

instance StructuredArrow.final_proj_of_isFiltered [IsFilteredOrEmpty C]
    (T : C ⥤ D) [Final T] (Y : D) : Final (StructuredArrow.proj Y T) := by
  refine ⟨fun X => ?_⟩
  rw [isConnected_iff_of_equivalence (ofStructuredArrowProjEquivalence T Y X)]
  exact (final_comp (Under.forget X) T).out _

instance CostructuredArrow.initial_proj_of_isCofiltered [IsCofilteredOrEmpty C]
    (T : C ⥤ D) [Initial T] (Y : D) : Initial (CostructuredArrow.proj T Y) := by
  refine ⟨fun X => ?_⟩
  rw [isConnected_iff_of_equivalence (ofCostructuredArrowProjEquivalence T Y X)]
  exact (initial_comp (Over.forget X) T).out _

section Pi

variable {α : Type u₁} {I : α → Type u₂} [∀ s, Category.{v₂} (I s)]

open IsFiltered in

instance final_eval [∀ s, IsFiltered (I s)] (s : α) : (Pi.eval I s).Final := by
  classical
  apply Functor.final_of_exists_of_isFiltered
  · exact fun i => ⟨Function.update (fun t => nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (∀ s, (c' : I s) × (c s ⟶ c')) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨coeq f g, coeqHom f g⟩
    refine ⟨fun t => (c't t).1, fun t => (c't t).2, ?_⟩
    dsimp only [Pi.eval_obj, Pi.eval_map, c't]
    rw [Function.update_same]
    simpa using coeq_condition _ _

open IsCofiltered in

instance initial_eval [∀ s, IsCofiltered (I s)] (s : α) : (Pi.eval I s).Initial := by
  classical
  apply Functor.initial_of_exists_of_isCofiltered
  · exact fun i => ⟨Function.update (fun t => nonempty.some) s i, ⟨by simpa using 𝟙 _⟩⟩
  · intro d c f g
    let c't : (∀ s, (c' : I s) × (c' ⟶ c s)) := Function.update (fun t => ⟨c t, 𝟙 (c t)⟩)
      s ⟨eq f g, eqHom f g⟩
    refine ⟨fun t => (c't t).1, fun t => (c't t).2, ?_⟩
    dsimp only [Pi.eval_obj, Pi.eval_map, c't]
    rw [Function.update_same]
    simpa using eq_condition _ _

end Pi

section Prod

open IsFiltered in

instance final_fst [IsFilteredOrEmpty C] [IsFiltered D] : (Prod.fst C D).Final := by
  apply Functor.final_of_exists_of_isFiltered
  · exact fun c => ⟨(c, nonempty.some), ⟨𝟙 c⟩⟩
  · intro c ⟨c', d'⟩ f g
    exact ⟨(coeq f g, d'), (coeqHom f g, 𝟙 d'), coeq_condition _ _⟩

instance final_snd [IsFiltered C] [IsFilteredOrEmpty D] : (Prod.snd C D).Final :=
  inferInstanceAs ((Prod.braiding C D).functor ⋙ Prod.fst D C).Final

open IsCofiltered in

instance initial_fst [IsCofilteredOrEmpty C] [IsCofiltered D] : (Prod.fst C D).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered
  · exact fun c => ⟨(c, nonempty.some), ⟨𝟙 c⟩⟩
  · intro c ⟨c', d'⟩ f g
    exact ⟨(eq f g, d'), (eqHom f g, 𝟙 d'), eq_condition _ _⟩

instance initial_snd [IsCofiltered C] [IsCofilteredOrEmpty D] : (Prod.snd C D).Initial :=
  inferInstanceAs ((Prod.braiding C D).functor ⋙ Prod.fst D C).Initial

end Prod

end CategoryTheory
