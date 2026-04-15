/-
Extracted from Algebra/Category/Ring/FinitePresentation.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# Finitely presentable objects in `Under R` with `R : CommRingCat`

In this file, we show that finitely presented algebras are finitely presentable in `Under R`,
i.e. `Hom_R(S, -)` preserves filtered colimits.

-/

open CategoryTheory Limits

universe vJ uJ u

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J]

variable (R : CommRingCat.{u}) (F : J ⥤ CommRingCat.{u}) (α : (Functor.const _).obj R ⟶ F)

variable {S : CommRingCat.{u}} (f : R ⟶ S) (c : Cocone F) (hc : IsColimit c)

variable [PreservesColimit F (forget CommRingCat)]

set_option backward.isDefEq.respectTransparency false in

include hc in

set_option backward.isDefEq.respectTransparency false in

include hc in

lemma RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit (hf : f.hom.FinitePresentation)
    (g : S ⟶ c.pt) (hg : ∀ i, f ≫ g = α.app i ≫ c.ι.app i) :
    ∃ (i : J) (g' : S ⟶ F.obj i), f ≫ g' = α.app i ∧ g = g' ≫ c.ι.app i := by
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  letI := f.hom.toAlgebra
  obtain ⟨n, hn⟩ := hf
  let P := CommRingCat.of (MvPolynomial (Fin n) R)
  let iP : R ⟶ P := CommRingCat.ofHom MvPolynomial.C
  obtain ⟨π, rfl, hπ, s, hs⟩ :
      ∃ π : P ⟶ S, iP ≫ π = f ∧ Function.Surjective π ∧ (RingHom.ker π.hom).FG := by
    obtain ⟨π, h₁, h₂⟩ := hn
    exact ⟨CommRingCat.ofHom π, by ext1; exact π.comp_algebraMap, h₁, h₂⟩
  obtain ⟨i, g', hg', hg''⟩ : ∃ (i : J) (g' : P ⟶ F.obj i),
      π ≫ g = g' ≫ c.ι.app i ∧ iP ≫ g' = α.app i := by
    choose j x h using fun i ↦ Types.jointly_surjective_of_isColimit hc' ((π ≫ g) (.X i))
    obtain ⟨i, ⟨hi⟩⟩ : ∃ i, Nonempty (∀ a, (j a ⟶ i)) := by
      have : ∃ i, ∀ a, Nonempty (j a ⟶ i) := by
        simpa using IsFiltered.sup_objs_exists (Finset.univ.image j)
      simpa [← exists_true_iff_nonempty, Classical.skolem, -exists_const_iff] using this
    refine ⟨i, CommRingCat.ofHom (MvPolynomial.eval₂Hom
      (α.app i).hom (F.map (hi _) <| x ·)), ?_, ?_⟩
    · ext1
      apply MvPolynomial.ringHom_ext
      · simpa using fun x ↦ congr($(hg i).hom x)
      · intro i
        simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
          Functor.const_obj_obj, CommRingCat.hom_ofHom, MvPolynomial.coe_eval₂Hom,
          MvPolynomial.eval₂_X]
        exact (congr($(c.w (hi i)).hom (x i)).trans (h i)).symm
    · ext x
      simp [P, iP]
  have : ∀ r : s, ∃ (i' : J) (hi' : i ⟶ i'), F.map hi' (g' r) = 0 := by
    intro r
    have := Types.FilteredColimit.isColimit_eq_iff _ hc' (xi := g' r) (j := i) (xj := (0 : F.obj i))
    suffices H : (g' ≫ c.ι.app i) r = 0 by
      obtain ⟨k, f, g, e⟩ := this.mp (by simpa using H)
      exact ⟨k, f, by simpa using e⟩
    rw [← hg']
    simp [show π r = 0 from hs.le (Ideal.subset_span r.2)]
  choose i' hi' hi'' using this
  obtain ⟨c'⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan i i' hi')
  refine ⟨c'.pt, CommRingCat.ofHom (RingHom.liftOfSurjective π.hom hπ
    ⟨(g' ≫ F.map (c'.ι.app none)).hom, ?_⟩), ?_, ?_⟩
  · rw [← hs, Ideal.span_le]
    intro r hr
    rw [← c'.w (.init ⟨r, hr⟩)]
    simp [hi'']
  · ext x
    suffices (iP ≫ g' ≫ F.map (c'.ι.app none)) x = α.app c'.pt x by
      simpa [RingHom.liftOfRightInverse_comp_apply] using this
    rw [← Category.assoc, hg'', ← NatTrans.naturality]
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
  · ext x
    obtain ⟨x, rfl⟩ := hπ x
    suffices (π ≫ g) x = (g' ≫ F.map (c'.ι.app none) ≫ c.ι.app _) x by
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom,
        RingHom.liftOfRightInverse_comp_apply, coe_comp, Function.comp_apply] using this
    rw [c.w, hg']
    rfl

set_option backward.isDefEq.respectTransparency false in

lemma CommRingCat.preservesColimit_coyoneda_of_finitePresentation
    (S : Under R) (hS : S.hom.hom.FinitePresentation) (F : J ⥤ Under R)
    [PreservesColimit (F ⋙ Under.forget R) (forget CommRingCat)] :
    PreservesColimit F (coyoneda.obj (.op S)) := by
  constructor
  intro c hc
  refine ⟨Types.FilteredColimit.isColimitOf _ _ ?_ ?_⟩
  · intro f
    obtain ⟨i, g, h₁, h₂⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
       R (F ⋙ Under.forget R) { app i := (F.obj i).hom } S.hom ((Under.forget R).mapCocone c)
      (PreservesColimit.preserves hc).some hS f.right (by simp)
    exact ⟨i, Under.homMk g h₁, Under.UnderMorphism.ext h₂⟩
  · intro i j f₁ f₂ e
    obtain ⟨k, hik, hjk, e⟩ := RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
      R (F ⋙ Under.forget R) { app i := (F.obj i).hom } S.hom ((Under.forget R).mapCocone c)
      (PreservesColimit.preserves hc).some
      (RingHom.FiniteType.of_finitePresentation hS).essFiniteType
      f₁.right (Under.w f₁) f₂.right (Under.w f₂) congr($(e).right)
    exact ⟨k, hik, hjk, Under.UnderMorphism.ext e⟩
