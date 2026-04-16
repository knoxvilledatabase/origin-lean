/-
Extracted from Analysis/Analytic/Linear.lean
Genuine: 36 | Conflates: 0 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.Analysis.Analytic.Basic

noncomputable section

/-!
# Linear functions are analytic

In this file we prove that a `ContinuousLinearMap` defines an analytic function with
the formal power series `f x = f a + f (x - a)`. We also prove similar results for bilinear maps.

TODO: port to use `CPolynomial`, and prove the stronger result that continuous linear maps are
continuously polynomial
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open scoped Topology NNReal ENNReal

open Set Filter Asymptotics

noncomputable section

namespace ContinuousLinearMap

@[simp]
theorem fpowerSeries_radius (f : E →L[𝕜] F) (x : E) : (f.fpowerSeries x).radius = ∞ :=
  (f.fpowerSeries x).radius_eq_top_of_forall_image_add_eq_zero 2 fun _ => rfl

protected theorem hasFPowerSeriesOnBall (f : E →L[𝕜] F) (x : E) :
    HasFPowerSeriesOnBall f (f.fpowerSeries x) x ∞ :=
  { r_le := by simp
    r_pos := ENNReal.coe_lt_top
    hasSum := fun _ => (hasSum_nat_add_iff' 2).1 <| by
      simp [Finset.sum_range_succ, ← sub_sub, hasSum_zero, fpowerSeries] }

protected theorem hasFPowerSeriesAt (f : E →L[𝕜] F) (x : E) :
    HasFPowerSeriesAt f (f.fpowerSeries x) x :=
  ⟨∞, f.hasFPowerSeriesOnBall x⟩

protected theorem analyticAt (f : E →L[𝕜] F) (x : E) : AnalyticAt 𝕜 f x :=
  (f.hasFPowerSeriesAt x).analyticAt

protected theorem analyticOnNhd (f : E →L[𝕜] F) (s : Set E) : AnalyticOnNhd 𝕜 f s :=
  fun x _ ↦ f.analyticAt x

protected theorem analyticWithinAt (f : E →L[𝕜] F) (s : Set E) (x : E) : AnalyticWithinAt 𝕜 f s x :=
  (f.analyticAt x).analyticWithinAt

protected theorem analyticOn (f : E →L[𝕜] F) (s : Set E) : AnalyticOn 𝕜 f s :=
  fun x _ ↦ f.analyticWithinAt _ x

alias analyticWithinOn := ContinuousLinearMap.analyticOn

def uncurryBilinear (f : E →L[𝕜] F →L[𝕜] G) : E × F[×2]→L[𝕜] G :=
  @ContinuousLinearMap.uncurryLeft 𝕜 1 (fun _ => E × F) G _ _ _ _ _ <|
    (↑(continuousMultilinearCurryFin1 𝕜 (E × F) G).symm : (E × F →L[𝕜] G) →L[𝕜] _).comp <|
      f.bilinearComp (fst _ _ _) (snd _ _ _)

def fpowerSeriesBilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) : FormalMultilinearSeries 𝕜 (E × F) G
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ (f x.1 x.2)
  | 1 => (continuousMultilinearCurryFin1 𝕜 (E × F) G).symm (f.deriv₂ x)
  | 2 => f.uncurryBilinear
  | _ => 0

@[simp]
theorem fpowerSeriesBilinear_radius (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    (f.fpowerSeriesBilinear x).radius = ∞ :=
  (f.fpowerSeriesBilinear x).radius_eq_top_of_forall_image_add_eq_zero 3 fun _ => rfl

protected theorem hasFPowerSeriesOnBall_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    HasFPowerSeriesOnBall (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x ∞ :=
  { r_le := by simp
    r_pos := ENNReal.coe_lt_top
    hasSum := fun _ =>
      (hasSum_nat_add_iff' 3).1 <| by
        simp only [Finset.sum_range_succ, Finset.sum_range_one, Prod.fst_add, Prod.snd_add,
          f.map_add_add]
        simp [fpowerSeriesBilinear, hasSum_zero] }

protected theorem hasFPowerSeriesAt_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    HasFPowerSeriesAt (fun x : E × F => f x.1 x.2) (f.fpowerSeriesBilinear x) x :=
  ⟨∞, f.hasFPowerSeriesOnBall_bilinear x⟩

protected theorem analyticAt_bilinear (f : E →L[𝕜] F →L[𝕜] G) (x : E × F) :
    AnalyticAt 𝕜 (fun x : E × F => f x.1 x.2) x :=
  (f.hasFPowerSeriesAt_bilinear x).analyticAt

protected theorem analyticWithinAt_bilinear (f : E →L[𝕜] F →L[𝕜] G) (s : Set (E × F)) (x : E × F) :
    AnalyticWithinAt 𝕜 (fun x : E × F => f x.1 x.2) s x :=
  (f.analyticAt_bilinear x).analyticWithinAt

protected theorem analyticOnNhd_bilinear (f : E →L[𝕜] F →L[𝕜] G) (s : Set (E × F)) :
    AnalyticOnNhd 𝕜 (fun x : E × F => f x.1 x.2) s :=
  fun x _ ↦ f.analyticAt_bilinear x

protected theorem analyticOn_bilinear (f : E →L[𝕜] F →L[𝕜] G) (s : Set (E × F)) :
    AnalyticOn 𝕜 (fun x : E × F => f x.1 x.2) s :=
  (f.analyticOnNhd_bilinear s).analyticOn

end ContinuousLinearMap

variable {s : Set E} {z : E} {t : Set (E × F)} {p : E × F}

lemma analyticAt_id : AnalyticAt 𝕜 (id : E → E) z :=
  (ContinuousLinearMap.id 𝕜 E).analyticAt z

lemma analyticWithinAt_id : AnalyticWithinAt 𝕜 (id : E → E) s z :=
  analyticAt_id.analyticWithinAt

theorem analyticOnNhd_id : AnalyticOnNhd 𝕜 (fun x : E ↦ x) s :=
  fun _ _ ↦ analyticAt_id

theorem analyticOn_id : AnalyticOn 𝕜 (fun x : E ↦ x) s :=
  fun _ _ ↦ analyticWithinAt_id

alias analyticWithinOn_id := analyticOn_id

theorem analyticAt_fst  : AnalyticAt 𝕜 (fun p : E × F ↦ p.fst) p :=
  (ContinuousLinearMap.fst 𝕜 E F).analyticAt p

theorem analyticWithinAt_fst  : AnalyticWithinAt 𝕜 (fun p : E × F ↦ p.fst) t p :=
  analyticAt_fst.analyticWithinAt

theorem analyticAt_snd : AnalyticAt 𝕜 (fun p : E × F ↦ p.snd) p :=
  (ContinuousLinearMap.snd 𝕜 E F).analyticAt p

theorem analyticWithinAt_snd : AnalyticWithinAt 𝕜 (fun p : E × F ↦ p.snd) t p :=
  analyticAt_snd.analyticWithinAt

theorem analyticOnNhd_fst : AnalyticOnNhd 𝕜 (fun p : E × F ↦ p.fst) t :=
  fun _ _ ↦ analyticAt_fst

theorem analyticOn_fst : AnalyticOn 𝕜 (fun p : E × F ↦ p.fst) t :=
  fun _ _ ↦ analyticWithinAt_fst

alias analyticWithinOn_fst := analyticOn_fst

theorem analyticOnNhd_snd : AnalyticOnNhd 𝕜 (fun p : E × F ↦ p.snd) t :=
  fun _ _ ↦ analyticAt_snd

theorem analyticOn_snd : AnalyticOn 𝕜 (fun p : E × F ↦ p.snd) t :=
  fun _ _ ↦ analyticWithinAt_snd

alias analyticWithinOn_snd := analyticOn_snd

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] F) (s : Set E) (x : E)

protected theorem analyticAt : AnalyticAt 𝕜 f x :=
  ((f : E →L[𝕜] F).hasFPowerSeriesAt x).analyticAt

protected theorem analyticOnNhd : AnalyticOnNhd 𝕜 f s :=
  fun x _ ↦ f.analyticAt x

protected theorem analyticWithinAt (f : E →L[𝕜] F) (s : Set E) (x : E) : AnalyticWithinAt 𝕜 f s x :=
  (f.analyticAt x).analyticWithinAt

protected theorem analyticOn (f : E →L[𝕜] F) (s : Set E) : AnalyticOn 𝕜 f s :=
  fun x _ ↦ f.analyticWithinAt _ x

alias analyticWithinOn := ContinuousLinearEquiv.analyticOn

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

variable (f : E ≃ₗᵢ[𝕜] F) (s : Set E) (x : E)

protected theorem analyticAt : AnalyticAt 𝕜 f x :=
  ((f : E →L[𝕜] F).hasFPowerSeriesAt x).analyticAt

protected theorem analyticOnNhd : AnalyticOnNhd 𝕜 f s :=
  fun x _ ↦ f.analyticAt x

protected theorem analyticWithinAt (f : E →L[𝕜] F) (s : Set E) (x : E) : AnalyticWithinAt 𝕜 f s x :=
  (f.analyticAt x).analyticWithinAt

protected theorem analyticOn (f : E →L[𝕜] F) (s : Set E) : AnalyticOn 𝕜 f s :=
  fun x _ ↦ f.analyticWithinAt _ x

alias analyticWithinOn := LinearIsometryEquiv.analyticOn

end LinearIsometryEquiv
