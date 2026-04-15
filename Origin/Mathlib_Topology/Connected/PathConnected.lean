/-
Extracted from Topology/Connected/PathConnected.lean
Genuine: 141 | Conflates: 0 | Dissolved: 1 | Infrastructure: 40
-/
import Origin.Core
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval

/-!
# Path connectedness

## Main definitions

In the file the unit interval `[0, 1]` in `ℝ` is denoted by `I`, and `X` is a topological space.

* `Path (x y : X)` is the type of paths from `x` to `y`, i.e., continuous maps from `I` to `X`
  mapping `0` to `x` and `1` to `y`.
* `Path.map` is the image of a path under a continuous map.
* `Joined (x y : X)` means there is a path between `x` and `y`.
* `Joined.somePath (h : Joined x y)` selects some path between two points `x` and `y`.
* `pathComponent (x : X)` is the set of points joined to `x`.
* `PathConnectedSpace X` is a predicate class asserting that `X` is non-empty and every two
  points of `X` are joined.

Then there are corresponding relative notions for `F : Set X`.

* `JoinedIn F (x y : X)` means there is a path `γ` joining `x` to `y` with values in `F`.
* `JoinedIn.somePath (h : JoinedIn F x y)` selects a path from `x` to `y` inside `F`.
* `pathComponentIn F (x : X)` is the set of points joined to `x` in `F`.
* `IsPathConnected F` asserts that `F` is non-empty and every two
  points of `F` are joined in `F`.
* `LocPathConnectedSpace X` is a predicate class asserting that `X` is locally path-connected:
  each point has a basis of path-connected neighborhoods (we do *not* ask these to be open).

## Main theorems

* `Joined` and `JoinedIn F` are transitive relations.

One can link the absolute and relative version in two directions, using `(univ : Set X)` or the
subtype `↥F`.

* `pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X)`
* `isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace ↥F`

For locally path connected spaces, we have
* `pathConnectedSpace_iff_connectedSpace : PathConnectedSpace X ↔ ConnectedSpace X`
* `IsOpen.isConnected_iff_isPathConnected (U_op : IsOpen U) : IsPathConnected U ↔ IsConnected U`

## Implementation notes

By default, all paths have `I` as their source and `X` as their target, but there is an
operation `Set.IccExtend` that will extend any continuous map `γ : I → X` into a continuous map
`IccExtend zero_le_one γ : ℝ → X` that is constant before `0` and after `1`.

This is used to define `Path.extend` that turns `γ : Path x y` into a continuous map
`γ.extend : ℝ → X` whose restriction to `I` is the original `γ`, and is equal to `x`
on `(-∞, 0]` and to `y` on `[1, +∞)`.
-/

noncomputable section

open Topology Filter unitInterval Set Function

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {ι : Type*}

/-! ### Paths -/

structure Path (x y : X) extends C(I, X) where
  /-- The start point of a `Path`. -/
  source' : toFun 0 = x
  /-- The end point of a `Path`. -/
  target' : toFun 1 = y

instance Path.funLike : FunLike (Path x y) I X where
  coe γ := ⇑γ.toContinuousMap
  coe_injective' γ₁ γ₂ h := by
    simp only [DFunLike.coe_fn_eq] at h
    cases γ₁; cases γ₂; congr

instance Path.continuousMapClass : ContinuousMapClass (Path x y) I X where
  map_continuous γ := show Continuous γ.toContinuousMap by fun_prop

@[ext]
protected theorem Path.ext : ∀ {γ₁ γ₂ : Path x y}, (γ₁ : I → X) = γ₂ → γ₁ = γ₂ := by
  rintro ⟨⟨x, h11⟩, h12, h13⟩ ⟨⟨x, h21⟩, h22, h23⟩ rfl
  rfl

namespace Path

@[simp]
theorem coe_mk_mk (f : I → X) (h₁) (h₂ : f 0 = x) (h₃ : f 1 = y) :
    ⇑(mk ⟨f, h₁⟩ h₂ h₃ : Path x y) = f :=
  rfl

variable (γ : Path x y)

@[continuity]
protected theorem continuous : Continuous γ :=
  γ.continuous_toFun

@[simp]
protected theorem source : γ 0 = x :=
  γ.source'

@[simp]
protected theorem target : γ 1 = y :=
  γ.target'

def simps.apply : I → X :=
  γ

initialize_simps_projections Path (toFun → simps.apply, -toContinuousMap)

@[simp]
theorem coe_toContinuousMap : ⇑γ.toContinuousMap = γ :=
  rfl

@[simp]
theorem coe_mk : ⇑(γ : C(I, X)) = γ :=
  rfl

instance hasUncurryPath {X α : Type*} [TopologicalSpace X] {x y : α → X} :
    HasUncurry (∀ a : α, Path (x a) (y a)) (α × I) X :=
  ⟨fun φ p => φ p.1 p.2⟩

@[refl, simps]
def refl (x : X) : Path x x where
  toFun _t := x
  continuous_toFun := continuous_const
  source' := rfl
  target' := rfl

@[simp]
theorem refl_range {a : X} : range (Path.refl a) = {a} := by simp [Path.refl, CoeFun.coe]

@[symm, simps]
def symm (γ : Path x y) : Path y x where
  toFun := γ ∘ σ
  continuous_toFun := by continuity
  source' := by simpa [-Path.target] using γ.target
  target' := by simpa [-Path.source] using γ.source

@[simp]
theorem symm_symm (γ : Path x y) : γ.symm.symm = γ := by
  ext t
  show γ (σ (σ t)) = γ t
  rw [unitInterval.symm_symm]

theorem symm_bijective : Function.Bijective (Path.symm : Path x y → Path y x) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem refl_symm {a : X} : (Path.refl a).symm = Path.refl a := by
  ext
  rfl

@[simp]
theorem symm_range {a b : X} (γ : Path a b) : range γ.symm = range γ := by
  ext x
  simp only [mem_range, Path.symm, DFunLike.coe, unitInterval.symm, SetCoe.exists, comp_apply,
    Subtype.coe_mk]
  constructor <;> rintro ⟨y, hy, hxy⟩ <;> refine ⟨1 - y, mem_iff_one_sub_mem.mp hy, ?_⟩ <;>
    convert hxy
  simp

/-! #### Space of paths -/

open ContinuousMap

instance topologicalSpace : TopologicalSpace (Path x y) :=
  TopologicalSpace.induced ((↑) : _ → C(I, X)) ContinuousMap.compactOpen

instance : ContinuousEval (Path x y) I X := .of_continuous_forget continuous_induced_dom

theorem _root_.Continuous.path_eval {Y} [TopologicalSpace Y] {f : Y → Path x y} {g : Y → I}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun y => f y (g y) := by
  continuity

theorem continuous_uncurry_iff {Y} [TopologicalSpace Y] {g : Y → Path x y} :
    Continuous ↿g ↔ Continuous g :=
  Iff.symm <| continuous_induced_rng.trans
    ⟨fun h => continuous_uncurry_of_continuous ⟨_, h⟩,
    continuous_of_continuous_uncurry (fun (y : Y) ↦ ContinuousMap.mk (g y))⟩

def extend : ℝ → X :=
  IccExtend zero_le_one γ

theorem _root_.Continuous.path_extend {γ : Y → Path x y} {f : Y → ℝ} (hγ : Continuous ↿γ)
    (hf : Continuous f) : Continuous fun t => (γ t).extend (f t) :=
  Continuous.IccExtend hγ hf

@[continuity, fun_prop]
theorem continuous_extend : Continuous γ.extend :=
  γ.continuous.Icc_extend'

theorem _root_.Filter.Tendsto.path_extend
    {l r : Y → X} {y : Y} {l₁ : Filter ℝ} {l₂ : Filter X} {γ : ∀ y, Path (l y) (r y)}
    (hγ : Tendsto (↿γ) (𝓝 y ×ˢ l₁.map (projIcc 0 1 zero_le_one)) l₂) :
    Tendsto (↿fun x => (γ x).extend) (𝓝 y ×ˢ l₁) l₂ :=
  Filter.Tendsto.IccExtend _ hγ

theorem _root_.ContinuousAt.path_extend {g : Y → ℝ} {l r : Y → X} (γ : ∀ y, Path (l y) (r y))
    {y : Y} (hγ : ContinuousAt (↿γ) (y, projIcc 0 1 zero_le_one (g y))) (hg : ContinuousAt g y) :
    ContinuousAt (fun i => (γ i).extend (g i)) y :=
  hγ.IccExtend (fun x => γ x) hg

@[simp]
theorem extend_extends {a b : X} (γ : Path a b) {t : ℝ}
    (ht : t ∈ (Icc 0 1 : Set ℝ)) : γ.extend t = γ ⟨t, ht⟩ :=
  IccExtend_of_mem _ γ ht

theorem extend_zero : γ.extend 0 = x := by simp

theorem extend_one : γ.extend 1 = y := by simp

theorem extend_extends' {a b : X} (γ : Path a b) (t : (Icc 0 1 : Set ℝ)) : γ.extend t = γ t :=
  IccExtend_val _ γ t

@[simp]
theorem extend_range {a b : X} (γ : Path a b) :
    range γ.extend = range γ :=
  IccExtend_range _ γ

theorem extend_of_le_zero {a b : X} (γ : Path a b) {t : ℝ}
    (ht : t ≤ 0) : γ.extend t = a :=
  (IccExtend_of_le_left _ _ ht).trans γ.source

theorem extend_of_one_le {a b : X} (γ : Path a b) {t : ℝ}
    (ht : 1 ≤ t) : γ.extend t = b :=
  (IccExtend_of_right_le _ _ ht).trans γ.target

@[simp]
theorem refl_extend {a : X} : (Path.refl a).extend = fun _ => a :=
  rfl

def ofLine {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) : Path x y where
  toFun := f ∘ ((↑) : unitInterval → ℝ)
  continuous_toFun := hf.comp_continuous continuous_subtype_val Subtype.prop
  source' := h₀
  target' := h₁

theorem ofLine_mem {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y) :
    ∀ t, ofLine hf h₀ h₁ t ∈ f '' I := fun ⟨t, t_in⟩ => ⟨t, t_in, rfl⟩

attribute [local simp] Iic_def

@[trans]
def trans (γ : Path x y) (γ' : Path y z) : Path x z where
  toFun := (fun t : ℝ => if t ≤ 1 / 2 then γ.extend (2 * t) else γ'.extend (2 * t - 1)) ∘ (↑)
  continuous_toFun := by
    refine
      (Continuous.if_le ?_ ?_ continuous_id continuous_const (by norm_num)).comp
        continuous_subtype_val <;>
    fun_prop
  source' := by norm_num
  target' := by norm_num

theorem trans_apply (γ : Path x y) (γ' : Path y z) (t : I) :
    (γ.trans γ') t =
      if h : (t : ℝ) ≤ 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else γ' ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ :=
  show ite _ _ _ = _ by split_ifs <;> rw [extend_extends]

@[simp]
theorem trans_symm (γ : Path x y) (γ' : Path y z) : (γ.trans γ').symm = γ'.symm.trans γ.symm := by
  ext t
  simp only [trans_apply, ← one_div, symm_apply, not_le, Function.comp_apply]
  split_ifs with h h₁ h₂ <;> rw [coe_symm_eq] at h
  · have ht : (t : ℝ) = 1 / 2 := by linarith
    norm_num [ht]
  · refine congr_arg _ (Subtype.ext ?_)
    norm_num [sub_sub_eq_add_sub, mul_sub]
  · refine congr_arg _ (Subtype.ext ?_)
    norm_num [mul_sub, h]
    ring -- TODO norm_num should really do this
  · exfalso
    linarith

@[simp]
theorem refl_trans_refl {a : X} :
    (Path.refl a).trans (Path.refl a) = Path.refl a := by
  ext
  simp only [Path.trans, ite_self, one_div, Path.refl_extend]
  rfl

theorem trans_range {a b c : X} (γ₁ : Path a b) (γ₂ : Path b c) :
    range (γ₁.trans γ₂) = range γ₁ ∪ range γ₂ := by
  rw [Path.trans]
  apply eq_of_subset_of_subset
  · rintro x ⟨⟨t, ht0, ht1⟩, hxt⟩
    by_cases h : t ≤ 1 / 2
    · left
      use ⟨2 * t, ⟨by linarith, by linarith⟩⟩
      rw [← γ₁.extend_extends]
      rwa [coe_mk_mk, Function.comp_apply, if_pos h] at hxt
    · right
      use ⟨2 * t - 1, ⟨by linarith, by linarith⟩⟩
      rw [← γ₂.extend_extends]
      rwa [coe_mk_mk, Function.comp_apply, if_neg h] at hxt
  · rintro x (⟨⟨t, ht0, ht1⟩, hxt⟩ | ⟨⟨t, ht0, ht1⟩, hxt⟩)
    · use ⟨t / 2, ⟨by linarith, by linarith⟩⟩
      have : t / 2 ≤ 1 / 2 := (div_le_div_iff_of_pos_right (zero_lt_two : (0 : ℝ) < 2)).mpr ht1
      rw [coe_mk_mk, Function.comp_apply, if_pos this, Subtype.coe_mk]
      ring_nf
      rwa [γ₁.extend_extends]
    · by_cases h : t = 0
      · use ⟨1 / 2, ⟨by linarith, by linarith⟩⟩
        rw [coe_mk_mk, Function.comp_apply, if_pos le_rfl, Subtype.coe_mk,
          mul_one_div_cancel (two_ne_zero' ℝ)]
        rw [γ₁.extend_one]
        rwa [← γ₂.extend_extends, h, γ₂.extend_zero] at hxt
      · use ⟨(t + 1) / 2, ⟨by linarith, by linarith⟩⟩
        replace h : t ≠ 0 := h
        have ht0 := lt_of_le_of_ne ht0 h.symm
        have : ¬(t + 1) / 2 ≤ 1 / 2 := by
          rw [not_le]
          linarith
        rw [coe_mk_mk, Function.comp_apply, Subtype.coe_mk, if_neg this]
        ring_nf
        rwa [γ₂.extend_extends]

def map' (γ : Path x y) {f : X → Y} (h : ContinuousOn f (range γ)) : Path (f x) (f y) where
  toFun := f ∘ γ
  continuous_toFun := h.comp_continuous γ.continuous (fun x ↦ mem_range_self x)
  source' := by simp
  target' := by simp

def map (γ : Path x y) {f : X → Y} (h : Continuous f) :
    Path (f x) (f y) := γ.map' h.continuousOn

@[simp]
theorem map_coe (γ : Path x y) {f : X → Y} (h : Continuous f) :
    (γ.map h : I → Y) = f ∘ γ := by
  ext t
  rfl

@[simp]
theorem map_symm (γ : Path x y) {f : X → Y} (h : Continuous f) :
    (γ.map h).symm = γ.symm.map h :=
  rfl

@[simp]
theorem map_trans (γ : Path x y) (γ' : Path y z) {f : X → Y}
    (h : Continuous f) : (γ.trans γ').map h = (γ.map h).trans (γ'.map h) := by
  ext t
  rw [trans_apply, map_coe, Function.comp_apply, trans_apply]
  split_ifs <;> rfl

@[simp]
theorem map_id (γ : Path x y) : γ.map continuous_id = γ := by
  ext
  rfl

@[simp]
theorem map_map (γ : Path x y) {Z : Type*} [TopologicalSpace Z]
    {f : X → Y} (hf : Continuous f) {g : Y → Z} (hg : Continuous g) :
    (γ.map hf).map hg = γ.map (hg.comp hf) := by
  ext
  rfl

def cast (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : Path x' y' where
  toFun := γ
  continuous_toFun := γ.continuous
  source' := by simp [hx]
  target' := by simp [hy]

@[simp]
theorem symm_cast {a₁ a₂ b₁ b₂ : X} (γ : Path a₂ b₂) (ha : a₁ = a₂) (hb : b₁ = b₂) :
    (γ.cast ha hb).symm = γ.symm.cast hb ha :=
  rfl

@[simp]
theorem trans_cast {a₁ a₂ b₁ b₂ c₁ c₂ : X} (γ : Path a₂ b₂)
    (γ' : Path b₂ c₂) (ha : a₁ = a₂) (hb : b₁ = b₂) (hc : c₁ = c₂) :
    (γ.cast ha hb).trans (γ'.cast hb hc) = (γ.trans γ').cast ha hc :=
  rfl

@[simp]
theorem cast_coe (γ : Path x y) {x' y'} (hx : x' = x) (hy : y' = y) : (γ.cast hx hy : I → X) = γ :=
  rfl

@[continuity, fun_prop]
theorem symm_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b : ι → X} (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => (γ t).symm :=
  h.comp (continuous_id.prodMap continuous_symm)

@[continuity]
theorem continuous_symm : Continuous (symm : Path x y → Path y x) :=
  continuous_uncurry_iff.mp <| symm_continuous_family _ (continuous_fst.eval continuous_snd)

@[continuity]
theorem continuous_uncurry_extend_of_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b : ι → X} (γ : ∀ t : ι, Path (a t) (b t)) (h : Continuous ↿γ) :
    Continuous ↿fun t => (γ t).extend := by
  apply h.comp (continuous_id.prodMap continuous_projIcc)
  exact zero_le_one

@[continuity]
theorem trans_continuous_family {ι : Type*} [TopologicalSpace ι]
    {a b c : ι → X} (γ₁ : ∀ t : ι, Path (a t) (b t)) (h₁ : Continuous ↿γ₁)
    (γ₂ : ∀ t : ι, Path (b t) (c t)) (h₂ : Continuous ↿γ₂) :
    Continuous ↿fun t => (γ₁ t).trans (γ₂ t) := by
  have h₁' := Path.continuous_uncurry_extend_of_continuous_family γ₁ h₁
  have h₂' := Path.continuous_uncurry_extend_of_continuous_family γ₂ h₂
  simp only [HasUncurry.uncurry, CoeFun.coe, Path.trans, (· ∘ ·)]
  refine Continuous.if_le ?_ ?_ (continuous_subtype_val.comp continuous_snd) continuous_const ?_
  · change
      Continuous ((fun p : ι × ℝ => (γ₁ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x : I → ℝ))
    exact h₁'.comp (continuous_id.prodMap <| continuous_const.mul continuous_subtype_val)
  · change
      Continuous ((fun p : ι × ℝ => (γ₂ p.1).extend p.2) ∘ Prod.map id (fun x => 2 * x - 1 : I → ℝ))
    exact
      h₂'.comp
        (continuous_id.prodMap <|
          (continuous_const.mul continuous_subtype_val).sub continuous_const)
  · rintro st hst
    simp [hst, mul_inv_cancel₀ (two_ne_zero' ℝ)]

@[continuity]
theorem _root_.Continuous.path_trans {f : Y → Path x y} {g : Y → Path y z} :
    Continuous f → Continuous g → Continuous fun t => (f t).trans (g t) := by
  intro hf hg
  apply continuous_uncurry_iff.mp
  exact trans_continuous_family _ (continuous_uncurry_iff.mpr hf) _ (continuous_uncurry_iff.mpr hg)

@[continuity]
theorem continuous_trans {x y z : X} : Continuous fun ρ : Path x y × Path y z => ρ.1.trans ρ.2 :=
  continuous_fst.path_trans continuous_snd

/-! #### Product of paths -/

section Prod

variable {a₁ a₂ a₃ : X} {b₁ b₂ b₃ : Y}

protected def prod (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) : Path (a₁, b₁) (a₂, b₂) where
  toContinuousMap := ContinuousMap.prodMk γ₁.toContinuousMap γ₂.toContinuousMap
  source' := by simp
  target' := by simp

@[simp]
theorem prod_coe (γ₁ : Path a₁ a₂) (γ₂ : Path b₁ b₂) :
    ⇑(γ₁.prod γ₂) = fun t => (γ₁ t, γ₂ t) :=
  rfl

theorem trans_prod_eq_prod_trans (γ₁ : Path a₁ a₂) (δ₁ : Path a₂ a₃) (γ₂ : Path b₁ b₂)
    (δ₂ : Path b₂ b₃) : (γ₁.prod γ₂).trans (δ₁.prod δ₂) = (γ₁.trans δ₁).prod (γ₂.trans δ₂) := by
  ext t <;>
  unfold Path.trans <;>
  simp only [Path.coe_mk_mk, Path.prod_coe, Function.comp_apply] <;>
  split_ifs <;>
  rfl

end Prod

section Pi

variable {χ : ι → Type*} [∀ i, TopologicalSpace (χ i)] {as bs cs : ∀ i, χ i}

protected def pi (γ : ∀ i, Path (as i) (bs i)) : Path as bs where
  toContinuousMap := ContinuousMap.pi fun i => (γ i).toContinuousMap
  source' := by simp
  target' := by simp

@[simp]
theorem pi_coe (γ : ∀ i, Path (as i) (bs i)) : ⇑(Path.pi γ) = fun t i => γ i t :=
  rfl

theorem trans_pi_eq_pi_trans (γ₀ : ∀ i, Path (as i) (bs i)) (γ₁ : ∀ i, Path (bs i) (cs i)) :
    (Path.pi γ₀).trans (Path.pi γ₁) = Path.pi fun i => (γ₀ i).trans (γ₁ i) := by
  ext t i
  unfold Path.trans
  simp only [Path.coe_mk_mk, Function.comp_apply, pi_coe]
  split_ifs <;> rfl

end Pi

/-! #### Pointwise multiplication/addition of two paths in a topological (additive) group -/

@[to_additive "Pointwise addition of paths in a topological additive group."]
protected def mul [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁) (γ₂ : Path a₂ b₂) :
    Path (a₁ * a₂) (b₁ * b₂) :=
  (γ₁.prod γ₂).map continuous_mul

@[to_additive]
protected theorem mul_apply [Mul X] [ContinuousMul X] {a₁ b₁ a₂ b₂ : X} (γ₁ : Path a₁ b₁)
    (γ₂ : Path a₂ b₂) (t : unitInterval) : (γ₁.mul γ₂) t = γ₁ t * γ₂ t :=
  rfl

/-! #### Truncating a path -/

def truncate {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (t₀ t₁ : ℝ) :
    Path (γ.extend <| min t₀ t₁) (γ.extend t₁) where
  toFun s := γ.extend (min (max s t₀) t₁)
  continuous_toFun :=
    γ.continuous_extend.comp ((continuous_subtype_val.max continuous_const).min continuous_const)
  source' := by
    simp only [min_def, max_def']
    norm_cast
    split_ifs with h₁ h₂ h₃ h₄
    · simp [γ.extend_of_le_zero h₁]
    · congr
      linarith
    · have h₄ : t₁ ≤ 0 := le_of_lt (by simpa using h₂)
      simp [γ.extend_of_le_zero h₄, γ.extend_of_le_zero h₁]
    all_goals rfl
  target' := by
    simp only [min_def, max_def']
    norm_cast
    split_ifs with h₁ h₂ h₃
    · simp [γ.extend_of_one_le h₂]
    · rfl
    · have h₄ : 1 ≤ t₀ := le_of_lt (by simpa using h₁)
      simp [γ.extend_of_one_le h₄, γ.extend_of_one_le (h₄.trans h₃)]
    · rfl

def truncateOfLE {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) {t₀ t₁ : ℝ}
    (h : t₀ ≤ t₁) : Path (γ.extend t₀) (γ.extend t₁) :=
  (γ.truncate t₀ t₁).cast (by rw [min_eq_left h]) rfl

theorem truncate_range {a b : X} (γ : Path a b) {t₀ t₁ : ℝ} :
    range (γ.truncate t₀ t₁) ⊆ range γ := by
  rw [← γ.extend_range]
  simp only [range_subset_iff, SetCoe.exists, SetCoe.forall]
  intro x _hx
  simp only [DFunLike.coe, Path.truncate, mem_range_self]

@[continuity]
theorem truncate_continuous_family {a b : X} (γ : Path a b) :
    Continuous (fun x => γ.truncate x.1 x.2.1 x.2.2 : ℝ × ℝ × I → X) :=
  γ.continuous_extend.comp
    (((continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).max continuous_fst).min
      (continuous_fst.comp continuous_snd))

@[continuity]
theorem truncate_const_continuous_family {a b : X} (γ : Path a b)
    (t : ℝ) : Continuous ↿(γ.truncate t) := by
  have key : Continuous (fun x => (t, x) : ℝ × I → ℝ × ℝ × I) := by fun_prop
  exact γ.truncate_continuous_family.comp key

@[simp]
theorem truncate_self {a b : X} (γ : Path a b) (t : ℝ) :
    γ.truncate t t = (Path.refl <| γ.extend t).cast (by rw [min_self]) rfl := by
  ext x
  rw [cast_coe]
  simp only [truncate, DFunLike.coe, refl, min_def, max_def]
  split_ifs with h₁ h₂ <;> congr

@[simp 1001] -- Porting note: increase `simp` priority so left-hand side doesn't simplify
theorem truncate_zero_zero {a b : X} (γ : Path a b) :
    γ.truncate 0 0 = (Path.refl a).cast (by rw [min_self, γ.extend_zero]) γ.extend_zero := by
  convert γ.truncate_self 0

-- DISSOLVED: truncate_one_one

@[simp]
theorem truncate_zero_one {a b : X} (γ : Path a b) :
    γ.truncate 0 1 = γ.cast (by simp [zero_le_one, extend_zero]) (by simp) := by
  ext x
  rw [cast_coe]
  have : ↑x ∈ (Icc 0 1 : Set ℝ) := x.2
  rw [truncate, coe_mk_mk, max_eq_left this.1, min_eq_left this.2, extend_extends']

/-! #### Reparametrising a path -/

def reparam (γ : Path x y) (f : I → I) (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    Path x y where
  toFun := γ ∘ f
  continuous_toFun := by fun_prop
  source' := by simp [hf₀]
  target' := by simp [hf₁]

@[simp]
theorem coe_reparam (γ : Path x y) {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : ⇑(γ.reparam f hfcont hf₀ hf₁) = γ ∘ f :=
  rfl

@[simp]
theorem reparam_id (γ : Path x y) : γ.reparam id continuous_id rfl rfl = γ := by
  ext
  rfl

theorem range_reparam (γ : Path x y) {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0)
    (hf₁ : f 1 = 1) : range (γ.reparam f hfcont hf₀ hf₁) = range γ := by
  change range (γ ∘ f) = range γ
  have : range f = univ := by
    rw [range_eq_univ]
    intro t
    have h₁ : Continuous (Set.IccExtend (zero_le_one' ℝ) f) := by continuity
    have := intermediate_value_Icc (zero_le_one' ℝ) h₁.continuousOn
    · rw [IccExtend_left, IccExtend_right, Icc.mk_zero, Icc.mk_one, hf₀, hf₁] at this
      rcases this t.2 with ⟨w, hw₁, hw₂⟩
      rw [IccExtend_of_mem _ _ hw₁] at hw₂
      exact ⟨_, hw₂⟩
  rw [range_comp, this, image_univ]

theorem refl_reparam {f : I → I} (hfcont : Continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
    (refl x).reparam f hfcont hf₀ hf₁ = refl x := by
  ext
  simp

end Path

/-! ### Being joined by a path -/

def Joined (x y : X) : Prop :=
  Nonempty (Path x y)

@[refl]
theorem Joined.refl (x : X) : Joined x x :=
  ⟨Path.refl x⟩

def Joined.somePath (h : Joined x y) : Path x y :=
  Nonempty.some h

@[symm]
theorem Joined.symm {x y : X} (h : Joined x y) : Joined y x :=
  ⟨h.somePath.symm⟩

@[trans]
theorem Joined.trans {x y z : X} (hxy : Joined x y) (hyz : Joined y z) : Joined x z :=
  ⟨hxy.somePath.trans hyz.somePath⟩

variable (X)

def pathSetoid : Setoid X where
  r := Joined
  iseqv := Equivalence.mk Joined.refl Joined.symm Joined.trans

def ZerothHomotopy :=
  Quotient (pathSetoid X)

instance ZerothHomotopy.inhabited : Inhabited (ZerothHomotopy ℝ) :=
  ⟨@Quotient.mk' ℝ (pathSetoid ℝ) 0⟩

variable {X}

/-! ### Being joined by a path inside a set -/

def JoinedIn (F : Set X) (x y : X) : Prop :=
  ∃ γ : Path x y, ∀ t, γ t ∈ F

variable {F : Set X}

theorem JoinedIn.mem (h : JoinedIn F x y) : x ∈ F ∧ y ∈ F := by
  rcases h with ⟨γ, γ_in⟩
  have : γ 0 ∈ F ∧ γ 1 ∈ F := by constructor <;> apply γ_in
  simpa using this

theorem JoinedIn.source_mem (h : JoinedIn F x y) : x ∈ F :=
  h.mem.1

theorem JoinedIn.target_mem (h : JoinedIn F x y) : y ∈ F :=
  h.mem.2

def JoinedIn.somePath (h : JoinedIn F x y) : Path x y :=
  Classical.choose h

theorem JoinedIn.somePath_mem (h : JoinedIn F x y) (t : I) : h.somePath t ∈ F :=
  Classical.choose_spec h t

theorem JoinedIn.joined_subtype (h : JoinedIn F x y) :
    Joined (⟨x, h.source_mem⟩ : F) (⟨y, h.target_mem⟩ : F) :=
  ⟨{  toFun := fun t => ⟨h.somePath t, h.somePath_mem t⟩
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }⟩

theorem JoinedIn.ofLine {f : ℝ → X} (hf : ContinuousOn f I) (h₀ : f 0 = x) (h₁ : f 1 = y)
    (hF : f '' I ⊆ F) : JoinedIn F x y :=
  ⟨Path.ofLine hf h₀ h₁, fun t => hF <| Path.ofLine_mem hf h₀ h₁ t⟩

theorem JoinedIn.joined (h : JoinedIn F x y) : Joined x y :=
  ⟨h.somePath⟩

theorem joinedIn_iff_joined (x_in : x ∈ F) (y_in : y ∈ F) :
    JoinedIn F x y ↔ Joined (⟨x, x_in⟩ : F) (⟨y, y_in⟩ : F) :=
  ⟨fun h => h.joined_subtype, fun h => ⟨h.somePath.map continuous_subtype_val, by simp⟩⟩

@[simp]
theorem joinedIn_univ : JoinedIn univ x y ↔ Joined x y := by
  simp [JoinedIn, Joined, exists_true_iff_nonempty]

theorem JoinedIn.mono {U V : Set X} (h : JoinedIn U x y) (hUV : U ⊆ V) : JoinedIn V x y :=
  ⟨h.somePath, fun t => hUV (h.somePath_mem t)⟩

theorem JoinedIn.refl (h : x ∈ F) : JoinedIn F x x :=
  ⟨Path.refl x, fun _t => h⟩

@[symm]
theorem JoinedIn.symm (h : JoinedIn F x y) : JoinedIn F y x := by
  cases' h.mem with hx hy
  simp_all only [joinedIn_iff_joined]
  exact h.symm

theorem JoinedIn.trans (hxy : JoinedIn F x y) (hyz : JoinedIn F y z) : JoinedIn F x z := by
  cases' hxy.mem with hx hy
  cases' hyz.mem with hx hy
  simp_all only [joinedIn_iff_joined]
  exact hxy.trans hyz

theorem Specializes.joinedIn (h : x ⤳ y) (hx : x ∈ F) (hy : y ∈ F) : JoinedIn F x y := by
  refine ⟨⟨⟨Set.piecewise {1} (const I y) (const I x), ?_⟩, by simp, by simp⟩, fun t ↦ ?_⟩
  · exact isClosed_singleton.continuous_piecewise_of_specializes continuous_const continuous_const
      fun _ ↦ h
  · simp only [Path.coe_mk_mk, piecewise]
    split_ifs <;> assumption

theorem Inseparable.joinedIn (h : Inseparable x y) (hx : x ∈ F) (hy : y ∈ F) : JoinedIn F x y :=
  h.specializes.joinedIn hx hy

theorem JoinedIn.map_continuousOn (h : JoinedIn F x y) {f : X → Y} (hf : ContinuousOn f F) :
    JoinedIn (f '' F) (f x) (f y) :=
  let ⟨γ, hγ⟩ := h
  ⟨γ.map' <| hf.mono (range_subset_iff.mpr hγ), fun t ↦ mem_image_of_mem _ (hγ t)⟩

theorem JoinedIn.map (h : JoinedIn F x y) {f : X → Y} (hf : Continuous f) :
    JoinedIn (f '' F) (f x) (f y) :=
  h.map_continuousOn hf.continuousOn

theorem Topology.IsInducing.joinedIn_image {f : X → Y} (hf : IsInducing f) (hx : x ∈ F)
    (hy : y ∈ F) : JoinedIn (f '' F) (f x) (f y) ↔ JoinedIn F x y := by
  refine ⟨?_, (.map · hf.continuous)⟩
  rintro ⟨γ, hγ⟩
  choose γ' hγ'F hγ' using hγ
  have h₀ : x ⤳ γ' 0 := by rw [← hf.specializes_iff, hγ', γ.source]
  have h₁ : γ' 1 ⤳ y := by rw [← hf.specializes_iff, hγ', γ.target]
  have h : JoinedIn F (γ' 0) (γ' 1) := by
    refine ⟨⟨⟨γ', ?_⟩, rfl, rfl⟩, hγ'F⟩
    simpa only [hf.continuous_iff, comp_def, hγ'] using map_continuous γ
  exact (h₀.joinedIn hx (hγ'F _)).trans <| h.trans <| h₁.joinedIn (hγ'F _) hy

/-! ### Path component -/

def pathComponent (x : X) :=
  { y | Joined x y }

theorem mem_pathComponent_iff : x ∈ pathComponent y ↔ Joined y x := .rfl

@[simp]
theorem mem_pathComponent_self (x : X) : x ∈ pathComponent x :=
  Joined.refl x

@[simp]
theorem pathComponent.nonempty (x : X) : (pathComponent x).Nonempty :=
  ⟨x, mem_pathComponent_self x⟩

theorem mem_pathComponent_of_mem (h : x ∈ pathComponent y) : y ∈ pathComponent x :=
  Joined.symm h

theorem pathComponent_symm : x ∈ pathComponent y ↔ y ∈ pathComponent x :=
  ⟨fun h => mem_pathComponent_of_mem h, fun h => mem_pathComponent_of_mem h⟩

theorem pathComponent_congr (h : x ∈ pathComponent y) : pathComponent x = pathComponent y := by
  ext z
  constructor
  · intro h'
    rw [pathComponent_symm]
    exact (h.trans h').symm
  · intro h'
    rw [pathComponent_symm] at h' ⊢
    exact h'.trans h

theorem pathComponent_subset_component (x : X) : pathComponent x ⊆ connectedComponent x :=
  fun y h =>
  (isConnected_range h.somePath.continuous).subset_connectedComponent ⟨0, by simp⟩ ⟨1, by simp⟩

def pathComponentIn (x : X) (F : Set X) :=
  { y | JoinedIn F x y }

@[simp]
theorem pathComponentIn_univ (x : X) : pathComponentIn x univ = pathComponent x := by
  simp [pathComponentIn, pathComponent, JoinedIn, Joined, exists_true_iff_nonempty]

theorem Joined.mem_pathComponent (hyz : Joined y z) (hxy : y ∈ pathComponent x) :
    z ∈ pathComponent x :=
  hxy.trans hyz

theorem mem_pathComponentIn_self (h : x ∈ F) : x ∈ pathComponentIn x F :=
  JoinedIn.refl h

theorem pathComponentIn_subset : pathComponentIn x F ⊆ F :=
  fun _ hy ↦ hy.target_mem

theorem pathComponentIn_nonempty_iff : (pathComponentIn x F).Nonempty ↔ x ∈ F :=
  ⟨fun ⟨_, ⟨γ, hγ⟩⟩ ↦ γ.source ▸ hγ 0, fun hx ↦ ⟨x, mem_pathComponentIn_self hx⟩⟩

theorem pathComponentIn_congr (h : x ∈ pathComponentIn y F) :
    pathComponentIn x F = pathComponentIn y F := by
  ext; exact ⟨h.trans, h.symm.trans⟩

@[gcongr]
theorem pathComponentIn_mono {G : Set X} (h : F ⊆ G) :
    pathComponentIn x F ⊆ pathComponentIn x G :=
  fun _ ⟨γ, hγ⟩ ↦ ⟨γ, fun t ↦ h (hγ t)⟩

/-! ### Path connected sets -/

def IsPathConnected (F : Set X) : Prop :=
  ∃ x ∈ F, ∀ {y}, y ∈ F → JoinedIn F x y

theorem isPathConnected_iff_eq : IsPathConnected F ↔ ∃ x ∈ F, pathComponentIn x F = F := by
  constructor <;> rintro ⟨x, x_in, h⟩ <;> use x, x_in
  · ext y
    exact ⟨fun hy => hy.mem.2, h⟩
  · intro y y_in
    rwa [← h] at y_in

theorem IsPathConnected.joinedIn (h : IsPathConnected F) :
    ∀ᵉ (x ∈ F) (y ∈ F), JoinedIn F x y := fun _x x_in _y y_in =>
  let ⟨_b, _b_in, hb⟩ := h
  (hb x_in).symm.trans (hb y_in)

theorem isPathConnected_iff :
    IsPathConnected F ↔ F.Nonempty ∧ ∀ᵉ (x ∈ F) (y ∈ F), JoinedIn F x y :=
  ⟨fun h =>
    ⟨let ⟨b, b_in, _hb⟩ := h; ⟨b, b_in⟩, h.joinedIn⟩,
    fun ⟨⟨b, b_in⟩, h⟩ => ⟨b, b_in, fun x_in => h _ b_in _ x_in⟩⟩

theorem IsPathConnected.image' (hF : IsPathConnected F)
    {f : X → Y} (hf : ContinuousOn f F) : IsPathConnected (f '' F) := by
  rcases hF with ⟨x, x_in, hx⟩
  use f x, mem_image_of_mem f x_in
  rintro _ ⟨y, y_in, rfl⟩
  refine ⟨(hx y_in).somePath.map' ?_, fun t ↦ ⟨_, (hx y_in).somePath_mem t, rfl⟩⟩
  exact hf.mono (range_subset_iff.2 (hx y_in).somePath_mem)

theorem IsPathConnected.image (hF : IsPathConnected F) {f : X → Y} (hf : Continuous f) :
    IsPathConnected (f '' F) :=
  hF.image' hf.continuousOn

nonrec theorem Topology.IsInducing.isPathConnected_iff {f : X → Y} (hf : IsInducing f) :
    IsPathConnected F ↔ IsPathConnected (f '' F) := by
  simp only [IsPathConnected, forall_mem_image, exists_mem_image]
  refine exists_congr fun x ↦ and_congr_right fun hx ↦ forall₂_congr fun y hy ↦ ?_
  rw [hf.joinedIn_image hx hy]

alias Inducing.isPathConnected_iff := IsInducing.isPathConnected_iff

@[simp]
theorem Homeomorph.isPathConnected_image {s : Set X} (h : X ≃ₜ Y) :
    IsPathConnected (h '' s) ↔ IsPathConnected s :=
  h.isInducing.isPathConnected_iff.symm

@[simp]
theorem Homeomorph.isPathConnected_preimage {s : Set Y} (h : X ≃ₜ Y) :
    IsPathConnected (h ⁻¹' s) ↔ IsPathConnected s := by
  rw [← Homeomorph.image_symm]; exact h.symm.isPathConnected_image

theorem IsPathConnected.mem_pathComponent (h : IsPathConnected F) (x_in : x ∈ F) (y_in : y ∈ F) :
    y ∈ pathComponent x :=
  (h.joinedIn x x_in y y_in).joined

theorem IsPathConnected.subset_pathComponent (h : IsPathConnected F) (x_in : x ∈ F) :
    F ⊆ pathComponent x := fun _y y_in => h.mem_pathComponent x_in y_in

theorem IsPathConnected.subset_pathComponentIn {s : Set X} (hs : IsPathConnected s)
    (hxs : x ∈ s) (hsF : s ⊆ F) : s ⊆ pathComponentIn x F :=
  fun y hys ↦ (hs.joinedIn x hxs y hys).mono hsF

theorem isPathConnected_singleton (x : X) : IsPathConnected ({x} : Set X) := by
  refine ⟨x, rfl, ?_⟩
  rintro y rfl
  exact JoinedIn.refl rfl

theorem isPathConnected_pathComponentIn (h : x ∈ F) : IsPathConnected (pathComponentIn x F) :=
  ⟨x, mem_pathComponentIn_self h, fun ⟨γ, hγ⟩ ↦ by
    refine ⟨γ, fun t ↦
      ⟨(γ.truncateOfLE t.2.1).cast (γ.extend_zero.symm) (γ.extend_extends' t).symm, fun t' ↦ ?_⟩⟩
    dsimp [Path.truncateOfLE, Path.truncate]
    exact γ.extend_extends' ⟨min (max t'.1 0) t.1, by simp [t.2.1, t.2.2]⟩ ▸ hγ _⟩

theorem isPathConnected_pathComponent : IsPathConnected (pathComponent x) := by
  rw [← pathComponentIn_univ]
  exact isPathConnected_pathComponentIn (mem_univ x)

theorem IsPathConnected.union {U V : Set X} (hU : IsPathConnected U) (hV : IsPathConnected V)
    (hUV : (U ∩ V).Nonempty) : IsPathConnected (U ∪ V) := by
  rcases hUV with ⟨x, xU, xV⟩
  use x, Or.inl xU
  rintro y (yU | yV)
  · exact (hU.joinedIn x xU y yU).mono subset_union_left
  · exact (hV.joinedIn x xV y yV).mono subset_union_right

theorem IsPathConnected.preimage_coe {U W : Set X} (hW : IsPathConnected W) (hWU : W ⊆ U) :
    IsPathConnected (((↑) : U → X) ⁻¹' W) := by
  rwa [IsInducing.subtypeVal.isPathConnected_iff, Subtype.image_preimage_val, inter_eq_right.2 hWU]

theorem IsPathConnected.exists_path_through_family {n : ℕ}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) → X) (hp : ∀ i, p i ∈ s) :
    ∃ γ : Path (p 0) (p n), range γ ⊆ s ∧ ∀ i, p i ∈ range γ := by
  let p' : ℕ → X := fun k => if h : k < n + 1 then p ⟨k, h⟩ else p ⟨0, n.zero_lt_succ⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : Path (p' 0) (p' n), (∀ i ≤ n, p' i ∈ range γ) ∧ range γ ⊆ s := by
    have hp' : ∀ i ≤ n, p' i ∈ s := by
      intro i hi
      simp [p', Nat.lt_succ_of_le hi, hp]
    clear_value p'
    clear hp p
    induction' n with n hn
    · use Path.refl (p' 0)
      constructor
      · rintro i hi
        rw [Nat.le_zero.mp hi]
        exact ⟨0, rfl⟩
      · rw [range_subset_iff]
        rintro _x
        exact hp' 0 le_rfl
    · rcases hn fun i hi => hp' i <| Nat.le_succ_of_le hi with ⟨γ₀, hγ₀⟩
      rcases h.joinedIn (p' n) (hp' n n.le_succ) (p' <| n + 1) (hp' (n + 1) <| le_rfl) with
        ⟨γ₁, hγ₁⟩
      let γ : Path (p' 0) (p' <| n + 1) := γ₀.trans γ₁
      use γ
      have range_eq : range γ = range γ₀ ∪ range γ₁ := γ₀.trans_range γ₁
      constructor
      · rintro i hi
        by_cases hi' : i ≤ n
        · rw [range_eq]
          left
          exact hγ₀.1 i hi'
        · rw [not_le, ← Nat.succ_le_iff] at hi'
          have : i = n.succ := le_antisymm hi hi'
          rw [this]
          use 1
          exact γ.target
      · rw [range_eq]
        apply union_subset hγ₀.2
        rw [range_subset_iff]
        exact hγ₁
  have hpp' : ∀ k < n + 1, p k = p' k := by
    intro k hk
    simp only [p', hk, dif_pos]
    congr
    ext
    rw [Fin.val_cast_of_lt hk]
  use γ.cast (hpp' 0 n.zero_lt_succ) (hpp' n n.lt_succ_self)
  simp only [γ.cast_coe]
  refine And.intro hγ.2 ?_
  rintro ⟨i, hi⟩
  suffices p ⟨i, hi⟩ = p' i by convert hγ.1 i (Nat.le_of_lt_succ hi)
  rw [← hpp' i hi]
  suffices i = i % n.succ by congr
  rw [Nat.mod_eq_of_lt hi]

theorem IsPathConnected.exists_path_through_family' {n : ℕ}
    {s : Set X} (h : IsPathConnected s) (p : Fin (n + 1) → X) (hp : ∀ i, p i ∈ s) :
    ∃ (γ : Path (p 0) (p n)) (t : Fin (n + 1) → I), (∀ t, γ t ∈ s) ∧ ∀ i, γ (t i) = p i := by
  rcases h.exists_path_through_family p hp with ⟨γ, hγ⟩
  rcases hγ with ⟨h₁, h₂⟩
  simp only [range, mem_setOf_eq] at h₂
  rw [range_subset_iff] at h₁
  choose! t ht using h₂
  exact ⟨γ, t, h₁, ht⟩

/-! ### Path connected spaces -/

@[mk_iff]
class PathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- A path-connected space must be nonempty. -/
  nonempty : Nonempty X
  /-- Any two points in a path-connected space must be joined by a continuous path. -/
  joined : ∀ x y : X, Joined x y

theorem pathConnectedSpace_iff_zerothHomotopy :
    PathConnectedSpace X ↔ Nonempty (ZerothHomotopy X) ∧ Subsingleton (ZerothHomotopy X) := by
  letI := pathSetoid X
  constructor
  · intro h
    refine ⟨(nonempty_quotient_iff _).mpr h.1, ⟨?_⟩⟩
    rintro ⟨x⟩ ⟨y⟩
    exact Quotient.sound (PathConnectedSpace.joined x y)
  · unfold ZerothHomotopy
    rintro ⟨h, h'⟩
    exact ⟨(nonempty_quotient_iff _).mp h, fun x y => Quotient.exact <| Subsingleton.elim ⟦x⟧ ⟦y⟧⟩

namespace PathConnectedSpace

variable [PathConnectedSpace X]

def somePath (x y : X) : Path x y :=
  Nonempty.some (joined x y)

end PathConnectedSpace

theorem pathConnectedSpace_iff_univ : PathConnectedSpace X ↔ IsPathConnected (univ : Set X) := by
  simp [pathConnectedSpace_iff, isPathConnected_iff, nonempty_iff_univ_nonempty]

theorem isPathConnected_iff_pathConnectedSpace : IsPathConnected F ↔ PathConnectedSpace F := by
  rw [pathConnectedSpace_iff_univ, IsInducing.subtypeVal.isPathConnected_iff, image_univ,
    Subtype.range_val_subtype, setOf_mem_eq]

theorem isPathConnected_univ [PathConnectedSpace X] : IsPathConnected (univ : Set X) :=
  pathConnectedSpace_iff_univ.mp inferInstance

theorem isPathConnected_range [PathConnectedSpace X] {f : X → Y} (hf : Continuous f) :
    IsPathConnected (range f) := by
  rw [← image_univ]
  exact isPathConnected_univ.image hf

theorem Function.Surjective.pathConnectedSpace [PathConnectedSpace X]
    {f : X → Y} (hf : Surjective f) (hf' : Continuous f) : PathConnectedSpace Y := by
  rw [pathConnectedSpace_iff_univ, ← hf.range_eq]
  exact isPathConnected_range hf'

instance Quotient.instPathConnectedSpace {s : Setoid X} [PathConnectedSpace X] :
    PathConnectedSpace (Quotient s) :=
  Quotient.mk'_surjective.pathConnectedSpace continuous_coinduced_rng

instance Real.instPathConnectedSpace : PathConnectedSpace ℝ where
  joined x y := ⟨⟨⟨fun (t : I) ↦ (1 - t) * x + t * y, by fun_prop⟩, by simp, by simp⟩⟩
  nonempty := inferInstance

theorem pathConnectedSpace_iff_eq : PathConnectedSpace X ↔ ∃ x : X, pathComponent x = univ := by
  simp [pathConnectedSpace_iff_univ, isPathConnected_iff_eq]

instance (priority := 100) PathConnectedSpace.connectedSpace [PathConnectedSpace X] :
    ConnectedSpace X := by
  rw [connectedSpace_iff_connectedComponent]
  rcases isPathConnected_iff_eq.mp (pathConnectedSpace_iff_univ.mp ‹_›) with ⟨x, _x_in, hx⟩
  use x
  rw [← univ_subset_iff]
  exact (by simpa using hx : pathComponent x = univ) ▸ pathComponent_subset_component x

theorem IsPathConnected.isConnected (hF : IsPathConnected F) : IsConnected F := by
  rw [isConnected_iff_connectedSpace]
  rw [isPathConnected_iff_pathConnectedSpace] at hF
  exact @PathConnectedSpace.connectedSpace _ _ hF

namespace PathConnectedSpace

variable [PathConnectedSpace X]

theorem exists_path_through_family {n : ℕ} (p : Fin (n + 1) → X) :
    ∃ γ : Path (p 0) (p n), ∀ i, p i ∈ range γ := by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family p fun _i => True.intro with ⟨γ, -, h⟩
  exact ⟨γ, h⟩

theorem exists_path_through_family' {n : ℕ} (p : Fin (n + 1) → X) :
    ∃ (γ : Path (p 0) (p n)) (t : Fin (n + 1) → I), ∀ i, γ (t i) = p i := by
  have : IsPathConnected (univ : Set X) := pathConnectedSpace_iff_univ.mp (by infer_instance)
  rcases this.exists_path_through_family' p fun _i => True.intro with ⟨γ, t, -, h⟩
  exact ⟨γ, t, h⟩

end PathConnectedSpace

/-! ### Locally path connected spaces -/

section LocPathConnectedSpace

class LocPathConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  /-- Each neighborhood filter has a basis of path-connected neighborhoods. -/
  path_connected_basis : ∀ x : X, (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s) id

export LocPathConnectedSpace (path_connected_basis)

theorem LocPathConnectedSpace.of_bases {p : X → ι → Prop} {s : X → ι → Set X}
    (h : ∀ x, (𝓝 x).HasBasis (p x) (s x)) (h' : ∀ x i, p x i → IsPathConnected (s x i)) :
    LocPathConnectedSpace X where
  path_connected_basis x := by
    rw [hasBasis_self]
    intro t ht
    rcases (h x).mem_iff.mp ht with ⟨i, hpi, hi⟩
    exact ⟨s x i, (h x).mem_of_mem hpi, h' x i hpi, hi⟩

alias locPathConnected_of_bases := LocPathConnectedSpace.of_bases

variable [LocPathConnectedSpace X]

protected theorem IsOpen.pathComponentIn (x : X) (hF : IsOpen F) :
    IsOpen (pathComponentIn x F) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  let ⟨s, hs⟩ := (path_connected_basis y).mem_iff.mp (hF.mem_nhds (pathComponentIn_subset hy))
  exact mem_of_superset hs.1.1 <| pathComponentIn_congr hy ▸
    hs.1.2.subset_pathComponentIn (mem_of_mem_nhds hs.1.1) hs.2

protected theorem IsOpen.pathComponent (x : X) : IsOpen (pathComponent x) := by
  rw [← pathComponentIn_univ]
  exact isOpen_univ.pathComponentIn _

protected theorem IsClosed.pathComponent (x : X) : IsClosed (pathComponent x) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hxy
  rcases (path_connected_basis y).ex_mem with ⟨V, hVy, hVc⟩
  filter_upwards [hVy] with z hz hxz
  exact hxy <|  hxz.trans (hVc.joinedIn _ hz _ (mem_of_mem_nhds hVy)).joined

protected theorem IsClopen.pathComponent (x : X) : IsClopen (pathComponent x) :=
  ⟨.pathComponent x, .pathComponent x⟩

theorem pathConnectedSpace_iff_connectedSpace : PathConnectedSpace X ↔ ConnectedSpace X := by
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ⟨inferInstance, fun x y ↦ ?_⟩⟩
  rw [← mem_pathComponent_iff, (IsClopen.pathComponent _).eq_univ] <;> simp

theorem pathComponent_eq_connectedComponent (x : X) : pathComponent x = connectedComponent x :=
  (pathComponent_subset_component x).antisymm <|
    (IsClopen.pathComponent x).connectedComponent_subset (mem_pathComponent_self _)

theorem pathConnected_subset_basis {U : Set X} (h : IsOpen U) (hx : x ∈ U) :
    (𝓝 x).HasBasis (fun s : Set X => s ∈ 𝓝 x ∧ IsPathConnected s ∧ s ⊆ U) id :=
  (path_connected_basis x).hasBasis_self_subset (IsOpen.mem_nhds h hx)

theorem isOpen_isPathConnected_basis (x : X) :
    (𝓝 x).HasBasis (fun s : Set X ↦ IsOpen s ∧ x ∈ s ∧ IsPathConnected s) id := by
  refine ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨u, hu⟩ ↦ mem_nhds_iff.mpr ⟨u, hu.2, hu.1.1, hu.1.2.1⟩⟩⟩
  have ⟨u, hus, hu, hxu⟩ := mem_nhds_iff.mp hs
  exact ⟨pathComponentIn x u, ⟨hu.pathComponentIn _, ⟨mem_pathComponentIn_self hxu,
    isPathConnected_pathComponentIn hxu⟩⟩, pathComponentIn_subset.trans hus⟩

theorem Topology.IsOpenEmbedding.locPathConnectedSpace {e : Y → X} (he : IsOpenEmbedding e) :
    LocPathConnectedSpace Y :=
  have (y : Y) :
      (𝓝 y).HasBasis (fun s ↦ s ∈ 𝓝 (e y) ∧ IsPathConnected s ∧ s ⊆ range e) (e ⁻¹' ·) :=
    he.basis_nhds <| pathConnected_subset_basis he.isOpen_range (mem_range_self _)
  .of_bases this fun x s ⟨_, hs, hse⟩ ↦ by
    rwa [he.isPathConnected_iff, image_preimage_eq_of_subset hse]

alias OpenEmbedding.locPathConnectedSpace := IsOpenEmbedding.locPathConnectedSpace

theorem IsOpen.locPathConnectedSpace {U : Set X} (h : IsOpen U) : LocPathConnectedSpace U :=
  h.isOpenEmbedding_subtypeVal.locPathConnectedSpace

alias locPathConnected_of_isOpen := IsOpen.locPathConnectedSpace

theorem IsOpen.isConnected_iff_isPathConnected {U : Set X} (U_op : IsOpen U) :
    IsConnected U ↔ IsPathConnected U := by
  rw [isConnected_iff_connectedSpace, isPathConnected_iff_pathConnectedSpace]
  haveI := U_op.locPathConnectedSpace
  exact pathConnectedSpace_iff_connectedSpace.symm

instance : LocallyConnectedSpace X := by
  refine ⟨forall_imp (fun x h ↦ ⟨fun s ↦ ?_⟩) isOpen_isPathConnected_basis⟩
  refine ⟨fun hs ↦ ?_, fun ⟨u, ⟨hu, hxu, _⟩, hus⟩ ↦ mem_nhds_iff.mpr ⟨u, hus, hu, hxu⟩⟩
  let ⟨u, ⟨hu, hxu, hu'⟩, hus⟩ := (h.mem_iff' s).mp hs
  exact ⟨u, ⟨hu, hxu, hu'.isConnected⟩, hus⟩

lemma locPathConnectedSpace_iff_isOpen_pathComponentIn {X : Type*} [TopologicalSpace X] :
    LocPathConnectedSpace X ↔ ∀ (x : X) (u : Set X), IsOpen u → IsOpen (pathComponentIn x u) :=
  ⟨fun _ _ _ hu ↦ hu.pathComponentIn _, fun h ↦ ⟨fun x ↦ ⟨fun s ↦ by
    refine ⟨fun hs ↦ ?_, fun ⟨_, ht⟩ ↦ Filter.mem_of_superset ht.1.1 ht.2⟩
    let ⟨u, hu⟩ := mem_nhds_iff.mp hs
    exact ⟨pathComponentIn x u, ⟨(h x u hu.2.1).mem_nhds (mem_pathComponentIn_self hu.2.2),
      isPathConnected_pathComponentIn hu.2.2⟩, pathComponentIn_subset.trans hu.1⟩⟩⟩⟩

lemma locPathConnectedSpace_iff_pathComponentIn_mem_nhds {X : Type*} [TopologicalSpace X] :
    LocPathConnectedSpace X ↔
    ∀ x : X, ∀ u : Set X, IsOpen u → x ∈ u → pathComponentIn x u ∈ nhds x := by
  rw [locPathConnectedSpace_iff_isOpen_pathComponentIn]
  simp_rw [forall_comm (β := Set X), ← imp_forall_iff]
  refine forall_congr' fun u ↦ imp_congr_right fun _ ↦ ?_
  exact ⟨fun h x hxu ↦ (h x).mem_nhds (mem_pathComponentIn_self hxu),
    fun h x ↦ isOpen_iff_mem_nhds.mpr fun y hy ↦
      pathComponentIn_congr hy ▸ h y <| pathComponentIn_subset hy⟩

lemma LocPathConnectedSpace.coinduced {Y : Type*} (f : X → Y) :
    @LocPathConnectedSpace Y (.coinduced f ‹_›) := by
  let _ := TopologicalSpace.coinduced f ‹_›; have hf : Continuous f := continuous_coinduced_rng
  refine locPathConnectedSpace_iff_isOpen_pathComponentIn.mpr fun y u hu ↦
    isOpen_coinduced.mpr <| isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
  have hx' := preimage_mono pathComponentIn_subset hx
  refine mem_nhds_iff.mpr ⟨pathComponentIn x (f ⁻¹' u), ?_,
    (hu.preimage hf).pathComponentIn _, mem_pathComponentIn_self hx'⟩
  rw [← image_subset_iff, ← pathComponentIn_congr hx]
  exact ((isPathConnected_pathComponentIn hx').image hf).subset_pathComponentIn
    ⟨x, mem_pathComponentIn_self hx', rfl⟩ <|
    (image_mono pathComponentIn_subset).trans <| u.image_preimage_subset f

lemma Topology.IsQuotientMap.locPathConnectedSpace {f : X → Y} (h : IsQuotientMap f) :
    LocPathConnectedSpace Y :=
  h.2 ▸ LocPathConnectedSpace.coinduced f

instance Quot.locPathConnectedSpace {r : X → X → Prop} : LocPathConnectedSpace (Quot r) :=
  isQuotientMap_quot_mk.locPathConnectedSpace

instance Quotient.locPathConnectedSpace {s : Setoid X} : LocPathConnectedSpace (Quotient s) :=
  isQuotientMap_quotient_mk'.locPathConnectedSpace

instance Sum.locPathConnectedSpace.{u} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [LocPathConnectedSpace X] [LocPathConnectedSpace Y] :
    LocPathConnectedSpace (X ⊕ Y) := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]; intro x u hu hxu; rw [mem_nhds_iff]
  obtain x | y := x
  · refine ⟨Sum.inl '' (pathComponentIn x (Sum.inl ⁻¹' u)), ?_, ?_, ?_⟩
    · apply IsPathConnected.subset_pathComponentIn
      · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_inl
      · exact ⟨x, mem_pathComponentIn_self hxu, rfl⟩
      · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
    · exact isOpenMap_inl _ <| (hu.preimage continuous_inl).pathComponentIn _
    · exact ⟨x, mem_pathComponentIn_self hxu, rfl⟩
  · refine ⟨Sum.inr '' (pathComponentIn y (Sum.inr ⁻¹' u)), ?_, ?_, ?_⟩
    · apply IsPathConnected.subset_pathComponentIn
      · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_inr
      · exact ⟨y, mem_pathComponentIn_self hxu, rfl⟩
      · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
    · exact isOpenMap_inr _ <| (hu.preimage continuous_inr).pathComponentIn _
    · exact ⟨y, mem_pathComponentIn_self hxu, rfl⟩

instance Sigma.locPathConnectedSpace {X : ι → Type*}
    [(i : ι) → TopologicalSpace (X i)] [(i : ι) → LocPathConnectedSpace (X i)] :
    LocPathConnectedSpace ((i : ι) × X i) := by
  rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]; intro x u hu hxu; rw [mem_nhds_iff]
  refine ⟨(Sigma.mk x.1) '' (pathComponentIn x.2 ((Sigma.mk x.1) ⁻¹' u)), ?_, ?_, ?_⟩
  · apply IsPathConnected.subset_pathComponentIn
    · exact (isPathConnected_pathComponentIn (by exact hxu)).image continuous_sigmaMk
    · exact ⟨x.2, mem_pathComponentIn_self hxu, rfl⟩
    · exact (image_mono pathComponentIn_subset).trans (u.image_preimage_subset _)
  · exact isOpenMap_sigmaMk _ <| (hu.preimage continuous_sigmaMk).pathComponentIn _
  · exact ⟨x.2, mem_pathComponentIn_self hxu, rfl⟩

end LocPathConnectedSpace
