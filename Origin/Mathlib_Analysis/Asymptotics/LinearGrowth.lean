/-
Extracted from Analysis/Asymptotics/LinearGrowth.lean
Genuine: 58 of 68 | Dissolved: 8 | Infrastructure: 2
-/
import Origin.Core

/-!
# Linear growth

This file defines the linear growth of a sequence `u : ℕ → R`. This notion comes in two
versions, using a `liminf` and a `limsup` respectively. Most properties are developed for
`R = EReal`.

## Main definitions

- `linearGrowthInf`, `linearGrowthSup`: respectively, `liminf` and `limsup` of `(u n) / n`.
- `linearGrowthInfTopHom`, `linearGrowthSupBotHom`: the functions `linearGrowthInf`,
  `linearGrowthSup` as homomorphisms preserving finitary `Inf`/`Sup` respectively.

## TODO

Generalize statements from `EReal` to `ENNReal` (or others). This may need additional typeclasses.

Lemma about coercion from `ENNReal` to `EReal`. This needs additional lemmas about
`ENNReal.toEReal`.
-/

namespace LinearGrowth

open EReal Filter Function

open scoped Topology

/-! ### Definition -/

section definition

variable {R : Type*} [ConditionallyCompleteLattice R] [Div R] [NatCast R]

noncomputable def linearGrowthInf (u : ℕ → R) : R := liminf (fun n ↦ u n / n) atTop

noncomputable def linearGrowthSup (u : ℕ → R) : R := limsup (fun n ↦ u n / n) atTop

end definition

/-! ### Basic properties -/

section basic_properties

variable {R : Type*} [ConditionallyCompleteLattice R] [Div R] [NatCast R] {u v : ℕ → R}

lemma linearGrowthInf_congr (h : u =ᶠ[atTop] v) :
    linearGrowthInf u = linearGrowthInf v :=
  liminf_congr (h.mono fun _ uv ↦ uv ▸ rfl)

lemma linearGrowthSup_congr (h : u =ᶠ[atTop] v) :
    linearGrowthSup u = linearGrowthSup v :=
  limsup_congr (h.mono fun _ uv ↦ uv ▸ rfl)

lemma linearGrowthInf_le_linearGrowthSup
    (h : IsBoundedUnder (· ≤ ·) atTop fun n ↦ u n / n := by isBoundedDefault)
    (h' : IsBoundedUnder (· ≥ ·) atTop fun n ↦ u n / n := by isBoundedDefault) :
    linearGrowthInf u ≤ linearGrowthSup u :=
  liminf_le_limsup h h'

end basic_properties

section basic_properties

variable {u v : ℕ → EReal} {a b : EReal}

lemma linearGrowthInf_eventually_monotone (h : u ≤ᶠ[atTop] v) :
    linearGrowthInf u ≤ linearGrowthInf v :=
  liminf_le_liminf (h.mono fun n u_v ↦ EReal.monotone_div_right_of_nonneg n.cast_nonneg' u_v)

lemma linearGrowthInf_monotone (h : u ≤ v) : linearGrowthInf u ≤ linearGrowthInf v :=
  linearGrowthInf_eventually_monotone (Eventually.of_forall h)

lemma linearGrowthSup_eventually_monotone (h : u ≤ᶠ[atTop] v) :
    linearGrowthSup u ≤ linearGrowthSup v :=
  limsup_le_limsup (h.mono fun n u_v ↦ monotone_div_right_of_nonneg n.cast_nonneg' u_v)

lemma linearGrowthSup_monotone (h : u ≤ v) : linearGrowthSup u ≤ linearGrowthSup v :=
  linearGrowthSup_eventually_monotone (Eventually.of_forall h)

lemma linearGrowthInf_le_linearGrowthSup_of_frequently_le (h : ∃ᶠ n in atTop, u n ≤ v n) :
    linearGrowthInf u ≤ linearGrowthSup v :=
  (liminf_le_limsup_of_frequently_le) <| h.mono fun n u_v ↦ by gcongr

lemma linearGrowthInf_le_iff :
    linearGrowthInf u ≤ a ↔ ∀ b > a, ∃ᶠ n : ℕ in atTop, u n ≤ b * n := by
  rw [linearGrowthInf, liminf_le_iff']
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n), mul_comm _ b]

lemma le_linearGrowthInf_iff :
    a ≤ linearGrowthInf u ↔ ∀ b < a, ∀ᶠ n : ℕ in atTop, b * n ≤ u n := by
  rw [linearGrowthInf, le_liminf_iff']
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

lemma linearGrowthSup_le_iff :
    linearGrowthSup u ≤ a ↔ ∀ b > a, ∀ᶠ n : ℕ in atTop, u n ≤ b * n := by
  rw [linearGrowthSup, limsup_le_iff']
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n), mul_comm _ b]

lemma le_linearGrowthSup_iff :
    a ≤ linearGrowthSup u ↔ ∀ b < a, ∃ᶠ n : ℕ in atTop, b * n ≤ u n := by
  rw [linearGrowthSup, le_limsup_iff']
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

lemma frequently_le_mul (h : linearGrowthInf u < a) :
    ∃ᶠ n : ℕ in atTop, u n ≤ a * n :=
  linearGrowthInf_le_iff.1 (le_refl (linearGrowthInf u)) a h

lemma eventually_mul_le (h : a < linearGrowthInf u) :
    ∀ᶠ n : ℕ in atTop, a * n ≤ u n :=
  le_linearGrowthInf_iff.1 (le_refl (linearGrowthInf u)) a h

lemma eventually_le_mul (h : linearGrowthSup u < a) :
    ∀ᶠ n : ℕ in atTop, u n ≤ a * n :=
  linearGrowthSup_le_iff.1 (le_refl (linearGrowthSup u)) a h

lemma frequently_mul_le (h : a < linearGrowthSup u) :
    ∃ᶠ n : ℕ in atTop, a * n ≤ u n :=
  le_linearGrowthSup_iff.1 (le_refl (linearGrowthSup u)) a h

lemma _root_.Frequently.linearGrowthInf_le (h : ∃ᶠ n : ℕ in atTop, u n ≤ a * n) :
    linearGrowthInf u ≤ a :=
  linearGrowthInf_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans <| by gcongr

lemma _root_.Eventually.le_linearGrowthInf (h : ∀ᶠ n : ℕ in atTop, a * n ≤ u n) :
    a ≤ linearGrowthInf u :=
  le_linearGrowthInf_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' <| by gcongr

lemma _root_.Eventually.linearGrowthSup_le (h : ∀ᶠ n : ℕ in atTop, u n ≤ a * n) :
    linearGrowthSup u ≤ a :=
  linearGrowthSup_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans <| by gcongr

lemma _root_.Frequently.le_linearGrowthSup (h : ∃ᶠ n : ℕ in atTop, a * n ≤ u n) :
    a ≤ linearGrowthSup u :=
  le_linearGrowthSup_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' <| by gcongr

/-! ### Special cases -/

lemma linearGrowthSup_bot : linearGrowthSup (⊥ : ℕ → EReal) = (⊥ : EReal) := by
  nth_rw 2 [← limsup_const (f := atTop (α := ℕ)) ⊥]
  refine limsup_congr <| (eventually_gt_atTop 0).mono fun n n_pos ↦ ?_
  exact bot_div_of_pos_ne_top (by positivity) (natCast_ne_top n)

lemma linearGrowthInf_bot : linearGrowthInf (⊥ : ℕ → EReal) = (⊥ : EReal) := by
  apply le_bot_iff.1
  rw [← linearGrowthSup_bot]
  exact linearGrowthInf_le_linearGrowthSup

lemma linearGrowthInf_top : linearGrowthInf ⊤ = (⊤ : EReal) := by
  nth_rw 2 [← liminf_const (f := atTop (α := ℕ)) ⊤]
  refine liminf_congr (eventually_atTop.2 ?_)
  exact ⟨1, fun n n_pos ↦ top_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩

lemma linearGrowthSup_top : linearGrowthSup (⊤ : ℕ → EReal) = (⊤ : EReal) := by
  apply top_le_iff.1
  rw [← linearGrowthInf_top]
  exact linearGrowthInf_le_linearGrowthSup

lemma linearGrowthInf_const (h : b ≠ ⊥) (h' : b ≠ ⊤) : linearGrowthInf (fun _ ↦ b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat h h').liminf_eq

lemma linearGrowthSup_const (h : b ≠ ⊥) (h' : b ≠ ⊤) : linearGrowthSup (fun _ ↦ b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat h h').limsup_eq

lemma linearGrowthInf_zero : linearGrowthInf 0 = (0 : EReal) :=
  linearGrowthInf_const zero_ne_bot zero_ne_top

lemma linearGrowthSup_zero : linearGrowthSup 0 = (0 : EReal) :=
  linearGrowthSup_const zero_ne_bot zero_ne_top

lemma linearGrowthInf_const_mul_self : linearGrowthInf (fun n ↦ a * n) = a :=
  le_antisymm (Frequently.linearGrowthInf_le (Frequently.of_forall fun _ ↦ le_refl _))
    (Eventually.le_linearGrowthInf (Eventually.of_forall fun _ ↦ le_refl _))

lemma linearGrowthSup_const_mul_self : linearGrowthSup (fun n ↦ a * n) = a :=
  le_antisymm (Eventually.linearGrowthSup_le (Eventually.of_forall fun _ ↦ le_refl _))
    (Frequently.le_linearGrowthSup (Frequently.of_forall fun _ ↦ le_refl _))

lemma linearGrowthInf_natCast_nonneg (v : ℕ → ℕ) :
    0 ≤ linearGrowthInf fun n ↦ (v n : EReal) :=
  (le_liminf_of_le) (Eventually.of_forall fun n ↦ div_nonneg (v n).cast_nonneg' n.cast_nonneg')

lemma tendsto_atTop_of_linearGrowthInf_pos (h : 0 < linearGrowthInf u) :
    Tendsto u atTop (𝓝 ⊤) := by
  obtain ⟨a, a_0, a_v⟩ := exists_between h
  apply tendsto_nhds_top_mono _ ((le_linearGrowthInf_iff (u := u)).1 (le_refl _) a a_v)
  refine tendsto_nhds_top_iff_real.2 fun M ↦ eventually_atTop.2 ?_
  lift a to ℝ using ⟨ne_top_of_lt a_v, ne_bot_of_gt a_0⟩
  rw [EReal.coe_pos] at a_0
  obtain ⟨n, hn⟩ := exists_nat_ge (M / a)
  refine ⟨n + 1, fun k k_n ↦ ?_⟩
  rw [← coe_coe_eq_natCast, ← coe_mul, EReal.coe_lt_coe_iff, mul_comm]
  exact (div_lt_iff₀ a_0).1 (hn.trans_lt (Nat.cast_lt.2 k_n))

/-! ### Addition and negation -/

lemma le_linearGrowthInf_add :
    linearGrowthInf u + linearGrowthInf v ≤ linearGrowthInf (u + v) := by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, ← add_div_of_nonneg_right n.cast_nonneg']

lemma linearGrowthInf_add_le (h : linearGrowthSup u ≠ ⊥ ∨ linearGrowthInf v ≠ ⊤)
    (h' : linearGrowthSup u ≠ ⊤ ∨ linearGrowthInf v ≠ ⊥) :
    linearGrowthInf (u + v) ≤ linearGrowthSup u + linearGrowthInf v := by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, ← add_div_of_nonneg_right n.cast_nonneg']

lemma linearGrowthInf_add_le' (h : linearGrowthInf u ≠ ⊥ ∨ linearGrowthSup v ≠ ⊤)
    (h' : linearGrowthInf u ≠ ⊤ ∨ linearGrowthSup v ≠ ⊥) :
    linearGrowthInf (u + v) ≤ linearGrowthInf u + linearGrowthSup v := by
  rw [add_comm u v, add_comm (linearGrowthInf u) (linearGrowthSup v)]
  exact linearGrowthInf_add_le h'.symm h.symm

lemma le_linearGrowthSup_add : linearGrowthSup u + linearGrowthInf v ≤ linearGrowthSup (u + v) := by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, add_div_of_nonneg_right n.cast_nonneg']

lemma le_linearGrowthSup_add' :
    linearGrowthInf u + linearGrowthSup v ≤ linearGrowthSup (u + v) := by
  rw [add_comm u v, add_comm (linearGrowthInf u) (linearGrowthSup v)]
  exact le_linearGrowthSup_add

lemma linearGrowthSup_add_le (h : linearGrowthSup u ≠ ⊥ ∨ linearGrowthSup v ≠ ⊤)
    (h' : linearGrowthSup u ≠ ⊤ ∨ linearGrowthSup v ≠ ⊥) :
    linearGrowthSup (u + v) ≤ linearGrowthSup u + linearGrowthSup v := by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, add_div_of_nonneg_right n.cast_nonneg']

lemma linearGrowthInf_neg : linearGrowthInf (-u) = - linearGrowthSup u := by
  rw [linearGrowthSup, ← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.neg_apply, div_eq_mul_inv, div_eq_mul_inv, ← neg_mul]

lemma linearGrowthSup_inv : linearGrowthSup (-u) = - linearGrowthInf u := by
  rw [linearGrowthInf, ← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.neg_apply, div_eq_mul_inv, div_eq_mul_inv, ← neg_mul]

/-! ### Affine bounds -/

lemma linearGrowthInf_le_of_eventually_le (hb : b ≠ ⊤) (h : ∀ᶠ n in atTop, u n ≤ v n + b) :
    linearGrowthInf u ≤ linearGrowthInf v := by
  apply (linearGrowthInf_eventually_monotone h).trans
  rcases eq_bot_or_bot_lt b with rfl | b_bot
  · simp only [add_bot, ← Pi.bot_def, linearGrowthInf_bot, bot_le]
  · apply (linearGrowthInf_add_le' _ _).trans_eq <;> rw [linearGrowthSup_const b_bot.ne' hb]
    · exact add_zero (linearGrowthInf v)
    · exact Or.inr EReal.zero_ne_top
    · exact Or.inr EReal.zero_ne_bot

lemma linearGrowthSup_le_of_eventually_le (hb : b ≠ ⊤) (h : ∀ᶠ n in atTop, u n ≤ v n + b) :
    linearGrowthSup u ≤ linearGrowthSup v := by
  apply (linearGrowthSup_eventually_monotone h).trans
  rcases eq_bot_or_bot_lt b with rfl | b_bot
  · simp only [add_bot, ← Pi.bot_def, linearGrowthSup_bot, bot_le]
  · apply (linearGrowthSup_add_le _ _).trans_eq <;> rw [linearGrowthSup_const b_bot.ne' hb]
    · exact add_zero (linearGrowthSup v)
    · exact Or.inr EReal.zero_ne_top
    · exact Or.inr EReal.zero_ne_bot

/-! ### Infimum and supremum -/

lemma linearGrowthInf_inf :
    linearGrowthInf (u ⊓ v) = min (linearGrowthInf u) (linearGrowthInf v) := by
  rw [linearGrowthInf, linearGrowthInf, linearGrowthInf, ← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

noncomputable def linearGrowthInfTopHom : InfTopHom (ℕ → EReal) EReal where
  toFun := linearGrowthInf
  map_inf' _ _ := linearGrowthInf_inf
  map_top' := linearGrowthInf_top

lemma linearGrowthInf_biInf {α : Type*} (u : α → ℕ → EReal) {s : Set α} (hs : s.Finite) :
    linearGrowthInf (⨅ x ∈ s, u x) = ⨅ x ∈ s, linearGrowthInf (u x) := by
  have := map_finset_inf linearGrowthInfTopHom hs.toFinset u
  simpa only [linearGrowthInfTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply]

lemma linearGrowthInf_iInf {ι : Type*} [Finite ι] (u : ι → ℕ → EReal) :
    linearGrowthInf (⨅ i, u i) = ⨅ i, linearGrowthInf (u i) := by
  rw [← iInf_univ, linearGrowthInf_biInf u Set.finite_univ, iInf_univ]

lemma linearGrowthSup_sup :
    linearGrowthSup (u ⊔ v) = max (linearGrowthSup u) (linearGrowthSup v) := by
  rw [linearGrowthSup, linearGrowthSup, linearGrowthSup, ← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

noncomputable def linearGrowthSupBotHom : SupBotHom (ℕ → EReal) EReal where
  toFun := linearGrowthSup
  map_sup' _ _ := linearGrowthSup_sup
  map_bot' := linearGrowthSup_bot

lemma linearGrowthSup_biSup {α : Type*} (u : α → ℕ → EReal) {s : Set α} (hs : s.Finite) :
    linearGrowthSup (⨆ x ∈ s, u x) = ⨆ x ∈ s, linearGrowthSup (u x) := by
  have := map_finset_sup linearGrowthSupBotHom hs.toFinset u
  simpa only [linearGrowthSupBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply]

lemma linearGrowthSup_iSup {ι : Type*} [Finite ι] (u : ι → ℕ → EReal) :
    linearGrowthSup (⨆ i, u i) = ⨆ i, linearGrowthSup (u i) := by
  rw [← iSup_univ, linearGrowthSup_biSup u Set.finite_univ, iSup_univ]

end basic_properties

/-! ### Composition -/

section composition

variable {u : ℕ → EReal} {v : ℕ → ℕ}

lemma Real.eventually_atTop_exists_int_between {a b : ℝ} (h : a < b) :
    ∀ᶠ x : ℝ in atTop, ∃ n : ℤ, a * x ≤ n ∧ n ≤ b * x := by
  refine (eventually_ge_atTop (b - a)⁻¹).mono fun x ab_x ↦ ?_
  rw [inv_le_iff_one_le_mul₀ (sub_pos_of_lt h), mul_comm, sub_mul, le_sub_iff_add_le'] at ab_x
  exact ⟨_, le_of_add_le_add_right (ab_x.trans (Int.lt_floor_add_one _).le), Int.floor_le _⟩

lemma Real.eventually_atTop_exists_nat_between {a b : ℝ} (h : a < b) (hb : 0 ≤ b) :
    ∀ᶠ x : ℝ in atTop, ∃ n : ℕ, a * x ≤ n ∧ n ≤ b * x := by
  filter_upwards [eventually_ge_atTop 0, Real.eventually_atTop_exists_int_between h]
    with x x_0 ⟨m, m_a, m_b⟩
  refine ⟨m.toNat, m_a.trans (Int.cast_le.2 m.self_le_toNat), ?_⟩
  apply le_of_eq_of_le _ (max_le m_b (mul_nonneg hb x_0))
  norm_cast
  exact Int.toNat_eq_max m

lemma EReal.eventually_atTop_exists_nat_between {a b : EReal} (h : a < b) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, a * n ≤ m ∧ m ≤ b * n :=
  match a with
  | ⊤ => (not_top_lt h).rec
  | ⊥ => by
    refine Eventually.of_forall fun n ↦ ⟨0, ?_, ?_⟩ <;> rw [Nat.cast_zero]
    · apply mul_nonpos_iff.2 -- Split apply and exact for a 0.5s. gain
      exact .inr ⟨bot_le, n.cast_nonneg'⟩
    · positivity
  | (a : ℝ) =>
    match b with
    | ⊤ => by
      refine (eventually_gt_atTop 0).mono fun n n_0 ↦ ?_
      obtain ⟨m, hm⟩ := exists_nat_ge_mul h.ne n
      exact ⟨m, hm, le_of_le_of_eq le_top (top_mul_of_pos (Nat.cast_pos'.2 n_0)).symm⟩
    | ⊥ => (not_lt_bot h).rec
    | (b : ℝ) => by
      obtain ⟨x, hx⟩ := eventually_atTop.1 <| Real.eventually_atTop_exists_nat_between
        (EReal.coe_lt_coe_iff.1 h) (EReal.coe_nonneg.1 hb)
      obtain ⟨n, x_n⟩ := exists_nat_ge x
      refine eventually_atTop.2 ⟨n, fun k n_k ↦ ?_⟩
      simp only [← coe_coe_eq_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      exact hx k (x_n.trans (Nat.cast_le.2 n_k))

-- DISSOLVED: tendsto_atTop_of_linearGrowthInf_natCast_pos

lemma le_linearGrowthInf_comp (hu : 0 ≤ᶠ[atTop] u) (hv : Tendsto v atTop atTop) :
    (linearGrowthInf fun n ↦ v n : EReal) * linearGrowthInf u ≤ linearGrowthInf (u ∘ v) := by
  have uv_0 : 0 ≤ linearGrowthInf (u ∘ v) := by
    rw [← linearGrowthInf_const zero_ne_bot zero_ne_top]
    exact linearGrowthInf_eventually_monotone (hv.eventually hu)
  apply EReal.mul_le_of_forall_lt_of_nonneg (linearGrowthInf_natCast_nonneg v) uv_0
  refine fun a ⟨_, a_v⟩ b ⟨b_0, b_u⟩ ↦ Eventually.le_linearGrowthInf ?_
  have b_uv := eventually_map.1 ((eventually_mul_le b_u).filter_mono hv)
  filter_upwards [b_uv, eventually_lt_of_lt_liminf a_v, eventually_gt_atTop 0]
    with n b_uvn a_vn n_0
  replace a_vn := ((lt_div_iff (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 a_vn).le
  rw [comp_apply, mul_comm a b, mul_assoc b a]
  exact b_uvn.trans' <| by gcongr

-- DISSOLVED: linearGrowthSup_comp_le

/-! ### Monotone sequences -/

lemma _root_.Monotone.linearGrowthSup_nonneg (h : Monotone u) (h' : u ≠ ⊥) :
    0 ≤ linearGrowthSup u :=
  (h.linearGrowthInf_nonneg h').trans (linearGrowthInf_le_linearGrowthSup)

lemma linearGrowthSup_comp_nonneg (h : Monotone u) (h' : u ≠ ⊥) (hv : Tendsto v atTop atTop) :
    0 ≤ linearGrowthSup (u ∘ v) :=
  (linearGrowthInf_comp_nonneg h h' hv).trans linearGrowthInf_le_linearGrowthSup

-- DISSOLVED: _root_.Monotone.linearGrowthInf_comp_le

-- DISSOLVED: _root_.Monotone.le_linearGrowthSup_comp

-- DISSOLVED: _root_.Monotone.linearGrowthInf_comp

-- DISSOLVED: _root_.Monotone.linearGrowthSup_comp

-- DISSOLVED: _root_.Monotone.linearGrowthInf_comp_mul

-- DISSOLVED: _root_.Monotone.linearGrowthSup_comp_mul

end composition

end LinearGrowth
