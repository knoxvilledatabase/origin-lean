/-
Extracted from Analysis/Normed/Field/Basic.lean
Genuine: 95 | Conflates: 7 | Dissolved: 0 | Infrastructure: 71
-/
import Origin.Core
import Mathlib.Algebra.Algebra.NonUnitalSubalgebra
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Submodule

noncomputable section

/-!
# Normed fields

In this file we define (semi)normed rings and fields. We also prove some theorems about these
definitions.

Some useful results that relate the topology of the normed field to the discrete topology include:
* `norm_eq_one_iff_ne_zero_of_discrete`

Methods for constructing a normed ring/field instance from a given real absolute value on a
ring/field are given in:
* AbsoluteValue.toNormedRing
* AbsoluteValue.toNormedField
-/

variable {α : Type*} {β : Type*} {ι : Type*}

open Filter

open scoped Topology NNReal

class NonUnitalSeminormedRing (α : Type*) extends Norm α, NonUnitalRing α,
  PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is submultiplicative. -/
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b

class SeminormedRing (α : Type*) extends Norm α, Ring α, PseudoMetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is submultiplicative. -/
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b

instance (priority := 100) SeminormedRing.toNonUnitalSeminormedRing [β : SeminormedRing α] :
    NonUnitalSeminormedRing α :=
  { β with }

class NonUnitalNormedRing (α : Type*) extends Norm α, NonUnitalRing α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is submultiplicative. -/
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b

instance (priority := 100) NonUnitalNormedRing.toNonUnitalSeminormedRing
    [β : NonUnitalNormedRing α] : NonUnitalSeminormedRing α :=
  { β with }

class NormedRing (α : Type*) extends Norm α, Ring α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is submultiplicative. -/
  norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b

class NormedDivisionRing (α : Type*) extends Norm α, DivisionRing α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is multiplicative. -/
  norm_mul' : ∀ a b, norm (a * b) = norm a * norm b

instance (priority := 100) NormedDivisionRing.toNormedRing [β : NormedDivisionRing α] :
    NormedRing α :=
  { β with norm_mul := fun a b => (NormedDivisionRing.norm_mul' a b).le }

instance (priority := 100) NormedRing.toSeminormedRing [β : NormedRing α] : SeminormedRing α :=
  { β with }

instance (priority := 100) NormedRing.toNonUnitalNormedRing [β : NormedRing α] :
    NonUnitalNormedRing α :=
  { β with }

class NonUnitalSeminormedCommRing (α : Type*) extends NonUnitalSeminormedRing α where
  /-- Multiplication is commutative. -/
  mul_comm : ∀ x y : α, x * y = y * x

class NonUnitalNormedCommRing (α : Type*) extends NonUnitalNormedRing α where
  /-- Multiplication is commutative. -/
  mul_comm : ∀ x y : α, x * y = y * x

instance (priority := 100) NonUnitalNormedCommRing.toNonUnitalSeminormedCommRing
    [β : NonUnitalNormedCommRing α] : NonUnitalSeminormedCommRing α :=
  { β with }

class SeminormedCommRing (α : Type*) extends SeminormedRing α where
  /-- Multiplication is commutative. -/
  mul_comm : ∀ x y : α, x * y = y * x

class NormedCommRing (α : Type*) extends NormedRing α where
  /-- Multiplication is commutative. -/
  mul_comm : ∀ x y : α, x * y = y * x

instance (priority := 100) SeminormedCommRing.toNonUnitalSeminormedCommRing
    [β : SeminormedCommRing α] : NonUnitalSeminormedCommRing α :=
  { β with }

instance (priority := 100) NormedCommRing.toNonUnitalNormedCommRing
    [β : NormedCommRing α] : NonUnitalNormedCommRing α :=
  { β with }

instance (priority := 100) NormedCommRing.toSeminormedCommRing [β : NormedCommRing α] :
    SeminormedCommRing α :=
  { β with }

instance PUnit.normedCommRing : NormedCommRing PUnit :=
  { PUnit.normedAddCommGroup, PUnit.commRing with
    norm_mul := fun _ _ => by simp }

class NormOneClass (α : Type*) [Norm α] [One α] : Prop where
  /-- The norm of the multiplicative identity is 1. -/
  norm_one : ‖(1 : α)‖ = 1

export NormOneClass (norm_one)

attribute [simp] norm_one

@[simp]
theorem nnnorm_one [SeminormedAddCommGroup α] [One α] [NormOneClass α] : ‖(1 : α)‖₊ = 1 :=
  NNReal.eq norm_one

-- CONFLATES (assumes ground = zero): NormOneClass.nontrivial
theorem NormOneClass.nontrivial (α : Type*) [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    Nontrivial α :=
  nontrivial_of_ne 0 1 <| ne_of_apply_ne norm <| by simp

instance (priority := 100) NonUnitalSeminormedCommRing.toNonUnitalCommRing
    [β : NonUnitalSeminormedCommRing α] : NonUnitalCommRing α :=
  { β with }

instance (priority := 100) SeminormedCommRing.toCommRing [β : SeminormedCommRing α] : CommRing α :=
  { β with }

instance (priority := 100) NonUnitalNormedRing.toNormedAddCommGroup [β : NonUnitalNormedRing α] :
    NormedAddCommGroup α :=
  { β with }

instance (priority := 100) NonUnitalSeminormedRing.toSeminormedAddCommGroup
    [NonUnitalSeminormedRing α] : SeminormedAddCommGroup α :=
  { ‹NonUnitalSeminormedRing α› with }

instance ULift.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass (ULift α) :=
  ⟨by simp [ULift.norm_def]⟩

instance Prod.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α]
    [SeminormedAddCommGroup β] [One β] [NormOneClass β] : NormOneClass (α × β) :=
  ⟨by simp [Prod.norm_def]⟩

instance Pi.normOneClass {ι : Type*} {α : ι → Type*} [Nonempty ι] [Fintype ι]
    [∀ i, SeminormedAddCommGroup (α i)] [∀ i, One (α i)] [∀ i, NormOneClass (α i)] :
    NormOneClass (∀ i, α i) :=
  ⟨by simpa [Pi.norm_def] using Finset.sup_const Finset.univ_nonempty 1⟩

instance MulOpposite.normOneClass [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass αᵐᵒᵖ :=
  ⟨@norm_one α _ _ _⟩

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α] {a a₁ a₂ b c : α}

theorem norm_mul_le (a b : α) : ‖a * b‖ ≤ ‖a‖ * ‖b‖ :=
  NonUnitalSeminormedRing.norm_mul _ _

theorem nnnorm_mul_le (a b : α) : ‖a * b‖₊ ≤ ‖a‖₊ * ‖b‖₊ := by
  simpa only [← norm_toNNReal, ← Real.toNNReal_mul (norm_nonneg _)] using
    Real.toNNReal_mono (norm_mul_le _ _)

lemma norm_mul_le_of_le {r₁ r₂ : ℝ} (h₁ : ‖a₁‖ ≤ r₁) (h₂ : ‖a₂‖ ≤ r₂) : ‖a₁ * a₂‖ ≤ r₁ * r₂ :=
  (norm_mul_le ..).trans <| mul_le_mul h₁ h₂ (norm_nonneg _) ((norm_nonneg _).trans h₁)

lemma nnnorm_mul_le_of_le {r₁ r₂ : ℝ≥0} (h₁ : ‖a₁‖₊ ≤ r₁) (h₂ : ‖a₂‖₊ ≤ r₂) :
    ‖a₁ * a₂‖₊ ≤ r₁ * r₂ := (nnnorm_mul_le ..).trans <| mul_le_mul' h₁ h₂

lemma norm_mul₃_le : ‖a * b * c‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ := norm_mul_le_of_le (norm_mul_le ..) le_rfl

lemma nnnorm_mul₃_le : ‖a * b * c‖₊ ≤ ‖a‖₊ * ‖b‖₊ * ‖c‖₊ :=
  nnnorm_mul_le_of_le (norm_mul_le ..) le_rfl

-- CONFLATES (assumes ground = zero): one_le_norm_one
theorem one_le_norm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖ :=
  (le_mul_iff_one_le_left <| norm_pos_iff.mpr (one_ne_zero : (1 : β) ≠ 0)).mp
    (by simpa only [mul_one] using norm_mul_le (1 : β) 1)

-- CONFLATES (assumes ground = zero): one_le_nnnorm_one
theorem one_le_nnnorm_one (β) [NormedRing β] [Nontrivial β] : 1 ≤ ‖(1 : β)‖₊ :=
  one_le_norm_one β

theorem mulLeft_bound (x : α) : ∀ y : α, ‖AddMonoidHom.mulLeft x y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_mul_le x

theorem mulRight_bound (x : α) : ∀ y : α, ‖AddMonoidHom.mulRight x y‖ ≤ ‖x‖ * ‖y‖ := fun y => by
  rw [mul_comm]
  exact norm_mul_le y x

instance NonUnitalSubalgebra.nonUnitalSeminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalSeminormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalSeminormedRing s :=
  { s.toSubmodule.seminormedAddCommGroup, s.toNonUnitalRing with
    norm_mul := fun a b => norm_mul_le a.1 b.1 }

@[nolint unusedArguments]
instance (priority := 75) NonUnitalSubalgebraClass.nonUnitalSeminormedRing {S 𝕜 E : Type*}
    [CommRing 𝕜] [NonUnitalSeminormedRing E] [Module 𝕜 E] [SetLike S E] [NonUnitalSubringClass S E]
    [SMulMemClass S 𝕜 E] (s : S) :
    NonUnitalSeminormedRing s :=
  { AddSubgroupClass.seminormedAddCommGroup s, NonUnitalSubringClass.toNonUnitalRing s with
    norm_mul := fun a b => norm_mul_le a.1 b.1 }

instance NonUnitalSubalgebra.nonUnitalNormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalNormedRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) : NonUnitalNormedRing s :=
  { s.nonUnitalSeminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

instance (priority := 75) NonUnitalSubalgebraClass.nonUnitalNormedRing {S 𝕜 E : Type*}
    [CommRing 𝕜] [NonUnitalNormedRing E] [Module 𝕜 E] [SetLike S E] [NonUnitalSubringClass S E]
    [SMulMemClass S 𝕜 E] (s : S) :
    NonUnitalNormedRing s :=
  { nonUnitalSeminormedRing s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

instance ULift.nonUnitalSeminormedRing : NonUnitalSeminormedRing (ULift α) :=
  { ULift.seminormedAddCommGroup, ULift.nonUnitalRing with
    norm_mul := fun x y => (norm_mul_le x.down y.down : _) }

instance Prod.nonUnitalSeminormedRing [NonUnitalSeminormedRing β] :
    NonUnitalSeminormedRing (α × β) :=
  { seminormedAddCommGroup, instNonUnitalRing with
    norm_mul := fun x y =>
      calc
        ‖x * y‖ = ‖(x.1 * y.1, x.2 * y.2)‖ := rfl
        _ = max ‖x.1 * y.1‖ ‖x.2 * y.2‖ := rfl
        _ ≤ max (‖x.1‖ * ‖y.1‖) (‖x.2‖ * ‖y.2‖) :=
          (max_le_max (norm_mul_le x.1 y.1) (norm_mul_le x.2 y.2))
        _ = max (‖x.1‖ * ‖y.1‖) (‖y.2‖ * ‖x.2‖) := by simp [mul_comm]
        _ ≤ max ‖x.1‖ ‖x.2‖ * max ‖y.2‖ ‖y.1‖ := by
          apply max_mul_mul_le_max_mul_max <;> simp [norm_nonneg]
        _ = max ‖x.1‖ ‖x.2‖ * max ‖y.1‖ ‖y.2‖ := by simp [max_comm]
        _ = ‖x‖ * ‖y‖ := rfl
         }

instance MulOpposite.instNonUnitalSeminormedRing : NonUnitalSeminormedRing αᵐᵒᵖ where
  __ := instNonUnitalRing
  __ := instSeminormedAddCommGroup
  norm_mul := MulOpposite.rec' fun x ↦ MulOpposite.rec' fun y ↦
    (norm_mul_le y x).trans_eq (mul_comm _ _)

end NonUnitalSeminormedRing

section SeminormedRing

variable [SeminormedRing α] {a b c : α}

instance Subalgebra.seminormedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedRing s :=
  { s.toSubmodule.seminormedAddCommGroup, s.toRing with
    norm_mul := fun a b => norm_mul_le a.1 b.1 }

@[nolint unusedArguments]
instance (priority := 75) SubalgebraClass.seminormedRing {S 𝕜 E : Type*} [CommRing 𝕜]
    [SeminormedRing E] [Algebra 𝕜 E] [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E]
    (s : S) : SeminormedRing s :=
  { AddSubgroupClass.seminormedAddCommGroup s, SubringClass.toRing s with
    norm_mul := fun a b => norm_mul_le a.1 b.1 }

instance Subalgebra.normedRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedRing s :=
  { s.seminormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

instance (priority := 75) SubalgebraClass.normedRing {S 𝕜 E : Type*} [CommRing 𝕜]
    [NormedRing E] [Algebra 𝕜 E] [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E]
    (s : S) : NormedRing s :=
  { seminormedRing s with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

theorem Nat.norm_cast_le : ∀ n : ℕ, ‖(n : α)‖ ≤ n * ‖(1 : α)‖
  | 0 => by simp
  | n + 1 => by
    rw [n.cast_succ, n.cast_succ, add_mul, one_mul]
    exact norm_add_le_of_le (Nat.norm_cast_le n) le_rfl

theorem List.norm_prod_le' : ∀ {l : List α}, l ≠ [] → ‖l.prod‖ ≤ (l.map norm).prod
  | [], h => (h rfl).elim
  | [a], _ => by simp
  | a::b::l, _ => by
    rw [List.map_cons, List.prod_cons, List.prod_cons (a := ‖a‖)]
    refine le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    exact List.norm_prod_le' (List.cons_ne_nil b l)

theorem List.nnnorm_prod_le' {l : List α} (hl : l ≠ []) : ‖l.prod‖₊ ≤ (l.map nnnorm).prod :=
  (List.norm_prod_le' hl).trans_eq <| by simp [NNReal.coe_list_prod, List.map_map]

theorem List.norm_prod_le [NormOneClass α] : ∀ l : List α, ‖l.prod‖ ≤ (l.map norm).prod
  | [] => by simp
  | a::l => List.norm_prod_le' (List.cons_ne_nil a l)

theorem List.nnnorm_prod_le [NormOneClass α] (l : List α) : ‖l.prod‖₊ ≤ (l.map nnnorm).prod :=
  l.norm_prod_le.trans_eq <| by simp [NNReal.coe_list_prod, List.map_map]

theorem Finset.norm_prod_le' {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α) : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  rcases s with ⟨⟨l⟩, hl⟩
  have : l.map f ≠ [] := by simpa using hs
  simpa using List.norm_prod_le' this

theorem Finset.nnnorm_prod_le' {α : Type*} [NormedCommRing α] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → α) : ‖∏ i ∈ s, f i‖₊ ≤ ∏ i ∈ s, ‖f i‖₊ :=
  (s.norm_prod_le' hs f).trans_eq <| by simp [NNReal.coe_prod]

theorem Finset.norm_prod_le {α : Type*} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι → α) : ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := by
  rcases s with ⟨⟨l⟩, hl⟩
  simpa using (l.map f).norm_prod_le

theorem Finset.nnnorm_prod_le {α : Type*} [NormedCommRing α] [NormOneClass α] (s : Finset ι)
    (f : ι → α) : ‖∏ i ∈ s, f i‖₊ ≤ ∏ i ∈ s, ‖f i‖₊ :=
  (s.norm_prod_le f).trans_eq <| by simp [NNReal.coe_prod]

theorem nnnorm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n
  | 1, _ => by simp only [pow_one, le_rfl]
  | n + 2, _ => by
    simpa only [pow_succ' _ (n + 1)] using
      le_trans (nnnorm_mul_le _ _) (mul_le_mul_left' (nnnorm_pow_le' a n.succ_pos) _)

theorem nnnorm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n :=
  Nat.recOn n (by simp only [pow_zero, nnnorm_one, le_rfl])
    fun k _hk => nnnorm_pow_le' a k.succ_pos

theorem norm_pow_le' (a : α) {n : ℕ} (h : 0 < n) : ‖a ^ n‖ ≤ ‖a‖ ^ n := by
  simpa only [NNReal.coe_pow, coe_nnnorm] using NNReal.coe_mono (nnnorm_pow_le' a h)

theorem norm_pow_le [NormOneClass α] (a : α) (n : ℕ) : ‖a ^ n‖ ≤ ‖a‖ ^ n :=
  Nat.recOn n (by simp only [pow_zero, norm_one, le_rfl])
    fun n _hn => norm_pow_le' a n.succ_pos

theorem eventually_norm_pow_le (a : α) : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ ‖a‖ ^ n :=
  eventually_atTop.mpr ⟨1, fun _b h => norm_pow_le' a (Nat.succ_le_iff.mp h)⟩

instance ULift.seminormedRing : SeminormedRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.ring with }

instance Prod.seminormedRing [SeminormedRing β] : SeminormedRing (α × β) :=
  { nonUnitalSeminormedRing, instRing with }

instance MulOpposite.instSeminormedRing : SeminormedRing αᵐᵒᵖ where
  __ := instRing
  __ := instNonUnitalSeminormedRing

lemma norm_sub_mul_le (ha : ‖a‖ ≤ 1) : ‖c - a * b‖ ≤ ‖c - a‖ + ‖1 - b‖ :=
  calc
    _ ≤ ‖c - a‖ + ‖a * (1 - b)‖ := by
        simpa [mul_one_sub] using norm_sub_le_norm_sub_add_norm_sub c a (a * b)
    _ ≤ ‖c - a‖ + ‖a‖ * ‖1 - b‖ := by gcongr; exact norm_mul_le ..
    _ ≤ ‖c - a‖ + 1 * ‖1 - b‖ := by gcongr
    _ = ‖c - a‖ + ‖1 - b‖ := by simp

lemma norm_sub_mul_le' (hb : ‖b‖ ≤ 1) : ‖c - a * b‖ ≤ ‖1 - a‖ + ‖c - b‖ := by
  rw [add_comm]; exact norm_sub_mul_le (α := αᵐᵒᵖ) hb

lemma nnnorm_sub_mul_le (ha : ‖a‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖c - a‖₊ + ‖1 - b‖₊ := norm_sub_mul_le ha

lemma nnnorm_sub_mul_le' (hb : ‖b‖₊ ≤ 1) : ‖c - a * b‖₊ ≤ ‖1 - a‖₊ + ‖c - b‖₊ := norm_sub_mul_le' hb

lemma norm_commutator_units_sub_one_le (a b : αˣ) :
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ ≤ 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ :=
  calc
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖ = ‖(a * b - b * a) * a⁻¹.val * b⁻¹.val‖ := by simp [sub_mul, *]
    _ ≤ ‖(a * b - b * a : α)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := norm_mul₃_le
    _ = ‖(a - 1 : α) * (b - 1) - (b - 1) * (a - 1)‖ * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      simp_rw [sub_one_mul, mul_sub_one]; abel_nf
    _ ≤ (‖(a - 1 : α) * (b - 1)‖ + ‖(b - 1 : α) * (a - 1)‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr; exact norm_sub_le ..
    _ ≤ (‖a.val - 1‖ * ‖b.val - 1‖ + ‖b.val - 1‖ * ‖a.val - 1‖) * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ := by
      gcongr <;> exact norm_mul_le ..
    _ = 2 * ‖a⁻¹.val‖ * ‖b⁻¹.val‖ * ‖a.val - 1‖ * ‖b.val - 1‖ := by ring

lemma nnnorm_commutator_units_sub_one_le (a b : αˣ) :
    ‖(a * b * a⁻¹ * b⁻¹).val - 1‖₊ ≤ 2 * ‖a⁻¹.val‖₊ * ‖b⁻¹.val‖₊ * ‖a.val - 1‖₊ * ‖b.val - 1‖₊ := by
  simpa using norm_commutator_units_sub_one_le a b

def RingHom.IsBounded {α : Type*} [SeminormedRing α] {β : Type*} [SeminormedRing β]
    (f : α →+* β) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : α, norm (f x) ≤ C * norm x

end SeminormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

instance ULift.nonUnitalNormedRing : NonUnitalNormedRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.normedAddCommGroup with }

instance Prod.nonUnitalNormedRing [NonUnitalNormedRing β] : NonUnitalNormedRing (α × β) :=
  { Prod.nonUnitalSeminormedRing, Prod.normedAddCommGroup with }

instance MulOpposite.instNonUnitalNormedRing : NonUnitalNormedRing αᵐᵒᵖ where
  __ := instNonUnitalRing
  __ := instNonUnitalSeminormedRing
  __ := instNormedAddCommGroup

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

-- CONFLATES (assumes ground = zero): Units.norm_pos
theorem Units.norm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖ :=
  norm_pos_iff.mpr (Units.ne_zero x)

-- CONFLATES (assumes ground = zero): Units.nnnorm_pos
theorem Units.nnnorm_pos [Nontrivial α] (x : αˣ) : 0 < ‖(x : α)‖₊ :=
  x.norm_pos

instance ULift.normedRing : NormedRing (ULift α) :=
  { ULift.seminormedRing, ULift.normedAddCommGroup with }

instance Prod.normedRing [NormedRing β] : NormedRing (α × β) :=
  { nonUnitalNormedRing, instRing with }

instance MulOpposite.instNormedRing : NormedRing αᵐᵒᵖ where
  __ := instRing
  __ := instSeminormedRing
  __ := instNormedAddCommGroup

end NormedRing

section NonUnitalSeminormedCommRing

variable [NonUnitalSeminormedCommRing α]

instance ULift.nonUnitalSeminormedCommRing : NonUnitalSeminormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.nonUnitalCommRing with }

instance Prod.nonUnitalSeminormedCommRing [NonUnitalSeminormedCommRing β] :
    NonUnitalSeminormedCommRing (α × β) :=
  { nonUnitalSeminormedRing, instNonUnitalCommRing with }

instance MulOpposite.instNonUnitalSeminormedCommRing : NonUnitalSeminormedCommRing αᵐᵒᵖ where
  __ := instNonUnitalSeminormedRing
  __ := instNonUnitalCommRing

end NonUnitalSeminormedCommRing

section NonUnitalNormedCommRing

variable [NonUnitalNormedCommRing α]

instance NonUnitalSubalgebra.nonUnitalSeminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalSeminormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalSeminormedCommRing s :=
  { s.nonUnitalSeminormedRing, s.toNonUnitalCommRing with }

instance NonUnitalSubalgebra.nonUnitalNormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*}
    [NonUnitalNormedCommRing E] [Module 𝕜 E] (s : NonUnitalSubalgebra 𝕜 E) :
    NonUnitalNormedCommRing s :=
  { s.nonUnitalSeminormedCommRing, s.nonUnitalNormedRing with }

instance ULift.nonUnitalNormedCommRing : NonUnitalNormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedCommRing, ULift.normedAddCommGroup with }

instance Prod.nonUnitalNormedCommRing [NonUnitalNormedCommRing β] :
    NonUnitalNormedCommRing (α × β) :=
  { Prod.nonUnitalSeminormedCommRing, Prod.normedAddCommGroup with }

instance MulOpposite.instNonUnitalNormedCommRing : NonUnitalNormedCommRing αᵐᵒᵖ where
  __ := instNonUnitalNormedRing
  __ := instNonUnitalSeminormedCommRing

end NonUnitalNormedCommRing

section SeminormedCommRing

variable [SeminormedCommRing α]

instance ULift.seminormedCommRing : SeminormedCommRing (ULift α) :=
  { ULift.nonUnitalSeminormedRing, ULift.commRing with }

instance Prod.seminormedCommRing [SeminormedCommRing β] : SeminormedCommRing (α × β) :=
  { Prod.nonUnitalSeminormedCommRing, instCommRing with }

instance MulOpposite.instSeminormedCommRing : SeminormedCommRing αᵐᵒᵖ where
  __ := instSeminormedRing
  __ := instNonUnitalSeminormedCommRing

end SeminormedCommRing

section NormedCommRing

instance Subalgebra.seminormedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [SeminormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : SeminormedCommRing s :=
  { s.seminormedRing, s.toCommRing with }

instance Subalgebra.normedCommRing {𝕜 : Type*} [CommRing 𝕜] {E : Type*} [NormedCommRing E]
    [Algebra 𝕜 E] (s : Subalgebra 𝕜 E) : NormedCommRing s :=
  { s.seminormedCommRing, s.normedRing with }

variable [NormedCommRing α]

instance ULift.normedCommRing : NormedCommRing (ULift α) :=
  { ULift.normedRing (α := α), ULift.seminormedCommRing with }

instance Prod.normedCommRing [NormedCommRing β] : NormedCommRing (α × β) :=
  { nonUnitalNormedRing, instCommRing with }

instance MulOpposite.instNormedCommRing : NormedCommRing αᵐᵒᵖ where
  __ := instNormedRing
  __ := instSeminormedCommRing

theorem IsPowMul.restriction {R S : Type*} [NormedCommRing R] [CommRing S] [Algebra R S]
    (A : Subalgebra R S) {f : S → ℝ} (hf_pm : IsPowMul f) :
    IsPowMul fun x : A => f x.val := fun x n hn => by
  simpa [SubsemiringClass.coe_pow] using hf_pm (↑x) hn

end NormedCommRing

section NormedDivisionRing

variable [NormedDivisionRing α] {a b : α}

@[simp]
theorem norm_mul (a b : α) : ‖a * b‖ = ‖a‖ * ‖b‖ :=
  NormedDivisionRing.norm_mul' a b

instance (priority := 900) NormedDivisionRing.to_normOneClass : NormOneClass α :=
  ⟨mul_left_cancel₀ (mt norm_eq_zero.1 (one_ne_zero' α)) <| by rw [← norm_mul, mul_one, mul_one]⟩

instance isAbsoluteValue_norm : IsAbsoluteValue (norm : α → ℝ) where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := norm_eq_zero
  abv_add' := norm_add_le
  abv_mul' := norm_mul

@[simp]
theorem nnnorm_mul (a b : α) : ‖a * b‖₊ = ‖a‖₊ * ‖b‖₊ :=
  NNReal.eq <| norm_mul a b

@[simps]
def normHom : α →*₀ ℝ where
  toFun := (‖·‖)
  map_zero' := norm_zero
  map_one' := norm_one
  map_mul' := norm_mul

@[simps]
def nnnormHom : α →*₀ ℝ≥0 where
  toFun := (‖·‖₊)
  map_zero' := nnnorm_zero
  map_one' := nnnorm_one
  map_mul' := nnnorm_mul

@[simp]
theorem norm_pow (a : α) : ∀ n : ℕ, ‖a ^ n‖ = ‖a‖ ^ n :=
  (normHom.toMonoidHom : α →* ℝ).map_pow a

@[simp]
theorem nnnorm_pow (a : α) (n : ℕ) : ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  (nnnormHom.toMonoidHom : α →* ℝ≥0).map_pow a n

protected theorem List.norm_prod (l : List α) : ‖l.prod‖ = (l.map norm).prod :=
  map_list_prod (normHom.toMonoidHom : α →* ℝ) _

protected theorem List.nnnorm_prod (l : List α) : ‖l.prod‖₊ = (l.map nnnorm).prod :=
  map_list_prod (nnnormHom.toMonoidHom : α →* ℝ≥0) _

@[simp]
theorem norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖ :=
  map_div₀ (normHom : α →*₀ ℝ) a b

@[simp]
theorem nnnorm_div (a b : α) : ‖a / b‖₊ = ‖a‖₊ / ‖b‖₊ :=
  map_div₀ (nnnormHom : α →*₀ ℝ≥0) a b

@[simp]
theorem norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹ :=
  map_inv₀ (normHom : α →*₀ ℝ) a

@[simp]
theorem nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹ :=
  NNReal.eq <| by simp

@[simp]
theorem norm_zpow : ∀ (a : α) (n : ℤ), ‖a ^ n‖ = ‖a‖ ^ n :=
  map_zpow₀ (normHom : α →*₀ ℝ)

@[simp]
theorem nnnorm_zpow : ∀ (a : α) (n : ℤ), ‖a ^ n‖₊ = ‖a‖₊ ^ n :=
  map_zpow₀ (nnnormHom : α →*₀ ℝ≥0)

theorem dist_inv_inv₀ {z w : α} (hz : z ≠ 0) (hw : w ≠ 0) :
    dist z⁻¹ w⁻¹ = dist z w / (‖z‖ * ‖w‖) := by
  rw [dist_eq_norm, inv_sub_inv' hz hw, norm_mul, norm_mul, norm_inv, norm_inv, mul_comm ‖z‖⁻¹,
    mul_assoc, dist_eq_norm', div_eq_mul_inv, mul_inv]

theorem nndist_inv_inv₀ {z w : α} (hz : z ≠ 0) (hw : w ≠ 0) :
    nndist z⁻¹ w⁻¹ = nndist z w / (‖z‖₊ * ‖w‖₊) :=
  NNReal.eq <| dist_inv_inv₀ hz hw

lemma norm_commutator_sub_one_le (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖a * b * a⁻¹ * b⁻¹ - 1‖ ≤ 2 * ‖a‖⁻¹ * ‖b‖⁻¹ * ‖a - 1‖ * ‖b - 1‖ := by
  simpa using norm_commutator_units_sub_one_le (.mk0 a ha) (.mk0 b hb)

lemma nnnorm_commutator_sub_one_le (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖a * b * a⁻¹ * b⁻¹ - 1‖₊ ≤ 2 * ‖a‖₊⁻¹ * ‖b‖₊⁻¹ * ‖a - 1‖₊ * ‖b - 1‖₊ := by
  simpa using nnnorm_commutator_units_sub_one_le (.mk0 a ha) (.mk0 b hb)

namespace NormedDivisionRing

section Discrete

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [DiscreteTopology 𝕜]

lemma norm_eq_one_iff_ne_zero_of_discrete {x : 𝕜} : ‖x‖ = 1 ↔ x ≠ 0 := by
  constructor <;> intro hx
  · contrapose! hx
    simp [hx]
  · have : IsOpen {(0 : 𝕜)} := isOpen_discrete {0}
    simp_rw [Metric.isOpen_singleton_iff, dist_eq_norm, sub_zero] at this
    obtain ⟨ε, εpos, h'⟩ := this
    wlog h : ‖x‖ < 1 generalizing 𝕜 with H
    · push_neg at h
      rcases h.eq_or_lt with h|h
      · rw [h]
      replace h := norm_inv x ▸ inv_lt_one_of_one_lt₀ h
      rw [← inv_inj, inv_one, ← norm_inv]
      exact H (by simpa) h' h
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ‖x‖ ^ k < ε := exists_pow_lt_of_lt_one εpos h
    rw [← norm_pow] at hk
    specialize h' _ hk
    simp [hx] at h'

@[simp]
lemma norm_le_one_of_discrete
    (x : 𝕜) : ‖x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl|hx
  · simp
  · simp [norm_eq_one_iff_ne_zero_of_discrete.mpr hx]

lemma discreteTopology_unit_closedBall_eq_univ : (Metric.closedBall 0 1 : Set 𝕜) = Set.univ := by
  ext
  simp

end Discrete

end NormedDivisionRing

end NormedDivisionRing

class NormedField (α : Type*) extends Norm α, Field α, MetricSpace α where
  /-- The distance is induced by the norm. -/
  dist_eq : ∀ x y, dist x y = norm (x - y)
  /-- The norm is multiplicative. -/
  norm_mul' : ∀ a b, norm (a * b) = norm a * norm b

-- CONFLATES (assumes ground = zero): NontriviallyNormedField
class NontriviallyNormedField (α : Type*) extends NormedField α where
  /-- The norm attains a value exceeding 1. -/
  non_trivial : ∃ x : α, 1 < ‖x‖

class DenselyNormedField (α : Type*) extends NormedField α where
  /-- The range of the norm is dense in the collection of nonnegative real numbers. -/
  lt_norm_lt : ∀ x y : ℝ, 0 ≤ x → x < y → ∃ a : α, x < ‖a‖ ∧ ‖a‖ < y

section NormedField

instance (priority := 100) DenselyNormedField.toNontriviallyNormedField [DenselyNormedField α] :
    NontriviallyNormedField α where
  non_trivial :=
    let ⟨a, h, _⟩ := DenselyNormedField.lt_norm_lt 1 2 zero_le_one one_lt_two
    ⟨a, h⟩

variable [NormedField α]

instance (priority := 100) NormedField.toNormedDivisionRing : NormedDivisionRing α :=
  { ‹NormedField α› with }

instance (priority := 100) NormedField.toNormedCommRing : NormedCommRing α :=
  { ‹NormedField α› with norm_mul := fun a b => (norm_mul a b).le }

@[simp]
theorem norm_prod (s : Finset β) (f : β → α) : ‖∏ b ∈ s, f b‖ = ∏ b ∈ s, ‖f b‖ :=
  map_prod normHom.toMonoidHom f s

@[simp]
theorem nnnorm_prod (s : Finset β) (f : β → α) : ‖∏ b ∈ s, f b‖₊ = ∏ b ∈ s, ‖f b‖₊ :=
  map_prod nnnormHom.toMonoidHom f s

end NormedField

namespace NormedField

section Nontrivially

variable (α) [NontriviallyNormedField α]

theorem exists_one_lt_norm : ∃ x : α, 1 < ‖x‖ :=
  ‹NontriviallyNormedField α›.non_trivial

theorem exists_lt_norm (r : ℝ) : ∃ x : α, r < ‖x‖ :=
  let ⟨w, hw⟩ := exists_one_lt_norm α
  let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw
  ⟨w ^ n, by rwa [norm_pow]⟩

theorem exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ‖x‖ ∧ ‖x‖ < r :=
  let ⟨w, hw⟩ := exists_lt_norm α r⁻¹
  ⟨w⁻¹, by rwa [← Set.mem_Ioo, norm_inv, ← Set.mem_inv, Set.inv_Ioo_0_left hr]⟩

theorem exists_norm_lt_one : ∃ x : α, 0 < ‖x‖ ∧ ‖x‖ < 1 :=
  exists_norm_lt α one_pos

variable {α}

@[instance]
theorem punctured_nhds_neBot (x : α) : NeBot (𝓝[≠] x) := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  rintro ε ε0
  rcases exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩
  refine ⟨x + b, mt (Set.mem_singleton_iff.trans add_right_eq_self).1 <| norm_pos_iff.1 hb0, ?_⟩
  rwa [dist_comm, dist_eq_norm, add_sub_cancel_left]

@[instance]
theorem nhdsWithin_isUnit_neBot : NeBot (𝓝[{ x : α | IsUnit x }] 0) := by
  simpa only [isUnit_iff_ne_zero] using punctured_nhds_neBot (0 : α)

end Nontrivially

section Densely

variable (α) [DenselyNormedField α]

theorem exists_lt_norm_lt {r₁ r₂ : ℝ} (h₀ : 0 ≤ r₁) (h : r₁ < r₂) : ∃ x : α, r₁ < ‖x‖ ∧ ‖x‖ < r₂ :=
  DenselyNormedField.lt_norm_lt r₁ r₂ h₀ h

theorem exists_lt_nnnorm_lt {r₁ r₂ : ℝ≥0} (h : r₁ < r₂) : ∃ x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂ :=
  mod_cast exists_lt_norm_lt α r₁.prop h

instance denselyOrdered_range_norm : DenselyOrdered (Set.range (norm : α → ℝ)) where
  dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_norm_lt α (norm_nonneg _) hxy
    exact ⟨⟨‖z‖, z, rfl⟩, h⟩

instance denselyOrdered_range_nnnorm : DenselyOrdered (Set.range (nnnorm : α → ℝ≥0)) where
  dense := by
    rintro ⟨-, x, rfl⟩ ⟨-, y, rfl⟩ hxy
    let ⟨z, h⟩ := exists_lt_nnnorm_lt α hxy
    exact ⟨⟨‖z‖₊, z, rfl⟩, h⟩

end Densely

end NormedField

-- CONFLATES (assumes ground = zero): NontriviallyNormedField.ofNormNeOne
def NontriviallyNormedField.ofNormNeOne {𝕜 : Type*} [h' : NormedField 𝕜]
    (h : ∃ x : 𝕜, x ≠ 0 ∧ ‖x‖ ≠ 1) : NontriviallyNormedField 𝕜 where
  toNormedField := h'
  non_trivial := by
    rcases h with ⟨x, hx, hx1⟩
    rcases hx1.lt_or_lt with hlt | hlt
    · use x⁻¹
      rw [norm_inv]
      exact (one_lt_inv₀ (norm_pos_iff.2 hx)).2 hlt
    · exact ⟨x, hlt⟩

instance Real.normedCommRing : NormedCommRing ℝ :=
  { Real.normedAddCommGroup, Real.commRing with norm_mul := fun x y => (abs_mul x y).le }

noncomputable instance Real.normedField : NormedField ℝ :=
  { Real.normedAddCommGroup, Real.field with
    norm_mul' := abs_mul }

noncomputable instance Real.denselyNormedField : DenselyNormedField ℝ where
  lt_norm_lt _ _ h₀ hr :=
    let ⟨x, h⟩ := exists_between hr
    ⟨x, by rwa [Real.norm_eq_abs, abs_of_nonneg (h₀.trans h.1.le)]⟩

namespace Real

theorem toNNReal_mul_nnnorm {x : ℝ} (y : ℝ) (hx : 0 ≤ x) : x.toNNReal * ‖y‖₊ = ‖x * y‖₊ := by
  ext
  simp only [NNReal.coe_mul, nnnorm_mul, coe_nnnorm, Real.toNNReal_of_nonneg, norm_of_nonneg, hx,
    NNReal.coe_mk]

theorem nnnorm_mul_toNNReal (x : ℝ) {y : ℝ} (hy : 0 ≤ y) : ‖x‖₊ * y.toNNReal = ‖x * y‖₊ := by
  rw [mul_comm, mul_comm x, toNNReal_mul_nnnorm x hy]

end Real

namespace NNReal

open NNReal

theorem norm_eq (x : ℝ≥0) : ‖(x : ℝ)‖ = x := by rw [Real.norm_eq_abs, x.abs_eq]

@[simp]
theorem nnnorm_eq (x : ℝ≥0) : ‖(x : ℝ)‖₊ = x :=
  NNReal.eq <| Real.norm_of_nonneg x.2

end NNReal

@[simp 1001] -- Porting note: increase priority so that the LHS doesn't simplify
theorem norm_norm [SeminormedAddCommGroup α] (x : α) : ‖‖x‖‖ = ‖x‖ :=
  Real.norm_of_nonneg (norm_nonneg _)

@[simp]
theorem nnnorm_norm [SeminormedAddCommGroup α] (a : α) : ‖‖a‖‖₊ = ‖a‖₊ := by
  rw [Real.nnnorm_of_nonneg (norm_nonneg a)]; rfl

theorem NormedAddCommGroup.tendsto_atTop [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)]
    {β : Type*} [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ‖f n - b‖ < ε :=
  (atTop_basis.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

theorem NormedAddCommGroup.tendsto_atTop' [Nonempty α] [Preorder α] [IsDirected α (· ≤ ·)]
    [NoMaxOrder α] {β : Type*} [SeminormedAddCommGroup β] {f : α → β} {b : β} :
    Tendsto f atTop (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ‖f n - b‖ < ε :=
  (atTop_basis_Ioi.tendsto_iff Metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

section RingHomIsometric

variable {R₁ R₂ : Type*}

class RingHomIsometric [Semiring R₁] [Semiring R₂] [Norm R₁] [Norm R₂] (σ : R₁ →+* R₂) : Prop where
  /-- The ring homomorphism is an isometry. -/
  is_iso : ∀ {x : R₁}, ‖σ x‖ = ‖x‖

attribute [simp] RingHomIsometric.is_iso

variable [SeminormedRing R₁]

instance RingHomIsometric.ids : RingHomIsometric (RingHom.id R₁) :=
  ⟨rfl⟩

end RingHomIsometric

/-! ### Induced normed structures -/

section Induced

variable {F : Type*} (R S : Type*)

variable [FunLike F R S]

abbrev NonUnitalSeminormedRing.induced [NonUnitalRing R] [NonUnitalSeminormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedRing R :=
  { SeminormedAddCommGroup.induced R S f, ‹NonUnitalRing R› with
    norm_mul := fun x y => by
      show ‖f (x * y)‖ ≤ ‖f x‖ * ‖f y‖
      exact (map_mul f x y).symm ▸ norm_mul_le (f x) (f y) }

abbrev NonUnitalNormedRing.induced [NonUnitalRing R] [NonUnitalNormedRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NonUnitalNormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf with }

abbrev SeminormedRing.induced [Ring R] [SeminormedRing S] [NonUnitalRingHomClass F R S] (f : F) :
    SeminormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹Ring R› with }

abbrev NormedRing.induced [Ring R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedRing R :=
  { NonUnitalSeminormedRing.induced R S f, NormedAddCommGroup.induced R S f hf, ‹Ring R› with }

abbrev NonUnitalSeminormedCommRing.induced [NonUnitalCommRing R] [NonUnitalSeminormedCommRing S]
    [NonUnitalRingHomClass F R S] (f : F) : NonUnitalSeminormedCommRing R :=
  { NonUnitalSeminormedRing.induced R S f, ‹NonUnitalCommRing R› with }

abbrev NonUnitalNormedCommRing.induced [NonUnitalCommRing R] [NonUnitalNormedCommRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NonUnitalNormedCommRing R :=
  { NonUnitalNormedRing.induced R S f hf, ‹NonUnitalCommRing R› with }

abbrev SeminormedCommRing.induced [CommRing R] [SeminormedRing S] [NonUnitalRingHomClass F R S]
    (f : F) : SeminormedCommRing R :=
  { NonUnitalSeminormedRing.induced R S f, SeminormedAddCommGroup.induced R S f, ‹CommRing R› with }

abbrev NormedCommRing.induced [CommRing R] [NormedRing S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedCommRing R :=
  { SeminormedCommRing.induced R S f, NormedAddCommGroup.induced R S f hf with }

abbrev NormedDivisionRing.induced [DivisionRing R] [NormedDivisionRing S]
    [NonUnitalRingHomClass F R S] (f : F) (hf : Function.Injective f) : NormedDivisionRing R :=
  { NormedAddCommGroup.induced R S f hf, ‹DivisionRing R› with
    norm_mul' := fun x y => by
      show ‖f (x * y)‖ = ‖f x‖ * ‖f y‖
      exact (map_mul f x y).symm ▸ norm_mul (f x) (f y) }

abbrev NormedField.induced [Field R] [NormedField S] [NonUnitalRingHomClass F R S] (f : F)
    (hf : Function.Injective f) : NormedField R :=
  { NormedDivisionRing.induced R S f hf with
    mul_comm := mul_comm }

theorem NormOneClass.induced {F : Type*} (R S : Type*) [Ring R] [SeminormedRing S]
    [NormOneClass S] [FunLike F R S] [RingHomClass F R S] (f : F) :
    @NormOneClass R (SeminormedRing.induced R S f).toNorm _ :=
  -- Porting note: is this `let` a bad idea somehow?
  let _ : SeminormedRing R := SeminormedRing.induced R S f
  { norm_one := (congr_arg norm (map_one f)).trans norm_one }

end Induced

namespace SubringClass

variable {S R : Type*} [SetLike S R]

instance toSeminormedRing [SeminormedRing R] [SubringClass S R] (s : S) : SeminormedRing s :=
  SeminormedRing.induced s R (SubringClass.subtype s)

instance toNormedRing [NormedRing R] [SubringClass S R] (s : S) : NormedRing s :=
  NormedRing.induced s R (SubringClass.subtype s) Subtype.val_injective

instance toSeminormedCommRing [SeminormedCommRing R] [_h : SubringClass S R] (s : S) :
    SeminormedCommRing s :=
  { SubringClass.toSeminormedRing s with mul_comm := mul_comm }

instance toNormedCommRing [NormedCommRing R] [SubringClass S R] (s : S) : NormedCommRing s :=
  { SubringClass.toNormedRing s with mul_comm := mul_comm }

end SubringClass

namespace SubfieldClass

variable {S F : Type*} [SetLike S F]

instance toNormedField [NormedField F] [SubfieldClass S F] (s : S) : NormedField s :=
  NormedField.induced s F (SubringClass.subtype s) Subtype.val_injective

end SubfieldClass

namespace AbsoluteValue

noncomputable def toNormedRing {R : Type*} [Ring R] (v : AbsoluteValue R ℝ) : NormedRing R where
  norm := v
  dist_eq _ _ := rfl
  dist_self x := by simp only [sub_self, MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom, map_zero]
  dist_comm := v.map_sub
  dist_triangle := v.sub_le
  edist_dist x y := rfl
  norm_mul x y := (v.map_mul x y).le
  eq_of_dist_eq_zero := by simp only [MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom,
    AbsoluteValue.map_sub_eq_zero_iff, imp_self, implies_true]

noncomputable def toNormedField {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : NormedField K where
  toField := inferInstanceAs (Field K)
  __ := v.toNormedRing
  norm_mul' := v.map_mul

end AbsoluteValue
