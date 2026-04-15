/-
Extracted from RingTheory/HahnSeries/Basic.lean
Genuine: 55 | Conflates: 0 | Dissolved: 20 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Order.WellFoundedSet

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`, with the most studied case being when `Γ` is
a linearly ordered abelian group and `R` is a field, in which case `HahnSeries Γ R` is a
valued field, with value group `Γ`.
These generalize Laurent series (with value group `ℤ`), and Laurent series are implemented that way
in the file `RingTheory/LaurentSeries`.

## Main Definitions
* If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are partially well-ordered.
* `support x` is the subset of `Γ` whose coefficients are nonzero.
* `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
* `orderTop x` is a minimal element of `WithTop Γ` where `x` has a nonzero
  coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
* `order x` is a minimal element of `Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is zero
  when `x = 0`.
* `map` takes each coefficient of a Hahn series to its target under a zero-preserving map.
* `embDomain` preserves coefficients, but embeds the index set `Γ` in a larger poset.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

open Finset Function

noncomputable section

@[ext]
structure HahnSeries (Γ : Type*) (R : Type*) [PartialOrder Γ] [Zero R] where
  /-- The coefficient function of a Hahn Series. -/
  coeff : Γ → R
  isPWO_support' : (Function.support coeff).IsPWO

variable {Γ Γ' R S : Type*}

namespace HahnSeries

section Zero

variable [PartialOrder Γ] [Zero R]

theorem coeff_injective : Injective (coeff : HahnSeries Γ R → Γ → R) :=
  fun _ _ => HahnSeries.ext

@[simp]
theorem coeff_inj {x y : HahnSeries Γ R} : x.coeff = y.coeff ↔ x = y :=
  coeff_injective.eq_iff

nonrec def support (x : HahnSeries Γ R) : Set Γ :=
  support x.coeff

@[simp]
theorem isPWO_support (x : HahnSeries Γ R) : x.support.IsPWO :=
  x.isPWO_support'

@[simp]
theorem isWF_support (x : HahnSeries Γ R) : x.support.IsWF :=
  x.isPWO_support.isWF

-- DISSOLVED: mem_support

instance : Zero (HahnSeries Γ R) :=
  ⟨{  coeff := 0
      isPWO_support' := by simp }⟩

instance : Inhabited (HahnSeries Γ R) :=
  ⟨0⟩

instance [Subsingleton R] : Subsingleton (HahnSeries Γ R) :=
  ⟨fun _ _ => HahnSeries.ext (by subsingleton)⟩

@[simp]
theorem zero_coeff {a : Γ} : (0 : HahnSeries Γ R).coeff a = 0 :=
  rfl

@[simp]
theorem coeff_fun_eq_zero_iff {x : HahnSeries Γ R} : x.coeff = 0 ↔ x = 0 :=
  coeff_injective.eq_iff' rfl

-- DISSOLVED: ne_zero_of_coeff_ne_zero

@[simp]
theorem support_zero : support (0 : HahnSeries Γ R) = ∅ :=
  Function.support_zero

-- DISSOLVED: support_nonempty_iff

@[simp]
theorem support_eq_empty_iff {x : HahnSeries Γ R} : x.support = ∅ ↔ x = 0 :=
  Function.support_eq_empty_iff.trans coeff_fun_eq_zero_iff

@[simps]
def map [Zero S] (x : HahnSeries Γ R) {F : Type*} [FunLike F R S] [ZeroHomClass F R S] (f : F) :
    HahnSeries Γ S where
  coeff g := f (x.coeff g)
  isPWO_support' := x.isPWO_support.mono <| Function.support_comp_subset (ZeroHomClass.map_zero f) _

@[simp]
protected lemma map_zero [Zero S] (f : ZeroHom R S) :
    (0 : HahnSeries Γ R).map f = 0 := by
  ext; simp

def ofIterate [PartialOrder Γ'] (x : HahnSeries Γ (HahnSeries Γ' R)) :
    HahnSeries (Γ ×ₗ Γ') R where
  coeff := fun g => coeff (coeff x g.1) g.2
  isPWO_support' := by
    refine Set.PartiallyWellOrderedOn.subsetProdLex ?_ ?_
    · refine Set.IsPWO.mono x.isPWO_support' ?_
      simp_rw [Set.image_subset_iff, support_subset_iff, Set.mem_preimage, Function.mem_support]
      exact fun _ ↦ ne_zero_of_coeff_ne_zero
    · exact fun a => by simpa [Function.mem_support, ne_eq] using (x.coeff a).isPWO_support'

@[simp]
lemma mk_eq_zero (f : Γ → R) (h) : HahnSeries.mk f h = 0 ↔ f = 0 := by
  rw [HahnSeries.ext_iff]
  rfl

def toIterate [PartialOrder Γ'] (x : HahnSeries (Γ ×ₗ Γ') R) :
    HahnSeries Γ (HahnSeries Γ' R) where
  coeff := fun g => {
    coeff := fun g' => coeff x (g, g')
    isPWO_support' := Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_support' g
  }
  isPWO_support' := by
    have h₁ : (Function.support fun g => HahnSeries.mk (fun g' => x.coeff (g, g'))
        (Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_support' g)) = Function.support
        fun g => fun g' => x.coeff (g, g') := by
      simp only [Function.support, ne_eq, mk_eq_zero]
    rw [h₁, Function.support_curry' x.coeff]
    exact Set.PartiallyWellOrderedOn.imageProdLex x.isPWO_support'

@[simps]
def iterateEquiv [PartialOrder Γ'] :
    HahnSeries Γ (HahnSeries Γ' R) ≃ HahnSeries (Γ ×ₗ Γ') R where
  toFun := ofIterate
  invFun := toIterate
  left_inv := congrFun rfl
  right_inv := congrFun rfl

open Classical in

def single (a : Γ) : ZeroHom R (HahnSeries Γ R) where
  toFun r :=
    { coeff := Pi.single a r
      isPWO_support' := (Set.isPWO_singleton a).mono Pi.support_single_subset }
  map_zero' := HahnSeries.ext (Pi.single_zero _)

variable {a b : Γ} {r : R}

@[simp]
theorem single_coeff_same (a : Γ) (r : R) : (single a r).coeff a = r := by
  classical exact Pi.single_eq_same (f := fun _ => R) a r

@[simp]
theorem single_coeff_of_ne (h : b ≠ a) : (single a r).coeff b = 0 := by
  classical exact Pi.single_eq_of_ne (f := fun _ => R) h r

open Classical in

theorem single_coeff : (single a r).coeff b = if b = a then r else 0 := by
  split_ifs with h <;> simp [h]

-- DISSOLVED: support_single_of_ne

theorem support_single_subset : support (single a r) ⊆ {a} := by
  classical exact Pi.support_single_subset

theorem eq_of_mem_support_single {b : Γ} (h : b ∈ support (single a r)) : b = a :=
  support_single_subset h

theorem single_eq_zero : single a (0 : R) = 0 :=
  (single a).map_zero

theorem single_injective (a : Γ) : Function.Injective (single a : R → HahnSeries Γ R) :=
  fun r s rs => by rw [← single_coeff_same a r, ← single_coeff_same a s, rs]

-- DISSOLVED: single_ne_zero

@[simp]
theorem single_eq_zero_iff {a : Γ} {r : R} : single a r = 0 ↔ r = 0 :=
  map_eq_zero_iff _ <| single_injective a

@[simp]
protected lemma map_single [Zero S] (f : ZeroHom R S) : (single a r).map f = single a (f r) := by
  ext g
  by_cases h : g = a <;> simp [h]

instance [Nonempty Γ] [Nontrivial R] : Nontrivial (HahnSeries Γ R) :=
  ⟨by
    obtain ⟨r, s, rs⟩ := exists_pair_ne R
    inhabit Γ
    refine ⟨single default r, single default s, fun con => rs ?_⟩
    rw [← single_coeff_same (default : Γ) r, con, single_coeff_same]⟩

section Order

open Classical in

def orderTop (x : HahnSeries Γ R) : WithTop Γ :=
  if h : x = 0 then ⊤ else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]
theorem orderTop_zero : orderTop (0 : HahnSeries Γ R) = ⊤ :=
  dif_pos rfl

-- DISSOLVED: orderTop_of_ne

-- DISSOLVED: ne_zero_iff_orderTop

theorem orderTop_eq_top_iff {x : HahnSeries Γ R} : orderTop x = ⊤ ↔ x = 0 := by
  constructor
  · contrapose!
    exact ne_zero_iff_orderTop.mp
  · simp_all only [orderTop_zero, implies_true]

theorem orderTop_eq_of_le {x : HahnSeries Γ R} {g : Γ} (hg : g ∈ x.support)
    (hx : ∀ g' ∈ x.support, g ≤ g') : orderTop x = g := by
  rw [orderTop_of_ne <| support_nonempty_iff.mp <| Set.nonempty_of_mem hg,
    x.isWF_support.min_eq_of_le hg hx]

-- DISSOLVED: untop_orderTop_of_ne_zero

-- DISSOLVED: coeff_orderTop_ne

-- DISSOLVED: orderTop_le_of_coeff_ne_zero

-- DISSOLVED: orderTop_single

theorem orderTop_single_le : a ≤ (single a r).orderTop := by
  by_cases hr : r = 0
  · simp only [hr, map_zero, orderTop_zero, le_top]
  · rw [orderTop_single hr]

theorem lt_orderTop_single {g g' : Γ} (hgg' : g < g') : g < (single g' r).orderTop :=
  lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hgg') orderTop_single_le

theorem coeff_eq_zero_of_lt_orderTop {x : HahnSeries Γ R} {i : Γ} (hi : i < x.orderTop) :
    x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · exact zero_coeff
  contrapose! hi
  rw [← mem_support] at hi
  rw [orderTop_of_ne hx, WithTop.coe_lt_coe]
  exact Set.IsWF.not_lt_min _ _ hi

open Classical in

def leadingCoeff (x : HahnSeries Γ R) : R :=
  if h : x = 0 then 0 else x.coeff (x.isWF_support.min (support_nonempty_iff.2 h))

@[simp]
theorem leadingCoeff_zero : leadingCoeff (0 : HahnSeries Γ R) = 0 :=
  dif_pos rfl

-- DISSOLVED: leadingCoeff_of_ne

theorem leadingCoeff_eq_iff {x : HahnSeries Γ R} : x.leadingCoeff = 0 ↔ x = 0 := by
  refine { mp := ?_, mpr := fun hx => hx ▸ leadingCoeff_zero }
  contrapose!
  exact fun hx => (leadingCoeff_of_ne hx) ▸ coeff_orderTop_ne (orderTop_of_ne hx)

-- DISSOLVED: leadingCoeff_ne_iff

theorem leadingCoeff_of_single {a : Γ} {r : R} : leadingCoeff (single a r) = r := by
  simp only [leadingCoeff, single_eq_zero_iff]
  by_cases h : r = 0 <;> simp [h]

variable [Zero Γ]

open Classical in

def order (x : HahnSeries Γ R) : Γ :=
  if h : x = 0 then 0 else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]
theorem order_zero : order (0 : HahnSeries Γ R) = 0 :=
  dif_pos rfl

-- DISSOLVED: order_of_ne

-- DISSOLVED: order_eq_orderTop_of_ne

-- DISSOLVED: coeff_order_ne_zero

-- DISSOLVED: order_le_of_coeff_ne_zero

-- DISSOLVED: order_single

theorem coeff_eq_zero_of_lt_order {x : HahnSeries Γ R} {i : Γ} (hi : i < x.order) :
    x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  contrapose! hi
  rw [← mem_support] at hi
  rw [order_of_ne hx]
  exact Set.IsWF.not_lt_min _ _ hi

-- DISSOLVED: zero_lt_orderTop_iff

theorem zero_lt_orderTop_of_order {x : HahnSeries Γ R} (hx : 0 < x.order) : 0 < x.orderTop := by
  by_cases h : x = 0
  · simp_all only [order_zero, lt_self_iff_false]
  · exact (zero_lt_orderTop_iff h).mpr hx

theorem zero_le_orderTop_iff {x : HahnSeries Γ R} : 0 ≤ x.orderTop ↔ 0 ≤ x.order := by
  by_cases h : x = 0
  · simp_all
  · simp_all [order_of_ne h, orderTop_of_ne h, zero_lt_orderTop_iff]

theorem leadingCoeff_eq {x : HahnSeries Γ R} : x.leadingCoeff = x.coeff x.order := by
  by_cases h : x = 0
  · rw [h, leadingCoeff_zero, zero_coeff]
  · rw [leadingCoeff_of_ne h, order_of_ne h]

end Order

section Domain

variable [PartialOrder Γ']

open Classical in

def embDomain (f : Γ ↪o Γ') : HahnSeries Γ R → HahnSeries Γ' R := fun x =>
  { coeff := fun b : Γ' => if h : b ∈ f '' x.support then x.coeff (Classical.choose h) else 0
    isPWO_support' :=
      (x.isPWO_support.image_of_monotone f.monotone).mono fun b hb => by
        contrapose! hb
        rw [Function.mem_support, dif_neg hb, Classical.not_not] }

@[simp]
theorem embDomain_coeff {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {a : Γ} :
    (embDomain f x).coeff (f a) = x.coeff a := by
  rw [embDomain]
  dsimp only
  by_cases ha : a ∈ x.support
  · rw [dif_pos (Set.mem_image_of_mem f ha)]
    exact congr rfl (f.injective (Classical.choose_spec (Set.mem_image_of_mem f ha)).2)
  · rw [dif_neg, Classical.not_not.1 fun c => ha ((mem_support _ _).2 c)]
    contrapose! ha
    obtain ⟨b, hb1, hb2⟩ := (Set.mem_image _ _ _).1 ha
    rwa [f.injective hb2] at hb1

@[simp]
theorem embDomain_mk_coeff {f : Γ → Γ'} (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') {x : HahnSeries Γ R} {a : Γ} :
    (embDomain ⟨⟨f, hfi⟩, hf _ _⟩ x).coeff (f a) = x.coeff a :=
  embDomain_coeff

theorem embDomain_notin_image_support {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'}
    (hb : b ∉ f '' x.support) : (embDomain f x).coeff b = 0 :=
  dif_neg hb

theorem support_embDomain_subset {f : Γ ↪o Γ'} {x : HahnSeries Γ R} :
    support (embDomain f x) ⊆ f '' x.support := by
  intro g hg
  contrapose! hg
  rw [mem_support, embDomain_notin_image_support hg, Classical.not_not]

theorem embDomain_notin_range {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'} (hb : b ∉ Set.range f) :
    (embDomain f x).coeff b = 0 :=
  embDomain_notin_image_support fun con => hb (Set.image_subset_range _ _ con)

@[simp]
theorem embDomain_zero {f : Γ ↪o Γ'} : embDomain f (0 : HahnSeries Γ R) = 0 := by
  ext
  simp [embDomain_notin_image_support]

@[simp]
theorem embDomain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} :
    embDomain f (single g r) = single (f g) r := by
  ext g'
  by_cases h : g' = f g
  · simp [h]
  rw [embDomain_notin_image_support, single_coeff_of_ne h]
  by_cases hr : r = 0
  · simp [hr]
  rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]

theorem embDomain_injective {f : Γ ↪o Γ'} :
    Function.Injective (embDomain f : HahnSeries Γ R → HahnSeries Γ' R) := fun x y xy => by
  ext g
  rw [HahnSeries.ext_iff, funext_iff] at xy
  have xyg := xy (f g)
  rwa [embDomain_coeff, embDomain_coeff] at xyg

end Domain

end Zero

section LocallyFiniteLinearOrder

variable [Zero R] [LinearOrder Γ]

theorem forallLTEqZero_supp_BddBelow (f : Γ → R) (n : Γ) (hn : ∀(m : Γ), m < n → f m = 0) :
    BddBelow (Function.support f) := by
  simp only [BddBelow, Set.Nonempty, lowerBounds]
  use n
  intro m hm
  rw [Function.mem_support, ne_eq] at hm
  exact not_lt.mp (mt (hn m) hm)

theorem BddBelow_zero [Nonempty Γ] : BddBelow (Function.support (0 : Γ → R)) := by
  simp only [support_zero', bddBelow_empty]

variable [LocallyFiniteOrder Γ]

theorem suppBddBelow_supp_PWO (f : Γ → R)
    (hf : BddBelow (Function.support f)) :
    (Function.support f).IsPWO :=
  Set.isWF_iff_isPWO.mp hf.wellFoundedOn_lt

@[simps]
def ofSuppBddBelow (f : Γ → R) (hf : BddBelow (Function.support f)) : HahnSeries Γ R where
  coeff := f
  isPWO_support' := suppBddBelow_supp_PWO f hf

@[simp]
theorem zero_ofSuppBddBelow [Nonempty Γ] : ofSuppBddBelow 0 BddBelow_zero = (0 : HahnSeries Γ R) :=
  rfl

-- DISSOLVED: order_ofForallLtEqZero

end LocallyFiniteLinearOrder

end HahnSeries
