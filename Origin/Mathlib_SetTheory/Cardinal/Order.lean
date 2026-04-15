/-
Extracted from SetTheory/Cardinal/Order.lean
Genuine: 9 of 13 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Order on cardinal numbers

We define the order on cardinal numbers and show its basic properties, including the ordered
semiring structure.

## Main definitions

* The order `c₁ ≤ c₂` is defined by `Cardinal.le_def α β : #α ≤ #β ↔ Nonempty (α ↪ β)`.
* `Order.IsSuccLimit c` means that `c` is a (weak) limit cardinal: `c ≠ 0 ∧ ∀ x < c, succ x < c`.
* `Cardinal.IsStrongLimit c` means that `c` is a strong limit cardinal:
  `c ≠ 0 ∧ ∀ x < c, 2 ^ x < c`.

## Main instances

* Cardinals form a `CanonicallyOrderedAdd` `OrderedCommSemiring` with the aforementioned sum and
  product.
* Cardinals form a `SuccOrder`. Use `Order.succ c` for the smallest cardinal greater than `c`.
* The less-than relation on cardinals forms a well-order.
* Cardinals form a `ConditionallyCompleteLinearOrderBot`. Bounded sets for cardinals in universe
  `u` are precisely the sets indexed by some type in universe `u`, see
  `Cardinal.bddAbove_iff_small`. One can use `sSup` for the cardinal supremum,
  and `sInf` for the minimum of a set of cardinals.

## Main statements

* Cantor's theorem: `Cardinal.cantor c : c < 2 ^ c`.
* König's theorem: `Cardinal.sum_lt_prod`

## Implementation notes

The current setup interweaves the order structure and the algebraic structure on `Cardinal` tightly.
For example, we need to know what a ring is in order to show that `0` is the smallest cardinality.
That is reflected in this file containing both the order and algebra structure.

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/

assert_not_exists Field

open List Function Order Set

noncomputable section

universe u v w v' w'

variable {α β : Type u}

namespace Cardinal

/-! ### Order on cardinals -/

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): partialOrder

-- INSTANCE (free from Core): linearOrder

theorem mk_le_of_injective {α β : Type u} {f : α → β} (hf : Injective f) : #α ≤ #β :=
  ⟨⟨f, hf⟩⟩

theorem _root_.Function.Embedding.cardinal_le {α β : Type u} (f : α ↪ β) : #α ≤ #β :=
  ⟨f⟩

theorem mk_le_of_surjective {α β : Type u} {f : α → β} (hf : Surjective f) : #β ≤ #α :=
  ⟨Embedding.ofSurjective f hf⟩

theorem le_mk_iff_exists_set {c : Cardinal} {α : Type u} : c ≤ #α ↔ ∃ p : Set α, #p = c :=
  ⟨inductionOn c fun _ ⟨⟨f, hf⟩⟩ => ⟨Set.range f, (Equiv.ofInjective f hf).cardinal_eq.symm⟩,
    fun ⟨_, e⟩ => e ▸ ⟨⟨Subtype.val, fun _ _ => Subtype.ext⟩⟩⟩

theorem mk_subtype_le {α : Type u} (p : α → Prop) : #(Subtype p) ≤ #α :=
  ⟨Embedding.subtype p⟩

theorem mk_set_le (s : Set α) : #s ≤ #α :=
  mk_subtype_le (· ∈ s)

theorem out_embedding {c c' : Cardinal} : c ≤ c' ↔ Nonempty (c.out ↪ c'.out) := by
  conv_lhs => rw [← Cardinal.mk_out c, ← Cardinal.mk_out c', le_def]

theorem lift_mk_le {α : Type v} {β : Type w} :
    lift.{max u w} #α ≤ lift.{max u v} #β ↔ Nonempty (α ↪ β) :=
  ⟨fun ⟨f⟩ => ⟨Embedding.congr Equiv.ulift Equiv.ulift f⟩, fun ⟨f⟩ =>
    ⟨Embedding.congr Equiv.ulift.symm Equiv.ulift.symm f⟩⟩

theorem lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #α ≤ lift.{u} #β ↔ Nonempty (α ↪ β) :=
  lift_mk_le.{0}

/-! ### `lift` sends `Cardinal.{u}` to an initial segment of `Cardinal.{max u v}`. -/
