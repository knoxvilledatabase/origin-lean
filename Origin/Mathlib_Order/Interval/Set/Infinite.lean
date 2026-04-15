/-
Extracted from Order/Interval/Set/Infinite.lean
Genuine: 12 of 18 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Infinitude of intervals

Bounded intervals in dense orders are infinite, as are unbounded intervals
in orders that are unbounded on the appropriate side. We also prove that an unbounded
preorder is an infinite type.
-/

variable {α : Type*} [Preorder α]

-- INSTANCE (free from Core): NoMaxOrder.infinite

-- INSTANCE (free from Core): NoMinOrder.infinite

namespace Set

section DenselyOrdered

variable [DenselyOrdered α] {a b : α} (h : a < b)

include h

theorem Ioo.infinite : Infinite (Ioo a b) :=
  @NoMaxOrder.infinite _ _ (nonempty_Ioo_subtype h) _

theorem Ioo_infinite : (Ioo a b).Infinite :=
  infinite_coe_iff.1 <| Ioo.infinite h

theorem Ico_infinite : (Ico a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ico_self

theorem Ico.infinite : Infinite (Ico a b) :=
  infinite_coe_iff.2 <| Ico_infinite h

theorem Ioc_infinite : (Ioc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ioc_self

theorem Ioc.infinite : Infinite (Ioc a b) :=
  infinite_coe_iff.2 <| Ioc_infinite h

theorem Icc_infinite : (Icc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Icc_self

theorem Icc.infinite : Infinite (Icc a b) :=
  infinite_coe_iff.2 <| Icc_infinite h

end DenselyOrdered

-- INSTANCE (free from Core): [NoMinOrder

theorem Iio_infinite [NoMinOrder α] (a : α) : (Iio a).Infinite :=
  infinite_coe_iff.1 inferInstance

-- INSTANCE (free from Core): [NoMinOrder

theorem Iic_infinite [NoMinOrder α] (a : α) : (Iic a).Infinite :=
  infinite_coe_iff.1 inferInstance

-- INSTANCE (free from Core): [NoMaxOrder

theorem Ioi_infinite [NoMaxOrder α] (a : α) : (Ioi a).Infinite :=
  infinite_coe_iff.1 inferInstance

-- INSTANCE (free from Core): [NoMaxOrder

theorem Ici_infinite [NoMaxOrder α] (a : α) : (Ici a).Infinite :=
  infinite_coe_iff.1 inferInstance

end Set
