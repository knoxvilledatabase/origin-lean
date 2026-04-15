/-
Extracted from Data/PNat/Interval.lean
Genuine: 5 of 11 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Finite intervals of positive naturals

This file proves that `ℕ+` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.
-/

open Finset Function PNat

namespace PNat

variable (a b : ℕ+)

-- INSTANCE (free from Core): instLocallyFiniteOrder

theorem map_subtype_embedding_Icc : (Icc a b).map (Embedding.subtype _) = Icc ↑a ↑b :=
  Finset.map_subtype_embedding_Icc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_Ico : (Ico a b).map (Embedding.subtype _) = Ico ↑a ↑b :=
  Finset.map_subtype_embedding_Ico _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_Ioc : (Ioc a b).map (Embedding.subtype _) = Ioc ↑a ↑b :=
  Finset.map_subtype_embedding_Ioc _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_Ioo : (Ioo a b).map (Embedding.subtype _) = Ioo ↑a ↑b :=
  Finset.map_subtype_embedding_Ioo _ _ _ fun _c _ _x hx _ hc _ => hc.trans_le hx

theorem map_subtype_embedding_uIcc : (uIcc a b).map (Embedding.subtype _) = uIcc ↑a ↑b :=
  map_subtype_embedding_Icc _ _

set_option backward.isDefEq.respectTransparency false in
