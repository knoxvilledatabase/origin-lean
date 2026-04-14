# Order Small Subdirs: Steps 1a-01 through 1a-08

Classified theorem-by-theorem. Every declaration read.

## 1a-01: Atoms/Finite.lean (11 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 9 | 81.8% |
| B2 | 0 | 0% |
| B3 | 2 | 18.2% |

**B1 (9):** `IsSimpleOrder.Fintype`, `IsSimpleOrder.Finite`, `Fintype.IsSimpleOrder.univ`, `Fintype.IsSimpleOrder.card`, `Bool.IsSimpleOrder`, `Finite.to_isCoatomic`, `Finite.to_isAtomic`, `IsStronglyCoatomic` (LocallyFiniteOrder, mechanical dual), `exists_covby_infinite_Iic_of_infinite_Iic` (mechanical dual)

**B3 (2):** `IsStronglyAtomic` (LocallyFiniteOrder — locally finite orders are strongly atomic), `exists_covby_infinite_Ici_of_infinite_Ici` (covering relations in infinite intervals)

## 1a-02: Circular/ZMod.lean (7 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 7 | 100% |
| B2 | 0 | 0% |
| B3 | 0 | 0% |

**B1 (7):** `CircularOrder ℤ`, `Int.btw_iff`, `Int.sbtw_iff`, `CircularOrder (Fin n)`, `Fin.btw_iff`, `Fin.sbtw_iff`, `CircularOrder (ZMod n)` — all typeclass instances and definitional unfoldings (`.rfl`)

## 1a-03: Lattice/Congruence.lean (5 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 1 | 20% |
| B2 | 0 | 0% |
| B3 | 4 | 80% |

**B1 (1):** `LatticeCon.ker` (kernel of lattice hom, closed by `simp_all`)

**B3 (4):** `r_inf_sup_iff` (congruence characterization), `closed_interval` (interval property), `transitive` (transitivity from interval property), `mk'` (alternative constructor for lattice congruences)

## 1a-04: Prod/Lex/Hom.lean (1 declaration)

| Bucket | Count | % |
|---|---|---|
| B1 | 1 | 100% |
| B2 | 0 | 0% |
| B3 | 0 | 0% |

**B1 (1):** `Prod.Lex.toLexOrderHom` (structural wrapping of `toLex` as OrderHom)

## 1a-05: Rel/GaloisConnection.lean (6 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 0 | 0% |
| B2 | 0 | 0% |
| B3 | 6 | 100% |

**B3 (6):** `gc_leftDual_rightDual` (Galois connection from relation), `leftDual_mem_rightFixedPoint`, `rightDual_mem_leftFixedPoint`, `equivFixedPoints` (bijection between fixed point sets), `rightDual_leftDual_le_of_le`, `leftDual_rightDual_le_of_le`

## 1a-06: Extension/ (11 declarations)

### Extension/Linear.lean (4 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 3 | 75% |
| B2 | 0 | 0% |
| B3 | 1 | 25% |

**B1 (3):** `LinearOrder (LinearExtension α)` instance, `toLinearExtension` (order hom), `Inhabited (LinearExtension α)`

**B3 (1):** `extend_partialOrder` (Szpilrajn extension theorem — any partial order extends to a linear order)

### Extension/Well.lean (7 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 5 | 71.4% |
| B2 | 0 | 0% |
| B3 | 2 | 28.6% |

**B1 (5):** `wellOrderExtension.isWellFounded_lt`, `wellOrderExtension.isWellOrder_lt`, `Inhabited (WellOrderExtension α)`, `LinearOrder (WellOrderExtension α)`, `WellOrderExtension.wellFoundedLT`

**B3 (2):** `wellOrderExtension` (constructing the well-order), `exists_well_order_ge` (any well-founded relation extends to a well-order)

### Extension/ totals: B1: 8, B2: 0, B3: 3

## 1a-07: ScottContinuity/ (7 declarations)

### ScottContinuity/Complete.lean (4 declarations)

**B3 (4):** `scottContinuous_iff_map_sSup` (Scott continuous ↔ commutes with directed sSup), `ScottContinuous.map_sSup` (alias), `scottContinuous_inf_right`, `ScottContinuous.inf₂` (meet is Scott continuous in complete linear orders)

### ScottContinuity/Prod.lean (3 declarations)

**B3 (3):** `ScottContinuousOn.fromProd` (Scott continuity on products), `ScottContinuous.fromProd`, `ScottContinuous.prod`

### ScottContinuity/ totals: B1: 0, B2: 0, B3: 7

## 1a-08: Types/ (43 declarations)

### Types/Defs.lean (32 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 18 | 56.3% |
| B2 | 12 | 37.5% |
| B3 | 2 | 6.3% |

**B1 (18):** `instSetoid`, `type`, `Zero`, `Inhabited`, `One`, `type_toType`, `type_eq_type`, `type_congr`, `type_of_isEmpty`, `type_of_unique`, `type_eq_one`, `inductionOn`, `inductionOn₂`, `inductionOn₃`, `liftOn`, `liftOn₂`, `liftOn_type`, `liftOn₂_type` — definitions, typeclass instances, definitional unfoldings

**B2 (12):** `type_eq_zero` (type α = 0 ↔ IsEmpty α), `type_ne_zero_iff`, `type_ne_zero`, `isEmpty_toType_iff` (o = 0), `nonempty_toType_iff` (o ≠ 0), `Nontrivial` (uses type_ne_zero), `NeZero (1 : OrderType)`, `Preorder` instance (defines ≤ via embeddings), `type_le_type_iff`, `type_le_type`, `zero_le`, `OrderBot` (bot = 0), `bot_eq_zero`, `not_lt_zero`, `pos_iff_ne_zero` — zero-management where 0 = empty order type

**B3 (2):** `omega0` (ω definition), `type_nat` (type ℕ = ω)

### Types/Arithmetic.lean (11 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 9 | 81.8% |
| B2 | 1 | 9.1% |
| B3 | 1 | 9.1% |

**B1 (9):** `HAdd`, `Add`, `type_lex_sum`, `AddMonoid`, `HMul`, `Mul`, `type_lex_prod`, `Monoid`, `OfNat` — arithmetic structure on OrderType

**B2 (1):** `ZeroLEOneClass` (0 ≤ 1 for OrderType)

**B3 (1):** `LeftDistribClass` (distributivity of lex product over lex sum)

### Types/ totals: B1: 27, B2: 13, B3: 3

## Summary: Steps 1a-01 through 1a-08

| Step | Subdir | Decls | B1 | B2 | B3 |
|---|---|---|---|---|---|
| 1a-01 | Atoms/ | 11 | 9 | 0 | 2 |
| 1a-02 | Circular/ | 7 | 7 | 0 | 0 |
| 1a-03 | Lattice/ | 5 | 1 | 0 | 4 |
| 1a-04 | Prod/ | 1 | 1 | 0 | 0 |
| 1a-05 | Rel/ | 6 | 0 | 0 | 6 |
| 1a-06 | Extension/ | 11 | 8 | 0 | 3 |
| 1a-07 | ScottContinuity/ | 7 | 0 | 0 | 7 |
| 1a-08 | Types/ | 43 | 27 | 13 | 3 |
| **Total** | | **91** | **53** | **13** | **25** |
| **%** | | | **58.2%** | **14.3%** | **27.5%** |
