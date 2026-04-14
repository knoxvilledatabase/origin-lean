# Order Step 1b: Monotone/ (317 declarations)

Classified theorem-by-theorem. Every declaration read.

## Monotone/Defs.lean (99 declarations)

**B1 (99):** Definitions and structural API for monotonicity concepts: `Monotone`, `Antitone`, `MonotoneOn`, `AntitoneOn`, `StrictMono`, `StrictAnti`, `StrictMonoOn`, `StrictAntiOn`. Basic properties: `Monotone.dual`, `Monotone.comp`, `StrictMono.comp`, `Monotone.iterate`, `StrictMono.iterate`, `Monotone.of_restrict`, `MonotoneOn.mono`, dual/comp/restrict lemmas for all 8 variants, `monotone_id`, `strictMono_id`, `monotone_const`, lattice operations (`Monotone.sup`, `Monotone.inf`), `Monotone.of_map_inf`, `Monotone.of_map_sup`, min/max interactions, order iso/embedding characterizations.

## Monotone/Basic.lean (107 declarations)

**B1 (107):** Extended structural API: dual rewriting lemmas (`monotone_comp_ofDual_iff`, etc.), `Monotone.restrict`, `Monotone.codRestrict`, `StrictMono.injective`, `StrictMono.comp_eq`, `StrictMono.ite`, monotone characterizations for ℕ and ℤ (`monotone_nat_of_le_succ`, `strictMono_nat_of_lt_succ`, `monotone_int_of_le_succ`, `strictMono_int_of_lt_succ`), comparison lemmas, `Monotone.isBoundedUnder_le`, `StrictMono.maximal_preimage_top`, `Subtype.mono_coe`, `Subtype.strictMono_coe`.

## Monotone/Monovary.lean (88 declarations)

**B1 (88):** Monovariance API: `Monovary`, `Antivary`, `MonovaryOn`, `AntivaryOn` definitions and their structural properties — `monovaryOn`, `antivaryOn`, `empty`, `univ`, `subset`, `const_left`, `const_right`, `monovary_self`, dual/comp lemmas, `Monovary.symm`, `Monotone.monovary`, `Antitone.antivary`, lattice interactions (`Monovary.sup`, `Monovary.inf`), reindexing.

## Monotone/Extension.lean (2 declarations)

**B3 (2):** `MonotoneOn.exists_monotone_extension` — if f is monotone and bounded on s, it admits a monotone extension to the whole space. `AntitoneOn.exists_antitone_extension` (dual). Genuine mathematical content (monotone extension theorem using csSup).

## Monotone/MonovaryOrder.lean (9 declarations)

**B3 (9):** `MonovaryOrder` (constructing a linear order from monovariance), `IsStrictTotalOrder` instance, equivalence theorems: `monovaryOn_iff_exists_monotoneOn`, `antivaryOn_iff_exists_monotoneOn_antitoneOn`, `monovaryOn_iff_exists_antitoneOn`, `antivaryOn_iff_exists_antitoneOn_monotoneOn`, `monovary_iff_exists_monotone`, `monovary_iff_exists_antitone`, `antivary_iff_exists_monotone_antitone`, `antivary_iff_exists_antitone_monotone` — monovarying functions can be made simultaneously monotone by choosing the right order.

## Monotone/Odd.lean (4 declarations)

**B3 (4):** `strictMono_of_odd_strictMonoOn_nonneg`, `strictAnti_of_odd_strictAntiOn_nonneg`, `monotone_of_odd_of_monotoneOn_nonneg`, `antitone_of_odd_of_monotoneOn_nonneg` — odd functions on ordered groups inherit monotonicity from the nonneg half.

## Monotone/Union.lean (8 declarations)

**B3 (8):** `StrictMonoOn.union` (gluing strict monotonicity on overlapping sets), `StrictMonoOn.Iic_union_Ici` (gluing on half-lines), `StrictAntiOn.union`, `StrictAntiOn.Iic_union_Ici`, `MonotoneOn.union_right`, `MonotoneOn.Iic_union_Ici`, `AntitoneOn.union_right`, `AntitoneOn.Iic_union_Ici` — gluing monotone functions on overlapping intervals.

## Monotone/ totals

| File | Decls | B1 | B2 | B3 |
|---|---|---|---|---|
| Defs.lean | 99 | 99 | 0 | 0 |
| Basic.lean | 107 | 107 | 0 | 0 |
| Monovary.lean | 88 | 88 | 0 | 0 |
| Extension.lean | 2 | 0 | 0 | 2 |
| MonovaryOrder.lean | 9 | 0 | 0 | 9 |
| Odd.lean | 4 | 0 | 0 | 4 |
| Union.lean | 8 | 0 | 0 | 8 |
| **Total** | **317** | **294** | **0** | **23** |
| **%** | | **92.7%** | **0%** | **7.3%** |

**Zero B2.** Monotonicity theory doesn't touch zero-management at all. The B3 is concentrated in the mathematically rich results: monotone extension, monovariance-to-monotonicity equivalence, odd function monotonicity, and interval gluing.
