# Order Small Subdirs: Steps 1a-09 and 1a-10

Classified theorem-by-theorem. Every declaration read.

## 1a-09: CompactlyGenerated/ (55 declarations)

### CompactlyGenerated/Basic.lean (52 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 8 | 15.4% |
| B2 | 4 | 7.7% |
| B3 | 40 | 76.9% |

**B1 (8):** Aliases and mechanical derivations from the TFAE equivalence: `wellFoundedGT_iff_isSupFiniteCompact`, `isSupFiniteCompact_iff_isSupClosedCompact`, `isSupClosedCompact_iff_wellFoundedGT`, `IsSupFiniteCompact.wellFoundedGT`, `IsSupClosedCompact.isSupFiniteCompact`, `WellFoundedGT.isSupClosedCompact`, `iSupIndep_iff_supIndep_of_injOn` (deprecated), `Directed.iSup_inf_eq` (comm of `inf_iSup_eq`)

**B2 (4):** Theorems carrying `≠ ⊥` hypotheses about independence/atomicity: `WellFoundedGT.finite_ne_bot_of_iSupIndep` (finite support of independent family), `WellFoundedGT.finite_of_iSupIndep` (requires `∀ i, t i ≠ ⊥`), `WellFoundedLT.finite_ne_bot_of_iSupIndep`, `WellFoundedLT.finite_of_iSupIndep`

**B3 (40):** The core mathematical content about compact elements and compactly generated lattices:
- Compact element characterizations: `isCompactElement_iff_le_of_directed_sSup_le`, `isCompactElement_iff_exists_le_sSup_of_le_sSup`, `isCompactElement_iff_exists_le_iSup_of_le_iSup`
- Compact element properties: `IsCompactElement.exists_finset_of_le_iSup`, `IsCompactElement.directed_sSup_lt_of_lt`, `isCompactElement_finsetSup`
- Well-foundedness equivalences: `WellFoundedGT.isSupFiniteCompact`, `IsSupFiniteCompact.isSupClosedCompact`, `IsSupClosedCompact.wellFoundedGT`, `isSupFiniteCompact_iff_all_elements_compact`, `wellFoundedGT_characterisations`
- Independence and finiteness: `WellFoundedGT.finite_of_sSupIndep`, `WellFoundedLT.finite_of_sSupIndep`, `sSupIndep_iff_finite`, `iSupIndep_iff_supIndep`, `sSupIndep_iUnion_of_directed`, `iSupIndep_sUnion_of_directed`, `disjoint_biSup_of_finite_disjoint_biSup`, `iSupIndep.disjoint_biSup_biSup`
- Compactly generated lattice properties: `sSup_compact_le_eq`, `sSup_compact_eq_top`, `le_iff_compact_le_imp`
- Upper continuity (inf distributes over directed sup): `DirectedOn.inf_sSup_eq`, `DirectedOn.sSup_inf_eq`, `Directed.inf_iSup_eq`, `inf_sSup_eq_iSup_inf_sup_finset`
- Disjointness from directed sup: `DirectedOn.disjoint_sSup_right`, `DirectedOn.disjoint_sSup_left`, `Directed.disjoint_iSup_right`, `Directed.disjoint_iSup_left`
- Compactly generated → coatomic/atomic: `isCompactlyGenerated_of_wellFoundedGT`, `Iic_coatomic_of_compact_element`, `coatomic_of_top_compact`
- Complemented lattice results: `isAtomic_of_complementedLattice`, `isAtomistic_of_complementedLattice`, `iSupIndep.iInf`, `exists_sSupIndep_disjoint_sSup_atoms`, `exists_sSupIndep_isCompl_sSup_atoms`, `exists_sSupIndep_of_sSup_atoms`, `exists_sSupIndep_of_sSup_atoms_eq_top`, `complementedLattice_of_sSup_atoms_eq_top`, `complementedLattice_of_isAtomistic`, `complementedLattice_iff_isAtomistic`

### CompactlyGenerated/Intervals.lean (3 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 0 | 0% |
| B2 | 0 | 0% |
| B3 | 3 | 100% |

**B3 (3):** `Iic.isCompactElement` (compact in interval), `Iic.instIsCompactlyGenerated` (Iic of compactly generated), `complementedLattice_of_complementedLattice_Iic` (complemented from intervals)

### CompactlyGenerated/ totals: B1: 8, B2: 4, B3: 43

**Heavy B3 domain (78.2%).** This is real lattice theory — compact elements, well-foundedness equivalences, independence, atomicity, complementation. The mathematical content is substantial and domain-specific.

## 1a-10: ConditionallyCompletePartialOrder/ (64 declarations)

### ConditionallyCompletePartialOrder/Defs.lean (5 declarations)

**B1 (5):** `DirectedOn.isLUB_csSup` (unpacks class axiom), `DirectedOn.le_csSup`, `DirectedOn.csSup_le`, `Directed.le_ciSup`, `Directed.ciSup_le` — basic API for the class, each generated dual counted

### ConditionallyCompletePartialOrder/Basic.lean (23 declarations)

**B1 (23):** All structural API. OrderDual instances (3), `le_csSup_of_le`, `csSup_le_csSup`, `le_csSup_iff`, `IsGreatest.directedOn`, `IsGreatest.csSup_eq`, `IsGreatest.csSup_mem`, `csSup_le_iff`, `notMem_of_csSup_lt`, `csSup_eq_of_forall_le_of_forall_lt_exists_gt`, `lt_csSup_of_lt`, `csSup_singleton`, `csInf_Ici`, `csInf_Ico`, `csInf_Icc`, `csSup_Iic`, `csSup_Ioc`, `csSup_Icc`, `sup_eq_top_of_top_mem`, `subset_Icc_csInf_csSup`, `csInf_le_csSup`

### ConditionallyCompletePartialOrder/Indexed.lean (36 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 34 | 94.4% |
| B2 | 0 | 0% |
| B3 | 2 | 5.6% |

**B1 (34):** Indexed cSup/cInf API: `isLUB_ciSup`, `isLUB_ciSup_set`, `ciSup_le_iff`, `ciSup_set_le_iff`, `le_ciSup_of_le`, `ciSup_mono`, `le_ciSup_set`, `ciSup_const`, `ciSup_unique`, `ciSup_subsingleton`, `ciSup_pos`, `ciSup_neg`, `ciSup_eq_ite`, `cbiSup_eq_of_forall`, `ciSup_eq_of_forall_le_of_forall_lt_exists_gt`, `Ici_ciSup`, `ciSup_Iic`, `ciInf_le_ciSup`. GaloisConnection interactions: `l_csSup_of_directedOn'`, `l_csSup_of_directedOn`, `l_ciSup_of_directed`, `l_ciSup_set_of_directedOn`, `u_csInf_of_directedOn`, `u_csInf_of_directedOn'`, `u_ciInf_of_directed`, `u_ciInf_set_of_directedOn`. OrderIso interactions: `map_csSup_of_directedOn`, `map_csSup_of_directedOn'`, `map_ciSup_of_directed`, `map_ciSup_set_of_directedOn`, `map_csInf_of_directedOn`, `map_csInf_of_directedOn'`, `map_ciInf_of_directed`, `map_ciInf_set_of_directedOn`

**B3 (2):** Nested intervals lemma: `Monotone.ciSup_mem_iInter_Icc_of_antitone` (if f monotone and g antitone with f ≤ g, then ⨆ f ∈ ⋂ [f n, g n]), `ciSup_mem_iInter_Icc_of_antitone_Icc` (variant)

### ConditionallyCompletePartialOrder/ totals: B1: 62, B2: 0, B3: 2

**Overwhelmingly B1 (96.9%).** Pure structural API for conditionally complete partial orders — the cSup/cInf API mirroring the conditionally complete lattice API.

## Running totals: Steps 1a-01 through 1a-10, 1a-16, 1a-17

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
| 1a-09 | CompactlyGenerated/ | 55 | 8 | 4 | 43 |
| 1a-10 | CondComplPartialOrder/ | 64 | 62 | 0 | 2 |
| 1a-16 | Defs/ | 119 | 119 | 0 | 0 |
| 1a-17 | RelIso/ | 121 | 117 | 0 | 4 |
| **Total** | | **450** | **359** | **17** | **74** |
| **%** | | | **79.8%** | **3.8%** | **16.4%** |
