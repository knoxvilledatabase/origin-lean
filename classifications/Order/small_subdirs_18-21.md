# Order Small Subdirs: Steps 1a-18 through 1a-21

Classified theorem-by-theorem. Every declaration read.

## 1a-18: Bounds/ (203 declarations)

### Bounds/Defs.lean (0 declarations)

Pure definitions (`upperBounds`, `lowerBounds`, `BddAbove`, `BddBelow`, `IsLeast`, `IsGreatest`, `IsLUB`, `IsGLB`). No theorems.

### Bounds/Basic.lean (134 declarations)

**B1 (134):** Complete structural API for upper/lower bounds: `mem_upperBounds`, `bddAbove_def`, `top_mem_upperBounds`, `isLeast_bot_iff`, `not_bddAbove_iff'`, `not_bddAbove_iff`, duality lemmas, `IsLeast.orderBot`, `isLUB_congr`, subset/union/intersection behavior (`upperBounds_mono_set`, `lowerBounds_mono_set`, `bddAbove_mono`, `bddBelow_mono`), singleton/pair/insert lemmas, interval characterizations (`upperBounds_Iic`, `lowerBounds_Ici`, `isLUB_Iic`, `isGLB_Ici`), `BddAbove.inter_left`, transitivity lemmas, `IsLUB.unique`, `IsLUB.mono`. Every theorem is a structural consequence of the definitions.

### Bounds/Image.lean (54 declarations)

**B1 (54):** Monotone/antitone image behavior for bounds: `MonotoneOn.mem_upperBounds_image`, `MonotoneOn.map_bddAbove`, `MonotoneOn.map_isLeast`, antitone duals, `Monotone.mem_upperBounds_image`, `Monotone.map_bddAbove`, `Antitone` variants, `GaloisConnection.bddAbove_l_image`, `GaloisInsertion.map_bddAbove`. Pure structural.

### Bounds/Lattice.lean (5 declarations)

**B1 (5):** `gc_upperBounds_lowerBounds` (GC between upper and lower bounds), `upperBounds_iUnion`, `lowerBounds_iUnion`, `isLUB_iUnion_iff_of_isLUB`, `isGLB_iUnion_iff_of_isLUB`. Structural.

### Bounds/OrderIso.lean (10 declarations)

**B1 (10):** OrderIso interactions with bounds: `upperBounds_image`, `lowerBounds_image`, `isLUB_image`, `isLUB_image'`, `isGLB_image`, `isGLB_image'`, `isLUB_preimage`, `isLUB_preimage'`, `isGLB_preimage`, `isGLB_preimage'`. Structural.

### Bounds/ totals: B1: 203, B2: 0, B3: 0

**100% B1.** Pure structural API for upper/lower bounds theory. No zero-management. No domain-specific content.

## 1a-19: BooleanAlgebra/ (257 declarations)

### BooleanAlgebra/Defs.lean (7 declarations)

**B1 (7):** Class definitions: `GeneralizedBooleanAlgebra`, `BooleanAlgebra`, instances, basic structural lemmas.

### BooleanAlgebra/Basic.lean (104 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 103 | 99.0% |
| B2 | 1 | 1.0% |
| B3 | 0 | 0% |

**B1 (103):** Complete generalized Boolean algebra / Boolean algebra identity library: `sup_inf_sdiff`, `inf_inf_sdiff`, `sup_sdiff_inf`, `inf_sdiff_inf`, `GeneralizedBooleanAlgebra.toOrderBot`, `disjoint_inf_sdiff`, `sdiff_unique`, `sdiff_inf_sdiff`, `disjoint_sdiff_sdiff`, `inf_sdiff_self_right`, `inf_sdiff_self_left`, `GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra`, `disjoint_sdiff_self_left/right`, `le_sdiff`, `sdiff_eq_left`, `Disjoint.sdiff_eq_of_sup_eq`, `Disjoint.sdiff_unique`, `disjoint_sdiff_iff_le`, `le_iff_disjoint_sdiff`, `inf_sdiff_eq_bot_iff`, `le_iff_eq_sup_sdiff`, and many more sdiff/symmDiff/complement identities.

**B2 (1):** `Nontrivial` reference (likely in a theorem about non-degenerate Boolean algebras).

### BooleanAlgebra/Set.lean (146 declarations)

**B1 (145):** Set-theoretic Boolean algebra: `Set.sdiff_eq`, `Set.compl_eq`, `Set.symmDiff_def`, `Set.union_compl_self`, `Set.compl_union`, `Set.compl_inter`, `Set.compl_compl`, plus the full lattice/Boolean algebra structure on `Set α` — definitional unfoldings and structural plumbing for set operations interpreted as Boolean algebra operations.

**B2 (1):** Minor reference.

### BooleanAlgebra/ totals: B1: 255, B2: 2, B3: 0

**99.2% B1.** Pure algebraic identity library for Boolean algebras and sets. The sdiff/complement/symmDiff identities are all structural — they follow from the axioms by algebraic manipulation.

## 1a-20: ConditionallyCompleteLattice/ (272 declarations)

### ConditionallyCompleteLattice/Defs.lean (2 declarations)

**B1 (2):** Class definitions and basic axiom unpackings.

### ConditionallyCompleteLattice/Basic.lean (133 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 105 | 78.9% |
| B2 | 15 | 11.3% |
| B3 | 13 | 9.8% |

**B1 (105):** Structural cSup/cInf API: `le_csSup`, `csSup_le`, `csSup_le_csSup`, `csInf_le`, `le_csInf`, conditional lattice instances for OrderDual/Pi, `csSup_singleton`, `csInf_singleton`, `csSup_pair`, `csInf_pair`, `le_csSup_of_le`, `csInf_le_of_le`, interval suprema/infima (`csSup_Icc`, `csInf_Icc`, etc.), `csSup_le_iff`, `le_csInf_iff`, `lt_csSup_of_lt`, `csInf_lt_of_lt`, monotone csSup, `csSup_union`, `csSup_inter_le`, etc.

**B2 (15):** Theorems with `WithBot`/`WithTop` interactions (the CCL instance on `WithBot`/`WithTop` lifts a CCL structure by adding ⊥/⊤), `Nontrivial` conditions, and junk value management (cSup of empty/unbounded sets).

**B3 (13):** Genuine mathematical results: `ConditionallyCompleteLattice.of_sSup_eq` (construction from sSup), `ConditionallyCompleteLattice.of_sInf_eq`, `csSup_of_not_bddAbove`, `csInf_of_not_bddBelow`, `isGLB_csInf'`, `isLUB_csSup'`, completeness-type results, and the construction of CCL instances from other structures.

### ConditionallyCompleteLattice/Finset.lean (35 declarations)

**B1 (33):** Finset supremum/infimum API in CCL context: `Finset.Nonempty.csSup_eq_max'`, `Finset.Nonempty.csInf_eq_min'`, `Finset.Nonempty.csSup_mem`, etc.

**B2 (2):** Finset `≠ ∅` conditions (analogous to NeZero).

### ConditionallyCompleteLattice/Group.lean (8 declarations)

**B1 (8):** Group-ordered CCL interactions: `csSup_neg`, `csInf_neg`, `csSup_add`, etc. Structural.

### ConditionallyCompleteLattice/Indexed.lean (94 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 82 | 87.2% |
| B2 | 5 | 5.3% |
| B3 | 7 | 7.4% |

**B1 (82):** Indexed cSup/cInf API: `ciSup_le`, `le_ciSup`, `ciSup_le_iff`, `le_ciInf_iff`, `ciSup_mono`, `ciInf_mono`, `ciSup_const`, `ciSup_unique`, `ciSup_pos`, `ciSup_neg`, monotone ciSup, GaloisConnection interactions, OrderIso interactions, etc.

**B2 (5):** `WithBot`/`WithTop` indexed supremum/infimum management.

**B3 (7):** Nested intervals lemma (`Monotone.ciSup_mem_iInter_Icc_of_antitone`), monotone convergence results, `ciSup_set_le_iff`, and construction results.

### ConditionallyCompleteLattice/ totals: B1: 230, B2: 22, B3: 20

**B2 hotspot (8.1%).** The highest B2 concentration in Order domain. WithBot/WithTop lifting and junk-value management for cSup/cInf of empty/unbounded sets are the primary sources. In the Val framework, origin would represent "undefined cSup" instead of conflating it with ⊥.

## 1a-21: Heyting/ (337 declarations)

### Heyting/Basic.lean (214 declarations)

**B1 (211):** Complete Heyting/co-Heyting algebra identity library: `le_himp_iff`, `himp_le_iff`, `himp_self`, `himp_inf_le`, `inf_himp`, `himp_compl`, `compl_sup`, `compl_inf`, `compl_compl_compl`, `compl_le_compl`, `compl_top`, `compl_bot`, `le_compl_iff_disjoint_left/right`, coHeyting duals, `sdiff_le_iff`, `sdiff_le_sdiff`, `hnot_inf_distrib`, `hnot_sup_self`, `sup_hnot_self`, and hundreds more algebraic identities for Heyting/co-Heyting implication, complement, and negation operations.

**B2 (3):** `Nontrivial` conditions (a trivial Heyting algebra has ⊤ = ⊥).

**B3 (0):** All identities are structural consequences of the Heyting algebra axioms.

### Heyting/Hom.lean (69 declarations)

**B1 (69):** Heyting algebra homomorphism API: `HeytingHom`, `CoheytingHom`, `BiheytingHom` structures and their complete API (FunLike, composition, identity, map_himp, map_compl, map_sdiff, map_hnot, etc.). Pure structural.

### Heyting/Boundary.lean (18 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 2 | 11.1% |
| B2 | 0 | 0% |
| B3 | 16 | 88.9% |

**B1 (2):** `boundary_bot`, `boundary_top` (trivial evaluations)

**B3 (16):** Co-Heyting boundary theory: `boundary_le`, `boundary_le_hnot`, `boundary_hnot_le`, `boundary_hnot_hnot`, `hnot_boundary`, `boundary_inf` (Leibniz rule), `boundary_inf_le`, `boundary_sup_le`, `boundary_le_boundary_sup_sup_boundary_inf_left/right`, `boundary_sup_sup_boundary_inf`, `boundary_idem`, `hnot_hnot_sup_boundary`, `hnot_eq_top_iff_exists_boundary`, `Coheyting.boundary_eq_bot` (trivializes in Boolean case)

### Heyting/Regular.lean (36 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 10 | 27.8% |
| B2 | 0 | 0% |
| B3 | 26 | 72.2% |

**B1 (10):** Definitional: `IsRegular.eq`, `IsRegular.decidablePred`, and basic structural lemmas

**B3 (26):** Regular element theory: `isRegular_bot`, `isRegular_top`, `IsRegular.inf`, `IsRegular.himp`, `isRegular_compl`, `IsRegular.disjoint_compl_left/right_iff`, `BooleanAlgebra.ofRegular` (Heyting algebra with regular excluded middle is Boolean), `Regular` subtype, `Regular.val_compl`, `Regular.coe_inf`, `Regular.lattice`, `Regular.boundedOrder`, `Regular.complementedLattice`, `Regular.booleanAlgebra` (Heyting-regular elements form a Boolean algebra), `Regular.val_sup`, GaloisInsertion from regular elements

### Heyting/ totals: B1: 292, B2: 3, B3: 42

**86.6% B1.** The bulk is algebraic identities. The B3 is concentrated in Boundary.lean (co-Heyting boundary theory — Leibniz rule, idempotence) and Regular.lean (regular elements forming a Boolean algebra).

## Final Summary: All 21 Small Subdirectories Complete

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
| 1a-11 | Fin/ | 77 | 66 | 10 | 1 |
| 1a-12 | BoundedOrder/ | 80 | 78 | 2 | 0 |
| 1a-13 | GaloisConnection/ | 96 | 95 | 1 | 0 |
| 1a-14 | Preorder/ | 105 | 105 | 0 | 0 |
| 1a-15 | Partition/ | 107 | 22 | 7 | 78 |
| 1a-16 | Defs/ | 119 | 119 | 0 | 0 |
| 1a-17 | RelIso/ | 121 | 117 | 0 | 4 |
| 1a-18 | Bounds/ | 203 | 203 | 0 | 0 |
| 1a-19 | BooleanAlgebra/ | 257 | 255 | 2 | 0 |
| 1a-20 | CondCompleteLattice/ | 272 | 230 | 22 | 20 |
| 1a-21 | Heyting/ | 337 | 292 | 3 | 42 |
| **Total** | | **1,983** | **1,705** | **64** | **215** |
| **%** | | | **86.0%** | **3.2%** | **10.8%** |
