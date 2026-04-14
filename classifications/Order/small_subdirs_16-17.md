# Order Small Subdirs: Steps 1a-16 and 1a-17

Classified theorem-by-theorem. Every declaration read.

## 1a-16: Defs/ (119 declarations)

### Defs/Unbundled.lean (56 declarations)

**B1 (56):** All structural. Relation class definitions (`IsIrrefl` → `Std.Irrefl` deprecation, `IsRefl`, `IsSymm`, `IsAsymm`, `IsAntisymm`, `IsTrans`, `IsTotal`, `IsPreorder`, `IsPartialOrder`, `IsLinearOrder`, `IsEquiv`, `IsStrictOrder`, `IsStrictWeakOrder`, `IsTrichotomous`, `IsStrictTotalOrder`), basic lemmas (`irrefl`, `refl`, `trans`, `symm`, `antisymm`, `asymm`, `trichotomous`), decidable instances, `_of` variants, `Minimal`/`Maximal` definitions, `IsUpperSet`/`IsLowerSet`/`UpperSet`/`LowerSet` definitions, `rel_congr` family, `extensional_of_trichotomous_of_irrefl`.

### Defs/PartialOrder.lean (32 declarations)

**B1 (32):** All structural. `Preorder` class, `Std.LawfulOrderLT`, `Std.IsPreorder` instances, basic preorder lemmas (`le_refl`, `le_rfl`, `le_trans`, `ge_trans`, `lt_iff_le_not_ge`, `lt_of_le_not_ge`, `le_of_eq`, `le_of_lt`, `not_le_of_gt`, `not_lt_of_ge`, `lt_irrefl`, `lt_of_lt_of_le`, `lt_of_le_of_lt`, `lt_trans`, `ne_of_lt`, `lt_asymm`, `le_of_lt_or_eq`, `le_of_eq_or_lt`), `Trans` instances, `decidableLTOfDecidableLE`, `WCovBy`/`CovBy` definitions, `PartialOrder` class, `Std.IsPartialOrder`, `le_antisymm`, `le_antisymm_iff`, `lt_of_le_of_ne`, `decidableEqOfDecidableLE`, `Decidable.lt_or_eq_of_le`, `lt_or_eq_of_le`.

### Defs/LinearOrder.lean (31 declarations)

**B1 (31):** All structural. `maxDefault`/`minDefault`, `LinearOrder` class, `Std.IsLinearOrder`, basic linear order lemmas (`le_total`, `le_of_not_ge`, `lt_of_not_ge`, `lt_or_ge`, `le_or_gt`, `lt_trichotomy`, `le_of_not_gt`, `lt_or_gt_of_ne`, `ne_iff_lt_or_gt`, `lt_iff_not_ge`, `not_lt`, `not_le`, `eq_or_gt_of_not_lt`, `le_imp_le_of_lt_imp_lt`), min/max API (`min_def`, `max_def`, `min_le_left`, `min_le_right`, `le_min`, `eq_min`, `min_comm`, `min_assoc`, `min_left_comm`, `min_self`, `min_eq_left`, `min_eq_right`, `lt_min`), `compare` API, `LinOrd` structure.

### Defs/ totals: B1: 119, B2: 0, B3: 0

**100% B1.** Pure order-theoretic definitions and their immediate API. No zero-management. No domain-specific content — this is the structural foundation that every ordered type inherits.

## 1a-17: RelIso/ (121 declarations)

### RelIso/Basic.lean (98 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 96 | 98.0% |
| B2 | 0 | 0% |
| B3 | 2 | 2.0% |

**B1 (96):** The entire API for `RelHom`, `RelEmbedding`, `RelIso`:
- `RelHom`: `FunLike`, `RelHomClass`, `map_rel`, `coe_fn_toFun`, `coeFn_mk`, `coe_fn_injective`, `ext`, `id`, `comp`, `swap`, `preimage`
- `RelHomClass`: `irrefl`, `asymm`, `acc`, `wellFounded`, `isWellFounded`
- `injective_of_increasing`, `Function.Surjective.wellFounded_iff`
- `RelEmbedding`: `toRelHom`, `Coe`, `FunLike`, `RelHomClass`, `EmbeddingLike`, `coe_toEmbedding`, `coe_toRelHom`, `toEmbedding_injective`, `toEmbedding_inj`, `injective`, `inj`, `map_rel_iff`, `coe_mk`, `coe_fn_injective`, `ext`, `refl`, `trans`, `Inhabited`, `trans_apply`, `coe_trans`, `swap`, `swap_apply`, `preimage`, `preimage_apply`, `eq_preimage`, `irrefl`, `stdRefl`, `symm`, `asymm`, `antisymm`, `isTrans`, `total`, `isPreorder`, `isPartialOrder`, `isLinearOrder`, `isStrictOrder`, `trichotomous`, `isStrictTotalOrder`, `acc`, `wellFounded`, `isWellFounded`, `isWellOrder`, `ofMapRelIff`, `ofMonotone`, `ofIsEmpty`, `sumLiftRelInl`, `sumLiftRelInr`, `sumLiftRelMap`, `sumLexInl`, `sumLexInr`, `sumLexMap`, `prodLexMkLeft`, `prodLexMkRight`, `prodLexMap`
- `Subtype.relEmbedding`, `Subtype.wellFoundedLT`, `Subtype.wellFoundedGT`
- `Quotient.mkRelHom`, `Quotient.outRelEmbedding`, `acc_lift₂_iff`, `wellFounded_lift₂_iff`
- `RelIso`: `toRelEmbedding`, `toEquiv_injective`, `CoeOut`, `FunLike`, `RelHomClass`, `EquivLike`, `coe_toRelEmbedding`, `coe_toEmbedding`, `map_rel_iff`, `coe_fn_mk`, `coe_fn_toEquiv`, `coe_fn_injective`, `ext`, `symm`, `refl`, `trans`, `Inhabited`, `default_def`, `apply_symm_apply`, `symm_apply_apply`, `symm_comp_self`, `self_comp_symm`, `symm_trans_apply`, `symm_symm_apply`, `apply_eq_iff_eq`, `apply_eq_iff_eq_symm_apply`, `symm_apply_eq`, `eq_symm_apply`, `symm_symm`, `symm_bijective`, `refl_symm`, `trans_refl`, `refl_trans`, `symm_trans_self`, `self_trans_symm`, `trans_assoc`, `cast`, `cast_symm`, `cast_refl`, `cast_trans`, `swap`, `compl`

**B3 (2):** `preimage_equivalence` (preimage of equivalence relation is equivalence — borderline, but states a mathematical fact), `injective_of_increasing` (increasing function on trichotomous order is injective)

### RelIso/Set.lean (23 declarations)

| Bucket | Count | % |
|---|---|---|
| B1 | 21 | 91.3% |
| B2 | 0 | 0% |
| B3 | 2 | 8.7% |

**B1 (21):** `RelHomClass.map_inf`, `map_sup`, `directed`, `directedOn`, `RelIso.range_eq`, `subrel_val`, `Subrel.relEmbedding`, `relEmbedding_apply`, `inclusionEmbedding`, `coe_inclusionEmbedding`, 7 `Subrel` instances (Refl, Symm, Asymm, Trans, Irrefl, Trichotomous, IsWellFounded), `IsPreorder`/`IsStrictOrder`/`IsWellOrder` instances, `RelIso.subrelUnivIso`, `RelEmbedding.codRestrict`, `codRestrict_apply`, `RelIso.image_eq_preimage_symm`, `RelIso.preimage_eq_image_symm`

**B3 (2):** `Acc.of_subrel` (accessibility from subrelation), `wellFounded_iff_wellFounded_subrel` (well-foundedness characterized by subrelation well-foundedness)

### RelIso/ totals: B1: 117, B2: 0, B3: 4

## Combined Summary: Steps 1a-01 through 1a-08, 1a-16, 1a-17

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
| 1a-16 | Defs/ | 119 | 119 | 0 | 0 |
| 1a-17 | RelIso/ | 121 | 117 | 0 | 4 |
| **Total** | | **331** | **289** | **13** | **29** |
| **%** | | | **87.3%** | **3.9%** | **8.8%** |
