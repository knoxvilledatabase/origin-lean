/-
Extracted from Algebra/Order/Module/HahnEmbedding.lean
Genuine: 33 of 44 | Dissolved: 3 | Infrastructure: 8
-/
import Origin.Core

/-!
# Hahn embedding theorem on ordered modules

This file proves a variant of the Hahn embedding theorem:

For a linearly ordered module `M` over an Archimedean division ring `K`,
there exists a strictly monotone linear map to lexicographically ordered
`R⟦FiniteArchimedeanClass M⟧` with an archimedean `K`-module `R`,
as long as there are embeddings from a certain family of Archimedean submodules to `R`.

The family of Archimedean submodules `HahnEmbedding.ArchimedeanStrata K M` is indexed by
`(c : ArchimedeanClass M)`, and each submodule is a complement of `ArchimedeanClass.ball K c`
under `ArchimedeanClass.closedBall K c`. The embeddings from these submodules are specified by
`HahnEmbedding.Seed K M R`.

By setting `K = ℚ` and `R = ℝ`, the condition can be trivially satisfied, leading
to a proof of the classic Hahn embedding theorem. (See `hahnEmbedding_isOrderedAddMonoid`)

## Main theorem

* `hahnEmbedding_isOrderedModule`:
  there exists a strictly monotone `M →ₗ[K] Lex R⟦FiniteArchimedeanClass M⟧` that maps
  `ArchimedeanClass M` to `HahnSeries.orderTop` in the expected way, as long as
  `HahnEmbedding.Seed K M R` is nonempty.

## References

* [M. Hausner, J.G. Wendel, *Ordered vector spaces*][hausnerwendel1952]
-/

/-! ### Step 1: base embedding

We start with `HahnEmbedding.ArchimedeanStrata` that gives a family of Archimedean submodules,
and a "seed" `HahnEmbedding.Seed` that specifies how to embed each
`HahnEmbedding.ArchimedeanStrata.stratum` into `R`.

From these, we create a partial map from the direct sum of all `stratum` to `R⟦Γ⟧`.
If `ArchimedeanClass M` is finite, the direct sum is the entire `M` and we are done
(though we don't handle this case separately). Otherwise, we will extend the map to `M` in the
following steps.
-/

open FiniteArchimedeanClass DirectSum HahnSeries

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]

variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable [Module K M] [IsOrderedModule K M]

variable {R : Type*} [AddCommGroup R] [LinearOrder R]

variable [Module K R]

namespace HahnEmbedding

variable (K M) in

structure ArchimedeanStrata where
  /-- For each `FiniteArchimedeanClass`, specify a corresponding submodule. -/
  stratum : FiniteArchimedeanClass M → Submodule K M
  /-- `stratum` and `FiniteArchimedeanClass.ball` are disjoint. -/
  disjoint_ball_stratum (c : FiniteArchimedeanClass M) : Disjoint (ball K c) (stratum c)
  /-- `stratum` and `FiniteArchimedeanClass.ball`
    are codisjoint under `FiniteArchimedeanClass.closedBall`. -/
  ball_sup_stratum_eq (c : FiniteArchimedeanClass M) : ball K c ⊔ stratum c = closedBall K c

namespace ArchimedeanStrata

variable (u : ArchimedeanStrata K M) {c : FiniteArchimedeanClass M}

-- INSTANCE (free from Core): :

theorem stratum_ne_bot : u.stratum c ≠ ⊥ :=
  fun eq ↦ (eq ▸ u.ball_sup_stratum_eq c).not_lt <| by simpa using ball_lt_closedBall _

-- INSTANCE (free from Core): nontrivial_stratum

-- DISSOLVED: archimedeanClassMk_of_mem_stratum

-- INSTANCE (free from Core): archimedean_stratum

theorem iSupIndep_stratum : iSupIndep u.stratum := by
  intro c
  rw [Submodule.disjoint_def']
  intro a ha b hb hab
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ b).mp hb
  obtain hf' := congr(ArchimedeanClass.mk $hf)
  contrapose! hf' with h0
  rw [← hab, DFinsupp.sum]
  by_cases! hnonempty : f.support.Nonempty
  · have hmem (x : FiniteArchimedeanClass M) : (f x).val ∈ u.stratum x :=
      Set.mem_of_mem_of_subset (f x).prop (by simp)
    have hmono : StrictMonoOn (fun i ↦ ArchimedeanClass.mk (f i).val) f.support := by
      intro x hx y hy hxy
      change ArchimedeanClass.mk (f x).val < ArchimedeanClass.mk (f y).val
      rw [u.archimedeanClassMk_of_mem_stratum (hmem x) (by simpa using hx)]
      rw [u.archimedeanClassMk_of_mem_stratum (hmem y) (by simpa using hy)]
      exact hxy
    rw [ArchimedeanClass.mk_sum hnonempty hmono, u.archimedeanClassMk_of_mem_stratum (hmem _)
      (by simpa using f.support.min'_mem hnonempty), ← val_mk h0, Subtype.coe_ne_coe]
    by_contra!
    obtain h := this ▸ Finset.min'_mem f.support hnonempty
    contrapose! h
    have := u.archimedeanClassMk_of_mem_stratum ha h0
    rw [← val_mk h0, ← Subtype.ext_iff] at this
    simpa [DFinsupp.notMem_support_iff, this] using (f c).prop
  · rw [hnonempty]
    symm
    simpa using h0

def baseDomain := ⨆ c, u.stratum c

abbrev stratum' (c : FiniteArchimedeanClass M) : Submodule K (baseDomain u) :=
  (u.stratum c).comap u.baseDomain.subtype

theorem iSupIndep_stratum' : iSupIndep u.stratum' := by
  apply (iSupIndep_map_orderIso_iff (Submodule.mapIic u.baseDomain)).mp
  apply iSupIndep.of_coe_Iic_comp
  convert u.iSupIndep_stratum
  ext1 c
  simpa using le_iSup _ _

theorem isInternal_stratum' : DirectSum.IsInternal u.stratum' := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top u.iSupIndep_stratum'
  apply Submodule.map_injective_of_injective u.baseDomain.subtype_injective
  suffices ⨆ i, u.baseDomain ⊓ u.stratum i = u.baseDomain by simpa using this
  apply iSup_congr
  intro c
  simpa using le_iSup _ _

noncomputable

-- INSTANCE (free from Core): :

end ArchimedeanStrata

variable (K M R) in

structure Seed extends ArchimedeanStrata K M where
  /-- For each stratum, specify a linear map to `R` as the Hahn series coefficient. -/
  coeff (c : FiniteArchimedeanClass M) : stratum c →ₗ[K] R
  /-- `coeff` is strictly monotone. -/
  strictMono_coeff (c : FiniteArchimedeanClass M) : StrictMono (coeff c)

variable (seed : Seed K M R)

namespace Seed

def coeff' (c : FiniteArchimedeanClass M) : seed.stratum' c →ₗ[K] R :=
  (seed.coeff c).comp (LinearMap.submoduleComap _ _)

noncomputable

def hahnCoeff : seed.baseDomain →ₗ[K] (⨁ _ : FiniteArchimedeanClass M, R) :=
  (DirectSum.lmap seed.coeff') ∘ₗ (DirectSum.decomposeLinearEquiv _).toLinearMap

theorem hahnCoeff_apply {x : seed.baseDomain} {f : Π₀ c, seed.stratum c}
    (h : x.val = f.sum fun c ↦ (seed.stratum c).subtype) (c : FiniteArchimedeanClass M) :
    seed.hahnCoeff x c = seed.coeff c (f c) := by
  suffices seed.baseDomain.subtype.submoduleComap
      (seed.stratum c) (DirectSum.decompose seed.stratum' x c) = f c by
    simp [Seed.hahnCoeff, coeff', decomposeLinearEquiv_apply, this]
  have hxm {c : FiniteArchimedeanClass M} (x : seed.stratum c) : x.val ∈ seed.baseDomain := by
    apply Set.mem_of_mem_of_subset x.prop
    simpa using le_iSup _ _
  let f' : ⨁ c, seed.stratum' c :=
    f.mapRange (fun c x ↦ (⟨⟨x.val, hxm x⟩, by simp⟩ : seed.stratum' c)) (by simp)
  have hf : f c = (seed.baseDomain.subtype.submoduleComap (seed.stratum c)) (f' c) := by
    apply Subtype.ext
    simp [f']
  have hx : x = (decompose seed.stratum').symm f' := by
    change x = f'.coeAddMonoidHom _
    apply Submodule.subtype_injective
    rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum_mapRange_index (by simp)]
    simp [h]
  simp [hf, hx]

set_option backward.isDefEq.respectTransparency false in

noncomputable

def baseEmbedding : M →ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ where
  domain := seed.baseDomain
  toFun := (toLexLinearEquiv _ _).toLinearMap ∘ₗ (HahnSeries.ofFinsuppLinearMap _) ∘ₗ
    (finsuppLequivDFinsupp K).symm.toLinearMap ∘ₗ seed.hahnCoeff

set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in

theorem coeff_baseEmbedding {x : seed.baseEmbedding.domain} {f : Π₀ c, seed.stratum c}
    (h : x.val = f.sum fun c ↦ (seed.stratum c).subtype) (c : FiniteArchimedeanClass M) :
    (ofLex ((baseEmbedding seed) x)).coeff c = seed.coeff c (f c) := by
  simpa [baseEmbedding] using seed.hahnCoeff_apply h c

set_option backward.isDefEq.respectTransparency false in

theorem mem_domain_baseEmbedding {x : M} {c : FiniteArchimedeanClass M} (h : x ∈ seed.stratum c) :
    x ∈ seed.baseEmbedding.domain := by
  apply Set.mem_of_mem_of_subset h
  rw [domain_baseEmbedding]
  simpa using le_iSup_iff.mpr fun _ h ↦ h c

end Seed

/-! ### Step 2: characterize partial embedding

We characterize the base embedding as a member of a class of partial linear embeddings
`HahnEmbedding.Partial`. These embeddings share nice properties, including being strictly monotone,
transferring `ArchimedeanClass` to `HahnEmbedding.orderTop`, and being "truncation-closed"
(see `HahnEmbedding.IsPartial.truncLT_mem_range`).
-/

set_option backward.isDefEq.respectTransparency false in

structure IsPartial (f : M →ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧) : Prop where
  /-- A partial Hahn embedding is strictly monotone. -/
  strictMono : StrictMono f
  /-- A partial Hahn embedding always extends `baseEmbedding`. -/
  baseEmbedding_le : seed.baseEmbedding ≤ f
  /-- If a Hahn series $f$ is in the range, then any truncation of $f$ is also in the range. -/
  truncLT_mem_range : ∀ x, ∀ c,
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (f x))) ∈ LinearMap.range f.toFun

namespace Seed

set_option backward.isDefEq.respectTransparency false in

theorem baseEmbedding_pos {x : seed.baseEmbedding.domain} (hx : 0 < x) :
    0 < seed.baseEmbedding x := by
  -- decompose `x` to sum of `stratum`
  have hmem : x.val ∈ seed.baseEmbedding.domain := x.prop
  simp_rw [seed.domain_baseEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  have hfpos : 0 < (f.sum fun _ x ↦ x.val) := by
    rw [hf]
    simpa using hx
  have hsupport : f.support.Nonempty := by
    obtain hne := hfpos.ne.symm
    contrapose! hne with hempty
    apply DFinsupp.sum_eq_zero
    intro c
    simpa using DFinsupp.notMem_support_iff.mp (Finset.eq_empty_iff_forall_notMem.mp hempty c)
  -- The dictating term for `HahnSeries` < is at the lowest archimedean class of `f.support`
  refine (HahnSeries.lt_iff _ _).mpr ⟨f.support.min' hsupport, ?_, ?_⟩
  · intro j hj
    rw [seed.coeff_baseEmbedding hf.symm]
    rw [DFinsupp.notMem_support_iff.mp ?_]
    · simp
    contrapose! hj
    rw [← Subtype.coe_le_coe, Subtype.coe_mk]
    exact Finset.min'_le f.support _ hj
  -- Show that `f`'s value at dominating archimedean class is positive
  rw [seed.coeff_baseEmbedding hf.symm]
  suffices (seed.coeff (f.support.min' hsupport)) 0 <
      (seed.coeff (f.support.min' hsupport)) (f (f.support.min' hsupport)) by
    simpa using this
  suffices 0 < (f (f.support.min' hsupport)).val by
    apply (seed.strictMono_coeff (f.support.min' hsupport))
    simpa using this
  -- using the fact that `f.sum` is positive, we only needs to show that
  -- the remaining terms of f after removing the dominating class is of higher class
  apply ArchimedeanClass.pos_of_pos_of_mk_lt hfpos
  rw [ArchimedeanClass.mk_sub_comm]
  have hferase : (f.sum fun _ x ↦ x.val) - (f (f.support.min' hsupport)).val =
      ∑ x ∈ f.support.erase (f.support.min' hsupport), (f x).val :=
    sub_eq_of_eq_add (Finset.sum_erase_add _ _ (Finset.min'_mem _ hsupport)).symm
  rw [hferase]
  -- Now both sides are `mk (∑ ...)`
  -- We rewrite them to `mk (dominating term)`
  have hmono : StrictMonoOn (fun x ↦ ArchimedeanClass.mk (f x).val) f.support := by
    intro c hc d hd h
    simp only
    rw [seed.archimedeanClassMk_of_mem_stratum (f c).prop (by simpa using hc)]
    rw [seed.archimedeanClassMk_of_mem_stratum (f d).prop (by simpa using hd)]
    exact h
  rw [DFinsupp.sum, ArchimedeanClass.mk_sum hsupport hmono]
  rw [seed.archimedeanClassMk_of_mem_stratum (f _).prop
    (by simpa using f.support.min'_mem hsupport)]
  by_cases! hsupport' : (f.support.erase (f.support.min' hsupport)).Nonempty
  · rw [ArchimedeanClass.mk_sum hsupport' (hmono.mono (by simp))]
    rw [seed.archimedeanClassMk_of_mem_stratum (f _).prop (by
      simpa using (Finset.mem_erase.mp <| (f.support.erase _).min'_mem hsupport').2)]
    apply Finset.min'_lt_of_mem_erase_min' (α := FiniteArchimedeanClass M)
    apply Finset.min'_mem _ _
  · -- special case: `f` has a single term, and becomes 0 after removing it
    simpa [hsupport'] using (f.support.min' hsupport).2.lt_top

set_option backward.isDefEq.respectTransparency false in

theorem baseEmbedding_strictMono [IsOrderedAddMonoid R] : StrictMono seed.baseEmbedding := by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  exact baseEmbedding_pos _ <| by simpa using h

set_option backward.isDefEq.respectTransparency false in

theorem truncLT_mem_range_baseEmbedding (x : seed.baseEmbedding.domain)
    (c : FiniteArchimedeanClass M) :
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (seed.baseEmbedding x))) ∈
    LinearMap.range seed.baseEmbedding.toFun := by
  -- decompose `x` to `stratum`
  have hmem : x.val ∈ seed.baseEmbedding.domain := x.prop
  simp_rw [seed.domain_baseEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  -- Truncating in the codomain is the same as truncating away some submodule
  let f' : Π₀ (i : FiniteArchimedeanClass M), seed.stratum i :=
    DFinsupp.mk f.support fun d ↦ if c.val ≤ d.val then 0 else f d.val
  refine ⟨⟨f'.sum fun d x ↦ x.val, ?_⟩, ?_⟩
  · rw [seed.domain_baseEmbedding, ArchimedeanStrata.baseDomain,
      Submodule.mem_iSup_iff_exists_dfinsupp']
    use f'
  apply_fun ofLex
  rw [ofLex_toLex, LinearPMap.toFun_eq_coe]
  ext d
  rw [seed.coeff_baseEmbedding rfl]
  unfold f'
  obtain hdc | hdc := lt_or_ge d c
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hdc,
      seed.coeff_baseEmbedding hf.symm]
    apply congrArg
    have hcd : ¬ c.val ≤ d.val := not_le_of_gt hdc
    simp only [DFinsupp.mk_apply, hcd, ↓reduceIte]
    aesop
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hdc]
    have hcd : c.val ≤ d.val := hdc
    simp only [DFinsupp.mk_apply, hcd, ↓reduceIte]
    convert LinearMap.map_zero _
    simp

theorem isPartial_baseEmbedding [IsOrderedAddMonoid R] : IsPartial seed seed.baseEmbedding where
  strictMono := seed.baseEmbedding_strictMono
  baseEmbedding_le := le_refl _
  truncLT_mem_range := seed.truncLT_mem_range_baseEmbedding

end Seed

set_option backward.isDefEq.respectTransparency false in

abbrev Partial := {f : M →ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ // IsPartial seed f}

namespace Partial

variable {seed} (f : Partial seed)

noncomputable

-- INSTANCE (free from Core): [IsOrderedAddMonoid

set_option backward.isDefEq.respectTransparency false in

noncomputable def toOrderAddMonoidHom : f.val.domain →+o Lex R⟦FiniteArchimedeanClass M⟧ where
  __ := f.val.toFun
  map_zero' := by simp
  monotone' := f.prop.strictMono.monotone

set_option backward.isDefEq.respectTransparency false in

theorem toOrderAddMonoidHom_injective : Function.Injective f.toOrderAddMonoidHom :=
  f.prop.strictMono.injective

set_option backward.isDefEq.respectTransparency false in

theorem mem_domain {x : M} {c : FiniteArchimedeanClass M} (hx : x ∈ seed.stratum c) :
    x ∈ f.val.domain := by
  apply Set.mem_of_subset_of_mem f.prop.baseEmbedding_le.1
  apply seed.mem_domain_baseEmbedding hx

set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in

open ArchimedeanClass in

theorem archimedeanClassMk_eq_iff [IsOrderedAddMonoid R] (x y : f.val.domain) :
    ArchimedeanClass.mk (f.val x) = .mk (f.val y) ↔ ArchimedeanClass.mk x.val = .mk y.val := by
  simp_rw [← toOrderAddMonoidHom_apply, ← orderHom_mk]
  trans ArchimedeanClass.mk x = .mk y
  · exact Function.Injective.eq_iff <| orderHom_injective <| toOrderAddMonoidHom_injective _
  · simp_rw [mk_eq_mk]
    aesop

set_option backward.isDefEq.respectTransparency false in

theorem orderTop_eq_iff [IsOrderedAddMonoid R] [Archimedean R] (x y : f.val.domain) :
    (ofLex (f.val x)).orderTop = (ofLex (f.val y)).orderTop ↔
    ArchimedeanClass.mk x.val = .mk y.val := by
  obtain hsubsingleton | hnontrivial := subsingleton_or_nontrivial M
  · have : y = x := Subtype.ext <| hsubsingleton.allEq _ _
    simp [this]
  have hnonempty : Nonempty (FiniteArchimedeanClass M) := inferInstance
  obtain c := hnonempty.some
  have : Nontrivial R := (seed.strictMono_coeff c).injective.nontrivial
  rw [← archimedeanClassMk_eq_iff]
  simp_rw [← HahnSeries.archimedeanClassOrderIsoWithTop_apply]
  rw [(HahnSeries.archimedeanClassOrderIsoWithTop (FiniteArchimedeanClass M) R).injective.eq_iff]

set_option backward.isDefEq.respectTransparency false in

theorem orderTop_eq_archimedeanClassMk [IsOrderedAddMonoid R] [Archimedean R] (x : f.val.domain) :
    FiniteArchimedeanClass.withTopOrderIso M (ofLex (f.val x)).orderTop = .mk x.val := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx0' : x.val ≠ 0 := by simpa using hx0
  -- Pick a representative `x'` from `stratum` with the same class as `x`.
  -- `f.val x'` is a `HahnSeries.single` whose `orderTop` is known
  obtain ⟨⟨x', hx'mem⟩, hx'0⟩ := exists_ne (0 : seed.stratum (.mk x hx0'))
  have heq : ArchimedeanClass.mk x' = .mk x.val := by
    apply seed.archimedeanClassMk_of_mem_stratum hx'mem
    simpa using hx'0
  let x'' : f.val.domain := ⟨x', mem_domain f hx'mem⟩
  have hx''mem : x''.val ∈ seed.stratum (mk x.val hx0') := hx'mem
  have h0 : (seed.coeff (mk x.val hx0')) ⟨x''.val, hx''mem⟩ ≠ 0 := by
    rw [(LinearMap.map_eq_zero_iff _ (seed.strictMono_coeff _).injective).ne]
    unfold x''
    simpa using hx'0
  have heq' : ArchimedeanClass.mk x''.val = .mk x.val := heq
  rw [← orderTop_eq_iff, apply_of_mem_stratum f hx''mem, ofLex_toLex,
    HahnSeries.orderTop_single h0] at heq'
  simp [← heq']

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: orderTop_eq_finiteArchimedeanClassMk

set_option backward.isDefEq.respectTransparency false in

theorem coeff_eq_zero_of_mem [IsOrderedAddMonoid R] [Archimedean R]
    {c : FiniteArchimedeanClass M} {x : f.val.domain} (hx : x.val ∈ ball K c)
    {d : FiniteArchimedeanClass M} (hd : d.val ≤ c) : (ofLex (f.val x)).coeff d = 0 := by
  obtain rfl | ne := eq_or_ne x 0
  · simp
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  apply_fun FiniteArchimedeanClass.withTopOrderIso _
  rw [orderTop_eq_archimedeanClassMk, FiniteArchimedeanClass.withTopOrderIso_apply_coe]
  apply lt_of_le_of_lt hd
  simpa using hx (by simpa using ne)

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: coeff_ne_zero

set_option backward.isDefEq.respectTransparency false in

theorem coeff_eq_of_mem [IsOrderedAddMonoid R] [Archimedean R] (x : M) {y z : f.val.domain}
    {c : FiniteArchimedeanClass M} (hy : y.val - x ∈ ball K c) (hz : z.val - x ∈ ball K c)
    {d : FiniteArchimedeanClass M} (hd : d ≤ c) :
    (ofLex (f.val y)).coeff d = (ofLex (f.val z)).coeff d := by
  apply eq_of_sub_eq_zero
  rw [← HahnSeries.coeff_sub, ← ofLex_sub, ← LinearPMap.map_sub]
  refine coeff_eq_zero_of_mem f ?_ hd
  have : (y - z).val = (y.val - x) - (z.val - x) := by
    push_cast
    simp
  rw [this]
  exact Submodule.sub_mem _ hy hz

/-! ### Step 3: extend the embedding

We create a larger `HahnEmbedding.Partial` from an existing one by adding a new element to the
domain and assigning an appropriate output that preserves all `HahnEmbedding.Partial`'s properties.
-/

set_option backward.isDefEq.respectTransparency false in

noncomputable

def evalCoeff (x : M) (c : FiniteArchimedeanClass M) : R :=
  open Classical in
  if h : ∃ y : f.val.domain, y.val - x ∈ ball K c then
    (ofLex (f.val h.choose)).coeff c
  else
    0

set_option backward.isDefEq.respectTransparency false in

theorem evalCoeff_eq [IsOrderedAddMonoid R] [Archimedean R] {x : M} {c : FiniteArchimedeanClass M}
    {y : f.val.domain} (hy : y.val - x ∈ ball K c) :
    evalCoeff f x c = (ofLex (f.val y)).coeff c := by
  have hnonempty : ∃ y : f.val.domain, y.val - x ∈ ball K c := ⟨y, hy⟩
  simpa [evalCoeff, dif_pos hnonempty] using coeff_eq_of_mem f x hnonempty.choose_spec hy le_rfl

set_option backward.isDefEq.respectTransparency false in

theorem evalCoeff_eq_zero {x : M} {c : FiniteArchimedeanClass M}
    (h : ¬∃ y : f.val.domain, y.val - x ∈ ball K c) :
    f.evalCoeff x c = 0 := by
  rw [evalCoeff, dif_neg h]

set_option backward.isDefEq.respectTransparency false in

theorem isWF_support_evalCoeff [IsOrderedAddMonoid R] [Archimedean R] (x : M) :
    (evalCoeff f x).support.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  by_contra! ⟨seq, ⟨hanti, hmem⟩⟩
  have hnonempty : ∃ y : f.val.domain, y.val - x ∈ ball K (seq 0) := by
    specialize hmem 0
    contrapose hmem with hempty
    simp [evalCoeff, dif_neg hempty]
  obtain ⟨y, hy⟩ := hnonempty
  have hmem' (n : ℕ) : seq n ∈ (ofLex (f.val y)).coeff.support := by
    specialize hmem n
    rw [Function.mem_support] at ⊢ hmem
    convert hmem using 1
    refine (f.evalCoeff_eq ((ball_strictAnti K).antitone ?_ hy)).symm
    simpa using hanti.antitone (show 0 ≤ n by simp)
  obtain hwf := (ofLex (f.val y)).isWF_support
  contrapose! hwf
  rw [Set.isWF_iff_no_descending_seq]
  simpa using ⟨seq, hanti, hmem'⟩

noncomputable

def eval [IsOrderedAddMonoid R] [Archimedean R] (x : M) :
    Lex R⟦FiniteArchimedeanClass M⟧ :=
  toLex { coeff := f.evalCoeff x
          isPWO_support' := (f.isWF_support_evalCoeff x).isPWO }
