/-
Extracted from Algebra/Homology/Factorizations/CM5a.lean
Genuine: 9 of 10 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Factorization lemma

In this file, we show that if `f : K ⟶ L` is a morphism between bounded below
cochain complexes in an abelian category with enough injectives,
there exists a factorization `ι ≫ π = f` with `ι : K ⟶ K'` a monomorphism that is also
a quasimorphism and `π : K' ⟶ L` a morphism which degreewise is an epimorphism with
an injective kernel, while `K'` is also bounded below (with precise bounds depending
on the available bounds for `K` and `L`): this is
`CochainComplex.Plus.modelCategoryQuillen.cm5a`. Using the factorization
obtained in the file `Mathlib/Algebra/Homology/Factorizations/CM5b.lean`,
we may assume `f : K ⇨ L` is a monomorphism (a case which appears as
the lemma `CochainComplex.Plus.modelCategoryQuillen.cm5a_cof`).

In the proof, the key (private) lemma is be
`CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.step` which shows that
if `f` is a monomorphism which is a quasi-isomorphism in degrees `≤ n₀` and
`n₀ + 1 = n₁`, then `f` has a factorisation `ι ≫ π = f`
where `ι` is a monomorphism that is a quasi-isomorphism in degrees `≤ n₁`,
and `π` is an isomorphism in degrees `≤ n₀` that is also a degreewise
epimorphism with an injective kernel. The proof of `step` decomposes
a two separate lemmas `step₁` and `step₂`: we first ensure that `ι`
induces a monomorphism in homology in degree `n₁`, and we proceed further
in `step₂`.

As we assume that both `K` and `L` are bounded below, we may find `n₀ : ℤ`
such that `K` and `L` are strictly `≥ n₀ + 1`: in particular, `f` induces
an isomorphism in degrees `≤ n₀`. Iterating the lemma `step`, we construct
a projective system `ℕᵒᵖ ⥤ CochainComplex C ℤ`
(see `CochainComplex.Plus.modelCategoryQuillen.cm5a_cof.cochainComplexFunctor`).
Degreewise, this projective system is essentially constant, which allows
to take its limit, which shall be the intermediate object in the
lemma `cm5a_cof`.

-/

open CategoryTheory Limits Opposite Abelian HomologicalComplex Pretriangulated

variable {C : Type*} [Category* C] [Abelian C]

namespace CochainComplex.Plus.modelCategoryQuillen

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

namespace cm5a_cof

def cofFib : ObjectProperty (Factorisation f) :=
  fun F ↦ Mono F.ι ∧ degreewiseEpiWithInjectiveKernel F.π

-- INSTANCE (free from Core): (F

variable {f} in

def quasiIsoLE (n : ℤ) : ObjectProperty (cofFib f).FullSubcategory :=
  fun F ↦ ∀ i ≤ n, QuasiIsoAt F.obj.ι i

variable {f} in

def isIsoLE (n : ℤ) : ObjectProperty (cofFib f).FullSubcategory :=
  fun F ↦ ∀ i ≤ n, IsIso (F.obj.π.f i)

namespace step₁

variable [EnoughInjectives C]

/-!
This section provides the material in order to prove the lemma `step₁` below.
Given a monomorphism `f : K ⟶ L` in `CochainComplex C ℤ` which is
a quasi-isomorphism in degrees `≤ n₀` (with `n₀ + 1 = n₁`), we construct
a factorization `ι f n₁ ≫ π K L n₁ = f` where the intermediate object
`mid K L n₁` is `S K n₁ ⊞ L`, with `S K n₁` the single complex in degree `n₁`
given by an injective object containing `K.opcycles n₁` (which is a cokernel of
the differential `K.X n₀ ⟶ K.X n₁`).
We obtain that `ι f n₁` is a quasi-isomorphism in degrees `≤ n₀` and
induces a monomorphism in homology in degree `n₀`,
and that `π K L n₁` is an isomorphism in degrees `≤ n₀` that is
also a degreewise epimorphism with an injective kernel. -/

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)

variable (K) in

noncomputable abbrev S : CochainComplex C ℤ :=
    ((single C _ n₁).obj (Injective.under (K.opcycles n₁)))

variable (K L) in

noncomputable abbrev mid := S K n₁ ⊞ L

variable (K) in

noncomputable def i : K ⟶ S K n₁ := mkHomToSingle (K.pOpcycles n₁ ≫ Injective.ι _) (by simp)

noncomputable abbrev ι : K ⟶ mid K L n₁ := biprod.lift (i K n₁) f

variable (K L) in

noncomputable abbrev π : mid K L n₁ ⟶ L := biprod.snd

variable (K L) in

noncomputable abbrev σ : L ⟶ mid K L n₁ := biprod.inr
