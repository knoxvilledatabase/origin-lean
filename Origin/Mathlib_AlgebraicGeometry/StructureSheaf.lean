/-
Extracted from AlgebraicGeometry/StructureSheaf.lean
Genuine: 9 of 13 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# The structure sheaf on `PrimeSpectrum R`.

We define the structure sheaf on `TopCat.of (PrimeSpectrum R)`, for an `R`-module `M` and prove
basic properties about it. We define this as a subsheaf of the sheaf of dependent functions into the
localizations, cut out by the condition that the function must be locally equal to a quotient of
an element of `M` by an element of `R`.

Because the condition "is equal to a fraction" passes to smaller open subsets,
the subset of functions satisfying this condition is automatically a subpresheaf.
Because the condition "is locally equal to a fraction" is local,
it is also a subsheaf.

(It may be helpful to refer back to `Mathlib/Topology/Sheaves/SheafOfFunctions.lean`,
where we show that dependent functions into any type family form a sheaf,
and also `Mathlib/Topology/Sheaves/LocalPredicate.lean`, where we characterise the predicates
which pick out sub-presheaves and sub-sheaves of these sheaves.)

When `M = R`, the structure sheaf is furthermore a sheaf of commutative rings, which we bundle as
`structureSheaf : Sheaf CommRingCat (PrimeSpectrum.Top R)`.

We then obtain two key descriptions of the structure sheaf. We show that the stalks `Mₓ` is the
localization of `M` at the prime corresponding to `x`, and we show that the sections `Γ(M, D(f))`
is the localization of `M` away from `f`.

Note that the results of this file are packaged into schemes and sheaf of modules in later files,
and one usually should not directly use the results in this file to respect the abstraction
boundaries.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

universe u

noncomputable section

variable {R M A : Type u} [CommRing R] [AddCommGroup M] [Module R M] [CommRing A] [Algebra R A]

open TopCat

open TopologicalSpace CategoryTheory Opposite

open PrimeSpectrum (basicOpen)

namespace AlgebraicGeometry

variable (R) in

public def PrimeSpectrum.Top : TopCat := TopCat.of (PrimeSpectrum R)

namespace StructureSheaf

variable {P : PrimeSpectrum.Top R}

variable (M P) in

abbrev Localizations : Type u := LocalizedModule P.asIdeal.primeCompl M

def IsFraction {U : Opens (PrimeSpectrum.Top R)} (f : Π x : U, Localizations M x.1) : Prop :=
  ∃ r s, ∀ x : U, ∃ hs : s ∉ x.1.asIdeal, f x = LocalizedModule.mk r ⟨s, hs⟩

variable (R M) in

def isFractionPrelocal : PrelocalPredicate (Localizations (R := R) M) where
  pred {_} f := IsFraction f
  res := by rintro V U i f ⟨r, s, w⟩; exact ⟨r, s, fun x => w (i x)⟩

variable (R M) in

def isLocallyFraction : LocalPredicate (Localizations (R := R) M) :=
  (isFractionPrelocal R M).sheafify

variable (M) in

def sectionsSubmodule (U : (Opens (PrimeSpectrum.Top R))) :
    Submodule R (Π x : U, Localizations M x.1) where
  carrier := { f | (isLocallyFraction R M).pred f }
  add_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, sb • ra + sa • rb, sa * sb, fun x ↦ ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
    obtain ⟨hsbx, hsb⟩ := wb ⟨x.1, x.2.2⟩
    exact ⟨x.1.asIdeal.primeCompl.mul_mem hsax hsbx,
      congr($hsa + $hsb).trans (LocalizedModule.mk_add_mk ..)⟩
  zero_mem' x := ⟨U, x.2, 𝟙 _, 0, 1, fun y ↦ by simp [Ideal.IsPrime.one_notMem]⟩
  smul_mem' r {a} ha x := by
    obtain ⟨V, m, i, ra, sa, wa⟩ := ha x
    exact ⟨V, m, i, r • ra, sa, fun x ↦ ⟨(wa x).1,
      congr(r • $((wa x).2)).trans (LocalizedModule.smul'_mk ..)⟩⟩

variable (A) in

def sectionsSubalgebra (U : (Opens (PrimeSpectrum.Top R))) :
    Subalgebra R (Π x : U, Localizations A x.1) where
  __ := sectionsSubmodule A U
  mul_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * rb, sa * sb, fun x ↦ ?_⟩
    obtain ⟨hsax, hsa⟩ := wa ⟨x.1, x.2.1⟩
    obtain ⟨hsbx, hsb⟩ := wb ⟨x.1, x.2.2⟩
    exact ⟨x.1.asIdeal.primeCompl.mul_mem hsax hsbx,
      congr($hsa * $hsb).trans (LocalizedModule.mk_mul_mk ..)⟩
  algebraMap_mem' r x :=
    ⟨U, x.2, 𝟙 _, algebraMap R A r, 1, fun y ↦ ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in

variable (M) in

def sectionsSubalgebraSubmodule (U : (Opens (PrimeSpectrum.Top R))) :
    Submodule (sectionsSubalgebra R U) (Π x : U, Localizations M x.1) where
  __ := sectionsSubmodule M U
  smul_mem' r {a} ha x := by
    obtain ⟨V, hxV, hVU, rx, rs, hr⟩ := r.2 x
    obtain ⟨W, hxW, hWU, ax, as, ha⟩ := ha x
    refine ⟨V ⊓ W, ⟨hxV, hxW⟩, homOfLE (inf_le_left.trans hVU.le), rx • ax, as * rs, fun y ↦ ?_⟩
    obtain ⟨hrsy, hry⟩ := hr ⟨y.1, y.2.1⟩
    obtain ⟨hasy, hay⟩ := ha ⟨y.1, y.2.2⟩
    exact ⟨y.1.asIdeal.primeCompl.mul_mem hasy hrsy, congr($hry • $hay)⟩

end StructureSheaf

open StructureSheaf

variable (R M) in

def structureSheafInType : Sheaf (Type u) (PrimeSpectrum.Top R) :=
  subsheafToTypes (isLocallyFraction R M)

-- INSTANCE (free from Core): (U

-- INSTANCE (free from Core): (U

-- INSTANCE (free from Core): (U

-- INSTANCE (free from Core): (U

local notation "Γ(" M ", " U ")" =>

  (Functor.obj (ObjectProperty.FullSubcategory.obj (structureSheafInType _ M))) (Opposite.op U)
