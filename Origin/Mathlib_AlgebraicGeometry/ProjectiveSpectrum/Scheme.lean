/-
Extracted from AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Proj as a scheme

This file is to prove that `Proj` is a scheme.

## Notation

* `Proj`      : `Proj` as a locally ringed space
* `Proj.T`    : the underlying topological space of `Proj`
* `Proj| U`   : `Proj` restricted to some open set `U`
* `Proj.T| U` : the underlying topological space of `Proj` restricted to open set `U`
* `pbo f`     : basic open set at `f` in `Proj`
* `Spec`      : `Spec` as a locally ringed space
* `Spec.T`    : the underlying topological space of `Spec`
* `sbo g`     : basic open set at `g` in `Spec`
* `A⁰_x`      : the degree zero part of localized ring `Aₓ`

## Implementation

In `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/StructureSheaf.lean`, we have given `Proj` a
structure sheaf so that `Proj` is a locally ringed space. In this file we will prove that `Proj`
equipped with this structure sheaf is a scheme. We achieve this by using an affine cover by basic
open sets in `Proj`, more specifically:

1. We prove that `Proj` can be covered by basic open sets at homogeneous elements of positive
    degree.
2. We prove that for any homogeneous element `f : A` of positive degree `m`, `Proj.T | (pbo f)` is
    homeomorphic to `Spec.T A⁰_f`:
  - forward direction `toSpec`:
    for any `x : pbo f`, i.e. a relevant homogeneous prime ideal `x`, send it to
    `A⁰_f ∩ span {g / 1 | g ∈ x}` (see `ProjIsoSpecTopComponent.ToSpec.carrier`). This ideal is
    prime, the proof is in `ProjIsoSpecTopComponent.ToSpec.toFun`. The fact that this function
    is continuous is found in `ProjIsoSpecTopComponent.toSpec`
  - backward direction `fromSpec`:
    for any `q : Spec A⁰_f`, we send it to `{a | ∀ i, aᵢᵐ/fⁱ ∈ q}`; we need this to be a
    homogeneous prime ideal that is relevant.
    * This is in fact an ideal, the proof can be found in
      `ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal`;
    * This ideal is also homogeneous, the proof can be found in
      `ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.homogeneous`;
    * This ideal is relevant, the proof can be found in
      `ProjIsoSpecTopComponent.FromSpec.carrier.relevant`;
    * This ideal is prime, the proof can be found in
      `ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.prime`.
    Hence we have a well-defined function `Spec.T A⁰_f → Proj.T | (pbo f)`, this function is called
    `ProjIsoSpecTopComponent.FromSpec.toFun`. But to prove the continuity of this function, we need
    to prove `fromSpec ∘ toSpec` and `toSpec ∘ fromSpec` are both identities; these are achieved in
    `ProjIsoSpecTopComponent.fromSpec_toSpec` and `ProjIsoSpecTopComponent.toSpec_fromSpec`.
3. Then we construct a morphism of locally ringed spaces `α : Proj| (pbo f) ⟶ Spec.T A⁰_f` as the
    following: by the Gamma-Spec adjunction, it is sufficient to construct a ring map
    `A⁰_f → Γ(Proj, pbo f)` from the ring of homogeneous localization of `A` away from `f` to the
    local sections of structure sheaf of projective spectrum on the basic open set around `f`.
    The map `A⁰_f → Γ(Proj, pbo f)` is constructed in `awayToΓ` and is defined by sending
    `s ∈ A⁰_f` to the section `x ↦ s` on `pbo f`.

## Main Definitions and Statements

For a homogeneous element `f` of degree `m`
* `ProjIsoSpecTopComponent.toSpec`: the continuous map between `Proj.T| pbo f` and `Spec.T A⁰_f`
  defined by sending `x : Proj| (pbo f)` to `A⁰_f ∩ span {g / 1 | g ∈ x}`. We also denote this map
  as `ψ`.
* `ProjIsoSpecTopComponent.ToSpec.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero,
  then the preimage of `sbo a/f^m` under `toSpec f` is `pbo f ∩ pbo a`.

If we further assume `m` is positive
* `ProjIsoSpecTopComponent.fromSpec`: the continuous map between `Spec.T A⁰_f` and `Proj.T| pbo f`
  defined by sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}` where `aᵢ` is the `i`-th coordinate of `a`.
  We also denote this map as `φ`
* `projIsoSpecTopComponent`: the homeomorphism `Proj.T| pbo f ≅ Spec.T A⁰_f` obtained by `φ` and
  `ψ`.
* `ProjectiveSpectrum.Proj.toSpec`: the morphism of locally ringed spaces between `Proj| pbo f`
  and `Spec A⁰_f` corresponding to the ring map `A⁰_f → Γ(Proj, pbo f)` under the Gamma-Spec
  adjunction defined by sending `s` to the section `x ↦ s` on `pbo f`.

Finally,
* `AlgebraicGeometry.Proj`: for any `ℕ`-graded ring `A`, `Proj A` is locally affine, hence is a
  scheme.

## Reference
* [Robin Hartshorne, *Algebraic Geometry*][Har77]: Chapter II.2 Proposition 2.5
-/

noncomputable section

namespace AlgebraicGeometry

open scoped DirectSum Pointwise

open DirectSum SetLike.GradedMonoid Localization

open Finset hiding mk_zero

variable {A σ : Type*}

variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

variable (𝒜 : ℕ → σ)

variable [GradedRing 𝒜]

open TopCat TopologicalSpace

open CategoryTheory Opposite

open ProjectiveSpectrum.StructureSheaf

set_option hygiene false

local notation3 "Proj" => Proj.toLocallyRingedSpace 𝒜

local notation3 "Proj.T" => PresheafedSpace.carrier <| SheafedSpace.toPresheafedSpace

  <| LocallyRingedSpace.toSheafedSpace <| Proj.toLocallyRingedSpace 𝒜

macro "Proj| " U:term : term =>

  `((Proj.toLocallyRingedSpace 𝒜).restrict

    (Opens.isOpenEmbedding (X := Proj.T) ($U : Opens Proj.T)))

local notation "Proj.T| " U => PresheafedSpace.carrier <| SheafedSpace.toPresheafedSpace

  <| LocallyRingedSpace.toSheafedSpace

    <| (LocallyRingedSpace.restrict Proj (Opens.isOpenEmbedding (X := Proj.T) (U : Opens Proj.T)))

local notation "pbo " x => ProjectiveSpectrum.basicOpen 𝒜 x

local notation "sbo " f => PrimeSpectrum.basicOpen f

local notation3 "Spec " ring => Spec.locallyRingedSpaceObj (CommRingCat.of ring)

local notation "Spec.T " ring =>

  (Spec.locallyRingedSpaceObj (CommRingCat.of ring)).toSheafedSpace.toPresheafedSpace.1

local notation3 "A⁰_ " f => HomogeneousLocalization.Away 𝒜 f

namespace ProjIsoSpecTopComponent

namespace ToSpec

open Ideal

variable {𝒜}

variable {f : A} {m : ℕ} (x : Proj| (pbo f))

def carrier : Ideal (A⁰_ f) :=
  Ideal.comap (algebraMap (A⁰_ f) (Away f))
    (x.val.asHomogeneousIdeal.toIdeal.map (algebraMap A (Away f)))
