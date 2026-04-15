/-
Extracted from NumberTheory/Cyclotomic/CyclotomicCharacter.lean
Genuine: 10 | Conflates: 0 | Dissolved: 9 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!

# The cyclotomic character

Let `L` be an integral domain and let `n : ℕ+` be a positive integer. If `μₙ` is the
group of `n`th roots of unity in `L` then any field automorphism `g` of `L`
induces an automorphism of `μₙ` which, being a cyclic group, must be of
the form `ζ ↦ ζ^j` for some integer `j = j(g)`, well-defined in `ZMod d`, with
`d` the cardinality of `μₙ`. The function `j` is a group homomorphism
`(L ≃+* L) →* ZMod d`.

Future work: If `L` is separably closed (e.g. algebraically closed) and `p` is a prime
number such that `p ≠ 0` in `L`, then applying the above construction with
`n = p^i` (noting that the size of `μₙ` is `p^i`) gives a compatible collection of
group homomorphisms `(L ≃+* L) →* ZMod (p^i)` which glue to give
a group homomorphism `(L ≃+* L) →* ℤₚ`; this is the `p`-adic cyclotomic character.

## Important definitions

Let `L` be an integral domain, `g : L ≃+* L` and `n : ℕ+`. Let `d` be the number of `n`th roots
of `1` in `L`.

* `ModularCyclotomicCharacter L n hn : (L ≃+* L) →* (ZMod n)ˣ` sends `g` to the unique `j` such
   that `g(ζ)=ζ^j` for all `ζ : rootsOfUnity n L`. Here `hn` is a proof that there
   are `n` `n`th roots of unity in `L`.

## Implementation note

In theory this could be set up as some theory about monoids, being a character
on monoid isomorphisms, but under the hypotheses that the `n`'th roots of unity
are cyclic. The advantage of sticking to integral domains is that finite subgroups
are guaranteed to be cyclic, so the weaker assumption that there are `n` `n`th
roots of unity is enough. All the applications I'm aware of are when `L` is a
field anyway.

Although I don't know whether it's of any use, `ModularCyclotomicCharacter'`
is the general case for integral domains, with target in `(ZMod d)ˣ`
where `d` is the number of `n`th roots of unity in `L`.

## TODO

* Prove the compatibility of `ModularCyclotomicCharacter n` and `ModularCyclotomicCharacter m`
  if `n ∣ m`.

* Define the cyclotomic character.

* Prove that it's continuous.

## Tags

cyclotomic character
-/

universe u

variable {L : Type u} [CommRing L] [IsDomain L]

variable (n : ℕ) [NeZero n]

theorem rootsOfUnity.integer_power_of_ringEquiv (g : L ≃+* L) :
    ∃ m : ℤ, ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ) := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic ((g : L ≃* L).restrictRootsOfUnity n).toMonoidHom
  exact ⟨m, fun t ↦ Units.ext_iff.1 <| SetCoe.ext_iff.2 <| hm t⟩

theorem rootsOfUnity.integer_power_of_ringEquiv' (g : L ≃+* L) :
    ∃ m : ℤ, ∀ t ∈ rootsOfUnity n L, g (t : Lˣ) = (t ^ m : Lˣ) := by
  simpa using rootsOfUnity.integer_power_of_ringEquiv n g

-- DISSOLVED: ModularCyclotomicCharacter_aux

-- DISSOLVED: ModularCyclotomicCharacter_aux_spec

-- DISSOLVED: ModularCyclotomicCharacter.toFun

namespace ModularCyclotomicCharacter

local notation "χ₀" => ModularCyclotomicCharacter.toFun

-- DISSOLVED: toFun_spec

-- DISSOLVED: toFun_spec'

-- DISSOLVED: toFun_spec''

theorem toFun_unique (g : L ≃+* L) (c : ZMod (Fintype.card (rootsOfUnity n L)))
    (hc : ∀ t : rootsOfUnity n L, g (t : Lˣ) = (t ^ c.val : Lˣ)) : c = χ₀ n g := by
  apply IsCyclic.ext Nat.card_eq_fintype_card (fun ζ ↦ ?_)
  specialize hc ζ
  suffices ((ζ ^ c.val : Lˣ) : L) = (ζ ^ (χ₀ n g).val : Lˣ) by exact_mod_cast this
  rw [← toFun_spec g ζ, hc]

theorem toFun_unique' (g : L ≃+* L) (c : ZMod (Fintype.card (rootsOfUnity n L)))
    (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) : c = χ₀ n g :=
  toFun_unique n g c (fun ⟨_, ht⟩ ↦ hc _ ht)

lemma id : χ₀ n (RingEquiv.refl L) = 1 := by
  refine (toFun_unique n (RingEquiv.refl L) 1 <| fun t ↦ ?_).symm
  have : 1 ≤ Fintype.card { x // x ∈ rootsOfUnity n L } := Fin.size_positive'
  obtain (h | h) := this.lt_or_eq
  · have := Fact.mk h
    simp [ZMod.val_one]
  · have := Fintype.card_le_one_iff_subsingleton.mp h.ge
    obtain rfl : t = 1 := Subsingleton.elim t 1
    simp

lemma comp (g h : L ≃+* L) : χ₀ n (g * h) =
    χ₀ n g * χ₀ n h := by
  refine (toFun_unique n (g * h) _ <| fun ζ ↦ ?_).symm
  change g (h (ζ : Lˣ)) = _
  rw [toFun_spec, ← Subgroup.coe_pow, toFun_spec, mul_comm, Subgroup.coe_pow, ← pow_mul,
    ← Subgroup.coe_pow]
  congr 2
  norm_cast
  simp only [pow_eq_pow_iff_modEq, ← ZMod.natCast_eq_natCast_iff, SubmonoidClass.coe_pow,
    ZMod.natCast_val, Nat.cast_mul, ZMod.cast_mul (m := orderOf ζ) orderOf_dvd_card]

end ModularCyclotomicCharacter

variable (L)

noncomputable

-- DISSOLVED: ModularCyclotomicCharacter'

lemma spec' (g : L ≃+* L) {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ ((ModularCyclotomicCharacter' L n g) : ZMod
      (Fintype.card { x // x ∈ rootsOfUnity n L })).val :=
  ModularCyclotomicCharacter.toFun_spec' g ht

lemma unique' (g : L ≃+* L) {c : ZMod (Fintype.card { x // x ∈ rootsOfUnity n L })}
    (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) :
    c = ModularCyclotomicCharacter' L n g :=
  ModularCyclotomicCharacter.toFun_unique' _ _ _ hc

-- DISSOLVED: ModularCyclotomicCharacter

namespace ModularCyclotomicCharacter

variable {n : ℕ} [NeZero n] (hn : Fintype.card { x // x ∈ rootsOfUnity n L } = n)

lemma spec (g : L ≃+* L) {t : Lˣ} (ht : t ∈ rootsOfUnity n L) :
    g t = t ^ ((ModularCyclotomicCharacter L hn g) : ZMod n).val := by
  rw [toFun_spec' g ht]
  congr 1
  exact (ZMod.ringEquivCongr_val _ _).symm

lemma unique (g : L ≃+* L) {c : ZMod n} (hc : ∀ t ∈ rootsOfUnity n L, g t = t ^ c.val) :
    c = ModularCyclotomicCharacter L hn g := by
  change c = (ZMod.ringEquivCongr hn) (toFun n g)
  rw [← toFun_unique' n g (ZMod.ringEquivCongr hn.symm c)
    (fun t ht ↦ by rw [hc t ht, ZMod.ringEquivCongr_val]), ← ZMod.ringEquivCongr_symm hn,
    RingEquiv.apply_symm_apply]

end ModularCyclotomicCharacter

variable {L}

-- DISSOLVED: IsPrimitiveRoot.autToPow_eq_ModularCyclotomicCharacter
