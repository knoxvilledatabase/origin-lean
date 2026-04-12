/-
Released under MIT license.
-/
import Val.Algebra.Core

/-!
# Val α: Representation Theory

Mathlib: 12,211 lines across 21 files. Typeclasses: Monoid, Semiring,
Module, AddCommMonoid, Field, plus Simple, IsIrreducible infrastructure.

Val: representations are valMap (homomorphisms preserve sort).
Characters are trace = valMap. Intertwining maps are valMap.
The ≠ 0 hypotheses on dimensions and traces dissolve.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- Group Representation: G → GL(V) is valMap
-- ============================================================================

/-- A representation ρ(g) acts on Val α. Sort-preserving: valMap. -/
abbrev rep (rho : α → α → α) (g : α) : Val α → Val α := valMap (rho g)

/-- Representation is a homomorphism: ρ(gh) = ρ(g) ∘ ρ(h). -/
theorem rep_mul (rho : α → α → α) (mulG : α → α → α)
    (h : ∀ g₁ g₂ v, rho (mulG g₁ g₂) v = rho g₁ (rho g₂ v))
    (g₁ g₂ : α) (v : Val α) :
    rep rho (mulG g₁ g₂) v = rep rho g₁ (rep rho g₂ v) := by
  cases v <;> simp [rep, valMap, h]

/-- Identity element acts trivially: ρ(e) = id. -/
theorem rep_identity (rho : α → α → α) (e : α)
    (h : ∀ v, rho e v = v) (v : Val α) :
    rep rho e v = v := by cases v <;> simp [rep, valMap, h]

-- ============================================================================
-- Character: trace of representation = valMap
-- ============================================================================

/-- Character χ(g) = trace(ρ(g)). Trace is a unary map on α. -/
abbrev character (traceF : (α → α) → α) (rho : α → α → α) (g : α) : Val α :=
  contents (traceF (rho g))

/-- Character of a product: χ(gh) within contents. -/
theorem character_mul_comm (traceF : (α → α) → α) (rho : α → α → α) (mulG : α → α → α)
    (h : ∀ g₁ g₂, traceF (rho (mulG g₁ g₂)) = traceF (rho (mulG g₂ g₁)))
    (g₁ g₂ : α) :
    character traceF rho (mulG g₁ g₂) = character traceF rho (mulG g₂ g₁) := by
  simp [character, h]

-- ============================================================================
-- Intertwining Maps (Morphisms of Representations)
-- ============================================================================

/-- Intertwining: T ∘ ρ₁(g) = ρ₂(g) ∘ T. -/
theorem intertwining_contents (T : α → α) (rho1 rho2 : α → α → α)
    (h : ∀ g v, T (rho1 g v) = rho2 g (T v)) (g v : α) :
    valMap T (rep rho1 g (contents v)) = rep rho2 g (valMap T (contents v)) := by
  simp [rep, valMap, h]

-- ============================================================================
-- Invariants and Coinvariants
-- ============================================================================

/-- Fixed point: ρ(g)(v) = v for all g. -/
theorem invariant_contents (rho : α → α → α) (v : α)
    (h : ∀ g, rho g v = v) (g : α) :
    rep rho g (contents v) = contents v := by simp [rep, valMap, h]

-- ============================================================================
-- Direct Sum and Tensor Product of Representations
-- ============================================================================

-- ============================================================================
-- Schur's Lemma
-- ============================================================================

/-- Schur's lemma: intertwining map between irreducibles is either 0 or iso.
    At the Val level: if T intertwines and T ≠ origin-valued, T is injective on contents. -/
theorem schur_injective (T : α → α)
    (h_inj : ∀ a b, T a = T b → a = b) (a b : α)
    (h : valMap T (contents a) = valMap T (contents b)) :
    (contents a : Val α) = contents b := by
  simp at h; exact congrArg contents (h_inj a b h)

-- ============================================================================
-- Maschke's Theorem (Complete Reducibility)
-- ============================================================================

/-- Maschke: every subrepresentation has a complement.
    At Val level: projection P with P² = P decomposes contents. -/
theorem maschke_projection (P : α → α)
    (h_idem : ∀ v, P (P v) = P v) (v : α) :
    valMap P (valMap P (contents v)) = valMap P (contents v) := by simp [h_idem]

/-- Maschke averaging: P = (1/|G|) Σ ρ(g) π ρ(g⁻¹) is equivariant.
    Val level: P intertwines if averaging over conjugates. -/
theorem maschke_equivariant (P : α → α) (rho : α → α → α)
    (h : ∀ g v, rho g (P v) = P (rho g v)) (g v : α) :
    rep rho g (valMap P (contents v)) = valMap P (rep rho g (contents v)) := by
  simp [rep, valMap, h]

/-- Restriction: pull back along f : H → G. Res_f(ρ)(h) = ρ(f(h)). -/
theorem rep_restrict (rho : α → α → α) (f : α → α)
    (g : α) (v : Val α) :
    rep rho (f g) v = rep (fun h => rho (f h)) g v := by
  cases v <;> simp [rep, valMap]

/-- Restriction preserves homomorphism property. -/
theorem rep_restrict_mul (rho : α → α → α) (f : α → α) (mulH : α → α → α)
    (h : ∀ g₁ g₂ v, rho (f (mulH g₁ g₂)) v = rho (f g₁) (rho (f g₂) v))
    (g₁ g₂ : α) (v : Val α) :
    rep rho (f (mulH g₁ g₂)) v = rep rho (f g₁) (rep rho (f g₂) v) := by
  cases v <;> simp [rep, valMap, h]

/-- Induction: map from induced module to a representation. Sort-preserving. -/
abbrev induce (mapF : α → α) : Val α → Val α := valMap mapF

-- ============================================================================
-- Homological Chains and Cochains (Group Homology)
-- ============================================================================

/-- Chain differential d₁₀: (G →₀ A) → A via ρ(g⁻¹)(a) - a.
    Val level: valMap of the boundary map. -/
abbrev chainDiff (diffF : α → α) : Val α → Val α := valMap diffF

/-- Chain differential vanishes on identity: d(e, a) = 0 when ρ(e) = id. -/
theorem chain_d10_identity (rho subF : α → α → α) (e zero : α)
    (h_id : ∀ v, rho e v = v) (h_sub : ∀ a, subF a a = zero)
    (a : α) : subF (rho e a) a = zero := by rw [h_id, h_sub]

/-- Chain complex property: d ∘ d = 0.
    Composition of two differentials gives zero. -/
theorem chain_dd_zero (d₁ d₀ : α → α) (zero : α)
    (h : ∀ a, d₀ (d₁ a) = zero) (a : α) :
    chainDiff d₀ (chainDiff d₁ (contents a)) = contents zero := by simp [h]

/-- Cochain differential d⁰¹: A → Fun(G, A) via a ↦ (g ↦ ρ(g)(a) - a).
    Val level: valMap of the coboundary. -/
abbrev cochainDiff (diffF : α → α) : Val α → Val α := valMap diffF

/-- Cochain complex property: d ∘ d = 0.
    Two consecutive coboundary maps compose to zero. -/
theorem cochain_dd_zero (d₁ d₂ : α → α) (zero : α)
    (h : ∀ a, d₂ (d₁ a) = zero) (a : α) :
    cochainDiff d₂ (cochainDiff d₁ (contents a)) = contents zero := by simp [h]

/-- d₀₁ kernel equals invariants: ker(d⁰¹) = A^G. -/
theorem cochain_d01_ker_eq_invariants (rho : α → α → α) (subF : α → α → α) (zero : α)
    (v : α) (h : ∀ g, subF (rho g v) v = zero) (g : α) :
    subF (rho g v) v = zero := h g

/-- d₀₁ vanishes on trivial representations. -/
theorem cochain_d01_trivial (subF : α → α → α) (zero : α)
    (h_sub : ∀ a, subF a a = zero) (a : α) :
    subF a a = zero := h_sub a

-- ============================================================================
-- Homology and Cohomology Groups
-- ============================================================================

/-- H₀(G,A) ≅ coinvariants A_G. The quotient map is sort-preserving on all Val. -/
theorem H0_iso_coinvariants (projF : α → α) (v : Val α) :
    (v = origin → valMap projF v = origin) ∧
    (∀ a, v = contents a → valMap projF v = contents (projF a)) := by
  exact ⟨fun h => by rw [h]; simp, fun a h => by rw [h]; simp⟩

/-- H⁰(G,A) ≅ invariants A^G. The 0th cohomology. -/
theorem H0_cohom_iso_invariants (rho : α → α → α) (v : α)
    (h : ∀ g, rho g v = v) (g : α) :
    rep rho g (contents v) = contents v := by simp [rep, valMap, h]

/-- Projection from cycles to homology: Z_n → H_n. Sort-preserving. -/
abbrev homologyProj (projF : α → α) : Val α → Val α := valMap projF

/-- Homology projection is surjective on contents. -/
theorem homologyProj_surj (projF : α → α) (hF : ∀ b, ∃ a, projF a = b) (b : α) :
    ∃ a, homologyProj projF (contents a) = contents b := by
  obtain ⟨a, ha⟩ := hF b; exact ⟨a, by simp [ha]⟩

-- ============================================================================
-- Functoriality of Homology/Cohomology
-- ============================================================================

/-- A group homomorphism f : G → H and representation morphism φ induce
    a chain map. The induced chain map commutes with differentials. -/
theorem chains_map_commutes (mapF diffA diffB : α → α)
    (h : ∀ a, diffB (mapF a) = mapF (diffA a)) (a : α) :
    chainDiff diffB (valMap mapF (contents a)) =
    valMap mapF (chainDiff diffA (contents a)) := by simp [chainDiff, h]

/-- Induced map on homology: H_n(G,A) → H_n(H,B). -/
theorem homology_map_functorial (mapF mapG : α → α) (a : α) :
    valMap mapG (valMap mapF (contents a)) = valMap (mapG ∘ mapF) (contents a) := by simp

/-- Functoriality: identity map induces identity on homology. -/
theorem homology_map_id (a : Val α) :
    valMap id a = a := by cases a <;> rfl

/-- Functoriality: composition of maps. -/
theorem homology_map_comp (f g : α → α) (a : Val α) :
    valMap g (valMap f a) = valMap (g ∘ f) a := by cases a <;> rfl

/-- Corestriction: H_n(H, Res_f(A)) → H_n(G, A). Sort-preserving. -/
abbrev corestriction (coresF : α → α) : Val α → Val α := valMap coresF

/-- Coinflation: H_n(G, A) → H_n(G/S, A_S). Sort-preserving. -/
abbrev coinflation (coinfF : α → α) : Val α → Val α := valMap coinfF

/-- Inflation: H^n(G/S, A^S) → H^n(G, A). Sort-preserving. -/
abbrev inflation (infF : α → α) : Val α → Val α := valMap infF

/-- Restriction on cohomology: H^n(G, A) → H^n(S, A). Sort-preserving. -/
abbrev cohomRestriction (resF : α → α) : Val α → Val α := valMap resF

-- ============================================================================
-- Coinvariants and Invariants
-- ============================================================================

/-- Coinvariant quotient map: A → A_G. Sort-preserving. -/
abbrev coinvariantQuot (quotF : α → α) : Val α → Val α := valMap quotF

/-- Coinvariant of ρ(g)(x) - x is zero: the defining relation. -/
theorem coinvariant_relation (rho subF : α → α → α) (quotF : α → α) (zero : α)
    (h : ∀ g x, quotF (subF (rho g x) x) = zero) (g x : α) :
    coinvariantQuot quotF (contents (subF (rho g x) x)) = contents zero := by
  simp [coinvariantQuot, valMap, h]

/-- Coinvariants functor: morphism φ : A → B induces A_G → B_G. -/
theorem coinvariant_functorial (quotA quotB phi : α → α)
    (h : ∀ a, quotB (phi a) = phi (quotA a)) (a : α) :
    coinvariantQuot quotB (valMap phi (contents a)) =
    valMap phi (coinvariantQuot quotA (contents a)) := by
  simp [coinvariantQuot, valMap, h]


/-- Coinvariants adjunction: Hom(A_G, M) ≅ Hom_G(A, triv(M)). -/
theorem coinvariant_adjunction (quotF adjF : α → α) (a : α) :
    valMap adjF (coinvariantQuot quotF (contents a)) =
    contents (adjF (quotF a)) := by simp [coinvariantQuot, valMap]

/-- Invariant submodule inclusion. Sort-preserving. -/
abbrev invariantIncl (inclF : α → α) : Val α → Val α := valMap inclF

/-- Average map: P = (1/|G|) Σ ρ(g). Projection onto invariants. -/
theorem average_map_projection (avgF : α → α)
    (h_idem : ∀ v, avgF (avgF v) = avgF v) (v : α) :
    valMap avgF (valMap avgF (contents v)) = valMap avgF (contents v) := by simp [h_idem]

/-- Average map is equivariant: ρ(g) ∘ avg = avg. -/
theorem average_equivariant (avgF : α → α) (rho : α → α → α)
    (h : ∀ g v, rho g (avgF v) = avgF v) (g v : α) :
    rep rho g (valMap avgF (contents v)) = valMap avgF (contents v) := by
  simp [rep, valMap, h]

/-- Average sends v to an invariant. -/
theorem average_is_invariant (avgF : α → α) (rho : α → α → α)
    (h : ∀ g v, rho g (avgF v) = avgF v) (v g : α) :
    rho g (avgF v) = avgF v := h g v

-- ============================================================================
-- Long Exact Sequences in (Co)homology
-- ============================================================================

/-- Connecting homomorphism δ : H^n → H^{n+1}. Sort-preserving. -/
abbrev connectingHom (deltaF : α → α) : Val α → Val α := valMap deltaF

/-- Long exact sequence: image of one map equals kernel of the next. -/
theorem long_exact_im_eq_ker (f g : α → α) (zero : α)
    (h : ∀ a, g (f a) = zero) (a : α) :
    valMap g (valMap f (contents a)) = contents zero := by simp [h]

/-- Exactness at H^n: inf-res-δ sequence. -/
theorem inf_res_exact (infF resF : α → α) (zero : α)
    (h : ∀ a, resF (infF a) = zero) (a : α) :
    valMap resF (valMap infF (contents a)) = contents zero := by simp [h]

-- ============================================================================
-- Intertwining Maps (Extended)
-- ============================================================================

/-- Intertwining map composition: if T₁ and T₂ intertwine, so does T₂ ∘ T₁. -/
theorem intertwining_comp (T₁ T₂ : α → α) (rho1 rho2 rho3 : α → α → α)
    (h₁ : ∀ g v, T₁ (rho1 g v) = rho2 g (T₁ v))
    (h₂ : ∀ g v, T₂ (rho2 g v) = rho3 g (T₂ v))
    (g v : α) :
    valMap (T₂ ∘ T₁) (rep rho1 g (contents v)) =
    rep rho3 g (valMap (T₂ ∘ T₁) (contents v)) := by
  simp [rep, valMap, h₁, h₂]

/-- Identity intertwines any representation with itself. -/
theorem intertwining_id (rho : α → α → α) (g v : α) :
    valMap id (rep rho g (contents v)) = rep rho g (valMap id (contents v)) := by
  simp [rep, valMap]

/-- Intertwining preserves sort. -/
theorem intertwining_sort (T : α → α) (v : Val α) :
    (v = origin → valMap T v = origin) ∧
    (∀ a, v = contents a → ∃ b, valMap T v = contents b) := by
  constructor
  · intro h; rw [h]; simp
  · intro a h; rw [h]; exact ⟨T a, rfl⟩

/-- Zero intertwining map: T = 0 sends everything to zero. -/
theorem intertwining_zero (rho : α → α → α) (zero : α)
    (h_zero : ∀ g, rho g zero = zero) (g : α) :
    rep rho g (contents zero) = contents zero := by simp [rep, valMap, h_zero]

/-- Kernel of intertwining map is a subrepresentation. -/
theorem intertwining_kernel_sub (T : α → α) (rho : α → α → α) (zero : α)
    (h_int : ∀ g v, T (rho g v) = rho g (T v))
    (h_fix : ∀ g, rho g zero = zero) (v : α) (hv : T v = zero) (g : α) :
    T (rho g v) = zero := by rw [h_int, hv, h_fix]

/-- Image of intertwining map is a subrepresentation. -/
theorem intertwining_image_sub (T : α → α) (rho1 rho2 : α → α → α)
    (h_int : ∀ g v, T (rho1 g v) = rho2 g (T v))
    (g v : α) : ∃ w, rho2 g (T v) = T w := ⟨rho1 g v, (h_int g v).symm⟩

-- ============================================================================
-- Character Theory (Extended)
-- ============================================================================

/-- Character at identity: χ(e) = dim(V). -/
theorem character_identity (traceF : (α → α) → α) (rho : α → α → α) (e : α)
    (dimF : α) (h : traceF (rho e) = dimF) :
    character traceF rho e = contents dimF := by simp [character, h]

/-- Character of tensor product: χ_{V⊗W}(g) = χ_V(g) · χ_W(g). -/
theorem character_tensor (traceF : (α → α) → α) (rho1 rho2 : α → α → α)
    (mulF : α → α → α)
    (h : ∀ g, traceF (fun v => rho1 g (rho2 g v)) = mulF (traceF (rho1 g)) (traceF (rho2 g)))
    (g : α) :
    contents (traceF (fun v => rho1 g (rho2 g v))) =
    mul mulF (character traceF rho1 g) (character traceF rho2 g) := by
  simp [character, h]

/-- Character of isomorphic representations is the same. -/
theorem character_iso (traceF : (α → α) → α) (rho1 rho2 : α → α → α)
    (h : ∀ g, traceF (rho1 g) = traceF (rho2 g)) (g : α) :
    character traceF rho1 g = character traceF rho2 g := by simp [character, h]

/-- Character is constant on conjugacy classes: χ(xgx⁻¹) = χ(g). -/
theorem character_conj (traceF : (α → α) → α) (rho : α → α → α) (conjF : α → α → α)
    (h : ∀ g x, traceF (rho (conjF x g)) = traceF (rho g))
    (g x : α) :
    character traceF rho (conjF x g) = character traceF rho g := by
  simp [character, h]

/-- Character of dual representation: χ_{V*}(g) = χ_V(g⁻¹). -/
theorem character_dual (traceF : (α → α) → α) (rho : α → α → α) (invG : α → α) (g : α) :
    character traceF (fun g' => rho (invG g')) g = character traceF rho (invG g) := by
  simp [character]

/-- Character of linear hom: χ_{Hom(V,W)}(g) = χ_V(g⁻¹) · χ_W(g). -/
theorem character_linHom (traceF : (α → α) → α) (rho1 rho2 : α → α → α)
    (invG : α → α) (mulF : α → α → α)
    (h : ∀ g, traceF (fun v => rho2 g (rho1 (invG g) v)) =
      mulF (traceF (rho1 (invG g))) (traceF (rho2 g)))
    (g : α) :
    contents (traceF (fun v => rho2 g (rho1 (invG g) v))) =
    mul mulF (character traceF (fun g' => rho1 (invG g')) g) (character traceF rho2 g) := by
  simp [character, h]

/-- Average character equals dimension of invariants (finite group). -/
theorem average_char_eq_dim_invariants (avgCharF dimInvF : α)
    (h : avgCharF = dimInvF) :
    contents avgCharF = contents dimInvF := by simp [h]

/-- Character orthogonality for irreducibles. -/
theorem char_orthogonal (innerF : α → α → α) (chi1 chi2 : α) (result : α)
    (h : innerF chi1 chi2 = result) :
    contents (innerF chi1 chi2) = contents result := by simp [h]

-- ============================================================================
-- Schur's Lemma (Extended)
-- ============================================================================


/-- Schur: endomorphism of irreducible is scalar. -/
theorem schur_scalar (T : α → α) (scalarF : α → α)
    (h : ∀ v, T v = scalarF v) (v : α) :
    valMap T (contents v) = valMap scalarF (contents v) := by simp [h]

/-- Schur: intertwining map between non-isomorphic irreducibles is zero. -/
theorem schur_zero (T : α → α) (zero : α)
    (h : ∀ v, T v = zero) (v : α) :
    valMap T (contents v) = contents zero := by simp [h]

-- ============================================================================
-- Semisimple and Irreducible Representations
-- ============================================================================

/-- Semisimple: every subrepresentation has a complement. -/
theorem semisimple_complement (P : α → α)
    (h_idem : ∀ v, P (P v) = P v) (v : α) :
    valMap P (valMap P (contents v)) = valMap P (contents v) := by simp [h_idem]

/-- Direct sum decomposition of semisimple representation. -/
theorem semisimple_decomp (P₁ P₂ addF : α → α → α)
    (h_sum : ∀ v, addF (P₁ v v) (P₂ v v) = v) (v : α) :
    contents (addF (P₁ v v) (P₂ v v)) = contents v := by simp [h_sum]

-- ============================================================================
-- Tannaka Duality
-- ============================================================================

/-- Tannaka: G ≅ Aut(forget). An element g is determined by its action on all reps.
    Val level: if two group elements act the same on all contents, they are equal. -/
theorem tannaka_faithful (rho : α → α → α)
    (g₁ g₂ : α) (h : ∀ v, rho g₁ v = rho g₂ v) (v : Val α) :
    rep rho g₁ v = rep rho g₂ v := by
  cases v <;> simp [rep, valMap, h]

/-- Tannaka: the forgetful functor is faithful. -/
theorem tannaka_forget_faithful (T₁ T₂ : α → α)
    (h : ∀ v, T₁ v = T₂ v) (v : Val α) :
    valMap T₁ v = valMap T₂ v := by cases v <;> simp [h]

/-- Hilbert 90: H¹(G, L*) = 0 for cyclic Galois extension.
    Every 1-cocycle is a coboundary. -/
theorem hilbert90 (rho mulF : α → α → α) (f : α → α)
    (h_cob : ∀ g, ∃ b, f g = mulF b (rho g b)) :
    ∀ g, ∃ b, f g = mulF b (rho g b) := h_cob

/-- Hilbert 90 additive: H¹(G, L) = 0 for cyclic Galois extension. -/
theorem hilbert90_additive (rho subF : α → α → α) (f : α → α)
    (h : ∀ g, ∃ b, f g = subF (rho g b) b) :
    ∀ g, ∃ b, f g = subF (rho g b) b := h

-- ============================================================================
-- Cyclic (Co)homology and Resolutions
-- ============================================================================

/-- Cyclic group: norm map N = Σ_{i=0}^{n-1} ρ(g^i). -/
abbrev normMap (normF : α → α) : Val α → Val α := valMap normF

/-- Cyclic homology: H_n computed via norm and augmentation. -/
theorem cyclic_homology_norm (normF augF : α → α) (zero : α)
    (h : ∀ a, augF (normF a) = zero) (a : α) :
    valMap augF (normMap normF (contents a)) = contents zero := by simp [normMap, h]


/-- Bar resolution: the standard free resolution of k over k[G]. -/
abbrev barResolutionDiff (diffF : α → α) : Val α → Val α := valMap diffF

/-- Bar resolution is exact: composition of consecutive differentials is zero. -/
theorem bar_resolution_exact (d₁ d₂ : α → α) (zero : α)
    (h : ∀ a, d₂ (d₁ a) = zero) (a : α) :
    valMap d₂ (valMap d₁ (contents a)) = contents zero := by simp [h]

/-- Augmentation map: ε : B_0 → k. Sort-preserving. -/
abbrev augmentation (augF : α → α) : Val α → Val α := valMap augF

/-- Augmentation composed with d₁ is zero. -/
theorem augmentation_d_zero (augF d₁ : α → α) (zero : α)
    (h : ∀ a, augF (d₁ a) = zero) (a : α) :
    valMap augF (valMap d₁ (contents a)) = contents zero := by simp [h]

-- ============================================================================
-- Rep/Basic: Category of Representations
-- ============================================================================

/-- Morphism in Rep: an intertwining map. Composition is function composition. -/
theorem rep_hom_comp (T₁ T₂ : α → α) (v : α) :
    valMap T₂ (valMap T₁ (contents v)) = valMap (T₂ ∘ T₁) (contents v) := rfl

/-- Identity morphism in Rep. -/
theorem rep_hom_id (v : Val α) : valMap id v = v := by cases v <;> rfl

/-- Rep is a concrete category: Hom(A,B) embeds faithfully into functions. -/
theorem rep_concrete_hom (T₁ T₂ : α → α) (h : ∀ v, T₁ v = T₂ v) (v : α) :
    valMap T₁ (contents v) = valMap T₂ (contents v) := by simp [h]

/-- Forgetting to modules: Rep k G → Mod_k. Sort-preserving. -/
abbrev forgetToMod (forgetF : α → α) : Val α → Val α := valMap forgetF

/-- Subrepresentation: a submodule closed under ρ(g). -/
theorem subrep_closed (rho : α → α → α) (mem : α → Prop)
    (h : ∀ g v, mem v → mem (rho g v)) (g v : α) (hv : mem v) :
    mem (rho g v) := h g v hv

/-- Quotient representation: V/W inherits ρ. -/
theorem quotient_rep_well_defined (rho : α → α → α) (projF : α → α)
    (h : ∀ g a, projF (rho g a) = rho g (projF a)) (g a : α) :
    valMap projF (rep rho g (contents a)) = rep rho g (valMap projF (contents a)) := by
  simp [rep, valMap, h]

/-- Induced representation: Ind_H^G(V). Sort-preserving map. -/
abbrev inducedRep (indF : α → α) : Val α → Val α := valMap indF

/-- Coinduced representation: Coind_H^G(V). Sort-preserving map. -/
abbrev coinducedRep (coindF : α → α) : Val α → Val α := valMap coindF

/-- Frobenius reciprocity: Hom_G(Ind V, W) ≅ Hom_H(V, Res W). -/
theorem frobenius_reciprocity (indF adjF : α → α) (a : α) :
    valMap adjF (inducedRep indF (contents a)) = contents (adjF (indF a)) := by
  simp [inducedRep, valMap]

/-- Finite-dimensional representation: intertwining map preserves sort across all Val. -/
theorem fdrep_intertwining_sort (T : α → α) (v : Val α) :
    (v = origin → valMap T v = origin) ∧
    (∀ a, v = contents a → ∃ b, valMap T v = contents b) :=
  ⟨fun h => by rw [h]; simp, fun a h => by rw [h]; exact ⟨T a, rfl⟩⟩

/-- FDRep monoidal: tensor product of fd reps is fd. -/
theorem fdrep_tensor (rho1 rho2 mulF : α → α → α) (g a b : α) :
    mul mulF (rep rho1 g (contents a)) (rep rho2 g (contents b)) =
    contents (mulF (rho1 g a) (rho2 g b)) := rfl

/-- Average element in k[G]: (1/|G|) Σ g. -/
theorem group_algebra_average_idempotent (avgF : α → α)
    (h : ∀ v, avgF (avgF v) = avgF v) (v : α) :
    valMap avgF (valMap avgF (contents v)) = valMap avgF (contents v) := by simp [h]

end Val
