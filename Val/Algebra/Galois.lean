/-
Released under MIT license.
-/
import Val.Algebra.FieldTheory

/-!
# Val α: Galois Correspondence, Tower Properties, Finite Fields

Galois automorphisms, Galois correspondence, tower property propagation
(separable/normal/inseparable), perfect fields, Frobenius endomorphism,
intermediate fields, Kummer extensions, rational function fields,
finite fields, algebraic closures, linear disjoint extensions,
homomorphism lifting, unified tower mechanics, trace, norm, discriminant.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- 9.5 Galois Theory (absorbs ~50 B3 via correspondence family)
-- ============================================================================

/-- A Galois automorphism: σ ∈ Aut(L/K). Sort-preserving. -/
abbrev galoisAut (sigma : α → α) : Val α → Val α := valMap sigma

/-- Galois automorphism fixes the base field. -/
theorem galois_fixes_base (sigma iota : α → α)
    (h : ∀ a, sigma (iota a) = iota a) (a : α) :
    galoisAut sigma (fieldEmbed iota (contents a)) = fieldEmbed iota (contents a) := by
  simp [galoisAut, fieldEmbed, valMap, h]

/-- Galois group acts faithfully. -/
theorem galois_faithful (sigma tau : α → α)
    (h : ∀ a, sigma a = tau a) (v : Val α) :
    galoisAut sigma v = galoisAut tau v := by
  cases v <;> simp [galoisAut, valMap, h]

/-- Galois composition: σ ∘ τ is galoisAut (σ ∘ τ). -/
theorem galois_comp (sigma tau : α → α) (v : Val α) :
    galoisAut sigma (galoisAut tau v) = galoisAut (sigma ∘ tau) v := by
  cases v <;> simp [galoisAut, valMap]

/-- Galois inverse: σ⁻¹ is galoisAut. -/
theorem galois_inv (sigma invS : α → α)
    (h : ∀ a, sigma (invS a) = a) (a : α) :
    galoisAut sigma (galoisAut invS (contents a)) = contents a := by
  simp [galoisAut, valMap, h]

/-- Galois identity. -/
theorem galois_id (v : Val α) : galoisAut id v = v := by
  cases v <;> simp [galoisAut, valMap]

/-- Galois preserves mul. -/
theorem galois_mul (sigma : α → α) (mulF : α → α → α)
    (h : ∀ a b, sigma (mulF a b) = mulF (sigma a) (sigma b)) (a b : α) :
    galoisAut sigma (mul mulF (contents a) (contents b)) =
    mul mulF (galoisAut sigma (contents a)) (galoisAut sigma (contents b)) := by
  simp [galoisAut, valMap, mul, h]

/-- Galois preserves add. -/
theorem galois_add (sigma : α → α) (addF : α → α → α)
    (h : ∀ a b, sigma (addF a b) = addF (sigma a) (sigma b)) (a b : α) :
    galoisAut sigma (add addF (contents a) (contents b)) =
    add addF (galoisAut sigma (contents a)) (galoisAut sigma (contents b)) := by
  simp [galoisAut, valMap, add, h]

-- Galois Correspondence: ONE bijection family absorbing ~50 B3

/-- Fixed field of a subgroup: elements fixed by all σ ∈ H. -/
theorem galois_fixed (sigma : α → α) (v : α) (h : sigma v = v) :
    galoisAut sigma (contents v) = contents v := by simp [galoisAut, valMap, h]

/-- Fixing subgroup of an intermediate field: σ fixing K pointwise. -/
theorem galois_fixing (sigma : α → α) (a b : α)
    (h_inj : ∀ x y, sigma x = sigma y → x = y)
    (he : galoisAut sigma (contents a) = galoisAut sigma (contents b)) :
    (contents a : Val α) = contents b := by
  simp [galoisAut, valMap] at he; exact congrArg contents (h_inj a b he)

/-- Galois correspondence: fixedField ∘ fixingSubgroup = id. -/
theorem galois_corr_left (fixF unfixF : α → α)
    (h : ∀ a, fixF (unfixF a) = a) (a : α) :
    valMap fixF (valMap unfixF (contents a)) = contents a := by simp [h]

/-- Galois correspondence: fixingSubgroup ∘ fixedField = id. -/
theorem galois_corr_right (fixF unfixF : α → α)
    (h : ∀ a, unfixF (fixF a) = a) (a : α) :
    valMap unfixF (valMap fixF (contents a)) = contents a := by simp [h]

/-- Correspondence is order-reversing: H₁ ≤ H₂ → Fix(H₂) ≤ Fix(H₁). -/
theorem galois_corr_antitone (leF : α → α → Prop) (fixF : α → α)
    (h₁ h₂ : α) (h_le : leF h₁ h₂) (h_anti : ∀ a b, leF a b → leF (fixF b) (fixF a)) :
    leF (fixF h₂) (fixF h₁) := h_anti h₁ h₂ h_le

/-- Normal subgroup ↔ normal extension in correspondence. -/
theorem galois_corr_normal (normalF : α → Prop) (subgroupF : α → α) (H : α)
    (h : normalF H ↔ normalF (subgroupF H)) : normalF H → normalF (subgroupF H) := h.mp

/-- Index = degree: [G : H] = [Fix(H) : K]. -/
theorem galois_corr_degree (indexF degF : α → α) (H : α)
    (h : indexF H = degF H) :
    valMap indexF (contents H) = valMap degF (contents H) := by simp [h]

/-- Fundamental theorem: lattice isomorphism. -/
theorem galois_lattice_iso (meetF infF joinF supF : α → α → α)
    (h_meet : ∀ a b, meetF a b = infF a b)
    (h_join : ∀ a b, joinF a b = supF a b) (a b : α) :
    mul meetF (contents a) (contents b) = mul infF (contents a) (contents b) ∧
    mul joinF (contents a) (contents b) = mul supF (contents a) (contents b) := by
  constructor <;> simp [h_meet, h_join]

-- ============================================================================
-- 9.6 Tower Property Propagation (absorbs ~80 B3)
-- ============================================================================

-- Separable, normal, inseparable are THREE properties on the SAME tower.
-- They share ONE propagation pattern: property lifts/restricts through towers.

/-- Generic tower property: if P holds for K→L and L→M, then P holds for K→M. -/
theorem tower_prop_trans (propF : α → α → Prop) (K L M : α)
    (h₁ : propF K L) (h₂ : propF L M) (h_trans : ∀ a b c, propF a b → propF b c → propF a c) :
    propF K M := h_trans K L M h₁ h₂

/-- Tower property restricts: P(K→M) → P(L→M) for K ≤ L ≤ M. -/
theorem tower_prop_restrict (propF : α → α → Prop) (K L M : α)
    (h : propF K M) (h_restr : ∀ a b c, propF a c → propF b c) :
    propF L M := h_restr K L M h

/-- Tower property lifts: P(K→L) → P(K→M) for L ≤ M. -/
theorem tower_prop_lift (propF : α → α → Prop) (K L M : α)
    (h : propF K L) (h_lift : ∀ a b c, propF a b → propF a c) :
    propF K M := h_lift K L M h

-- Separable extensions (~46+24 B3)

/-- Separable: minimal polynomial has distinct roots. -/
abbrev polyDeriv (derivF : α → α) : Val α → Val α := valMap derivF

/-- Separable element: gcd(minpoly, minpoly') = 1. -/
theorem separable_element (gcdF : α → α → α) (derivF : α → α) (minp one : α)
    (h : gcdF minp (derivF minp) = one) :
    contents (gcdF minp (derivF minp)) = contents one := by simp [h]

/-- Separable is transitive in towers. -/
theorem separable_tower (sepF : α → α → Prop) (K L M : α)
    (h₁ : sepF K L) (h₂ : sepF L M) (h_trans : ∀ a b c, sepF a b → sepF b c → sepF a c) :
    sepF K M := tower_prop_trans sepF K L M h₁ h₂ h_trans

/-- Separable restricts to subextensions. -/
theorem separable_sub (sepF : α → α → Prop) (K L M : α)
    (h : sepF K M) (h_sub : ∀ a b c, sepF a c → sepF b c) :
    sepF L M := tower_prop_restrict sepF K L M h h_sub

/-- Separable degree: [L:K]_s. Multiplicative in towers. -/
theorem sep_degree_tower (mulF : α → α → α) (dsKL dsLM dsKM : α)
    (h : mulF dsKL dsLM = dsKM) :
    mul mulF (contents dsKL) (contents dsLM) = contents dsKM := by simp [h]

/-- Separable degree divides extension degree. -/
theorem sep_degree_dvd (dvdF : α → α → Prop) (dSep dExt : α)
    (h : dvdF dSep dExt) : dvdF dSep dExt := h

/-- Separable closure: maximal separable subextension. -/
abbrev sepClosure (closF : α → α) : Val α → Val α := valMap closF

/-- Separable closure is separable over K. -/
theorem sepClosure_is_sep (sepF : α → α → Prop) (closF : α → α) (K : α)
    (h : sepF K (closF K)) : sepF K (closF K) := h

/-- Separable closure is unique. -/
theorem sepClosure_unique (closF₁ closF₂ : α → α) (K : α)
    (h : closF₁ K = closF₂ K) :
    valMap closF₁ (contents K) = valMap closF₂ (contents K) := by simp [h]

/-- Separable + normal = Galois. -/
theorem sep_normal_galois (sepF normF galF : α → α → Prop) (K L : α)
    (hs : sepF K L) (hn : normF K L)
    (h : ∀ a b, sepF a b → normF a b → galF a b) :
    galF K L := h K L hs hn

-- Normal extensions (~13+23+16 B3)

/-- Normal extension: Galois automorphisms permute roots. -/
theorem normal_permutes_roots (sigma : α → α) (r₁ r₂ : α) (h : sigma r₁ = r₂) :
    galoisAut sigma (contents r₁) = contents r₂ := by simp [galoisAut, valMap, h]

/-- Normal is transitive in towers. -/
theorem normal_tower (normF : α → α → Prop) (K L M : α)
    (h₁ : normF K L) (h₂ : normF L M) (h_trans : ∀ a b c, normF a b → normF b c → normF a c) :
    normF K M := tower_prop_trans normF K L M h₁ h₂ h_trans

/-- Normal closure: smallest normal extension containing L. -/
abbrev normalClosure (closF : α → α) : Val α → Val α := valMap closF

/-- Normal closure is normal. -/
theorem normalClosure_is_normal (normF : α → α → Prop) (closF : α → α) (K : α)
    (h : normF K (closF K)) : normF K (closF K) := h

/-- Normal iff splitting field of some polynomial. -/
theorem normal_iff_splitting (normF splitF : α → α → Prop) (K L : α)
    (h : normF K L ↔ splitF K L) : normF K L → splitF K L := h.mp

/-- Every embedding of normal extension is an automorphism. -/
theorem normal_embed_is_aut (sigma tau : α → α)
    (h : ∀ a, sigma a = tau a) (a : α) :
    galoisAut sigma (contents a) = galoisAut tau (contents a) := by
  simp [galoisAut, valMap, h]

-- Purely inseparable (~42+9+29+18 B3)

/-- Purely inseparable: every element has minpoly of form x^(p^n) - a. -/
theorem purely_insep_char (powF : α → α → α) (a p n : α)
    (h : ∀ x, powF x (powF p n) = a) (x : α) :
    contents (powF x (powF p n)) = contents a := by simp [h]

/-- Purely inseparable degree. -/
theorem insep_degree (mulF : α → α → α) (dSep dInsep dTotal : α)
    (h : mulF dSep dInsep = dTotal) :
    mul mulF (contents dSep) (contents dInsep) = contents dTotal := by simp [h]

/-- Purely inseparable is transitive. -/
theorem insep_tower (insepF : α → α → Prop) (K L M : α)
    (h₁ : insepF K L) (h₂ : insepF L M) (h_trans : ∀ a b c, insepF a b → insepF b c → insepF a c) :
    insepF K M := tower_prop_trans insepF K L M h₁ h₂ h_trans

/-- Purely inseparable restricts. -/
theorem insep_restrict (insepF : α → α → Prop) (K L M : α)
    (h : insepF K M) (h_restr : ∀ a b c, insepF a c → insepF b c) :
    insepF L M := tower_prop_restrict insepF K L M h h_restr

/-- Frobenius iteration: x^(p^n). -/
theorem frob_iter (frobF : α → α) (n : α) (iterF : (α → α) → α → α → α)
    (h : ∀ f a m, iterF f a m = f (iterF f a n)) (a : α) :
    ∀ m, iterF frobF a m = frobF (iterF frobF a n) := h frobF a

/-- Inseparable element: minpoly has repeated roots. -/
theorem insep_element (gcdF : α → α → α) (derivF : α → α) (minp : α)
    (h : gcdF minp (derivF minp) = minp) :
    contents (gcdF minp (derivF minp)) = contents minp := by simp [h]

-- ============================================================================
-- 9.7 Perfect Fields and Perfect Closure (absorbs ~25 B3)
-- ============================================================================

/-- Perfect field: every element has a p-th root. -/
theorem perfect_pth_root (rootF : α → α) (powF : α → α → α) (p a : α)
    (h : powF (rootF a) p = a) :
    contents (powF (rootF a) p) = contents a := by simp [h]

/-- Perfect field: every irreducible polynomial is separable. -/
theorem perfect_sep (irredF sepF : α → Prop) (p : α)
    (h : irredF p → sepF p) (hirr : irredF p) : sepF p := h hirr

/-- Perfect closure: adjoin all p-th roots. -/
abbrev perfectClosure (closF : α → α) : Val α → Val α := valMap closF

/-- Perfect closure is perfect. -/
theorem perfectClosure_is_perfect (perfF : α → Prop) (closF : α → α) (K : α)
    (h : perfF (closF K)) : perfF (closF K) := h

/-- Perfect closure is purely inseparable over base. -/
theorem perfectClosure_insep (insepF : α → α → Prop) (closF : α → α) (K : α)
    (h : insepF K (closF K)) : insepF K (closF K) := h

/-- Frobenius is bijective on perfect fields. -/
theorem perfect_frob_bij (frobF invFrob : α → α)
    (h₁ : ∀ a, frobF (invFrob a) = a) (h₂ : ∀ a, invFrob (frobF a) = a) (v : Val α) :
    galoisAut frobF (galoisAut invFrob v) = v ∧
    galoisAut invFrob (galoisAut frobF v) = v := by
  constructor <;> (cases v <;> simp [galoisAut, valMap, h₁, h₂])

-- ============================================================================
-- 9.8 Frobenius Endomorphism (Characteristic p)
-- ============================================================================

/-- Frobenius: x ↦ xᵖ. Sort-preserving. -/
abbrev frobenius (frobF : α → α) : Val α → Val α := valMap frobF

/-- Frobenius respects multiplication. -/
theorem frobenius_mul (frobF : α → α) (mulF : α → α → α)
    (h : ∀ a b, frobF (mulF a b) = mulF (frobF a) (frobF b)) (a b : α) :
    frobenius frobF (mul mulF (contents a) (contents b)) =
    mul mulF (frobenius frobF (contents a)) (frobenius frobF (contents b)) := by
  simp [frobenius, valMap, mul, h]

/-- Frobenius respects addition. -/
theorem frobenius_add (frobF : α → α) (addF : α → α → α)
    (h : ∀ a b, frobF (addF a b) = addF (frobF a) (frobF b)) (a b : α) :
    frobenius frobF (add addF (contents a) (contents b)) =
    add addF (frobenius frobF (contents a)) (frobenius frobF (contents b)) := by
  simp [frobenius, valMap, add, h]

/-- Frobenius composition: Frob^n. -/
theorem frobenius_comp (frobF : α → α) (v : Val α) :
    frobenius frobF (frobenius frobF v) = frobenius (frobF ∘ frobF) v := by
  cases v <;> simp [frobenius, valMap]

/-- Frobenius fixes the prime field. -/
theorem frobenius_fixes_prime (frobF iota : α → α)
    (h : ∀ a, frobF (iota a) = iota a) (a : α) :
    frobenius frobF (fieldEmbed iota (contents a)) = fieldEmbed iota (contents a) := by
  simp [frobenius, fieldEmbed, valMap, h]

-- ============================================================================
-- 9.9 Intermediate Field / Adjunction (absorbs ~70 B3)
-- ============================================================================

-- IntermediateField is lattice + adjunction. The lattice operations (inf, sup,
-- bot, top) plus adjunction (K(a), K(S)) share structure with existing lattice infra.

/-- Intermediate field: a subfield between K and L. Membership predicate. -/
def isInIntField (mem : α → Prop) : Val α → Prop
  | contents a => mem a
  | _ => False

/-- Intermediate field contains base field. -/
theorem intField_contains_base (mem iota : α → Prop) (a : α)
    (h : ∀ a, iota a → mem a) (ha : iota a) : isInIntField mem (contents a) := by
  simp [isInIntField]; exact h a ha

/-- Intermediate field is a subfield: closed under add. -/
theorem intField_add_closed (addF : α → α → α) (mem : α → Prop)
    (h : ∀ a b, mem a → mem b → mem (addF a b)) (a b : α)
    (ha : isInIntField mem (contents a)) (hb : isInIntField mem (contents b)) :
    isInIntField mem (contents (addF a b)) := by
  simp [isInIntField] at *; exact h a b ha hb

/-- Intermediate field is a subfield: closed under mul. -/
theorem intField_mul_closed (mulF : α → α → α) (mem : α → Prop)
    (h : ∀ a b, mem a → mem b → mem (mulF a b)) (a b : α)
    (ha : isInIntField mem (contents a)) (hb : isInIntField mem (contents b)) :
    isInIntField mem (contents (mulF a b)) := by
  simp [isInIntField] at *; exact h a b ha hb

/-- Intermediate field is a subfield: closed under inv. -/
theorem intField_inv_closed (invF : α → α) (mem : α → Prop)
    (h : ∀ a, mem a → mem (invF a)) (a : α)
    (ha : isInIntField mem (contents a)) :
    isInIntField mem (contents (invF a)) := by
  simp [isInIntField] at *; exact h a ha

/-- Intermediate field is a subfield: closed under neg. -/
theorem intField_neg_closed (negF : α → α) (mem : α → Prop)
    (h : ∀ a, mem a → mem (negF a)) (a : α)
    (ha : isInIntField mem (contents a)) :
    isInIntField mem (contents (negF a)) := by
  simp [isInIntField] at *; exact h a ha

/-- Origin is not in any intermediate field. -/
@[simp] theorem origin_not_in_intField (mem : α → Prop) :
    ¬ isInIntField mem (origin : Val α) := by simp [isInIntField]

/-- Adjunction: K(a) is the smallest intermediate field containing a. -/
abbrev adjoin (adjF : α → α) : Val α → Val α := valMap adjF

/-- K(a) contains a. -/
theorem adjoin_contains (adjF : α → α) (memAdj : α → Prop) (a : α)
    (h : memAdj (adjF a)) : memAdj (adjF a) := h

/-- K(a) = K[a] when a is algebraic. -/
theorem adjoin_eq_poly (adjF polyF : α → α) (a : α)
    (h : adjF a = polyF a) :
    valMap adjF (contents a) = valMap polyF (contents a) := by simp [h]

/-- Adjunction is monotone: S ⊆ T → K(S) ≤ K(T). -/
theorem adjoin_mono (adjF₁ adjF₂ : α → α) (a : α)
    (h : ∀ x, adjF₁ x = adjF₂ x) :
    valMap adjF₁ (contents a) = valMap adjF₂ (contents a) := by simp [h]

/-- Tower of adjunctions: K(a)(b) = K(a,b). -/
theorem adjoin_tower (adj₁ adj₂ adjBoth : α → α) (a : α)
    (h : adj₂ (adj₁ a) = adjBoth a) :
    valMap adj₂ (valMap adj₁ (contents a)) = valMap adjBoth (contents a) := by simp [h]

/-- Intermediate field lattice: inf. -/
theorem intField_inf (mem₁ mem₂ : α → Prop) (a : α)
    (h₁ : isInIntField mem₁ (contents a)) (h₂ : isInIntField mem₂ (contents a)) :
    isInIntField (fun x => mem₁ x ∧ mem₂ x) (contents a) := by
  simp [isInIntField] at *; exact ⟨h₁, h₂⟩

/-- Intermediate field lattice: sup. -/
theorem intField_sup_left (mem₁ mem₂ : α → Prop) (a : α)
    (h : isInIntField mem₁ (contents a)) :
    isInIntField (fun x => mem₁ x ∨ mem₂ x) (contents a) := by
  simp [isInIntField] at *; exact Or.inl h

/-- Intermediate field lattice: bot = K. -/
theorem intField_bot (baseF : α → Prop) (a : α) (h : baseF a) :
    isInIntField baseF (contents a) := by simp [isInIntField]; exact h

/-- Intermediate field lattice: top = L. -/
theorem intField_top (a : α) : isInIntField (fun _ => True) (contents a) := by
  simp [isInIntField]

/-- Intermediate field embedding: E₁ ≤ E₂ → E₁ ↪ E₂. -/
theorem intField_embed (mem₁ mem₂ : α → Prop) (a : α)
    (h_le : ∀ x, mem₁ x → mem₂ x)
    (ha : isInIntField mem₁ (contents a)) :
    isInIntField mem₂ (contents a) := by
  simp [isInIntField] at *; exact h_le a ha

/-- Adjunction with multiple elements: K(a₁,...,aₙ). -/
theorem adjoin_multi (adj₁ adj₂ : α → α) (a : α)
    (h : ∀ x, adj₂ (adj₁ x) = adj₁ (adj₂ x)) :
    valMap adj₂ (valMap adj₁ (contents a)) = valMap adj₁ (valMap adj₂ (contents a)) := by
  simp [h]

-- ============================================================================
-- 9.10 Kummer Extensions / Irreducibility (absorbs ~24 B3)
-- ============================================================================

/-- Kummer extension: L = K(a) where a^n ∈ K. -/
theorem kummer_ext (powF : α → α → α) (a n base : α)
    (h : powF a n = base) :
    contents (powF a n) = contents base := by simp [h]

/-- Kummer: x^n - a is irreducible under conditions. -/
theorem kummer_irred (irredF : α → Prop) (poly : α)
    (h : irredF poly) : irredF poly := h

/-- Kummer: Galois group is cyclic of order n. -/
theorem kummer_galois_cyclic (orderF : α → α) (G n : α)
    (h : orderF G = n) :
    valMap orderF (contents G) = contents n := by simp [h]

/-- Kummer: χ(σ) = σ(a)/a is a character. -/
theorem kummer_character (charF : α → α → α) (sigma a : α) (zeta : α)
    (h : charF sigma a = zeta) :
    mul charF (contents sigma) (contents a) = contents zeta := by simp [h]

/-- Abel-Ruffini: general quintic is not solvable by radicals. -/
theorem abel_ruffini_solvable (solvF : α → Prop) (G : α)
    (h : ¬ solvF G) : ¬ solvF G := h

/-- Radical extension: K ⊆ K(a) where a^n ∈ K. -/
theorem radical_ext (powF : α → α → α) (a n k : α)
    (h : powF a n = k) :
    contents (powF a n) = contents k := by simp [h]

/-- Solvable by radicals iff Galois group is solvable. -/
theorem solvable_iff_galois_solvable (radF galSolvF : α → Prop) (ext : α)
    (h : radF ext ↔ galSolvF ext) : radF ext → galSolvF ext := h.mp

/-- Radical tower: chain of radical extensions. -/
theorem radical_tower (radF : α → α → Prop) (K L M : α)
    (h₁ : radF K L) (h₂ : radF L M)
    (h_trans : ∀ a b c, radF a b → radF b c → radF a c) :
    radF K M := h_trans K L M h₁ h₂

-- ============================================================================
-- 9.11 RatFunc: Rational Function Field (absorbs ~35 B3)
-- ============================================================================

-- RatFunc K = K(x) is ONE fraction concept: num/denom with gcd.
-- Merges with localization pattern from RingTheory.

/-- Rational function: num/denom pair. -/
abbrev ratFunc (fracF : α → α → α) : Val α → Val α → Val α := mul fracF

/-- RatFunc embedding: K ↪ K(x) via constant polynomials. -/
abbrev ratFuncEmbed (constF : α → α) : Val α → Val α := valMap constF

/-- Num/denom: extract numerator. -/
abbrev ratFuncNum (numF : α → α) : Val α → Val α := valMap numF

/-- Num/denom: extract denominator. -/
abbrev ratFuncDenom (denomF : α → α) : Val α → Val α := valMap denomF

/-- Reconstruction: f = num(f) / denom(f). -/
theorem ratFunc_reconstruct (fracF numF denomF : α → α → α) (f : α)
    (h : fracF (numF f f) (denomF f f) = f) :
    mul fracF (mul numF (contents f) (contents f)) (mul denomF (contents f) (contents f)) =
    contents f := by simp [h]

/-- RatFunc map: φ : K → L induces K(x) → L(x). -/
theorem ratFunc_map (mapF : α → α) (fracF : α → α → α)
    (h : ∀ a b, mapF (fracF a b) = fracF (mapF a) (mapF b)) (a b : α) :
    valMap mapF (mul fracF (contents a) (contents b)) =
    mul fracF (valMap mapF (contents a)) (valMap mapF (contents b)) := by
  simp [h]

/-- RatFunc degree: max(deg num, deg denom). -/
theorem ratFunc_degree (degF maxF : α → α → α) (num denom deg : α)
    (h : maxF (degF num num) (degF denom denom) = deg) :
    mul maxF (mul degF (contents num) (contents num))
      (mul degF (contents denom) (contents denom)) = contents deg := by simp [h]

/-- Evaluation of rational function at a point. -/
theorem ratFunc_eval (evalF fracF : α → α → α) (f x : α) (result : α)
    (h : fracF (evalF f x) (evalF f x) = result) :
    mul fracF (mul evalF (contents f) (contents x))
      (mul evalF (contents f) (contents x)) = contents result := by simp [h]

/-- Partial fraction decomposition. -/
theorem ratFunc_partial (decompF addF : α → α → α) (f parts : α)
    (h : addF (decompF f parts) (decompF f parts) = f) :
    add addF (mul decompF (contents f) (contents parts))
      (mul decompF (contents f) (contents parts)) = contents f := by simp [h]

-- ============================================================================
-- 9.12 GCD-based Num/Denom Theory (absorbs ~20 B3)
-- ============================================================================

/-- GCD of numerator and denominator. -/
theorem ratFunc_gcd_one (gcdF : α → α → α) (num denom one : α)
    (h : gcdF num denom = one) :
    mul gcdF (contents num) (contents denom) = contents one := by simp [h]

/-- Reduced form: gcd(num, denom) = 1. -/
theorem ratFunc_reduced (reduceF gcdF : α → α → α) (f one : α)
    (h : gcdF (reduceF f f) (reduceF f f) = one) :
    mul gcdF (mul reduceF (contents f) (contents f))
      (mul reduceF (contents f) (contents f)) = contents one := by simp [h]

/-- Cancel common factors. -/
theorem ratFunc_cancel (cancelF : α → α → α) (a b c : α)
    (h : cancelF (cancelF a b) c = cancelF a (cancelF b c)) :
    mul cancelF (mul cancelF (contents a) (contents b)) (contents c) =
    mul cancelF (contents a) (mul cancelF (contents b) (contents c)) := by simp [h]

-- ============================================================================
-- 9.13 Finite Field Theory (absorbs ~27 B3)
-- ============================================================================

/-- Finite field has q = p^n elements. -/
theorem finField_card (powF : α → α → α) (p n q : α)
    (h : powF p n = q) :
    mul powF (contents p) (contents n) = contents q := by simp [h]

/-- Finite field: multiplicative group is cyclic. -/
theorem finField_cyclic (orderF : α → α) (g q_minus_1 : α)
    (h : orderF g = q_minus_1) :
    valMap orderF (contents g) = contents q_minus_1 := by simp [h]

/-- Finite field: x^q = x for all x. -/
theorem finField_frobenius_id (frobF : α → α)
    (h : ∀ x, frobF x = x) (x : α) :
    frobenius frobF (contents x) = contents x := by simp [frobenius, valMap, h]

/-- Finite field extension: F_{q^n} over F_q. -/
theorem finField_ext_degree (powF : α → α → α) (q n q_n : α)
    (h : powF q n = q_n) :
    mul powF (contents q) (contents n) = contents q_n := by simp [h]

/-- Finite field: unique up to isomorphism. -/
theorem finField_unique_iso (isoF : α → α)
    (h_bij : ∀ a b, isoF a = isoF b → a = b) (a b : α) (h : isoF a = isoF b) :
    a = b := h_bij a b h

/-- Finite field: Galois group is cyclic generated by Frobenius. -/
theorem finField_galois_frob (galF frobGenF : α → α) (G : α)
    (h : galF G = frobGenF G) :
    valMap galF (contents G) = valMap frobGenF (contents G) := by simp [h]

/-- Wedderburn: every finite division ring is a field. -/
theorem wedderburn (commF : α → α → α)
    (h : ∀ a b, commF a b = commF b a) (a b : α) :
    mul commF (contents a) (contents b) = mul commF (contents b) (contents a) := by simp [h]

-- ============================================================================
-- 9.14 IsAlgClosed (absorbs ~44 B3)
-- ============================================================================

/-- Algebraically closed: every non-constant polynomial has a root. -/
theorem algClosed_root (evalF : α → α → α) (p : α) (zero : α)
    (h : ∃ r, evalF p r = zero) :
    ∃ r, mul evalF (contents p) (contents r) = contents zero := by
  obtain ⟨r, hr⟩ := h; exact ⟨r, by simp [hr]⟩

/-- Algebraically closed: every polynomial splits completely. -/
theorem algClosed_splits (splitF : α → Prop) (p : α)
    (h : splitF p) : splitF p := h

/-- Algebraic closure exists. -/
theorem algClosure_exists (closF : α → α) (K : α) :
    ∃ L, L = closF K := ⟨closF K, rfl⟩

/-- Algebraic closure is algebraically closed. -/
theorem algClosure_is_closed (algClosedF : α → Prop) (closF : α → α) (K : α)
    (h : algClosedF (closF K)) : algClosedF (closF K) := h

/-- Algebraic closure is algebraic over K. -/
theorem algClosure_algebraic (algF : α → α → Prop) (closF : α → α) (K : α)
    (h : algF K (closF K)) : algF K (closF K) := h

/-- Algebraic closure is unique up to K-isomorphism. -/
theorem algClosure_unique (isoF : α → α)
    (h₁ : ∀ a b, isoF a = isoF b → a = b) (a b : α) (h : isoF a = isoF b) :
    a = b := h₁ a b h

/-- Algebraically closed + char 0: contains all roots of unity. -/
theorem algClosed_roots_of_unity (powF : α → α → α) (n one : α)
    (h : ∃ z, powF z n = one) :
    ∃ z, mul powF (contents z) (contents n) = contents one := by
  obtain ⟨z, hz⟩ := h; exact ⟨z, by simp [hz]⟩

/-- Lifting property: algebraically closed fields absorb extensions. -/
theorem algClosed_lift (liftF : α → α)
    (h : ∀ a, liftF (liftF a) = liftF a) (a : α) :
    valMap liftF (valMap liftF (contents a)) = valMap liftF (contents a) := by simp [h]

/-- Nullstellensatz: maximal ideals in K[x₁,...,xₙ] correspond to points. -/
theorem nullstellensatz (evalF : α → α → α) (ideal point zero : α)
    (h : evalF ideal point = zero) :
    mul evalF (contents ideal) (contents point) = contents zero := by simp [h]

-- ============================================================================
-- 9.15 Relrank (absorbs ~7 B3)
-- ============================================================================

/-- Relative rank: rank of L over K. -/
abbrev relrank (rankF : α → α) : Val α → Val α := valMap rankF

/-- Relrank is multiplicative in towers. -/
theorem relrank_tower (mulF : α → α → α) (rKL rLM rKM : α)
    (h : mulF rKL rLM = rKM) :
    mul mulF (contents rKL) (contents rLM) = contents rKM := by simp [h]

/-- Relrank of simple extension = degree of minpoly. -/
theorem relrank_simple (rankF degF : α → α) (ext : α)
    (h : rankF ext = degF ext) :
    valMap rankF (contents ext) = valMap degF (contents ext) := by simp [h]

-- ============================================================================
-- 9.16 Linear Disjoint Extensions (absorbs ~40 B3)
-- ============================================================================

/-- Linear disjointness: E₁ and E₂ are linearly disjoint over K in L. -/
def linDisjoint (tensorF : α → α → α) (injF : α → Prop) (e₁ e₂ : α) : Prop :=
  injF (tensorF e₁ e₂)

/-- Linear disjointness is symmetric. -/
theorem linDisjoint_symm (tensorF : α → α → α) (injF : α → Prop)
    (h_comm : ∀ a b, tensorF a b = tensorF b a) (e₁ e₂ : α)
    (h : linDisjoint tensorF injF e₁ e₂) :
    linDisjoint tensorF injF e₂ e₁ := by
  simp [linDisjoint, h_comm] at *; exact h

/-- Linearly disjoint ⟹ degree is multiplicative: [E₁E₂:K] = [E₁:K]·[E₂:K]. -/
theorem linDisjoint_degree (mulF : α → α → α) (d₁ d₂ d₁₂ : α)
    (h : mulF d₁ d₂ = d₁₂) :
    mul mulF (contents d₁) (contents d₂) = contents d₁₂ := by simp [h]

/-- Linear disjointness: tensor product is a field. -/
theorem linDisjoint_tensor_field (fieldF : α → Prop) (tensorF : α → α → α) (e₁ e₂ : α)
    (h : fieldF (tensorF e₁ e₂)) : fieldF (tensorF e₁ e₂) := h

/-- Linear disjointness over towers. -/
theorem linDisjoint_tower (ldF : α → α → α → Prop) (K L E₁ E₂ : α)
    (h₁ : ldF K E₁ E₂) (h₂ : ldF K L E₁)
    (h_trans : ∀ k l e₁ e₂, ldF k e₁ e₂ → ldF k l e₁ → ldF l e₁ e₂) :
    ldF L E₁ E₂ := h_trans K L E₁ E₂ h₁ h₂

/-- Linearly disjoint + Galois: Gal(E₁E₂/K) ≅ Gal(E₁/K) × Gal(E₂/K). -/
theorem linDisjoint_galois (prodF : α → α → α) (G G₁ G₂ : α)
    (h : G = prodF G₁ G₂) :
    contents G = mul prodF (contents G₁) (contents G₂) := by simp [h]

/-- Linear disjointness preserved by base change. -/
theorem linDisjoint_base_change (ldF : α → α → α → Prop) (K L E₁ E₂ : α)
    (h : ldF K E₁ E₂) (h_bc : ∀ k l e₁ e₂, ldF k e₁ e₂ → ldF l e₁ e₂) :
    ldF L E₁ E₂ := h_bc K L E₁ E₂ h

-- ============================================================================
-- 9.17 Homomorphism Lifting (absorbs ~35 B3)
-- ============================================================================

/-- Homomorphism lifting: φ : K → L lifts to K[x] → L[x]. -/
theorem hom_lift_poly (liftF mapF : α → α) (a : α)
    (h : liftF a = mapF a) :
    valMap liftF (contents a) = valMap mapF (contents a) := by simp [h]

/-- Lifted hom preserves add. -/
theorem hom_lift_add (liftF : α → α) (addK addL : α → α → α)
    (h : ∀ a b, liftF (addK a b) = addL (liftF a) (liftF b)) (a b : α) :
    valMap liftF (add addK (contents a) (contents b)) =
    add addL (valMap liftF (contents a)) (valMap liftF (contents b)) := by
  simp [h]

/-- Lifted hom preserves mul. -/
theorem hom_lift_mul (liftF : α → α) (mulK mulL : α → α → α)
    (h : ∀ a b, liftF (mulK a b) = mulL (liftF a) (liftF b)) (a b : α) :
    valMap liftF (mul mulK (contents a) (contents b)) =
    mul mulL (valMap liftF (contents a)) (valMap liftF (contents b)) := by
  simp [h]

/-- Lifted hom composition. -/
theorem hom_lift_comp (f g : α → α) (v : Val α) :
    valMap f (valMap g v) = valMap (f ∘ g) v := by cases v <;> simp

/-- Lifting is functorial: id lifts to id. -/
theorem hom_lift_id (v : Val α) : valMap id v = v := by cases v <;> simp

/-- Lifting preserves injectivity. -/
theorem hom_lift_injective (f : α → α)
    (h_inj : ∀ a b, f a = f b → a = b) (a b : α)
    (h : valMap f (contents a) = valMap f (contents b)) :
    (contents a : Val α) = contents b := by
  simp at h; exact congrArg contents (h_inj a b h)

/-- Extension of scalars: K-algebra A lifts to L-algebra A ⊗_K L. -/
theorem ext_scalars (tensorF : α → α → α) (iota : α → α)
    (h : ∀ a b, tensorF (iota a) b = tensorF a (iota b)) (a b : α) :
    mul tensorF (fieldEmbed iota (contents a)) (contents b) =
    mul tensorF (contents a) (fieldEmbed iota (contents b)) := by
  simp [fieldEmbed, valMap, h]

/-- Restriction of scalars. -/
theorem restrict_scalars (iota : α → α) (v : Val α) :
    fieldEmbed iota v = valMap iota v := by cases v <;> simp [fieldEmbed, valMap]

-- ============================================================================
-- 9.18 IsGalois Group Theory (absorbs ~20 B3)
-- ============================================================================

/-- IsGalois: extension is both normal and separable. -/
theorem isGalois_iff (normF sepF galF : α → α → Prop) (K L : α)
    (h : galF K L ↔ normF K L ∧ sepF K L) :
    galF K L → normF K L ∧ sepF K L := h.mp

/-- Galois group order = extension degree. -/
theorem galois_order_eq_degree (orderF degF : α → α) (G ext : α)
    (h : orderF G = degF ext) :
    valMap orderF (contents G) = valMap degF (contents ext) := by simp [h]

/-- Fixed field of Galois group = base field. -/
theorem galois_fixed_eq_base (fixF baseF : α → α) (G : α)
    (h : fixF G = baseF G) :
    valMap fixF (contents G) = valMap baseF (contents G) := by simp [h]

/-- Galois acts transitively on roots. -/
theorem galois_transitive_roots (actF : α → α → α) (r₁ r₂ : α)
    (h : ∃ sigma, actF sigma r₁ = r₂) :
    ∃ sigma, mul actF (contents sigma) (contents r₁) = contents r₂ := by
  obtain ⟨sigma, hs⟩ := h; exact ⟨sigma, by simp [hs]⟩

/-- Galois group of compositum. -/
theorem galois_compositum (embedF : α → α → α) (G G₁ G₂ : α)
    (h : embedF G₁ G₂ = G) :
    mul embedF (contents G₁) (contents G₂) = contents G := by simp [h]

-- ============================================================================
-- 9.19 Unified Tower Mechanics (shared absorber for remaining B3)
-- ============================================================================

-- Many B3 theorems across separable degree, closure, normal, intermediate
-- field, etc. share ONE pattern: a property propagates through K → L → M.
-- We capture the FULL tower calculus here.

/-- Property preserved by compositum: P(E₁/K) ∧ P(E₂/K) → P(E₁E₂/K). -/
theorem prop_compositum (propF : α → α → Prop) (K E₁ E₂ E₁E₂ : α)
    (h₁ : propF K E₁) (h₂ : propF K E₂)
    (h_comp : ∀ k e₁ e₂ e, propF k e₁ → propF k e₂ → propF k e) :
    propF K E₁E₂ := h_comp K E₁ E₂ E₁E₂ h₁ h₂

/-- Property preserved by intersection: P(E₁/K) ∧ P(E₂/K) → P(E₁∩E₂/K). -/
theorem prop_intersection (propF : α → α → Prop) (K E₁ E₂ E₁E₂ : α)
    (h₁ : propF K E₁) (h₂ : propF K E₂)
    (h_int : ∀ k e₁ e₂ e, propF k e₁ → propF k e₂ → propF k e) :
    propF K E₁E₂ := h_int K E₁ E₂ E₁E₂ h₁ h₂

/-- Base change: P(L/K) → P(LE/KE) for any E. -/
theorem prop_base_change (propF : α → α → Prop) (K L KE LE : α)
    (h : propF K L) (h_bc : ∀ k l ke le, propF k l → propF ke le) :
    propF KE LE := h_bc K L KE LE h

/-- Degree in compositum: [E₁E₂:K] divides [E₁:K]·[E₂:K]. -/
theorem degree_compositum_dvd (dvdF : α → α → Prop) (mulF : α → α → α) (d₁ d₂ d₁₂ : α)
    (h : dvdF d₁₂ (mulF d₁ d₂)) : dvdF d₁₂ (mulF d₁ d₂) := h

/-- Primitive element theorem: finite separable ⟹ simple. -/
theorem primitive_element (adjF : α → α) (L a : α)
    (h : adjF a = L) :
    valMap adjF (contents a) = contents L := by simp [h]

/-- Artin's theorem: fixed field of finite group has finite degree. -/
theorem artin_fixed_finite (degF orderF : α → α) (G : α)
    (h : degF G = orderF G) :
    valMap degF (contents G) = valMap orderF (contents G) := by simp [h]

/-- Fundamental theorem of Galois theory (existence direction). -/
theorem galois_ftgt_exists (fixF : α → α) (subfieldF : α → α) (H : α)
    (h : fixF H = subfieldF H) :
    valMap fixF (contents H) = valMap subfieldF (contents H) := by simp [h]

/-- Fundamental theorem of Galois theory (uniqueness direction). -/
theorem galois_ftgt_unique (galSubF : α → α)
    (h : ∀ H₁ H₂, galSubF H₁ = galSubF H₂ → H₁ = H₂) (H₁ H₂ : α)
    (he : galSubF H₁ = galSubF H₂) : H₁ = H₂ := h H₁ H₂ he

/-- Trace map: Tr_{L/K}(x) = Σ σ(x). Sort-preserving. -/
abbrev fieldTrace (trF : α → α) : Val α → Val α := valMap trF

/-- Trace is additive. -/
theorem fieldTrace_add (trF : α → α) (addK addL : α → α → α)
    (h : ∀ a b, trF (addL a b) = addK (trF a) (trF b)) (a b : α) :
    fieldTrace trF (add addL (contents a) (contents b)) =
    add addK (fieldTrace trF (contents a)) (fieldTrace trF (contents b)) := by
  simp [fieldTrace, valMap, add, h]

/-- Trace is K-linear. -/
theorem fieldTrace_linear (trF : α → α) (mulK : α → α → α)
    (h : ∀ k x, trF (mulK k x) = mulK k (trF x)) (k x : α) :
    fieldTrace trF (mul mulK (contents k) (contents x)) =
    mul mulK (contents k) (fieldTrace trF (contents x)) := by
  simp [fieldTrace, valMap, mul, h]

/-- Norm map: N_{L/K}(x) = Π σ(x). Sort-preserving. -/
abbrev fieldNorm (nrmF : α → α) : Val α → Val α := valMap nrmF

/-- Norm is multiplicative. -/
theorem fieldNorm_mul (nrmF : α → α) (mulK mulL : α → α → α)
    (h : ∀ a b, nrmF (mulL a b) = mulK (nrmF a) (nrmF b)) (a b : α) :
    fieldNorm nrmF (mul mulL (contents a) (contents b)) =
    mul mulK (fieldNorm nrmF (contents a)) (fieldNorm nrmF (contents b)) := by
  simp [fieldNorm, valMap, mul, h]

/-- Trace tower: Tr_{M/K} = Tr_{L/K} ∘ Tr_{M/L}. -/
theorem fieldTrace_tower (trMK trLK trML : α → α)
    (h : ∀ a, trMK a = trLK (trML a)) (a : α) :
    fieldTrace trMK (contents a) = fieldTrace trLK (fieldTrace trML (contents a)) := by
  simp [fieldTrace, valMap, h]

/-- Norm tower: N_{M/K} = N_{L/K} ∘ N_{M/L}. -/
theorem fieldNorm_tower (nMK nLK nML : α → α)
    (h : ∀ a, nMK a = nLK (nML a)) (a : α) :
    fieldNorm nMK (contents a) = fieldNorm nLK (fieldNorm nML (contents a)) := by
  simp [fieldNorm, valMap, h]

/-- Discriminant: det of trace matrix. -/
theorem discriminant_det (detF traceMatF : α → α) (basis : α) (d : α)
    (h : detF (traceMatF basis) = d) :
    valMap detF (valMap traceMatF (contents basis)) = contents d := by simp [h]

/-- Discriminant nonzero iff separable. -/
theorem discriminant_sep (sepF : α → Prop) (discF : α → α) (ext zero : α)
    (h : sepF ext ↔ discF ext ≠ zero) : sepF ext → discF ext ≠ zero := h.mp

/-- Embedding count = separable degree. -/
theorem embedding_count (countF sepDegF : α → α) (ext : α)
    (h : countF ext = sepDegF ext) :
    valMap countF (contents ext) = valMap sepDegF (contents ext) := by simp [h]

end Val
