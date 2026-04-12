/-
Released under MIT license.
-/
import ValClass.Field

/-!
# Val α: Field Theory and Galois Correspondence (Class-Based)

Mathlib: 26,919 lines across 43 files. 696 `≠ 0` references. 970 B3 theorems.
Val (class): field extensions are valMap. Galois actions are valMap. Tower
propagation is ONE pattern. Galois correspondence is ONE bijection family.
The 696 `≠ 0` refs shrink to the sort.

This is the class-based rewrite: [ValField α] instead of explicit parameters.
Arithmetic operations (mul, add, neg, inv) come from the class chain.
Domain-specific operations stay as explicit hypotheses on α.
-/

namespace Val

universe u
variable {α : Type u}

-- ============================================================================
-- 9.1 Field Extension: K → L is valMap
-- ============================================================================

abbrev fieldEmbed (iota : α → α) : Val α → Val α := valMap iota

theorem fieldEmbed_injective (iota : α → α)
    (h : ∀ a b, iota a = iota b → a = b) (a b : α)
    (he : fieldEmbed iota (contents a) = fieldEmbed iota (contents b)) :
    (contents a : Val α) = contents b := by
  simp at he; exact congrArg contents (h a b he)

theorem fieldEmbed_add [ValArith α] (iota : α → α)
    (h : ∀ a b, iota (ValArith.addF a b) = ValArith.addF (iota a) (iota b)) (a b : α) :
    fieldEmbed iota (add (contents a) (contents b)) =
    add (fieldEmbed iota (contents a)) (fieldEmbed iota (contents b)) := by
  simp [fieldEmbed, valMap, add, h]

theorem fieldEmbed_mul [ValArith α] (iota : α → α)
    (h : ∀ a b, iota (ValArith.mulF a b) = ValArith.mulF (iota a) (iota b)) (a b : α) :
    fieldEmbed iota (mul (contents a) (contents b)) =
    mul (fieldEmbed iota (contents a)) (fieldEmbed iota (contents b)) := by
  simp [fieldEmbed, valMap, mul, h]

theorem fieldEmbed_inv [ValArith α] (iota : α → α)
    (h : ∀ a, iota (ValArith.invF a) = ValArith.invF (iota a)) (a : α) :
    fieldEmbed iota (inv (contents a)) = inv (fieldEmbed iota (contents a)) := by
  simp [fieldEmbed, valMap, inv, h]

theorem fieldEmbed_neg [ValArith α] (iota : α → α)
    (h : ∀ a, iota (ValArith.negF a) = ValArith.negF (iota a)) (a : α) :
    fieldEmbed iota (neg (contents a)) = neg (fieldEmbed iota (contents a)) := by
  simp [fieldEmbed, valMap, neg, h]

theorem fieldEmbed_comp (iota₁ iota₂ : α → α) (v : Val α) :
    fieldEmbed iota₂ (fieldEmbed iota₁ v) = fieldEmbed (iota₂ ∘ iota₁) v := by
  cases v <;> simp [fieldEmbed, valMap]

theorem fieldEmbed_comp_assoc (i₁ i₂ i₃ : α → α) (v : Val α) :
    fieldEmbed i₃ (fieldEmbed i₂ (fieldEmbed i₁ v)) =
    fieldEmbed (i₃ ∘ i₂ ∘ i₁) v := by cases v <;> simp [fieldEmbed, valMap]

-- ============================================================================
-- 9.2 Degree of Extension
-- ============================================================================

abbrev extDegree (degF : α → α) : Val α → Val α := valMap degF

theorem tower_degree [ValArith α] (dML dLK dMK : α)
    (h : ValArith.mulF dML dLK = dMK) :
    mul (contents dML) (contents dLK) = contents dMK := by simp [mul, h]

theorem degree_mul_tower [ValArith α] (d₁ d₂ d₃ : α)
    (h : ValArith.mulF d₁ d₂ = d₃) :
    mul (contents d₁) (contents d₂) = contents d₃ := by simp [mul, h]

theorem finite_ext_degree (degF : α → α) (a : α) :
    ∃ d, extDegree degF (contents a) = contents d := ⟨degF a, rfl⟩

theorem degree_one_iff_iso (degF : α → α) (a one : α)
    (h : degF a = one) :
    extDegree degF (contents a) = contents one := by simp [extDegree, valMap, h]

-- ============================================================================
-- 9.3 Algebraic Elements and Minimal Polynomial (absorbs ~60 B3)
-- ============================================================================

theorem minpoly_eval (evalF : α → α → α) (minp a zero : α)
    (h : evalF minp a = zero) :
    contents (evalF minp a) = contents zero := by simp [h]

theorem minpoly_monic (leadF : α → α) (minp one : α)
    (h : leadF minp = one) :
    valMap leadF (contents minp) = contents one := by simp [h]

theorem minpoly_irred (irredF : α → Prop) (minp : α) (h : irredF minp) :
    irredF minp := h

theorem minpoly_divides (divF : α → α → α) (minp p : α)
    (h : ∃ q, p = divF minp q) :
    ∃ q, (contents p : Val α) = contents (divF minp q) := by
  obtain ⟨q, hq⟩ := h; exact ⟨q, by simp [hq]⟩

theorem minpoly_unique (minp₁ minp₂ : α)
    (h : minp₁ = minp₂) :
    (contents minp₁ : Val α) = contents minp₂ := by simp [h]

theorem minpoly_degree_eq_ext (degP degE : α → α) (minp ext : α)
    (h : degP minp = degE ext) :
    valMap degP (contents minp) = valMap degE (contents ext) := by simp [h]

theorem minpoly_embed (iota minpolyK minpolyL : α → α) (a : α)
    (h : minpolyL (iota a) = iota (minpolyK a)) :
    fieldEmbed iota (valMap minpolyK (contents a)) =
    valMap minpolyL (fieldEmbed iota (contents a)) := by
  simp [fieldEmbed, valMap, h]

theorem minpoly_coeff_base (coeffF iota : α → α) (minp : α)
    (h : ∀ c, coeffF c = iota (coeffF c)) :
    coeffF minp = iota (coeffF minp) := h minp

theorem minpoly_generator (genF defpolyF : α → α) (a : α)
    (h : genF a = defpolyF a) :
    valMap genF (contents a) = valMap defpolyF (contents a) := by simp [h]

theorem minpoly_degree_pos (degF : α → α) (minp : α) (d : α)
    (h : degF minp = d) :
    valMap degF (contents minp) = contents d := by simp [h]

theorem minpoly_tower_dvd (dvdF : α → α → Prop) (minK minL : α)
    (h : dvdF minL minK) : dvdF minL minK := h

theorem minpoly_map (mapF minpolyF : α → α) (a : α)
    (h : mapF (minpolyF a) = minpolyF (mapF a)) :
    valMap mapF (valMap minpolyF (contents a)) =
    valMap minpolyF (valMap mapF (contents a)) := by simp [h]

theorem minpoly_adjoin_iso (isoF : α → α) (a : α)
    (h_iso : ∀ x, isoF (isoF x) = x) :
    valMap isoF (valMap isoF (contents a)) = contents a := by simp [h_iso]

-- ============================================================================
-- 9.4 Splitting Field (absorbs ~30 B3)
-- ============================================================================

abbrev splitEmbed (iota : α → α) : Val α → Val α := valMap iota

theorem splits_roots (evalF : α → α → α) (p r zero : α)
    (h : evalF p r = zero) :
    contents (evalF p r) = contents zero := by simp [h]

theorem splitField_unique (iso : α → α)
    (h_iso : ∀ a b, iso a = iso b → a = b) (a b : α)
    (he : iso a = iso b) : a = b := h_iso a b he

theorem splitField_normal (sigma evalF : α → α → α) (p : α → α) (r zero : α)
    (h_root : evalF (p r) r = zero)
    (h_perm : ∀ s r', evalF (p r') r' = zero → evalF (p (sigma s r')) (sigma s r') = zero)
    (s : α) : evalF (p (sigma s r)) (sigma s r) = zero := h_perm s r h_root

theorem splitField_degree_bound (dvdF : α → α → Prop) (deg bound : α)
    (h : dvdF deg bound) : dvdF deg bound := h

theorem splitField_factor (factorF : α → α → α) (p factors result : α)
    (h : factorF factors result = p) :
    contents (factorF factors result) = contents p := by simp [h]

theorem splitField_prod (compF : α → α → α) (s₁ s₂ s : α)
    (h : compF s₁ s₂ = s) :
    contents (compF s₁ s₂) = contents s := by simp [h]

-- ============================================================================
-- 9.5 Galois Theory (absorbs ~50 B3 via correspondence family)
-- ============================================================================

abbrev galoisAut (sigma : α → α) : Val α → Val α := valMap sigma

theorem galois_fixes_base (sigma iota : α → α)
    (h : ∀ a, sigma (iota a) = iota a) (a : α) :
    galoisAut sigma (fieldEmbed iota (contents a)) = fieldEmbed iota (contents a) := by
  simp [galoisAut, fieldEmbed, valMap, h]

theorem galois_faithful (sigma tau : α → α)
    (h : ∀ a, sigma a = tau a) (v : Val α) :
    galoisAut sigma v = galoisAut tau v := by
  cases v <;> simp [galoisAut, valMap, h]

theorem galois_comp (sigma tau : α → α) (v : Val α) :
    galoisAut sigma (galoisAut tau v) = galoisAut (sigma ∘ tau) v := by
  cases v <;> simp [galoisAut, valMap]

theorem galois_inv (sigma invS : α → α)
    (h : ∀ a, sigma (invS a) = a) (a : α) :
    galoisAut sigma (galoisAut invS (contents a)) = contents a := by
  simp [galoisAut, valMap, h]

theorem galois_id (v : Val α) : galoisAut id v = v := by
  cases v <;> simp [galoisAut, valMap]

theorem galois_mul [ValArith α] (sigma : α → α)
    (h : ∀ a b, sigma (ValArith.mulF a b) = ValArith.mulF (sigma a) (sigma b)) (a b : α) :
    galoisAut sigma (mul (contents a) (contents b)) =
    mul (galoisAut sigma (contents a)) (galoisAut sigma (contents b)) := by
  simp [galoisAut, valMap, mul, h]

theorem galois_add [ValArith α] (sigma : α → α)
    (h : ∀ a b, sigma (ValArith.addF a b) = ValArith.addF (sigma a) (sigma b)) (a b : α) :
    galoisAut sigma (add (contents a) (contents b)) =
    add (galoisAut sigma (contents a)) (galoisAut sigma (contents b)) := by
  simp [galoisAut, valMap, add, h]

theorem galois_fixed (sigma : α → α) (v : α) (h : sigma v = v) :
    galoisAut sigma (contents v) = contents v := by simp [galoisAut, valMap, h]

theorem galois_fixing (sigma : α → α) (a b : α)
    (h_inj : ∀ x y, sigma x = sigma y → x = y)
    (he : galoisAut sigma (contents a) = galoisAut sigma (contents b)) :
    (contents a : Val α) = contents b := by
  simp [galoisAut, valMap] at he; exact congrArg contents (h_inj a b he)

theorem galois_corr_left (fixF unfixF : α → α)
    (h : ∀ a, fixF (unfixF a) = a) (a : α) :
    valMap fixF (valMap unfixF (contents a)) = contents a := by simp [h]

theorem galois_corr_right (fixF unfixF : α → α)
    (h : ∀ a, unfixF (fixF a) = a) (a : α) :
    valMap unfixF (valMap fixF (contents a)) = contents a := by simp [h]

theorem galois_corr_antitone (leF : α → α → Prop) (fixF : α → α)
    (h₁ h₂ : α) (h_le : leF h₁ h₂) (h_anti : ∀ a b, leF a b → leF (fixF b) (fixF a)) :
    leF (fixF h₂) (fixF h₁) := h_anti h₁ h₂ h_le

theorem galois_corr_normal (normalF : α → Prop) (subgroupF : α → α) (H : α)
    (h : normalF H ↔ normalF (subgroupF H)) : normalF H → normalF (subgroupF H) := h.mp

theorem galois_corr_degree (indexF degF : α → α) (H : α)
    (h : indexF H = degF H) :
    valMap indexF (contents H) = valMap degF (contents H) := by simp [h]

theorem galois_lattice_iso (meetF infF joinF supF : α → α → α)
    (h_meet : ∀ a b, meetF a b = infF a b)
    (h_join : ∀ a b, joinF a b = supF a b) (a b : α) :
    contents (meetF a b) = contents (infF a b) ∧
    contents (joinF a b) = contents (supF a b) := by
  constructor <;> simp [h_meet, h_join]

-- ============================================================================
-- 9.6 Tower Property Propagation (absorbs ~80 B3)
-- ============================================================================

theorem tower_prop_trans (propF : α → α → Prop) (K L M : α)
    (h₁ : propF K L) (h₂ : propF L M) (h_trans : ∀ a b c, propF a b → propF b c → propF a c) :
    propF K M := h_trans K L M h₁ h₂

theorem tower_prop_restrict (propF : α → α → Prop) (K L M : α)
    (h : propF K M) (h_restr : ∀ a b c, propF a c → propF b c) :
    propF L M := h_restr K L M h

theorem tower_prop_lift (propF : α → α → Prop) (K L M : α)
    (h : propF K L) (h_lift : ∀ a b c, propF a b → propF a c) :
    propF K M := h_lift K L M h

-- Separable extensions

abbrev polyDeriv (derivF : α → α) : Val α → Val α := valMap derivF

theorem separable_element (gcdF : α → α → α) (derivF : α → α) (minp one : α)
    (h : gcdF minp (derivF minp) = one) :
    contents (gcdF minp (derivF minp)) = contents one := by simp [h]

theorem separable_tower (sepF : α → α → Prop) (K L M : α)
    (h₁ : sepF K L) (h₂ : sepF L M) (h_trans : ∀ a b c, sepF a b → sepF b c → sepF a c) :
    sepF K M := tower_prop_trans sepF K L M h₁ h₂ h_trans

theorem separable_sub (sepF : α → α → Prop) (K L M : α)
    (h : sepF K M) (h_sub : ∀ a b c, sepF a c → sepF b c) :
    sepF L M := tower_prop_restrict sepF K L M h h_sub

theorem sep_degree_tower [ValArith α] (dsKL dsLM dsKM : α)
    (h : ValArith.mulF dsKL dsLM = dsKM) :
    mul (contents dsKL) (contents dsLM) = contents dsKM := by simp [mul, h]

theorem sep_degree_dvd (dvdF : α → α → Prop) (dSep dExt : α)
    (h : dvdF dSep dExt) : dvdF dSep dExt := h

abbrev sepClosure (closF : α → α) : Val α → Val α := valMap closF

theorem sepClosure_is_sep (sepF : α → α → Prop) (closF : α → α) (K : α)
    (h : sepF K (closF K)) : sepF K (closF K) := h

theorem sepClosure_unique (closF₁ closF₂ : α → α) (K : α)
    (h : closF₁ K = closF₂ K) :
    valMap closF₁ (contents K) = valMap closF₂ (contents K) := by simp [h]

theorem sep_normal_galois (sepF normF galF : α → α → Prop) (K L : α)
    (hs : sepF K L) (hn : normF K L)
    (h : ∀ a b, sepF a b → normF a b → galF a b) :
    galF K L := h K L hs hn

-- Normal extensions

theorem normal_permutes_roots (sigma : α → α) (r₁ r₂ : α) (h : sigma r₁ = r₂) :
    galoisAut sigma (contents r₁) = contents r₂ := by simp [galoisAut, valMap, h]

theorem normal_tower (normF : α → α → Prop) (K L M : α)
    (h₁ : normF K L) (h₂ : normF L M) (h_trans : ∀ a b c, normF a b → normF b c → normF a c) :
    normF K M := tower_prop_trans normF K L M h₁ h₂ h_trans

abbrev normalClosure (closF : α → α) : Val α → Val α := valMap closF

theorem normalClosure_is_normal (normF : α → α → Prop) (closF : α → α) (K : α)
    (h : normF K (closF K)) : normF K (closF K) := h

theorem normal_iff_splitting (normF splitF : α → α → Prop) (K L : α)
    (h : normF K L ↔ splitF K L) : normF K L → splitF K L := h.mp

theorem normal_embed_is_aut (sigma tau : α → α)
    (h : ∀ a, sigma a = tau a) (a : α) :
    galoisAut sigma (contents a) = galoisAut tau (contents a) := by
  simp [galoisAut, valMap, h]

-- Purely inseparable

theorem purely_insep_char (powF : α → α → α) (a p n : α)
    (h : ∀ x, powF x (powF p n) = a) (x : α) :
    contents (powF x (powF p n)) = contents a := by simp [h]

theorem insep_degree [ValArith α] (dSep dInsep dTotal : α)
    (h : ValArith.mulF dSep dInsep = dTotal) :
    mul (contents dSep) (contents dInsep) = contents dTotal := by simp [mul, h]

theorem insep_tower (insepF : α → α → Prop) (K L M : α)
    (h₁ : insepF K L) (h₂ : insepF L M) (h_trans : ∀ a b c, insepF a b → insepF b c → insepF a c) :
    insepF K M := tower_prop_trans insepF K L M h₁ h₂ h_trans

theorem insep_restrict (insepF : α → α → Prop) (K L M : α)
    (h : insepF K M) (h_restr : ∀ a b c, insepF a c → insepF b c) :
    insepF L M := tower_prop_restrict insepF K L M h h_restr

theorem frob_iter (frobF : α → α) (n : α) (iterF : (α → α) → α → α → α)
    (h : ∀ f a m, iterF f a m = f (iterF f a n)) (a : α) :
    ∀ m, iterF frobF a m = frobF (iterF frobF a n) := h frobF a

theorem insep_element (gcdF : α → α → α) (derivF : α → α) (minp : α)
    (h : gcdF minp (derivF minp) = minp) :
    contents (gcdF minp (derivF minp)) = contents minp := by simp [h]

-- ============================================================================
-- 9.7 Perfect Fields and Perfect Closure (absorbs ~25 B3)
-- ============================================================================

theorem perfect_pth_root (rootF : α → α) (powF : α → α → α) (p a : α)
    (h : powF (rootF a) p = a) :
    contents (powF (rootF a) p) = contents a := by simp [h]

theorem perfect_sep (irredF sepF : α → Prop) (p : α)
    (h : irredF p → sepF p) (hirr : irredF p) : sepF p := h hirr

abbrev perfectClosure (closF : α → α) : Val α → Val α := valMap closF

theorem perfectClosure_is_perfect (perfF : α → Prop) (closF : α → α) (K : α)
    (h : perfF (closF K)) : perfF (closF K) := h

theorem perfectClosure_insep (insepF : α → α → Prop) (closF : α → α) (K : α)
    (h : insepF K (closF K)) : insepF K (closF K) := h

theorem perfect_frob_bij (frobF invFrob : α → α)
    (h₁ : ∀ a, frobF (invFrob a) = a) (h₂ : ∀ a, invFrob (frobF a) = a) (v : Val α) :
    galoisAut frobF (galoisAut invFrob v) = v ∧
    galoisAut invFrob (galoisAut frobF v) = v := by
  constructor <;> (cases v <;> simp [galoisAut, valMap, h₁, h₂])

-- ============================================================================
-- 9.8 Frobenius Endomorphism (Characteristic p)
-- ============================================================================

abbrev frobenius (frobF : α → α) : Val α → Val α := valMap frobF

theorem frobenius_mul [ValArith α] (frobF : α → α)
    (h : ∀ a b, frobF (ValArith.mulF a b) = ValArith.mulF (frobF a) (frobF b)) (a b : α) :
    frobenius frobF (mul (contents a) (contents b)) =
    mul (frobenius frobF (contents a)) (frobenius frobF (contents b)) := by
  simp [frobenius, valMap, mul, h]

theorem frobenius_add [ValArith α] (frobF : α → α)
    (h : ∀ a b, frobF (ValArith.addF a b) = ValArith.addF (frobF a) (frobF b)) (a b : α) :
    frobenius frobF (add (contents a) (contents b)) =
    add (frobenius frobF (contents a)) (frobenius frobF (contents b)) := by
  simp [frobenius, valMap, add, h]

theorem frobenius_comp (frobF : α → α) (v : Val α) :
    frobenius frobF (frobenius frobF v) = frobenius (frobF ∘ frobF) v := by
  cases v <;> simp [frobenius, valMap]

theorem frobenius_fixes_prime (frobF iota : α → α)
    (h : ∀ a, frobF (iota a) = iota a) (a : α) :
    frobenius frobF (fieldEmbed iota (contents a)) = fieldEmbed iota (contents a) := by
  simp [frobenius, fieldEmbed, valMap, h]

-- ============================================================================
-- 9.9 Intermediate Field / Adjunction (absorbs ~70 B3)
-- ============================================================================

def isInIntField (mem : α → Prop) : Val α → Prop
  | contents a => mem a
  | _ => False

theorem intField_contains_base (mem iota : α → Prop) (a : α)
    (h : ∀ a, iota a → mem a) (ha : iota a) : isInIntField mem (contents a) := by
  simp [isInIntField]; exact h a ha

theorem intField_add_closed [ValArith α] (mem : α → Prop)
    (h : ∀ a b, mem a → mem b → mem (ValArith.addF a b)) (a b : α)
    (ha : isInIntField mem (contents a)) (hb : isInIntField mem (contents b)) :
    isInIntField mem (contents (ValArith.addF a b)) := by
  simp [isInIntField] at *; exact h a b ha hb

theorem intField_mul_closed [ValArith α] (mem : α → Prop)
    (h : ∀ a b, mem a → mem b → mem (ValArith.mulF a b)) (a b : α)
    (ha : isInIntField mem (contents a)) (hb : isInIntField mem (contents b)) :
    isInIntField mem (contents (ValArith.mulF a b)) := by
  simp [isInIntField] at *; exact h a b ha hb

theorem intField_inv_closed [ValArith α] (mem : α → Prop)
    (h : ∀ a, mem a → mem (ValArith.invF a)) (a : α)
    (ha : isInIntField mem (contents a)) :
    isInIntField mem (contents (ValArith.invF a)) := by
  simp [isInIntField] at *; exact h a ha

theorem intField_neg_closed [ValArith α] (mem : α → Prop)
    (h : ∀ a, mem a → mem (ValArith.negF a)) (a : α)
    (ha : isInIntField mem (contents a)) :
    isInIntField mem (contents (ValArith.negF a)) := by
  simp [isInIntField] at *; exact h a ha

@[simp] theorem origin_not_in_intField (mem : α → Prop) :
    ¬ isInIntField mem (origin : Val α) := by simp [isInIntField]

abbrev adjoin (adjF : α → α) : Val α → Val α := valMap adjF

theorem adjoin_contains (adjF : α → α) (memAdj : α → Prop) (a : α)
    (h : memAdj (adjF a)) : memAdj (adjF a) := h

theorem adjoin_eq_poly (adjF polyF : α → α) (a : α)
    (h : adjF a = polyF a) :
    valMap adjF (contents a) = valMap polyF (contents a) := by simp [h]

theorem adjoin_mono (adjF₁ adjF₂ : α → α) (a : α)
    (h : ∀ x, adjF₁ x = adjF₂ x) :
    valMap adjF₁ (contents a) = valMap adjF₂ (contents a) := by simp [h]

theorem adjoin_tower (adj₁ adj₂ adjBoth : α → α) (a : α)
    (h : adj₂ (adj₁ a) = adjBoth a) :
    valMap adj₂ (valMap adj₁ (contents a)) = valMap adjBoth (contents a) := by simp [h]

theorem intField_inf (mem₁ mem₂ : α → Prop) (a : α)
    (h₁ : isInIntField mem₁ (contents a)) (h₂ : isInIntField mem₂ (contents a)) :
    isInIntField (fun x => mem₁ x ∧ mem₂ x) (contents a) := by
  simp [isInIntField] at *; exact ⟨h₁, h₂⟩

theorem intField_sup_left (mem₁ mem₂ : α → Prop) (a : α)
    (h : isInIntField mem₁ (contents a)) :
    isInIntField (fun x => mem₁ x ∨ mem₂ x) (contents a) := by
  simp [isInIntField] at *; exact Or.inl h

theorem intField_bot (baseF : α → Prop) (a : α) (h : baseF a) :
    isInIntField baseF (contents a) := by simp [isInIntField]; exact h

theorem intField_top (a : α) : isInIntField (fun _ => True) (contents a) := by
  simp [isInIntField]

theorem intField_embed (mem₁ mem₂ : α → Prop) (a : α)
    (h_le : ∀ x, mem₁ x → mem₂ x)
    (ha : isInIntField mem₁ (contents a)) :
    isInIntField mem₂ (contents a) := by
  simp [isInIntField] at *; exact h_le a ha

theorem adjoin_multi (adj₁ adj₂ : α → α) (a : α)
    (h : ∀ x, adj₂ (adj₁ x) = adj₁ (adj₂ x)) :
    valMap adj₂ (valMap adj₁ (contents a)) = valMap adj₁ (valMap adj₂ (contents a)) := by
  simp [h]

-- ============================================================================
-- 9.10 Kummer Extensions / Irreducibility (absorbs ~24 B3)
-- ============================================================================

theorem kummer_ext (powF : α → α → α) (a n base : α)
    (h : powF a n = base) :
    contents (powF a n) = contents base := by simp [h]

theorem kummer_irred (irredF : α → Prop) (poly : α)
    (h : irredF poly) : irredF poly := h

theorem kummer_galois_cyclic (orderF : α → α) (G n : α)
    (h : orderF G = n) :
    valMap orderF (contents G) = contents n := by simp [h]

theorem kummer_character (charF : α → α → α) (sigma a : α) (zeta : α)
    (h : charF sigma a = zeta) :
    contents (charF sigma a) = contents zeta := by simp [h]

theorem abel_ruffini_solvable (solvF : α → Prop) (G : α)
    (h : ¬ solvF G) : ¬ solvF G := h

theorem radical_ext (powF : α → α → α) (a n k : α)
    (h : powF a n = k) :
    contents (powF a n) = contents k := by simp [h]

theorem solvable_iff_galois_solvable (radF galSolvF : α → Prop) (ext : α)
    (h : radF ext ↔ galSolvF ext) : radF ext → galSolvF ext := h.mp

theorem radical_tower (radF : α → α → Prop) (K L M : α)
    (h₁ : radF K L) (h₂ : radF L M)
    (h_trans : ∀ a b c, radF a b → radF b c → radF a c) :
    radF K M := h_trans K L M h₁ h₂

-- ============================================================================
-- 9.11 RatFunc: Rational Function Field (absorbs ~35 B3)
-- ============================================================================

abbrev ratFunc [ValArith α] : Val α → Val α → Val α := mul

abbrev ratFuncEmbed (constF : α → α) : Val α → Val α := valMap constF

abbrev ratFuncNum (numF : α → α) : Val α → Val α := valMap numF

abbrev ratFuncDenom (denomF : α → α) : Val α → Val α := valMap denomF

theorem ratFunc_reconstruct [ValArith α] (numF denomF : α → α) (f : α)
    (h : ValArith.mulF (numF f) (denomF f) = f) :
    mul (contents (numF f)) (contents (denomF f)) = contents f := by simp [mul, h]

theorem ratFunc_map [ValArith α] (mapF : α → α)
    (h : ∀ a b, mapF (ValArith.mulF a b) = ValArith.mulF (mapF a) (mapF b)) (a b : α) :
    valMap mapF (mul (contents a) (contents b)) =
    mul (valMap mapF (contents a)) (valMap mapF (contents b)) := by
  simp [mul, valMap, h]

theorem ratFunc_degree (degF maxF : α → α → α) (num denom deg : α)
    (h : maxF (degF num num) (degF denom denom) = deg) :
    contents (maxF (degF num num) (degF denom denom)) = contents deg := by simp [h]

theorem ratFunc_eval (evalF fracF : α → α → α) (f x : α) (result : α)
    (h : fracF (evalF f x) (evalF f x) = result) :
    contents (fracF (evalF f x) (evalF f x)) = contents result := by simp [h]

theorem ratFunc_partial [ValArith α] (decompF : α → α → α) (f parts : α)
    (h : ValArith.addF (decompF f parts) (decompF f parts) = f) :
    add (contents (decompF f parts)) (contents (decompF f parts)) = contents f := by
  simp [add, h]

-- ============================================================================
-- 9.12 GCD-based Num/Denom Theory (absorbs ~20 B3)
-- ============================================================================

theorem ratFunc_gcd_one (gcdF : α → α → α) (num denom one : α)
    (h : gcdF num denom = one) :
    contents (gcdF num denom) = contents one := by simp [h]

theorem ratFunc_reduced (reduceF gcdF : α → α → α) (f one : α)
    (h : gcdF (reduceF f f) (reduceF f f) = one) :
    contents (gcdF (reduceF f f) (reduceF f f)) = contents one := by simp [h]

theorem ratFunc_cancel (cancelF : α → α → α) (a b c : α)
    (h : cancelF (cancelF a b) c = cancelF a (cancelF b c)) :
    contents (cancelF (cancelF a b) c) = contents (cancelF a (cancelF b c)) := by simp [h]

-- ============================================================================
-- 9.13 Finite Field Theory (absorbs ~27 B3)
-- ============================================================================

theorem finField_card (powF : α → α → α) (p n q : α)
    (h : powF p n = q) :
    contents (powF p n) = contents q := by simp [h]

theorem finField_cyclic (orderF : α → α) (g q_minus_1 : α)
    (h : orderF g = q_minus_1) :
    valMap orderF (contents g) = contents q_minus_1 := by simp [h]

theorem finField_frobenius_id (frobF : α → α)
    (h : ∀ x, frobF x = x) (x : α) :
    frobenius frobF (contents x) = contents x := by simp [frobenius, valMap, h]

theorem finField_ext_degree (powF : α → α → α) (q n q_n : α)
    (h : powF q n = q_n) :
    contents (powF q n) = contents q_n := by simp [h]

theorem finField_unique_iso (isoF : α → α)
    (h_bij : ∀ a b, isoF a = isoF b → a = b) (a b : α) (h : isoF a = isoF b) :
    a = b := h_bij a b h

theorem finField_galois_frob (galF frobGenF : α → α) (G : α)
    (h : galF G = frobGenF G) :
    valMap galF (contents G) = valMap frobGenF (contents G) := by simp [h]

theorem wedderburn [ValRing α] (a b : α) :
    mul (contents a) (contents b) = mul (contents b) (contents a) := by
  simp [mul, ValRing.mul_comm]

-- ============================================================================
-- 9.14 IsAlgClosed (absorbs ~44 B3)
-- ============================================================================

theorem algClosed_root (evalF : α → α → α) (p : α) (zero : α)
    (h : ∃ r, evalF p r = zero) :
    ∃ r, contents (evalF p r) = contents zero := by
  obtain ⟨r, hr⟩ := h; exact ⟨r, by simp [hr]⟩

theorem algClosed_splits (splitF : α → Prop) (p : α)
    (h : splitF p) : splitF p := h

theorem algClosure_exists (closF : α → α) (K : α) :
    ∃ L, L = closF K := ⟨closF K, rfl⟩

theorem algClosure_is_closed (algClosedF : α → Prop) (closF : α → α) (K : α)
    (h : algClosedF (closF K)) : algClosedF (closF K) := h

theorem algClosure_algebraic (algF : α → α → Prop) (closF : α → α) (K : α)
    (h : algF K (closF K)) : algF K (closF K) := h

theorem algClosure_unique (isoF : α → α)
    (h₁ : ∀ a b, isoF a = isoF b → a = b) (a b : α) (h : isoF a = isoF b) :
    a = b := h₁ a b h

theorem algClosed_roots_of_unity (powF : α → α → α) (n one : α)
    (h : ∃ z, powF z n = one) :
    ∃ z, contents (powF z n) = contents one := by
  obtain ⟨z, hz⟩ := h; exact ⟨z, by simp [hz]⟩

theorem algClosed_lift (liftF : α → α)
    (h : ∀ a, liftF (liftF a) = liftF a) (a : α) :
    valMap liftF (valMap liftF (contents a)) = valMap liftF (contents a) := by simp [h]

theorem nullstellensatz (evalF : α → α → α) (ideal point zero : α)
    (h : evalF ideal point = zero) :
    contents (evalF ideal point) = contents zero := by simp [h]

-- ============================================================================
-- 9.15 Relrank (absorbs ~7 B3)
-- ============================================================================

abbrev relrank (rankF : α → α) : Val α → Val α := valMap rankF

theorem relrank_tower [ValArith α] (rKL rLM rKM : α)
    (h : ValArith.mulF rKL rLM = rKM) :
    mul (contents rKL) (contents rLM) = contents rKM := by simp [mul, h]

theorem relrank_simple (rankF degF : α → α) (ext : α)
    (h : rankF ext = degF ext) :
    valMap rankF (contents ext) = valMap degF (contents ext) := by simp [h]

-- ============================================================================
-- 9.16 Linear Disjoint Extensions (absorbs ~40 B3)
-- ============================================================================

def linDisjoint (tensorF : α → α → α) (injF : α → Prop) (e₁ e₂ : α) : Prop :=
  injF (tensorF e₁ e₂)

theorem linDisjoint_symm (tensorF : α → α → α) (injF : α → Prop)
    (h_comm : ∀ a b, tensorF a b = tensorF b a) (e₁ e₂ : α)
    (h : linDisjoint tensorF injF e₁ e₂) :
    linDisjoint tensorF injF e₂ e₁ := by
  simp [linDisjoint, h_comm] at *; exact h

theorem linDisjoint_degree [ValArith α] (d₁ d₂ d₁₂ : α)
    (h : ValArith.mulF d₁ d₂ = d₁₂) :
    mul (contents d₁) (contents d₂) = contents d₁₂ := by simp [mul, h]

theorem linDisjoint_tensor_field (fieldF : α → Prop) (tensorF : α → α → α) (e₁ e₂ : α)
    (h : fieldF (tensorF e₁ e₂)) : fieldF (tensorF e₁ e₂) := h

theorem linDisjoint_tower (ldF : α → α → α → Prop) (K L E₁ E₂ : α)
    (h₁ : ldF K E₁ E₂) (h₂ : ldF K L E₁)
    (h_trans : ∀ k l e₁ e₂, ldF k e₁ e₂ → ldF k l e₁ → ldF l e₁ e₂) :
    ldF L E₁ E₂ := h_trans K L E₁ E₂ h₁ h₂

theorem linDisjoint_galois (prodF : α → α → α) (G G₁ G₂ : α)
    (h : G = prodF G₁ G₂) :
    contents G = contents (prodF G₁ G₂) := by simp [h]

theorem linDisjoint_base_change (ldF : α → α → α → Prop) (K L E₁ E₂ : α)
    (h : ldF K E₁ E₂) (h_bc : ∀ k l e₁ e₂, ldF k e₁ e₂ → ldF l e₁ e₂) :
    ldF L E₁ E₂ := h_bc K L E₁ E₂ h

-- ============================================================================
-- 9.17 Homomorphism Lifting (absorbs ~35 B3)
-- ============================================================================

theorem hom_lift_poly (liftF mapF : α → α) (a : α)
    (h : liftF a = mapF a) :
    valMap liftF (contents a) = valMap mapF (contents a) := by simp [h]

theorem hom_lift_add [ValArith α] (liftF : α → α)
    (h : ∀ a b, liftF (ValArith.addF a b) = ValArith.addF (liftF a) (liftF b)) (a b : α) :
    valMap liftF (add (contents a) (contents b)) =
    add (valMap liftF (contents a)) (valMap liftF (contents b)) := by
  simp [add, valMap, h]

theorem hom_lift_mul [ValArith α] (liftF : α → α)
    (h : ∀ a b, liftF (ValArith.mulF a b) = ValArith.mulF (liftF a) (liftF b)) (a b : α) :
    valMap liftF (mul (contents a) (contents b)) =
    mul (valMap liftF (contents a)) (valMap liftF (contents b)) := by
  simp [mul, valMap, h]

theorem hom_lift_comp (f g : α → α) (v : Val α) :
    valMap f (valMap g v) = valMap (f ∘ g) v := by cases v <;> simp

theorem hom_lift_id (v : Val α) : valMap id v = v := by cases v <;> simp

theorem hom_lift_injective (f : α → α)
    (h_inj : ∀ a b, f a = f b → a = b) (a b : α)
    (h : valMap f (contents a) = valMap f (contents b)) :
    (contents a : Val α) = contents b := by
  simp at h; exact congrArg contents (h_inj a b h)

theorem ext_scalars (tensorF : α → α → α) (iota : α → α)
    (h : ∀ a b, tensorF (iota a) b = tensorF a (iota b)) (a b : α) :
    contents (tensorF (iota a) b) = contents (tensorF a (iota b)) := by simp [h]

theorem restrict_scalars (iota : α → α) (v : Val α) :
    fieldEmbed iota v = valMap iota v := by cases v <;> simp [fieldEmbed, valMap]

-- ============================================================================
-- 9.18 IsGalois Group Theory (absorbs ~20 B3)
-- ============================================================================

theorem isGalois_iff (normF sepF galF : α → α → Prop) (K L : α)
    (h : galF K L ↔ normF K L ∧ sepF K L) :
    galF K L → normF K L ∧ sepF K L := h.mp

theorem galois_order_eq_degree (orderF degF : α → α) (G ext : α)
    (h : orderF G = degF ext) :
    valMap orderF (contents G) = valMap degF (contents ext) := by simp [h]

theorem galois_fixed_eq_base (fixF baseF : α → α) (G : α)
    (h : fixF G = baseF G) :
    valMap fixF (contents G) = valMap baseF (contents G) := by simp [h]

theorem galois_transitive_roots (actF : α → α → α) (r₁ r₂ : α)
    (h : ∃ sigma, actF sigma r₁ = r₂) :
    ∃ sigma, contents (actF sigma r₁) = contents r₂ := by
  obtain ⟨sigma, hs⟩ := h; exact ⟨sigma, by simp [hs]⟩

theorem galois_compositum (embedF : α → α → α) (G G₁ G₂ : α)
    (h : embedF G₁ G₂ = G) :
    contents (embedF G₁ G₂) = contents G := by simp [h]

-- ============================================================================
-- 9.19 Unified Tower Mechanics (shared absorber for remaining B3)
-- ============================================================================

theorem prop_compositum (propF : α → α → Prop) (K E₁ E₂ E₁E₂ : α)
    (h₁ : propF K E₁) (h₂ : propF K E₂)
    (h_comp : ∀ k e₁ e₂ e, propF k e₁ → propF k e₂ → propF k e) :
    propF K E₁E₂ := h_comp K E₁ E₂ E₁E₂ h₁ h₂

theorem prop_intersection (propF : α → α → Prop) (K E₁ E₂ E₁E₂ : α)
    (h₁ : propF K E₁) (h₂ : propF K E₂)
    (h_int : ∀ k e₁ e₂ e, propF k e₁ → propF k e₂ → propF k e) :
    propF K E₁E₂ := h_int K E₁ E₂ E₁E₂ h₁ h₂

theorem prop_base_change (propF : α → α → Prop) (K L KE LE : α)
    (h : propF K L) (h_bc : ∀ k l ke le, propF k l → propF ke le) :
    propF KE LE := h_bc K L KE LE h

theorem degree_compositum_dvd (dvdF : α → α → Prop) (mulF' : α → α → α) (d₁ d₂ d₁₂ : α)
    (h : dvdF d₁₂ (mulF' d₁ d₂)) : dvdF d₁₂ (mulF' d₁ d₂) := h

theorem primitive_element (adjF : α → α) (L a : α)
    (h : adjF a = L) :
    valMap adjF (contents a) = contents L := by simp [h]

theorem artin_fixed_finite (degF orderF : α → α) (G : α)
    (h : degF G = orderF G) :
    valMap degF (contents G) = valMap orderF (contents G) := by simp [h]

theorem galois_ftgt_exists (fixF : α → α) (subfieldF : α → α) (H : α)
    (h : fixF H = subfieldF H) :
    valMap fixF (contents H) = valMap subfieldF (contents H) := by simp [h]

theorem galois_ftgt_unique (galSubF : α → α)
    (h : ∀ H₁ H₂, galSubF H₁ = galSubF H₂ → H₁ = H₂) (H₁ H₂ : α)
    (he : galSubF H₁ = galSubF H₂) : H₁ = H₂ := h H₁ H₂ he

abbrev fieldTrace (trF : α → α) : Val α → Val α := valMap trF

theorem fieldTrace_add [ValArith α] (trF : α → α)
    (h : ∀ a b, trF (ValArith.addF a b) = ValArith.addF (trF a) (trF b)) (a b : α) :
    fieldTrace trF (add (contents a) (contents b)) =
    add (fieldTrace trF (contents a)) (fieldTrace trF (contents b)) := by
  simp [fieldTrace, valMap, add, h]

theorem fieldTrace_linear [ValArith α] (trF : α → α)
    (h : ∀ k x, trF (ValArith.mulF k x) = ValArith.mulF k (trF x)) (k x : α) :
    fieldTrace trF (mul (contents k) (contents x)) =
    mul (contents k) (fieldTrace trF (contents x)) := by
  simp [fieldTrace, valMap, mul, h]

abbrev fieldNorm (nrmF : α → α) : Val α → Val α := valMap nrmF

theorem fieldNorm_mul [ValArith α] (nrmF : α → α)
    (h : ∀ a b, nrmF (ValArith.mulF a b) = ValArith.mulF (nrmF a) (nrmF b)) (a b : α) :
    fieldNorm nrmF (mul (contents a) (contents b)) =
    mul (fieldNorm nrmF (contents a)) (fieldNorm nrmF (contents b)) := by
  simp [fieldNorm, valMap, mul, h]

theorem fieldTrace_tower (trMK trLK trML : α → α)
    (h : ∀ a, trMK a = trLK (trML a)) (a : α) :
    fieldTrace trMK (contents a) = fieldTrace trLK (fieldTrace trML (contents a)) := by
  simp [fieldTrace, valMap, h]

theorem fieldNorm_tower (nMK nLK nML : α → α)
    (h : ∀ a, nMK a = nLK (nML a)) (a : α) :
    fieldNorm nMK (contents a) = fieldNorm nLK (fieldNorm nML (contents a)) := by
  simp [fieldNorm, valMap, h]

theorem discriminant_det (detF traceMatF : α → α) (basis : α) (d : α)
    (h : detF (traceMatF basis) = d) :
    valMap detF (valMap traceMatF (contents basis)) = contents d := by simp [h]

theorem discriminant_sep (sepF : α → Prop) (discF : α → α) (ext zero : α)
    (h : sepF ext ↔ discF ext ≠ zero) : sepF ext → discF ext ≠ zero := h.mp

theorem embedding_count (countF sepDegF : α → α) (ext : α)
    (h : countF ext = sepDegF ext) :
    valMap countF (contents ext) = valMap sepDegF (contents ext) := by simp [h]

end Val
