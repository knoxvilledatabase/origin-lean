/-
Extracted from Algebra/Group/EvenFunction.lean
Genuine: 24 of 24 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Even and odd functions

We define even functions `α → β` assuming `α` has a negation, and odd functions assuming both `α`
and `β` have negation.

These definitions are `Function.Even` and `Function.Odd`; and they are `protected`, to avoid
conflicting with the root-level definitions `Even` and `Odd` (which, for functions, mean that the
function takes even resp. odd _values_, a wholly different concept).
-/

assert_not_exists Module.IsTorsionFree NoZeroSMulDivisors

namespace Function

variable {α β : Type*} [Neg α]

protected def Even (f : α → β) : Prop := ∀ a, f (-a) = f a

protected def Odd [Neg β] (f : α → β) : Prop := ∀ a, f (-a) = -(f a)

lemma Even.const (b : β) : Function.Even (fun _ : α ↦ b) := fun _ ↦ rfl

lemma Even.zero [Zero β] : Function.Even (fun (_ : α) ↦ (0 : β)) := Even.const 0

lemma Odd.zero [NegZeroClass β] : Function.Odd (fun (_ : α) ↦ (0 : β)) := fun _ ↦ neg_zero.symm

section composition

variable {γ : Type*}

lemma Even.left_comp {g : α → β} (hg : g.Even) (f : β → γ) : (f ∘ g).Even :=
  (congr_arg f <| hg ·)

lemma Even.comp_odd [Neg β] {f : β → γ} (hf : f.Even) {g : α → β} (hg : g.Odd) :
    (f ∘ g).Even := by
  intro a
  simp only [comp_apply, hg a, hf _]

lemma Odd.comp_odd [Neg β] [Neg γ] {f : β → γ} (hf : f.Odd) {g : α → β} (hg : g.Odd) :
    (f ∘ g).Odd := by
  intro a
  simp only [comp_apply, hg a, hf _]

end composition

lemma Even.add [Add β] {f g : α → β} (hf : f.Even) (hg : g.Even) : (f + g).Even := by
  intro a
  simp only [hf a, hg a, Pi.add_apply]

lemma Odd.add [SubtractionCommMonoid β] {f g : α → β} (hf : f.Odd) (hg : g.Odd) : (f + g).Odd := by
  intro a
  simp only [hf a, hg a, Pi.add_apply, neg_add]

section smul

variable {γ : Type*} {f : α → β} {g : α → γ}

lemma Even.smul_even [SMul β γ] (hf : f.Even) (hg : g.Even) : (f • g).Even := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a]

lemma Even.smul_odd [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hf : f.Even) (hg : g.Odd) :
    (f • g).Odd := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg]

lemma Odd.smul_even [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Even) :
    (f • g).Odd := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, neg_smul]

lemma Odd.smul_odd [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Odd) :
    (f • g).Even := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg, neg_smul, neg_neg]

lemma Even.const_smul [SMul β γ] (hg : g.Even) (r : β) : (r • g).Even := by
  intro a
  simp only [Pi.smul_apply, hg a]

lemma Odd.const_smul [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hg : g.Odd) (r : β) :
    (r • g).Odd := by
  intro a
  simp only [Pi.smul_apply, hg a, smul_neg]

end smul

section mul

variable {R : Type*} [Mul R] {f g : α → R}

lemma Even.mul_even (hf : f.Even) (hg : g.Even) : (f * g).Even := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a]

lemma Even.mul_odd [HasDistribNeg R] (hf : f.Even) (hg : g.Odd) : (f * g).Odd := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg]

lemma Odd.mul_even [HasDistribNeg R] (hf : f.Odd) (hg : g.Even) : (f * g).Odd := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, neg_mul]

lemma Odd.mul_odd [HasDistribNeg R] (hf : f.Odd) (hg : g.Odd) : (f * g).Even := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg, neg_mul, neg_neg]

end mul

section torsionfree

variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

lemma zero_of_even_and_odd [Neg α] (he : f.Even) (ho : f.Odd) : f = 0 := by
  ext r
  rw [Pi.zero_apply, ← neg_eq_self, ← ho, he]

lemma Odd.finset_sum_eq_zero [InvolutiveNeg α] {f : α → β} (hf : f.Odd) {s : Finset α}
    (hs : Finset.map (Equiv.neg α).toEmbedding s = s) :
    s.sum f = 0 := by
  simpa [neg_eq_self, funext hf, hs] using (Finset.sum_map s (Equiv.neg α).toEmbedding f).symm

lemma Odd.sum_eq_zero [Fintype α] [InvolutiveNeg α] {f : α → β} (hf : f.Odd) : ∑ a, f a = 0 :=
  hf.finset_sum_eq_zero <| Finset.map_univ_equiv (Equiv.neg α)

lemma Odd.map_zero [NegZeroClass α] (hf : f.Odd) : f 0 = 0 := by simp [← neg_eq_self, ← hf 0]

end torsionfree

end Function
