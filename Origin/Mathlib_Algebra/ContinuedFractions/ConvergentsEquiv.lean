/-
Extracted from Algebra/ContinuedFractions/ConvergentsEquiv.lean
Genuine: 13 of 14 | Dissolved: 1 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equivalence of Recursive and Direct Computations of Convergents of Generalized Continued Fractions

## Summary

We show the equivalence of two computations of convergents (recurrence relation (`convs`) vs.
direct evaluation (`convs'`)) for generalized continued fractions
(`GenContFract`s) on linear ordered fields. We follow the proof from
[hardy2008introduction], Chapter 10. Here's a sketch:

Let `c` be a continued fraction `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`, visually:
$$
  c = h + \dfrac{a_0}
                {b_0 + \dfrac{a_1}
                             {b_1 + \dfrac{a_2}
                                          {b_2 + \dfrac{a_3}
                                                       {b_3 + \dots}}}}
$$
One can compute the convergents of `c` in two ways:
1. Directly evaluating the fraction described by `c` up to a given `n` (`convs'`)
2. Using the recurrence (`convs`):
  - `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
  - `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

To show the equivalence of the computations in the main theorem of this file
`convs_eq_convs'`, we proceed by induction. The case `n = 0` is trivial.

For `n + 1`, we first "squash" the `n + 1`th position of `c` into the `n`th position to obtain
another continued fraction
  `c' := [h; (a₀, b₀),..., (aₙ-₁, bₙ-₁), (aₙ, bₙ + aₙ₊₁ / bₙ₊₁), (aₙ₊₁, bₙ₊₁),...]`.
This squashing process is formalised in section `Squash`. Note that directly evaluating `c` up to
position `n + 1` is equal to evaluating `c'` up to `n`. This is shown in lemma
`succ_nth_conv'_eq_squashGCF_nth_conv'`.

By the inductive hypothesis, the two computations for the `n`th convergent of `c` coincide.
So all that is left to show is that the recurrence relation for `c` at `n + 1` and `c'` at
`n` coincide. This can be shown by another induction.
The corresponding lemma in this file is `succ_nth_conv_eq_squashGCF_nth_conv`.

## Main Theorems

- `GenContFract.convs_eq_convs'` shows the equivalence under a strict positivity restriction
  on the sequence.
- `ContFract.convs_eq_convs'` shows the equivalence for regular continued fractions.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction
- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]

## Tags

fractions, recurrence, equivalence
-/

variable {K : Type*} {n : ℕ}

namespace GenContFract

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

section Squash

/-!
We will show the equivalence of the computations by induction. To make the induction work, we need
to be able to *squash* the nth and (n + 1)th value of a sequence. This squashing itself and the
lemmas about it are not very interesting. As a reader, you hence might want to skip this section.
-/

section WithDivisionRing

variable [DivisionRing K]

def squashSeq (s : Stream'.Seq <| Pair K) (n : ℕ) : Stream'.Seq (Pair K) :=
  match Prod.mk (s.get? n) (s.get? (n + 1)) with
  | ⟨some gp_n, some gp_succ_n⟩ =>
    Stream'.Seq.nats.zipWith
      -- return the squashed value at position `n`; otherwise, do nothing.
      (fun n' gp => if n' = n then ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ else gp) s
  | _ => s

/-! We now prove some simple lemmas about the squashed sequence -/

theorem squashSeq_eq_self_of_terminated (terminatedAt_succ_n : s.TerminatedAt (n + 1)) :
    squashSeq s n = s := by
  change s.get? (n + 1) = none at terminatedAt_succ_n
  cases s_nth_eq : s.get? n <;> simp only [*, squashSeq]

theorem squashSeq_nth_of_not_terminated {gp_n gp_succ_n : Pair K} (s_nth_eq : s.get? n = some gp_n)
    (s_succ_nth_eq : s.get? (n + 1) = some gp_succ_n) :
    (squashSeq s n).get? n = some ⟨gp_n.a, gp_n.b + gp_succ_n.a / gp_succ_n.b⟩ := by
  simp [*, squashSeq]

theorem squashSeq_nth_of_lt {m : ℕ} (m_lt_n : m < n) : (squashSeq s n).get? m = s.get? m := by
  cases s_succ_nth_eq : s.get? (n + 1) with
  | none => rw [squashSeq_eq_self_of_terminated s_succ_nth_eq]
  | some =>
    obtain ⟨gp_n, s_nth_eq⟩ : ∃ gp_n, s.get? n = some gp_n :=
      s.ge_stable n.le_succ s_succ_nth_eq
    simp [*, squashSeq, m_lt_n.ne]

theorem squashSeq_succ_n_tail_eq_squashSeq_tail_n :
    (squashSeq s (n + 1)).tail = squashSeq s.tail n := by
  cases s_succ_succ_nth_eq : s.get? (n + 2) with
  | none =>
    cases s_succ_nth_eq : s.get? (n + 1) <;>
      simp only [squashSeq, Stream'.Seq.get?_tail, s_succ_nth_eq, s_succ_succ_nth_eq]
  | some gp_succ_succ_n =>
    obtain ⟨gp_succ_n, s_succ_nth_eq⟩ : ∃ gp_succ_n, s.get? (n + 1) = some gp_succ_n :=
      s.ge_stable (n + 1).le_succ s_succ_succ_nth_eq
    -- apply extensionality with `m` and continue by cases `m = n`.
    ext1 m
    rcases Decidable.em (m = n) with m_eq_n | m_ne_n
    · simp [*, squashSeq]
    · cases s_succ_mth_eq : s.get? (m + 1)
      · simp only [*, squashSeq, Stream'.Seq.get?_tail, Stream'.Seq.get?_zipWith,
          Option.map₂_none_right]
      · simp [*, squashSeq]

theorem succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq :
    convs'Aux s (n + 2) = convs'Aux (squashSeq s n) (n + 1) := by
  cases s_succ_nth_eq : s.get? <| n + 1 with
  | none =>
    rw [squashSeq_eq_self_of_terminated s_succ_nth_eq,
      convs'Aux_stable_step_of_terminated s_succ_nth_eq]
  | some gp_succ_n =>
    induction n generalizing s gp_succ_n with
    | zero =>
      obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head :=
        s.ge_stable zero_le_one s_succ_nth_eq
      have : (squashSeq s 0).head = some ⟨gp_head.a, gp_head.b + gp_succ_n.a / gp_succ_n.b⟩ :=
        squashSeq_nth_of_not_terminated s_head_eq s_succ_nth_eq
      simp_all [convs'Aux, Stream'.Seq.head, Stream'.Seq.get?_tail]
    | succ m IH =>
      obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head :=
        s.ge_stable (m + 2).zero_le s_succ_nth_eq
      suffices
        gp_head.a / (gp_head.b + convs'Aux s.tail (m + 2)) =
          convs'Aux (squashSeq s (m + 1)) (m + 2)
        by simpa only [convs'Aux, s_head_eq]
      have : (squashSeq s (m + 1)).head = some gp_head :=
        (squashSeq_nth_of_lt m.succ_pos).trans s_head_eq
      simp_all [convs'Aux, squashSeq_succ_n_tail_eq_squashSeq_tail_n]

/-! Let us now lift the squashing operation to gcfs. -/

def squashGCF (g : GenContFract K) : ℕ → GenContFract K
  | 0 =>
    match g.s.get? 0 with
    | none => g
    | some gp => ⟨g.h + gp.a / gp.b, g.s⟩
  | n + 1 => ⟨g.h, squashSeq g.s n⟩

/-! Again, we derive some simple lemmas that are not really of interest. This time for the
squashed gcf. -/

theorem squashGCF_eq_self_of_terminated (terminatedAt_n : TerminatedAt g n) :
    squashGCF g n = g := by
  cases n with
  | zero =>
    change g.s.get? 0 = none at terminatedAt_n
    simp only [squashGCF, terminatedAt_n]
  | succ =>
    cases g
    simp only [squashGCF, mk.injEq, true_and]
    exact squashSeq_eq_self_of_terminated terminatedAt_n

theorem squashGCF_nth_of_lt {m : ℕ} (m_lt_n : m < n) :
    (squashGCF g (n + 1)).s.get? m = g.s.get? m := by
  simp only [squashGCF, squashSeq_nth_of_lt m_lt_n]

theorem succ_nth_conv'_eq_squashGCF_nth_conv' :
    g.convs' (n + 1) = (squashGCF g n).convs' n := by
  cases n with
  | zero =>
    cases g_s_head_eq : g.s.get? 0 <;>
      simp [g_s_head_eq, squashGCF, convs', convs'Aux, Stream'.Seq.head]
  | succ =>
    simp only [succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq, convs',
      squashGCF]

theorem contsAux_eq_contsAux_squashGCF_of_le {m : ℕ} :
    m ≤ n → contsAux g m = (squashGCF g n).contsAux m :=
  Nat.strong_induction_on m
    (by
      clear m
      intro m IH m_le_n
      rcases m with - | m'
      · rfl
      · rcases n with - | n'
        · exact (m'.not_succ_le_zero m_le_n).elim
        -- 1 ≰ 0
        · rcases m' with - | m''
          · rfl
          · -- get some inequalities to instantiate the IH for m'' and m'' + 1
            have m'_lt_n : m'' + 1 < n' + 1 := m_le_n
            have succ_m''th_contsAux_eq := IH (m'' + 1) (lt_add_one (m'' + 1)) m'_lt_n.le
            have : m'' < m'' + 2 := lt_add_of_pos_right m'' zero_lt_two
            have m''th_contsAux_eq := IH m'' this (le_trans this.le m_le_n)
            have : (squashGCF g (n' + 1)).s.get? m'' = g.s.get? m'' :=
              squashGCF_nth_of_lt (Nat.succ_lt_succ_iff.mp m'_lt_n)
            simp [contsAux, succ_m''th_contsAux_eq, m''th_contsAux_eq, this])

end WithDivisionRing

-- DISSOLVED: succ_nth_conv_eq_squashGCF_nth_conv

end Squash

theorem convs_eq_convs' [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (s_pos : ∀ {gp : Pair K} {m : ℕ}, m < n → g.s.get? m = some gp → 0 < gp.a ∧ 0 < gp.b) :
    g.convs n = g.convs' n := by
  induction n generalizing g with
  | zero => simp
  | succ n IH =>
    let g' := squashGCF g n
    -- first replace the rhs with the squashed computation
    suffices g.convs (n + 1) = g'.convs' n by
      rwa [succ_nth_conv'_eq_squashGCF_nth_conv']
    rcases Decidable.em (TerminatedAt g n) with terminatedAt_n | not_terminatedAt_n
    · have g'_eq_g : g' = g := squashGCF_eq_self_of_terminated terminatedAt_n
      rw [convs_stable_of_terminated n.le_succ terminatedAt_n, g'_eq_g, IH _]
      intro _ _ m_lt_n s_mth_eq
      exact s_pos (Nat.lt_succ_of_lt m_lt_n) s_mth_eq
    · suffices g.convs (n + 1) = g'.convs n by
        -- invoke the IH for the squashed gcf
        rwa [← IH]
        intro gp' m m_lt_n s_mth_eq'
        -- case distinction on m + 1 = n or m + 1 < n
        rcases m_lt_n with n | succ_m_lt_n
        · -- the difficult case at the squashed position: we first obtain the values from
          -- the sequence
          obtain ⟨gp_succ_m, s_succ_mth_eq⟩ : ∃ gp_succ_m, g.s.get? (m + 1) = some gp_succ_m :=
            Option.ne_none_iff_exists'.mp not_terminatedAt_n
          obtain ⟨gp_m, mth_s_eq⟩ : ∃ gp_m, g.s.get? m = some gp_m :=
            g.s.ge_stable m.le_succ s_succ_mth_eq
          -- we then plug them into the recurrence
          suffices 0 < gp_m.a ∧ 0 < gp_m.b + gp_succ_m.a / gp_succ_m.b by
            have ot : g'.s.get? m = some ⟨gp_m.a, gp_m.b + gp_succ_m.a / gp_succ_m.b⟩ :=
              squashSeq_nth_of_not_terminated mth_s_eq s_succ_mth_eq
            grind
          have m_lt_n : m < m.succ := Nat.lt_succ_self m
          refine ⟨(s_pos (Nat.lt_succ_of_lt m_lt_n) mth_s_eq).left, ?_⟩
          refine add_pos (s_pos (Nat.lt_succ_of_lt m_lt_n) mth_s_eq).right ?_
          have : 0 < gp_succ_m.a ∧ 0 < gp_succ_m.b := s_pos (lt_add_one <| m + 1) s_succ_mth_eq
          exact div_pos this.left this.right
        · -- the easy case: before the squashed position, nothing changes
          refine s_pos (Nat.lt_succ_of_lt <| Nat.lt_succ_of_lt succ_m_lt_n) ?_
          exact Eq.trans (squashGCF_nth_of_lt succ_m_lt_n).symm s_mth_eq'
      -- now the result follows from the fact that the convergents coincide at the squashed position
      -- as established in `succ_nth_conv_eq_squashGCF_nth_conv`.
      have : ∀ ⦃b⦄, g.partDens.get? n = some b → b ≠ 0 := by
        intro b nth_partDen_eq
        obtain ⟨gp, s_nth_eq, ⟨refl⟩⟩ : ∃ gp, g.s.get? n = some gp ∧ gp.b = b :=
          exists_s_b_of_partDen nth_partDen_eq
        exact (ne_of_lt (s_pos (lt_add_one n) s_nth_eq).right).symm
      exact succ_nth_conv_eq_squashGCF_nth_conv @this

end GenContFract

open GenContFract

namespace ContFract

theorem convs_eq_convs' [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {c : ContFract K} :
    (↑c : GenContFract K).convs = (↑c : GenContFract K).convs' := by
  ext n
  apply GenContFract.convs_eq_convs'
  intro gp m _ s_nth_eq
  exact ⟨zero_lt_one.trans_le ((c : SimpContFract K).property m gp.a
    (partNum_eq_s_a s_nth_eq)).symm.le, c.property m gp.b <| partDen_eq_s_b s_nth_eq⟩

end ContFract
