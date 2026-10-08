import PadicBinaryEnvelopeTransfer
import ActualFirstHitReconstruction
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic Erdos1135.Tao

namespace CollatzCanonical.IntegerStationaryEnvelope

noncomputable def integerEnvelopeValue (n : ℕ) : ℝ :=
  (canonicalIntegerEnvelope (n : ℤ_[3])).toReal

theorem canonicalIntegerEnvelope_natCast_ne_top {n : ℕ} (hn : 0 < n) :
    canonicalIntegerEnvelope (n : ℤ_[3]) ≠ ∞ :=
  ne_of_lt ((canonicalIntegerEnvelope_natCast_le n hn).trans_lt (actualIntegerTrace_lt_top n))

theorem integerEnvelopeValue_nonneg (n : ℕ) : 0 ≤ integerEnvelopeValue n :=
  ENNReal.toReal_nonneg

theorem padicBinaryTransfer_natCast (f : ℤ_[3] → ℝ≥0∞) (n : ℕ) :
    padicBinaryTransfer f (n : ℤ_[3]) =
      (1 / 2 : ℝ≥0∞) * f ((2 * n : ℕ) : ℤ_[3]) +
      (3 / 2 : ℝ≥0∞) * (if n % 3 = 2 then f (oddPredecessor n : ℤ_[3]) else 0) := by
  unfold padicBinaryTransfer
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  congr 1
  by_cases h : n % 3 = 2
  · rw [if_pos h, ← padicAffineBranch_oddPredecessor h, padicOddLiftENN_apply_branch]
  · rw [if_neg h, padicOddLiftENN_eq_zero _ (padicAffineBranch_natCast_not_mem_range h)]

def BinarySuperharmonic (f : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → (1 / 2 : ℝ) * f (2 * n) +
    (3 / 2 : ℝ) * (if n % 3 = 2 then f (oddPredecessor n) else 0) ≤ f n

theorem integerEnvelopeValue_superharmonic : BinarySuperharmonic integerEnvelopeValue := by
  intro n hn
  have h := canonicalIntegerEnvelope_transfer_le (n : ℤ_[3])
  rw [padicBinaryTransfer_natCast] at h
  have ht := ne_top_of_le_ne_top (canonicalIntegerEnvelope_natCast_ne_top hn) h
  have hr := ENNReal.toReal_mono (canonicalIntegerEnvelope_natCast_ne_top hn) h
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mp ht).1 (ENNReal.add_ne_top.mp ht).2] at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat] at hr
  change _ ≤ integerEnvelopeValue n at hr
  split_ifs at hr ⊢ <;> simpa only [integerEnvelopeValue, ENNReal.toReal_zero] using hr

noncomputable def markedOddDepthAt (p : ℕ → ℝ) (k n A : ℕ) : ℝ :=
  ∑' q : ℕ, oddDepthHitTerm k n (q, A) * p q

noncomputable def markedOddDepthTruncation (p : ℕ → ℝ) (A k n : ℕ) : ℝ :=
  ∑ a ∈ Finset.range A, markedOddDepthAt p k n a

theorem markedOddDepth_summable {p : ℕ → ℝ} {L : ℝ}
    (hp : ∀ q, 0 ≤ p q) (hL : ∀ q, p q ≤ L) {n : ℕ} (hn : 0 < n) (k : ℕ) :
    Summable (fun x : ℕ × ℕ => oddDepthHitTerm k n x * p x.1) := by
  apply Summable.of_nonneg_of_le
    (fun x => mul_nonneg (oddDepthHitTerm_nonneg k n x) (hp x.1))
    (fun x => mul_le_mul_of_nonneg_left (hL x.1) (oddDepthHitTerm_nonneg k n x))
    ((odd_depth_hit_summable hn k).mul_right L)

theorem markedOddDepthAt_summable {p : ℕ → ℝ} {L : ℝ}
    (hp : ∀ q, 0 ≤ p q) (hL : ∀ q, p q ≤ L) {n : ℕ} (hn : 0 < n) (k A : ℕ) :
    Summable (fun q : ℕ => oddDepthHitTerm k n (q, A) * p q) :=
  (markedOddDepth_summable hp hL hn k).prod_symm.prod_factor A

theorem markedOddDepthAt_nonneg {p : ℕ → ℝ} (hp : ∀ q, 0 ≤ p q) (k n A : ℕ) :
    0 ≤ markedOddDepthAt p k n A :=
  tsum_nonneg (fun q => mul_nonneg (oddDepthHitTerm_nonneg k n (q, A)) (hp q))

theorem markedOddDepthAt_zero_time (p : ℕ → ℝ) (k n : ℕ) :
    markedOddDepthAt p k n 0 = if k = 0 ∧ n % 2 = 1 then p n else 0 := by
  classical
  unfold markedOddDepthAt
  rw [tsum_eq_single n]
  · simp only [oddDepthHitTerm, iterate, oddCount, orbitRatio, pow_zero, div_self
      (by norm_num : (1 : ℝ) ≠ 0)]
    by_cases hk : k = 0 <;> by_cases hn : n % 2 = 1 <;> simp [hk, hn, eq_comm]
  · intro q hq
    simp [oddDepthHitTerm, iterate, hq]

theorem oddDepthHitTerm_zero_depth_succ (n q A : ℕ) :
    oddDepthHitTerm 0 n (q, A + 1) = 0 := by
  apply if_neg
  rintro ⟨ho, _, hc⟩
  change oddCount (A + 1) q = 0 at hc
  have h := oddCount_pos_of_odd_start (Nat.succ_pos A) ho
  exact (Nat.ne_of_gt h) hc

theorem markedOddDepthTruncation_zero_depth (p : ℕ → ℝ) (A n : ℕ) :
    markedOddDepthTruncation p (A + 1) 0 n = if n % 2 = 1 then p n else 0 := by
  unfold markedOddDepthTruncation
  rw [Finset.sum_range_succ']
  have hz : (∑ a ∈ Finset.range A, markedOddDepthAt p 0 n (a + 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    simp only [markedOddDepthAt, oddDepthHitTerm_zero_depth_succ, zero_mul, tsum_zero]
  rw [hz, zero_add, markedOddDepthAt_zero_time]
  simp

theorem oddDepthHitTerm_succ_split (k n q A : ℕ) :
    oddDepthHitTerm (k + 1) n (q, A + 1) =
      (1 / 2 : ℝ) * oddDepthHitTerm (k + 1) (2 * n) (q, A) +
      (3 / 2 : ℝ) * (if n % 3 = 2 then
        oddDepthHitTerm k (oddPredecessor n) (q, A) else 0) := by
  by_cases ho : q % 2 = 1
  · by_cases hh : iterate (A + 1) q = n
    · have hc := step_preimage_iff.mp hh
      rcases hc with he | ⟨hres, he⟩
      · have hcount : oddCount (A + 1) q = oddCount A q := by
          simp [oddCount, he]
        have hratio : orbitRatio (A + 1) q = (1 / 2 : ℝ) * orbitRatio A q := by
          rw [orbitRatio_add, he, orbitRatio_one_even, mul_comm]
        have hz : (if n % 3 = 2 then oddDepthHitTerm k (oddPredecessor n) (q, A) else 0) = 0 := by
          split_ifs with hn
          · have hne : iterate A q ≠ oddPredecessor n := by
              have hop := (oddPredecessor_spec hn).2.1
              rw [he]
              omega
            simp [oddDepthHitTerm, hne]
          · rfl
        rw [hz]
        simp only [oddDepthHitTerm, ho, hh, he, true_and, hcount, mul_zero, add_zero]
        split_ifs <;> simp_all
      · have hp := (oddPredecessor_spec hres).2.1
        have hne : iterate A q ≠ 2 * n := by rw [he]; omega
        have hcount : oddCount (A + 1) q = oddCount A q + 1 := by
          simp only [oddCount, he, hp]
        have hratio : orbitRatio (A + 1) q = (3 / 2 : ℝ) * orbitRatio A q := by
          rw [orbitRatio_add, he, orbitRatio_one_odd hp, mul_comm]
        simp only [oddDepthHitTerm, ho, hh, he, hres, if_true, true_and,
          hcount, Nat.add_right_cancel_iff]
        split_ifs <;> simp_all
    · have he : iterate A q ≠ 2 * n := by
        intro h
        apply hh
        change step (iterate A q) = n
        rw [h, step_two_mul]
      have hz : (if n % 3 = 2 then oddDepthHitTerm k (oddPredecessor n) (q, A) else 0) = 0 := by
        split_ifs with hn
        · have hne : iterate A q ≠ oddPredecessor n := by
            intro h
            apply hh
            change step (iterate A q) = n
            rw [h, (oddPredecessor_spec hn).2.2]
          simp [oddDepthHitTerm, hne]
        · rfl
      rw [hz]
      simp [oddDepthHitTerm, hh, he]
  · simp [oddDepthHitTerm, ho]

theorem markedOddDepthAt_succ_split {p : ℕ → ℝ} {L : ℝ}
    (hp : ∀ q, 0 ≤ p q) (hL : ∀ q, p q ≤ L) {n : ℕ} (hn : 0 < n) (k A : ℕ) :
    markedOddDepthAt p (k + 1) n (A + 1) =
      (1 / 2 : ℝ) * markedOddDepthAt p (k + 1) (2 * n) A +
      (3 / 2 : ℝ) * (if n % 3 = 2 then
        markedOddDepthAt p k (oddPredecessor n) A else 0) := by
  unfold markedOddDepthAt
  simp_rw [oddDepthHitTerm_succ_split, add_mul, mul_assoc]
  by_cases hres : n % 3 = 2
  · simp only [if_pos hres]
    rw [((markedOddDepthAt_summable hp hL (by omega) (k + 1) A).mul_left (1 / 2)).tsum_add
      ((markedOddDepthAt_summable hp hL (oddPredecessor_spec hres).1 k A).mul_left (3 / 2)),
      tsum_mul_left, tsum_mul_left]
  · simp only [if_neg hres, zero_mul, mul_zero, add_zero]
    exact tsum_mul_left

theorem markedOddDepthTruncation_succ_split {p : ℕ → ℝ} {L : ℝ}
    (hp : ∀ q, 0 ≤ p q) (hL : ∀ q, p q ≤ L) {n : ℕ} (hn : 0 < n) (k A : ℕ) :
    markedOddDepthTruncation p (A + 1) (k + 1) n =
      (1 / 2 : ℝ) * markedOddDepthTruncation p A (k + 1) (2 * n) +
      (3 / 2 : ℝ) * (if n % 3 = 2 then
        markedOddDepthTruncation p A k (oddPredecessor n) else 0) := by
  unfold markedOddDepthTruncation
  rw [Finset.sum_range_succ', markedOddDepthAt_zero_time]
  simp only [Nat.succ_ne_zero, false_and, if_false, add_zero]
  simp_rw [markedOddDepthAt_succ_split hp hL hn]
  by_cases hres : n % 3 = 2
  · simp only [if_pos hres, Finset.sum_add_distrib, ← Finset.mul_sum]
  · simp only [if_neg hres, mul_zero, add_zero, ← Finset.mul_sum]

theorem markedOddDepthTruncation_le {f p : ℕ → ℝ} {L : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : BinarySuperharmonic f)
    (hp : ∀ q, 0 ≤ p q) (hL : ∀ q, p q ≤ L)
    (hpf : ∀ q, 0 < q → p q ≤ f q) (A k : ℕ) {n : ℕ} (hn : 0 < n) :
    markedOddDepthTruncation p A k n ≤ f n := by
  induction A generalizing k n with
  | zero => simpa only [markedOddDepthTruncation, Finset.range_zero, Finset.sum_empty] using hf n
  | succ A ih =>
    cases k with
    | zero =>
      rw [markedOddDepthTruncation_zero_depth]
      split_ifs
      · exact hpf n hn
      · exact hf n
    | succ k =>
      rw [markedOddDepthTruncation_succ_split hp hL hn]
      apply le_trans _ (hs n hn)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (ih (k + 1) (by omega)) (by norm_num)
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        split_ifs with hres
        · exact ih k (oddPredecessor_spec hres).1
        · rfl

theorem markedOddDepthAt_tsum_le {f p : ℕ → ℝ} {L : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : BinarySuperharmonic f)
    (hp : ∀ q, 0 ≤ p q) (hL : ∀ q, p q ≤ L)
    (hpf : ∀ q, 0 < q → p q ≤ f q) (k : ℕ) {n : ℕ} (hn : 0 < n) :
    (∑' A : ℕ, markedOddDepthAt p k n A) ≤ f n := by
  apply Real.tsum_le_of_sum_range_le (markedOddDepthAt_nonneg hp k n)
  intro A
  exact markedOddDepthTruncation_le hf hs hp hL hpf A k hn

theorem markedOddDepth_tsum_le {f p : ℕ → ℝ} {L : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : BinarySuperharmonic f)
    (hp : ∀ q, 0 ≤ p q) (hL : ∀ q, p q ≤ L)
    (hpf : ∀ q, 0 < q → p q ≤ f q) (k : ℕ) {n : ℕ} (hn : 0 < n) :
    (∑' x : ℕ × ℕ, oddDepthHitTerm k n x * p x.1) ≤ f n := by
  rw [(markedOddDepth_summable hp hL hn k).tsum_prod,
    ← (markedOddDepth_summable hp hL hn k).tsum_comm]
  exact markedOddDepthAt_tsum_le hf hs hp hL hpf k hn

theorem markedOddCumulative_summable {p : ℕ → ℝ} {L : ℝ}
    (hp : ∀ q, 0 ≤ p q) (hL : ∀ q, p q ≤ L) {n : ℕ} (hn : 0 < n) (K : ℕ) :
    Summable (fun x : ℕ × ℕ => oddCumulativeHitTerm K n x * p x.1) := by
  apply Summable.of_nonneg_of_le
    (fun x => mul_nonneg (oddCumulativeHitTerm_nonneg K n x) (hp x.1))
    (fun x => mul_le_mul_of_nonneg_left (hL x.1) (oddCumulativeHitTerm_nonneg K n x))
    ((odd_cumulative_hit_summable hn K).mul_right L)

theorem markedOddCumulative_tsum_le {f p : ℕ → ℝ} {L : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : BinarySuperharmonic f)
    (hp : ∀ q, 0 ≤ p q) (hL : ∀ q, p q ≤ L)
    (hpf : ∀ q, 0 < q → p q ≤ f q) (K : ℕ) {n : ℕ} (hn : 0 < n) :
    (∑' x : ℕ × ℕ, oddCumulativeHitTerm K n x * p x.1) ≤ ((K : ℝ) + 1) * f n := by
  simp_rw [oddCumulativeHitTerm_eq_sum, Finset.sum_mul]
  rw [Summable.tsum_finsetSum (fun k _ => markedOddDepth_summable hp hL hn k)]
  calc
    _ ≤ ∑ k ∈ Finset.range (K + 1), f n := by
      apply Finset.sum_le_sum
      intro k _
      exact markedOddDepth_tsum_le hf hs hp hL hpf k hn
    _ = _ := by simp

theorem markedFirstHitPartial_summable {p : ℕ → ℝ} {L : ℝ}
    (hp : ∀ q, 0 ≤ p q) (hL : ∀ q, p q ≤ L) {n : ℕ} (hn : 0 < n) (K : ℕ) :
    Summable (fun q : ℕ => firstHitPartialTerm K n q * p q) := by
  apply Summable.of_nonneg_of_le
    (fun q => mul_nonneg (firstHitPartialTerm_nonneg K n q) (hp q))
    (fun q => mul_le_mul_of_nonneg_left (hL q) (firstHitPartialTerm_nonneg K n q))
    ((firstHitPartialTerm_summable hn K).mul_right L)

theorem firstHitPartial_marked_le_superharmonic {f p : ℕ → ℝ} {L : ℝ}
    (hf : ∀ n, 0 ≤ f n) (hs : BinarySuperharmonic f)
    (hp : ∀ q, 0 ≤ p q) (hL : ∀ q, p q ≤ L)
    (hpf : ∀ q, 0 < q → p q ≤ f q) (K : ℕ) {n : ℕ} (hn : 0 < n) :
    (∑' q : ℕ, firstHitPartialTerm K n q * p q) ≤ ((K : ℝ) + 1) * f n := by
  classical
  apply le_trans _ (markedOddCumulative_tsum_le hf hs hp hL hpf K hn)
  rw [(markedOddCumulative_summable hp hL hn K).tsum_prod]
  apply Summable.tsum_le_tsum _ (markedFirstHitPartial_summable hp hL hn K)
    (markedOddCumulative_summable hp hL hn K).prod
  intro q
  by_cases hh : ∃ A, iterate A q = n
  · have hfirst := firstHitTime_spec hh
    rw [firstHitPartialTerm_of_first_hit hfirst K]
    by_cases hg : q % 2 = 1 ∧ oddCount (firstHitTime hh) q ≤ K
    · rw [if_pos hg]
      have he : oddCumulativeHitTerm K n (q, firstHitTime hh) = orbitRatio (firstHitTime hh) q := by
        simp only [oddCumulativeHitTerm, hg.1, hfirst.1, hg.2, and_self, if_true]
      rw [← he]
      exact ((markedOddCumulative_summable hp hL hn K).prod_factor q).le_tsum (firstHitTime hh)
        (fun A _ => mul_nonneg (oddCumulativeHitTerm_nonneg K n (q, A)) (hp q))
    · rw [if_neg hg, zero_mul]
      exact tsum_nonneg (fun A => mul_nonneg (oddCumulativeHitTerm_nonneg K n (q, A)) (hp q))
  · simp only [firstHitPartialTerm, dif_neg hh, ite_self, zero_mul]
    exact tsum_nonneg (fun A => mul_nonneg (oddCumulativeHitTerm_nonneg K n (q, A)) (hp q))

theorem firstHitPartial_marked_le_integerEnvelope {p : ℕ → ℝ} {L : ℝ}
    (hp : ∀ q, 0 ≤ p q) (hL : ∀ q, p q ≤ L)
    (hpf : ∀ q, 0 < q → p q ≤ integerEnvelopeValue q) (K : ℕ) {n : ℕ} (hn : 0 < n) :
    (∑' q : ℕ, firstHitPartialTerm K n q * p q) ≤
      ((K : ℝ) + 1) * integerEnvelopeValue n :=
  firstHitPartial_marked_le_superharmonic integerEnvelopeValue_nonneg
    integerEnvelopeValue_superharmonic hp hL hpf K hn

#print axioms integerEnvelopeValue_superharmonic
#print axioms markedOddDepthTruncation_le
#print axioms firstHitPartial_marked_le_integerEnvelope

end CollatzCanonical.IntegerStationaryEnvelope
