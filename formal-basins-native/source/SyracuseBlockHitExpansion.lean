import SyracuseBlockOperator
import GreenParityDecomposition

set_option autoImplicit false
open Classical

namespace CollatzCylinderPacking.Arithmetic

noncomputable def blockDepthHitTerm (s : ℝ) (k N : ℕ) (p : ℕ × ℕ) : ℝ :=
  if p.1 % 2 = 1 ∧ iterate p.2 p.1 = N ∧ oddCount p.2 p.1 = k
    then (orbitRatio p.2 p.1) ^ s else 0

theorem blockDepthHitTerm_nonneg (s : ℝ) (k N : ℕ) (p : ℕ × ℕ) :
    0 ≤ blockDepthHitTerm s k N p := by
  unfold blockDepthHitTerm
  split_ifs
  · exact (Real.rpow_pos_of_pos (orbitRatio_pos _ _) _).le
  · exact le_rfl

theorem blockWordTerm_eq_orbitRatio_rpow {s : ℝ} {k N : ℕ} (hN : 0 < N)
    {w : GeometricWord k} (hv : ValidWord k N w) :
    blockWordTerm s k N w = (orbitRatio (wordLength k w) (tupleEndpoint N (wordList k w))) ^ s := by
  rw [blockWordTerm, if_pos hv, orbitRatio, valid_word_oddCount hN hv]
  exact (block_weight_rpow s k (wordLength k w)).symm

/-- Positive-depth block words are exactly actual odd-start hitting paths,
with the s-th power of their true inverse weight. -/
theorem block_depth_hit_hasSum {s : ℝ} (hs : 0 < s) {k N : ℕ}
    (hk : 0 < k) (hN : 0 < N) :
    HasSum (blockDepthHitTerm s k N) (syracuseBlockIterate s k N) := by
  let g : {w : GeometricWord k // ValidWord k N w} → ℕ × ℕ :=
    fun w => (tupleEndpoint N (wordList k w.val), wordLength k w.val)
  have hg : Function.Injective g := valid_word_endpoint_time_injective hk hN
  have hz (p : ℕ × ℕ) (hp : p ∉ Set.range g) : blockDepthHitTerm s k N p = 0 := by
    unfold blockDepthHitTerm
    apply if_neg
    rintro ⟨ho, hh, hc⟩
    have hex := hitting_path_word (by omega : 0 < p.1) ho hh
    rw [hc] at hex
    obtain ⟨w, hv, hl, he⟩ := hex
    exact hp ⟨⟨w, hv⟩, Prod.ext he hl⟩
  apply (hg.hasSum_iff hz).mp
  have hsub : HasSum (fun w : {w : GeometricWord k // ValidWord k N w} =>
      blockWordTerm s k N w.val) (syracuseBlockIterate s k N) := by
    apply (hasSum_subtype_iff_of_support_subset (f := blockWordTerm s k N)
      (s := {w | ValidWord k N w}) ?_).mpr
    · rw [syracuseBlockIterate_eq_word_sum hs]
      exact (blockWordTerm_summable hs k N).hasSum
    · intro w hw
      by_contra hv
      change ¬ ValidWord k N w at hv
      exact hw (by simp [blockWordTerm, hv])
  convert hsub using 1
  funext w
  have hp := valid_tuple_path hN w.property
  have ho := hp.2.2.2 (wordList_ne_nil hk w.val)
  have hh := hp.2.1
  rw [wordList_sum] at hh
  have hc := valid_word_oddCount hN w.property
  simp only [Function.comp_def, g, blockDepthHitTerm, ho, hh, hc, and_self, if_true]
  exact (blockWordTerm_eq_orbitRatio_rpow hN w.property).symm

theorem block_depth_zero_hasSum (s : ℝ) (N : ℕ) :
    HasSum (blockDepthHitTerm s 0 N) (if N % 2 = 1 then (1 : ℝ) else 0) := by
  have hv : blockDepthHitTerm s 0 N (N, 0) = if N % 2 = 1 then (1 : ℝ) else 0 := by
    simp [blockDepthHitTerm, iterate, oddCount, orbitRatio]
  rw [← hv]
  apply hasSum_single (N, 0)
  intro p hp
  unfold blockDepthHitTerm
  apply if_neg
  rintro ⟨ho, hh, hc⟩
  have hA : p.2 = 0 := by
    by_contra hn
    have hpos := oddCount_pos_of_odd_start (Nat.pos_of_ne_zero hn) ho
    omega
  have hq : p.1 = N := by simpa only [hA, iterate] using hh
  exact hp (Prod.ext hq hA)

theorem block_depth_sum_at_endpoint (s : ℝ) (N : ℕ) (p : ℕ × ℕ) :
    HasSum (fun k : ℕ => blockDepthHitTerm s k N p) (oddGreenHitTerm s N p) := by
  have hv : blockDepthHitTerm s (oddCount p.2 p.1) N p = oddGreenHitTerm s N p := by
    simp only [blockDepthHitTerm, oddGreenHitTerm, allHitTerm, and_true]
    split_ifs <;> simp_all
  rw [← hv]
  apply hasSum_single (oddCount p.2 p.1)
  intro k hk
  unfold blockDepthHitTerm
  exact if_neg (fun h => hk h.2.2.symm)

theorem block_depth_joint_summable {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    Summable (fun p : (ℕ × ℕ) × ℕ => blockDepthHitTerm s p.2 N p.1) := by
  apply (summable_prod_of_nonneg (fun p => blockDepthHitTerm_nonneg _ _ _ _)).mpr
  refine ⟨fun p => (block_depth_sum_at_endpoint s N p).summable, ?_⟩
  simpa only [(block_depth_sum_at_endpoint s N _).tsum_eq] using oddGreenHitTerm_summable hs hN

theorem syracuseBlockIterate_eq_depth_sum {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (k : ℕ) :
    syracuseBlockIterate s k N = (∑' p : ℕ × ℕ, blockDepthHitTerm s k N p) +
      (if k = 0 then if N % 2 = 0 then (1 : ℝ) else 0 else 0) := by
  cases k with
  | zero =>
    rw [(block_depth_zero_hasSum s N).tsum_eq]
    rcases (show N % 2 = 0 ∨ N % 2 = 1 by omega) with h | h <;>
      simp [syracuseBlockIterate, h]
  | succ k =>
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, add_zero]
    exact (block_depth_hit_hasSum hs (Nat.succ_pos k) hN).tsum_eq.symm

/-- The full sum of odd-block iterates is the odd-endpoint hitting sum,
with the empty word restored at an even target. -/
theorem syracuseBlockIterate_hasSum {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    HasSum (fun k : ℕ => syracuseBlockIterate s k N)
      ((if N % 2 = 0 then (1 : ℝ) else 0) + ∑' p : ℕ × ℕ, oddGreenHitTerm s N p) := by
  have hj := block_depth_joint_summable hs hN
  have hrows : Summable (fun k : ℕ => ∑' p : ℕ × ℕ, blockDepthHitTerm s k N p) :=
    hj.prod_symm.prod
  have he : (∑' k : ℕ, ∑' p : ℕ × ℕ, blockDepthHitTerm s k N p) =
      ∑' p : ℕ × ℕ, oddGreenHitTerm s N p := by
    rw [Summable.tsum_comm (f := fun p k => blockDepthHitTerm s k N p) hj]
    exact tsum_congr (fun p => (block_depth_sum_at_endpoint s N p).tsum_eq)
  have hr : HasSum (fun k : ℕ => ∑' p : ℕ × ℕ, blockDepthHitTerm s k N p)
      (∑' p : ℕ × ℕ, oddGreenHitTerm s N p) := by
    rw [← he]
    exact hrows.hasSum
  have hsingle : HasSum (fun k : ℕ => if k = 0 then
      if N % 2 = 0 then (1 : ℝ) else 0 else 0) (if N % 2 = 0 then (1 : ℝ) else 0) := by
    exact hasSum_ite_eq 0 _
  simpa only [← syracuseBlockIterate_eq_depth_sum (by linarith : 0 < s) hN, add_comm] using hr.add hsingle

#print axioms block_depth_hit_hasSum
#print axioms syracuseBlockIterate_hasSum

end CollatzCylinderPacking.Arithmetic
