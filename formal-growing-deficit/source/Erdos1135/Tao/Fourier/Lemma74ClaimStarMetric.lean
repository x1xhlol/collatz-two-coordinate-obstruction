import Erdos1135.Tao.Fourier.Lemma74CanonicalRaw

/-!
# Lemma 7.4 Claim (*) Metric Case

This leaf proves the metric/exponential first case of Tao's Claim (*).  It
stops before weak-black propagation, source membership, seeds, coherence, and
family assembly.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Point

theorem abs_jReal_sub_le_of_distSq_le_sq
    (p q : TaoSection7Point) {rho : ℝ} (hrho : 0 ≤ rho)
    (hdist : p.distSq q ≤ rho ^ 2) :
    |p.jReal - q.jReal| ≤ rho := by
  apply abs_le_of_sq_le_sq
  · dsimp [distSq] at hdist
    nlinarith [sq_nonneg (p.lReal - q.lReal)]
  · exact hrho

theorem abs_lReal_sub_le_of_distSq_le_sq
    (p q : TaoSection7Point) {rho : ℝ} (hrho : 0 ≤ rho)
    (hdist : p.distSq q ≤ rho ^ 2) :
    |p.lReal - q.lReal| ≤ rho := by
  apply abs_le_of_sq_le_sq
  · dsimp [distSq] at hdist
    nlinarith [sq_nonneg (p.jReal - q.jReal)]
  · exact hrho

end TaoSection7Point

theorem taoSection7SoutheastWeight_eq_coordinates
    (a q : TaoSection7Point)
    (hj : (a.j : ℕ) ≤ (q.j : ℕ)) (hl : q.l ≤ a.l) :
    taoSection7SoutheastWeight a q =
      (q.jReal - a.jReal) * Real.log 9 +
        (a.lReal - q.lReal) * Real.log 2 := by
  have hH :
      ((taoSection7SoutheastH a q : ℕ) : ℝ) =
        ((q.j : ℕ) : ℝ) - ((a.j : ℕ) : ℝ) := by
    simp [taoSection7SoutheastH, Nat.cast_sub hj]
  have hVInt := taoSection7SoutheastV_intCast a q hl
  have hV :
      ((taoSection7SoutheastV a q : ℕ) : ℝ) =
        ((a.l : ℤ) : ℝ) - ((q.l : ℤ) : ℝ) := by
    exact_mod_cast hVInt
  rw [taoSection7SoutheastWeight, hH, hV]
  rfl

theorem taoSection7Triangle_mem_iff_southeastWeight_le
    (Delta : TaoSection7Triangle) (q : TaoSection7Point)
    (hj : Delta.cornerJ ≤ q.j) (hl : q.l ≤ Delta.cornerL) :
    Delta.Mem q ↔
      taoSection7SoutheastWeight Delta.topLeft q ≤ Delta.size := by
  have hjNat : (Delta.cornerJ : ℕ) ≤ (q.j : ℕ) := by
    exact_mod_cast hj
  simp only [TaoSection7Triangle.Mem]
  constructor
  · intro h
    have hweight := h.2.2
    rw [taoSection7SoutheastWeight_eq_coordinates Delta.topLeft q hjNat hl]
    simpa [TaoSection7Point.jReal, TaoSection7Point.lReal,
      TaoSection7Triangle.topLeft, TaoSection7Triangle.horizontalDepth,
      TaoSection7Triangle.verticalDepth, Nat.cast_sub hjNat] using hweight
  · intro hweight
    refine ⟨hj, hl, ?_⟩
    rw [taoSection7SoutheastWeight_eq_coordinates Delta.topLeft q hjNat hl]
      at hweight
    simpa [TaoSection7Point.jReal, TaoSection7Point.lReal,
      TaoSection7Triangle.topLeft, TaoSection7Triangle.horizontalDepth,
      TaoSection7Triangle.verticalDepth, Nat.cast_sub hjNat] using hweight

/-- The weighted geometry of the southeast exterior region in Claim (*) Case 1. -/
theorem taoSection7ClaimStar_case1_weight_bounds
    (Delta : TaoSection7Triangle) (q : TaoSection7Point) {rho : ℝ}
    (hrho : 0 ≤ rho) (hqOut : ¬ Delta.Mem q) (hqNear : Delta.Near rho q)
    (hj : Delta.cornerJ ≤ q.j) (hl : q.l ≤ Delta.cornerL) :
    Delta.size < taoSection7SoutheastWeight Delta.topLeft q ∧
      taoSection7SoutheastWeight Delta.topLeft q ≤
        Delta.size + (Real.log 9 + Real.log 2) * rho := by
  have hstrict :
      Delta.size < taoSection7SoutheastWeight Delta.topLeft q := by
    exact lt_of_not_ge (fun hle => hqOut
      ((taoSection7Triangle_mem_iff_southeastWeight_le Delta q hj hl).2 hle))
  rcases hqNear with ⟨r, hrMem, hdist⟩
  have hrj : Delta.cornerJ ≤ r.j := hrMem.1
  have hrl : r.l ≤ Delta.cornerL := hrMem.2.1
  have hrWeight :
      taoSection7SoutheastWeight Delta.topLeft r ≤ Delta.size :=
    (taoSection7Triangle_mem_iff_southeastWeight_le Delta r hrj hrl).1 hrMem
  have hjCoord := TaoSection7Point.abs_jReal_sub_le_of_distSq_le_sq
    q r hrho hdist
  have hlCoord := TaoSection7Point.abs_lReal_sub_le_of_distSq_le_sq
    q r hrho hdist
  have hjDiff : q.jReal - r.jReal ≤ rho :=
    (le_abs_self _).trans hjCoord
  have hlDiff : r.lReal - q.lReal ≤ rho := by
    have hneg : -(q.lReal - r.lReal) ≤ rho :=
      (neg_le_abs _).trans hlCoord
    linarith
  have hlog9 : 0 ≤ Real.log (9 : ℝ) := (Real.log_pos (by norm_num)).le
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hjTerm :
      (q.jReal - r.jReal) * Real.log 9 ≤ rho * Real.log 9 :=
    mul_le_mul_of_nonneg_right hjDiff hlog9
  have hlTerm :
      (r.lReal - q.lReal) * Real.log 2 ≤ rho * Real.log 2 :=
    mul_le_mul_of_nonneg_right hlDiff hlog2
  have hjNat : (Delta.topLeft.j : ℕ) ≤ (q.j : ℕ) := by
    exact_mod_cast hj
  have hrjNat : (Delta.topLeft.j : ℕ) ≤ (r.j : ℕ) := by
    exact_mod_cast hrj
  constructor
  · exact hstrict
  · rw [taoSection7SoutheastWeight_eq_coordinates Delta.topLeft q hjNat hl]
    calc
      (q.jReal - Delta.topLeft.jReal) * Real.log 9 +
          (Delta.topLeft.lReal - q.lReal) * Real.log 2 =
        ((r.jReal - Delta.topLeft.jReal) * Real.log 9 +
          (Delta.topLeft.lReal - r.lReal) * Real.log 2) +
            (q.jReal - r.jReal) * Real.log 9 +
              (r.lReal - q.lReal) * Real.log 2 := by ring
      _ ≤ taoSection7SoutheastWeight Delta.topLeft r +
          rho * Real.log 9 + rho * Real.log 2 := by
        rw [taoSection7SoutheastWeight_eq_coordinates Delta.topLeft r hrjNat hrl]
        linarith
      _ ≤ Delta.size + (Real.log 9 + Real.log 2) * rho := by
        nlinarith

/-- Corrected Case 1 of Claim (*): a southeast point outside the triangle is white. -/
theorem taoSection7CanonicalClaimStar_case1
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon)
    (q : TaoSection7Point)
    (hqOut :
      ¬ (taoSection7CanonicalTriangle hxi hscalar p).Mem q)
    (hqNear :
      (taoSection7CanonicalTriangle hxi hscalar p).Near
        (taoSection7TriangleSeparation epsilon) q)
    (hj :
      (taoSection7CanonicalTriangle hxi hscalar p).cornerJ ≤ q.j)
    (hl : q.l ≤
      (taoSection7CanonicalTriangle hxi hscalar p).cornerL) :
    taoSection7SourceWhitePoint n xi epsilon q := by
  let w := taoSection7CanonicalTopLeftWitness hxi hscalar p
  let Delta := taoSection7CanonicalTriangle hxi hscalar p
  let rho := taoSection7TriangleSeparation epsilon
  let D := taoSection7SoutheastWeight w.topLeft q
  have hrho : 0 ≤ rho := hscalar.separation_one.trans' (by norm_num)
  have hbounds := taoSection7ClaimStar_case1_weight_bounds
    Delta q hrho hqOut hqNear hj hl
  have hDgt : Delta.size < D := by
    simpa [D, Delta, w, taoSection7CanonicalTriangle,
      TaoSection7TopLeftWitness.triangle, TaoSection7Triangle.topLeft,
      taoSection7CanonicalTopLeftWitness] using hbounds.1
  have hDupper : D ≤ Delta.size + (Real.log 9 + Real.log 2) * rho := by
    simpa [D, Delta, w, taoSection7CanonicalTriangle,
      TaoSection7TopLeftWitness.triangle, TaoSection7Triangle.topLeft,
      taoSection7CanonicalTopLeftWitness] using hbounds.2
  have htop := taoSection7CanonicalTopLeft_abs_eq hxi hscalar p
  have hpredEq :
      Real.exp D * |taoSection7SourceTheta n xi w.topLeft| =
        epsilon * Real.exp (-Delta.size + D) := by
    rw [htop]
    change Real.exp D * (epsilon * Real.exp (-Delta.size)) =
      epsilon * Real.exp (-Delta.size + D)
    calc
      Real.exp D * (epsilon * Real.exp (-Delta.size)) =
          epsilon * (Real.exp (-Delta.size) * Real.exp D) := by ring
      _ = epsilon * Real.exp (-Delta.size + D) := by rw [Real.exp_add]
  have hpredLower :
      epsilon < Real.exp D * |taoSection7SourceTheta n xi w.topLeft| := by
    rw [hpredEq]
    have hexp : 1 < Real.exp (-Delta.size + D) :=
      (Real.one_lt_exp_iff).2 (by linarith)
    nlinarith [hscalar.epsilon_pos]
  have hpredUpper :
      Real.exp D * |taoSection7SourceTheta n xi w.topLeft| ≤
        epsilon * Real.exp ((Real.log 9 + Real.log 2) * rho) := by
    rw [hpredEq]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by linarith)) hscalar.epsilon_pos.le
  have hguard :
      Real.exp D * |taoSection7SourceTheta n xi w.topLeft| < (1 / 2 : ℝ) :=
    (hpredUpper.trans hscalar.combined_weak).trans_lt (by norm_num)
  have hjNat : (w.topLeft.j : ℕ) ≤ (q.j : ℕ) := by
    exact_mod_cast hj
  have hexact := abs_taoSection7SourceTheta_southeast_eq_of_lt_half
    n xi w.topLeft q hjNat hl hguard
  unfold taoSection7SourceWhitePoint taoSection7White
  change epsilon < |taoSection7SourceTheta n xi q|
  rw [hexact]
  exact hpredLower

end

end Tao
end Erdos1135
