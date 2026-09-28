import Erdos1135.Tao.Fourier.Lemma74ClaimStarMetric

/-!
# Lemma 7.4 Claim (*) Propagation Support

This leaf isolates the finite weak-black propagation and the analytic envelope
lemmas needed by Cases 2 and 3 of Tao's Claim (*).
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Point

theorem right_rightN (p : TaoSection7Point) (k : ℕ) :
    p.right.rightN k = p.rightN (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [rightN_succ, rightN_succ]
      exact congrArg right ih

theorem left_right (p : TaoSection7Point)
    (h : 1 < (p.right.j : ℕ)) :
    p.right.left h = p := by
  cases p with
  | mk j l =>
      apply ext'
      · apply Subtype.ext
        rfl
      · rfl

theorem right_left (p : TaoSection7Point) (h : 1 < (p.j : ℕ)) :
    (p.left h).right = p := by
  cases p with
  | mk j l =>
      apply ext'
      · apply Subtype.ext
        change ((j : ℕ) - 1) + 1 = (j : ℕ)
        have hj : 1 < (j : ℕ) := by simpa using h
        omega
      · rfl

end TaoSection7Point

namespace TaoSection7WeakBlackAdjacency

/-- Propagate weak blackness left across a finite row using Claim (ii). -/
theorem propagate_left_rightN
    {epsilon : ℝ} {theta : TaoSection7Point → ℝ}
    (h : TaoSection7WeakBlackAdjacency epsilon theta)
    (p : TaoSection7Point) (m : ℕ)
    (hstart : TaoSection7WeakBlack theta (p.rightN m))
    (hlower : ∀ k < m,
      TaoSection7WeakBlack theta ((p.rightN k).down)) :
    TaoSection7WeakBlack theta p := by
  induction m generalizing p with
  | zero => simpa using hstart
  | succ m ih =>
      have hright : TaoSection7WeakBlack theta p.right := by
        apply ih p.right
        · simpa [TaoSection7Point.right_rightN] using hstart
        · intro k hk
          simpa [TaoSection7Point.right_rightN] using
            hlower (k + 1) (by omega)
      exact h.claim_ii p hright (by
        simpa using hlower 0 (by omega))

/-- Propagate weak blackness right across a finite row using Claim (iii). -/
theorem propagate_right_rightN
    {epsilon : ℝ} {theta : TaoSection7Point → ℝ}
    (h : TaoSection7WeakBlackAdjacency epsilon theta)
    (p : TaoSection7Point) (m : ℕ)
    (hstart : TaoSection7WeakBlack theta p)
    (hlower : ∀ k < m,
      TaoSection7WeakBlack theta ((p.rightN (k + 1)).down)) :
    TaoSection7WeakBlack theta (p.rightN m) := by
  induction m with
  | zero => simpa using hstart
  | succ m ih =>
      have hprev : TaoSection7WeakBlack theta (p.rightN m) :=
        ih (fun k hk => hlower k (by omega))
      rw [TaoSection7Point.rightN_succ]
      let next := (p.rightN m).right
      have hj : 1 < (next.j : ℕ) := by
        dsimp [next]
        simp
      have hleftEq : next.left hj = p.rightN m := by
        simpa [next] using TaoSection7Point.left_right (p.rightN m) hj
      apply h.claim_iii next hj
      · rw [hleftEq]
        exact hprev
      · simpa [next, ← TaoSection7Point.rightN_succ] using
          hlower m (by omega)

/-- Propagate weak blackness upward across a finite column using Claim (ii). -/
theorem propagate_up_upN
    {epsilon : ℝ} {theta : TaoSection7Point → ℝ}
    (h : TaoSection7WeakBlackAdjacency epsilon theta)
    (p : TaoSection7Point) (m : ℕ)
    (hstart : TaoSection7WeakBlack theta p)
    (hright : ∀ k < m,
      TaoSection7WeakBlack theta ((p.upN (k + 1)).right)) :
    TaoSection7WeakBlack theta (p.upN m) := by
  induction m with
  | zero => simpa using hstart
  | succ m ih =>
      have hprev : TaoSection7WeakBlack theta (p.upN m) :=
        ih (fun k hk => hright k (by omega))
      apply h.claim_ii (p.upN (m + 1))
      · exact hright m (by omega)
      · simpa using hprev

end TaoSection7WeakBlackAdjacency

/-- A bounded southeast move from a raw black point is weakly black. -/
theorem taoSection7SourceTheta_weakBlack_of_black_southeast
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon E : ℝ}
    (a q : TaoSection7Point)
    (ha : taoSection7SourceBlackPoint n xi epsilon a)
    (hj : (a.j : ℕ) ≤ (q.j : ℕ)) (hl : q.l ≤ a.l)
    (hweight : taoSection7SoutheastWeight a q ≤ E)
    (henvelope : epsilon * Real.exp E ≤ (1 / 100 : ℝ)) :
    TaoSection7WeakBlack (taoSection7SourceTheta n xi) q := by
  have haTheta : |taoSection7SourceTheta n xi a| ≤ epsilon := by
    simpa [taoSection7SourceBlackPoint, taoSection7Black] using ha
  unfold TaoSection7WeakBlack
  calc
    |taoSection7SourceTheta n xi q| ≤
        Real.exp (taoSection7SoutheastWeight a q) *
          |taoSection7SourceTheta n xi a| :=
      abs_taoSection7SourceTheta_southeast_le n xi a q hj hl
    _ ≤ Real.exp E * epsilon := by
      exact mul_le_mul (Real.exp_le_exp.mpr hweight) haTheta
        (abs_nonneg _) (Real.exp_pos _).le
    _ = epsilon * Real.exp E := by ring
    _ ≤ (1 / 100 : ℝ) := henvelope

/-- The canonical top-left identity turns a weight envelope into weak blackness. -/
theorem taoSection7Canonical_weakBlack_of_weight_le
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon E : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon)
    (q : TaoSection7Point)
    (hj :
      ((taoSection7CanonicalTopLeftWitness hxi hscalar p).topLeft.j : ℕ) ≤
        (q.j : ℕ))
    (hl : q.l ≤
      (taoSection7CanonicalTopLeftWitness hxi hscalar p).topLeft.l)
    (hweight :
      taoSection7SoutheastWeight
          (taoSection7CanonicalTopLeftWitness hxi hscalar p).topLeft q ≤
        taoSection7CanonicalTriangleSize hxi hscalar p + E)
    (henvelope : epsilon * Real.exp E ≤ (1 / 100 : ℝ)) :
    TaoSection7WeakBlack (taoSection7SourceTheta n xi) q := by
  let a := (taoSection7CanonicalTopLeftWitness hxi hscalar p).topLeft
  let s := taoSection7CanonicalTriangleSize hxi hscalar p
  have htransport := abs_taoSection7SourceTheta_southeast_le
    n xi a q hj hl
  have htop := taoSection7CanonicalTopLeft_abs_eq hxi hscalar p
  unfold TaoSection7WeakBlack
  calc
    |taoSection7SourceTheta n xi q| ≤
        Real.exp (taoSection7SoutheastWeight a q) *
          |taoSection7SourceTheta n xi a| := htransport
    _ = epsilon * Real.exp
        (-s + taoSection7SoutheastWeight a q) := by
      rw [htop]
      change Real.exp (taoSection7SoutheastWeight a q) *
          (epsilon * Real.exp (-s)) =
        epsilon * Real.exp (-s + taoSection7SoutheastWeight a q)
      rw [Real.exp_add]
      ring
    _ ≤ epsilon * Real.exp E := by
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) hscalar.epsilon_pos.le
    _ ≤ (1 / 100 : ℝ) := henvelope

theorem taoSection7Near_height_above_corner_le
    (Delta : TaoSection7Triangle) (q : TaoSection7Point) {rho : ℝ}
    (hrho : 0 ≤ rho) (hqNear : Delta.Near rho q) :
    q.lReal - Delta.topLeft.lReal ≤ rho := by
  rcases hqNear with ⟨r, hrMem, hdist⟩
  have hcoord := TaoSection7Point.abs_lReal_sub_le_of_distSq_le_sq
    q r hrho hdist
  have hqr : q.lReal - r.lReal ≤ rho :=
    (le_abs_self _).trans hcoord
  have hrl : r.lReal ≤ Delta.topLeft.lReal := by
    change ((r.l : ℤ) : ℝ) ≤ ((Delta.cornerL : ℤ) : ℝ)
    exact_mod_cast hrMem.2.1
  linarith

theorem taoSection7Near_corner_left_gap_le
    (Delta : TaoSection7Triangle) (q : TaoSection7Point) {rho : ℝ}
    (hrho : 0 ≤ rho) (hqNear : Delta.Near rho q) :
    Delta.topLeft.jReal - q.jReal ≤ rho := by
  rcases hqNear with ⟨r, hrMem, hdist⟩
  have hcoord := TaoSection7Point.abs_jReal_sub_le_of_distSq_le_sq
    q r hrho hdist
  have hrq : r.jReal - q.jReal ≤ rho := by
    have hneg : -(q.jReal - r.jReal) ≤ rho :=
      (neg_le_abs _).trans hcoord
    linarith
  have hrj : Delta.topLeft.jReal ≤ r.jReal := by
    change (((Delta.cornerJ : ℕ) : ℝ)) ≤ (((r.j : ℕ) : ℝ))
    exact_mod_cast hrMem.1
  linarith

/-- Nearness controls every intermediate point on the canonical top row. -/
theorem taoSection7Near_topRow_weight_le
    (Delta : TaoSection7Triangle) (q x : TaoSection7Point) {rho : ℝ}
    (hrho : 0 ≤ rho) (hqNear : Delta.Near rho q)
    (hxj : Delta.cornerJ ≤ x.j) (hxq : x.j ≤ q.j)
    (hxl : x.l = Delta.cornerL) :
    taoSection7SoutheastWeight Delta.topLeft x ≤
      Delta.size + Real.log 9 * rho := by
  rcases hqNear with ⟨r, hrMem, hdist⟩
  have hrj : Delta.cornerJ ≤ r.j := hrMem.1
  have hrl : r.l ≤ Delta.cornerL := hrMem.2.1
  have hrWeight :
      taoSection7SoutheastWeight Delta.topLeft r ≤ Delta.size :=
    (taoSection7Triangle_mem_iff_southeastWeight_le Delta r hrj hrl).1 hrMem
  have hcoord := TaoSection7Point.abs_jReal_sub_le_of_distSq_le_sq
    q r hrho hdist
  have hqr : q.jReal - r.jReal ≤ rho :=
    (le_abs_self _).trans hcoord
  have hxqr : x.jReal - r.jReal ≤ rho := by
    have hxqReal : x.jReal ≤ q.jReal := by
      change (((x.j : ℕ) : ℝ)) ≤ (((q.j : ℕ) : ℝ))
      exact_mod_cast hxq
    linarith
  have hlog9 : 0 ≤ Real.log (9 : ℝ) := (Real.log_pos (by norm_num)).le
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hxTerm :
      (x.jReal - r.jReal) * Real.log 9 ≤ rho * Real.log 9 :=
    mul_le_mul_of_nonneg_right hxqr hlog9
  have hrVertical :
      0 ≤ (Delta.topLeft.lReal - r.lReal) * Real.log 2 := by
    apply mul_nonneg
    · change 0 ≤ ((Delta.cornerL : ℤ) : ℝ) - ((r.l : ℤ) : ℝ)
      exact_mod_cast (sub_nonneg.mpr hrl)
    · exact hlog2
  have hxjNat : (Delta.topLeft.j : ℕ) ≤ (x.j : ℕ) := by
    exact_mod_cast hxj
  have hrjNat : (Delta.topLeft.j : ℕ) ≤ (r.j : ℕ) := by
    exact_mod_cast hrj
  have hxlLe : x.l ≤ Delta.topLeft.l := by
    simp [TaoSection7Triangle.topLeft, hxl]
  rw [taoSection7SoutheastWeight_eq_coordinates Delta.topLeft x hxjNat
    hxlLe]
  rw [taoSection7SoutheastWeight_eq_coordinates Delta.topLeft r hrjNat hrl]
    at hrWeight
  have hxlReal : x.lReal = Delta.topLeft.lReal := by
    change ((x.l : ℤ) : ℝ) = ((Delta.cornerL : ℤ) : ℝ)
    exact_mod_cast hxl
  rw [hxlReal]
  nlinarith

/-- Nearness controls every intermediate point on the canonical right column. -/
theorem taoSection7Near_rightColumn_weight_le
    (Delta : TaoSection7Triangle) (q x : TaoSection7Point) {rho : ℝ}
    (hrho : 0 ≤ rho) (hqNear : Delta.Near rho q)
    (hxj : x.j = Delta.cornerJ) (hqx : q.l ≤ x.l)
    (hxl : x.l ≤ Delta.cornerL) :
    taoSection7SoutheastWeight Delta.topLeft x ≤
      Delta.size + Real.log 2 * rho := by
  rcases hqNear with ⟨r, hrMem, hdist⟩
  have hrj : Delta.cornerJ ≤ r.j := hrMem.1
  have hrl : r.l ≤ Delta.cornerL := hrMem.2.1
  have hrWeight :
      taoSection7SoutheastWeight Delta.topLeft r ≤ Delta.size :=
    (taoSection7Triangle_mem_iff_southeastWeight_le Delta r hrj hrl).1 hrMem
  have hcoord := TaoSection7Point.abs_lReal_sub_le_of_distSq_le_sq
    q r hrho hdist
  have hrq : r.lReal - q.lReal ≤ rho := by
    have hneg : -(q.lReal - r.lReal) ≤ rho :=
      (neg_le_abs _).trans hcoord
    linarith
  have hrx : r.lReal - x.lReal ≤ rho := by
    have hqxReal : q.lReal ≤ x.lReal := by
      change ((q.l : ℤ) : ℝ) ≤ ((x.l : ℤ) : ℝ)
      exact_mod_cast hqx
    linarith
  have hlog9 : 0 ≤ Real.log (9 : ℝ) := (Real.log_pos (by norm_num)).le
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hxTerm :
      (r.lReal - x.lReal) * Real.log 2 ≤ rho * Real.log 2 :=
    mul_le_mul_of_nonneg_right hrx hlog2
  have hrHorizontal :
      0 ≤ (r.jReal - Delta.topLeft.jReal) * Real.log 9 := by
    apply mul_nonneg
    · apply sub_nonneg.mpr
      change (((Delta.cornerJ : ℕ) : ℝ)) ≤ (((r.j : ℕ) : ℝ))
      exact_mod_cast hrj
    · exact hlog9
  have hxjNat : (Delta.topLeft.j : ℕ) ≤ (x.j : ℕ) := by
    simp [TaoSection7Triangle.topLeft, hxj]
  have hrjNat : (Delta.topLeft.j : ℕ) ≤ (r.j : ℕ) := by
    exact_mod_cast hrj
  have hxlTop : x.l ≤ Delta.topLeft.l := by
    simpa [TaoSection7Triangle.topLeft] using hxl
  rw [taoSection7SoutheastWeight_eq_coordinates Delta.topLeft x hxjNat hxlTop]
  rw [taoSection7SoutheastWeight_eq_coordinates Delta.topLeft r hrjNat hrl]
    at hrWeight
  have hxjReal : x.jReal = Delta.topLeft.jReal := by
    simp [TaoSection7Point.jReal, TaoSection7Triangle.topLeft, hxj]
  rw [hxjReal]
  nlinarith

end

end Tao
end Erdos1135
