import Erdos1135.Tao.Fourier.Lemma74ClaimStarPropagation

/-!
# Lemma 7.4 Canonical Claim (*)

This leaf proves the two weak-black propagation cases and assembles the three
corrected cases into Claim (*) for one canonical raw triangle.  It stops
before source membership, seeds, coherence, and family assembly.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Corrected Case 2 of Claim (*): a black point strictly above the top edge
would force the selected first-white point to be black. -/
theorem taoSection7CanonicalClaimStar_case2
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon)
    (q : TaoSection7Point)
    (hqNear :
      (taoSection7CanonicalTriangle hxi hscalar p).Near
        (taoSection7TriangleSeparation epsilon) q)
    (hj :
      (taoSection7CanonicalTopLeftWitness hxi hscalar p).topLeft.j ≤ q.j)
    (hl :
      (taoSection7CanonicalTopLeftWitness hxi hscalar p).topLeft.l < q.l) :
    ¬ taoSection7SourceBlackInDomain n xi epsilon (n / 2) q := by
  intro hqBlack
  let w := taoSection7CanonicalTopLeftWitness hxi hscalar p
  let Delta := taoSection7CanonicalTriangle hxi hscalar p
  let rho := taoSection7TriangleSeparation epsilon
  let theta := taoSection7SourceTheta n xi
  let blue : TaoSection7Point := ⟨q.j, w.topLeft.l + 1⟩
  have hrho : 0 ≤ rho := by
    exact hscalar.separation_one.trans' (by norm_num)
  have hheight := taoSection7Near_height_above_corner_le
    Delta q hrho hqNear
  have hheight' : q.lReal - w.topLeft.lReal ≤ rho := by
    simpa [Delta, taoSection7CanonicalTriangle,
      TaoSection7TopLeftWitness.triangle, TaoSection7Triangle.topLeft, w] using hheight
  have hblueL : blue.l ≤ q.l := by
    dsimp [blue, w]
    omega
  have hblueWeight :
      taoSection7SoutheastWeight q blue ≤ Real.log 2 * rho := by
    rw [taoSection7SoutheastWeight_eq_coordinates q blue (by simp [blue]) hblueL]
    have hblueJ : blue.jReal = q.jReal := by rfl
    have hblueGap : q.lReal - blue.lReal ≤ rho := by
      dsimp [blue, w, TaoSection7Point.lReal] at hheight' ⊢
      norm_num at hheight' ⊢
      linarith
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
    rw [hblueJ]
    nlinarith [mul_le_mul_of_nonneg_right hblueGap hlog2]
  have hblueWeak : TaoSection7WeakBlack theta blue := by
    exact taoSection7SourceTheta_weakBlack_of_black_southeast
      q blue hqBlack.2 (by simp [blue]) hblueL hblueWeight hscalar.log_two_weak
  have hadj : TaoSection7WeakBlackAdjacency epsilon theta :=
    taoSection7SourceTheta_weakBlackAdjacency n xi epsilon
  let boundary := w.columnTopUp
  have hboundaryWeak : TaoSection7WeakBlack theta boundary := by
    rcases lt_trichotomy (q.j : ℕ) (p.1.j : ℕ) with hleft | heq | hright
    · let m := (p.1.j : ℕ) - (q.j : ℕ)
      have hm : (q.j : ℕ) + m = (p.1.j : ℕ) := by
        dsimp [m]
        omega
      have htarget : blue.rightN m = boundary := by
        apply TaoSection7Point.ext'
        · apply Subtype.ext
          calc
            ((blue.rightN m).j : ℕ) = (blue.j : ℕ) + m :=
              TaoSection7Point.rightN_j blue m
            _ = (boundary.j : ℕ) := by
              dsimp [blue, boundary, TaoSection7TopLeftWitness.columnTopUp]
              exact hm
        · simp [blue, boundary, TaoSection7TopLeftWitness.columnTopUp]
      rw [← htarget]
      apply hadj.propagate_right_rightN blue m hblueWeak
      intro k hk
      let x := (blue.rightN (k + 1)).down
      have hxLeft : w.topLeft.j ≤ x.j := by
        apply hj.trans
        change (q.j : ℕ) ≤ (x.j : ℕ)
        simp [x, blue]
      have hxRight : x.j ≤ p.1.j := by
        change (x.j : ℕ) ≤ (p.1.j : ℕ)
        simp [x, blue]
        dsimp [m] at hk
        omega
      have hxL : x.l = w.topLeft.l := by
        simp [x, blue]
      have hxBlack := w.horizontal_black x hxLeft hxRight hxL
      exact taoSection7Black_to_weak hscalar.epsilon_le_one_hundredth
        (taoSection7SourceBlackInDomain_geometryBlack hxBlack)
    · have hblueEq : blue = boundary := by
        apply TaoSection7Point.ext'
        · apply Subtype.ext
          exact heq
        · rfl
      simpa [hblueEq] using hblueWeak
    · let m := (q.j : ℕ) - (p.1.j : ℕ)
      have hm : (p.1.j : ℕ) + m = (q.j : ℕ) := by
        dsimp [m]
        omega
      have hstart : boundary.rightN m = blue := by
        apply TaoSection7Point.ext'
        · apply Subtype.ext
          calc
            ((boundary.rightN m).j : ℕ) = (boundary.j : ℕ) + m :=
              TaoSection7Point.rightN_j boundary m
            _ = (blue.j : ℕ) := by
              dsimp [boundary, blue, TaoSection7TopLeftWitness.columnTopUp]
              exact hm
        · simp [boundary, blue, TaoSection7TopLeftWitness.columnTopUp]
      apply hadj.propagate_left_rightN boundary m (by simpa [hstart] using hblueWeak)
      intro k hk
      let x := (boundary.rightN k).down
      have hxj : Delta.cornerJ ≤ x.j := by
        change w.topLeft.j ≤ x.j
        apply w.topLeft_j_le.trans
        change (p.1.j : ℕ) ≤ (x.j : ℕ)
        simp [x, boundary, TaoSection7TopLeftWitness.columnTopUp]
      have hxq : x.j ≤ q.j := by
        change (x.j : ℕ) ≤ (q.j : ℕ)
        simp [x, boundary, TaoSection7TopLeftWitness.columnTopUp]
        dsimp [m] at hk
        omega
      have hxL : x.l = Delta.cornerL := by
        simp [x, boundary, Delta, w, taoSection7CanonicalTriangle,
          TaoSection7TopLeftWitness.columnTopUp,
          TaoSection7TopLeftWitness.triangle]
      have hxWeight := taoSection7Near_topRow_weight_le
        Delta q x hrho hqNear hxj hxq hxL
      apply taoSection7Canonical_weakBlack_of_weight_le
        hxi hscalar p x
      · exact_mod_cast hxj
      · simpa [Delta, taoSection7CanonicalTriangle,
          TaoSection7TopLeftWitness.triangle] using le_of_eq hxL
      · simpa [Delta, taoSection7CanonicalTriangle,
          TaoSection7TopLeftWitness.triangle, TaoSection7Triangle.topLeft, mul_comm] using hxWeight
      · simpa [mul_comm] using hscalar.log_nine_weak
  have hcolumnTopBlack :=
    taoSection7SourceBlackInDomain_geometryBlack w.columnTop_black
  have hboundaryGeom : TaoSection7Black epsilon theta boundary := by
    apply hadj.claim_i_down boundary hboundaryWeak
    have hdownEq : boundary.down = w.columnTop := by
      apply TaoSection7Point.ext'
      · rfl
      · simp [boundary, TaoSection7TopLeftWitness.columnTopUp,
          TaoSection7TopLeftWitness.columnTop]
    rw [hdownEq]
    exact hcolumnTopBlack
  have hboundaryRaw : taoSection7SourceBlackPoint n xi epsilon boundary :=
    (taoSection7SourceBlackPoint_iff_geometryBlack n xi epsilon boundary).2
      hboundaryGeom
  apply w.columnTopUp_white
  refine ⟨?_, hboundaryRaw⟩
  simpa [boundary, TaoSection7TopLeftWitness.columnTopUp,
    taoSection7SourcePointInDomain] using p.2.1

/-- Corrected Case 3 of Claim (*): a black point left of the top-left column
would force the selected predecessor to be black. -/
theorem taoSection7CanonicalClaimStar_case3
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon)
    (q : TaoSection7Point)
    (hqNear :
      (taoSection7CanonicalTriangle hxi hscalar p).Near
        (taoSection7TriangleSeparation epsilon) q)
    (hj : q.j <
      (taoSection7CanonicalTopLeftWitness hxi hscalar p).topLeft.j) :
    ¬ taoSection7SourceBlackInDomain n xi epsilon (n / 2) q := by
  intro hqBlack
  let w := taoSection7CanonicalTopLeftWitness hxi hscalar p
  let Delta := taoSection7CanonicalTriangle hxi hscalar p
  let rho := taoSection7TriangleSeparation epsilon
  let theta := taoSection7SourceTheta n xi
  have hrho : 0 ≤ rho := by
    exact hscalar.separation_one.trans' (by norm_num)
  rcases w.left_boundary_white with hOne | ⟨hjStar, hpredWhite⟩
  · have hqPos := q.j.pos
    have hjNat : (q.j : ℕ) < (w.topLeft.j : ℕ) := by
      exact_mod_cast (show q.j < w.topLeft.j by simpa [w] using hj)
    exact (by omega : False)
  let pred := w.topLeft.left hjStar
  have hpredRight : pred.right = w.topLeft := by
    exact TaoSection7Point.right_left w.topLeft hjStar
  let green : TaoSection7Point := ⟨pred.j, q.l⟩
  have hcornerGap := taoSection7Near_corner_left_gap_le
    Delta q hrho hqNear
  have hcornerGap' : w.topLeft.jReal - q.jReal ≤ rho := by
    simpa [Delta, taoSection7CanonicalTriangle,
      TaoSection7TopLeftWitness.triangle, TaoSection7Triangle.topLeft, w] using hcornerGap
  have hqGreenJ : (q.j : ℕ) ≤ (green.j : ℕ) := by
    dsimp [green, pred]
    have hjNat : (q.j : ℕ) < (w.topLeft.j : ℕ) := by exact_mod_cast hj
    omega
  have hgreenWeight :
      taoSection7SoutheastWeight q green ≤ Real.log 9 * rho := by
    rw [taoSection7SoutheastWeight_eq_coordinates q green hqGreenJ (by rfl)]
    have hgreenL : green.lReal = q.lReal := by rfl
    have hgreenGap : green.jReal - q.jReal ≤ rho := by
      dsimp [green, pred, TaoSection7Point.jReal] at hcornerGap' ⊢
      simp at hcornerGap' ⊢
      linarith
    have hlog9 : 0 ≤ Real.log (9 : ℝ) := (Real.log_pos (by norm_num)).le
    rw [hgreenL]
    nlinarith [mul_le_mul_of_nonneg_right hgreenGap hlog9]
  have hgreenWeak : TaoSection7WeakBlack theta green :=
    taoSection7SourceTheta_weakBlack_of_black_southeast
      q green hqBlack.2 hqGreenJ (by rfl) hgreenWeight hscalar.log_nine_weak
  have hadj : TaoSection7WeakBlackAdjacency epsilon theta :=
    taoSection7SourceTheta_weakBlackAdjacency n xi epsilon
  have hpredWeak : TaoSection7WeakBlack theta pred := by
    by_cases hbelow : q.l < w.topLeft.l
    · let m := (w.topLeft.l - q.l).toNat
      have hmCast : (m : ℤ) = w.topLeft.l - q.l := by
        exact Int.toNat_of_nonneg (sub_nonneg.mpr hbelow.le)
      have htarget : green.upN m = pred := by
        apply TaoSection7Point.ext'
        · rfl
        · simp [green, pred, TaoSection7Point.upN, hmCast]
      rw [← htarget]
      apply hadj.propagate_up_upN green m hgreenWeak
      intro k hk
      let x := (green.upN (k + 1)).right
      have hxjW : x.j = w.topLeft.j := by
        have h := congrArg (fun z : TaoSection7Point => z.j) hpredRight
        simpa [x, green, TaoSection7Point.upN, TaoSection7Point.right] using h
      have hxj : x.j = Delta.cornerJ := by
        simpa [Delta, w, taoSection7CanonicalTriangle,
          TaoSection7TopLeftWitness.triangle] using hxjW
      have hqx : q.l ≤ x.l := by
        dsimp [x, green, TaoSection7Point.upN]
        omega
      have hxl : x.l ≤ Delta.cornerL := by
        have hkLe : k + 1 ≤ m := by omega
        have hkCast : ((k + 1 : ℕ) : ℤ) ≤ (m : ℤ) := by
          exact_mod_cast hkLe
        rw [hmCast] at hkCast
        change x.l ≤ w.topLeft.l
        have hxL : x.l = q.l + ((k + 1 : ℕ) : ℤ) := by
          simp [x, green, TaoSection7Point.upN]
        rw [hxL]
        omega
      have hxWeight := taoSection7Near_rightColumn_weight_le
        Delta q x hrho hqNear hxj hqx hxl
      apply taoSection7Canonical_weakBlack_of_weight_le
        hxi hscalar p x
      · exact_mod_cast hxjW.symm.le
      · simpa [Delta, w, taoSection7CanonicalTriangle,
          TaoSection7TopLeftWitness.triangle] using hxl
      · simpa [Delta, taoSection7CanonicalTriangle,
          TaoSection7TopLeftWitness.triangle, TaoSection7Triangle.topLeft, mul_comm] using hxWeight
      · simpa [mul_comm] using hscalar.log_two_weak
    · have htopLe : w.topLeft.l ≤ q.l := le_of_not_gt hbelow
      have hheight := taoSection7Near_height_above_corner_le
        Delta q hrho hqNear
      have hheight' : q.lReal - w.topLeft.lReal ≤ rho := by
        simpa [Delta, taoSection7CanonicalTriangle,
          TaoSection7TopLeftWitness.triangle, TaoSection7Triangle.topLeft, w] using hheight
      have hqPredJ : (q.j : ℕ) ≤ (pred.j : ℕ) := by
        exact hqGreenJ
      have hpredWeight :
          taoSection7SoutheastWeight q pred ≤
            (Real.log 9 + Real.log 2) * rho := by
        rw [taoSection7SoutheastWeight_eq_coordinates q pred hqPredJ htopLe]
        have hhorizontal : pred.jReal - q.jReal ≤ rho := by
          dsimp [pred, TaoSection7Point.jReal] at hcornerGap' ⊢
          simp at hcornerGap' ⊢
          linarith
        have hvertical : q.lReal - pred.lReal ≤ rho := by
          dsimp [pred]
          exact hheight'
        have hlog9 : 0 ≤ Real.log (9 : ℝ) :=
          (Real.log_pos (by norm_num)).le
        have hlog2 : 0 ≤ Real.log (2 : ℝ) :=
          (Real.log_pos (by norm_num)).le
        nlinarith [mul_le_mul_of_nonneg_right hhorizontal hlog9,
          mul_le_mul_of_nonneg_right hvertical hlog2]
      exact taoSection7SourceTheta_weakBlack_of_black_southeast
        q pred hqBlack.2 hqPredJ htopLe hpredWeight hscalar.combined_weak
  have htopLeftGeom :=
    taoSection7SourceBlackInDomain_geometryBlack w.topLeft_black
  have hpredGeom : TaoSection7Black epsilon theta pred := by
    apply hadj.claim_i_right pred hpredWeak
    simpa [hpredRight] using htopLeftGeom
  have hpredRaw : taoSection7SourceBlackPoint n xi epsilon pred :=
    (taoSection7SourceBlackPoint_iff_geometryBlack n xi epsilon pred).2 hpredGeom
  apply hpredWhite
  refine ⟨?_, hpredRaw⟩
  unfold taoSection7SourcePointInDomain
  have htopLeSource : (w.topLeft.j : ℕ) ≤ (p.1.j : ℕ) := by
    exact_mod_cast w.topLeft_j_le
  have hpredJ : (pred.j : ℕ) = (w.topLeft.j : ℕ) - 1 := by
    rfl
  rw [hpredJ]
  exact (Nat.sub_le _ _).trans (htopLeSource.trans p.2.1)

theorem taoSection7CanonicalTriangle_claimStar
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    (taoSection7CanonicalTriangle hxi hscalar p).ClaimStar
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2))
      (taoSection7TriangleSeparation epsilon) := by
  intro q hqOut hqNear
  let w := taoSection7CanonicalTopLeftWitness hxi hscalar p
  by_cases hj : w.topLeft.j ≤ q.j
  · by_cases hl : q.l ≤ w.topLeft.l
    · intro hqBlack
      have hwhite := taoSection7CanonicalClaimStar_case1
        hxi hscalar p q hqOut hqNear (by
          simpa [w, taoSection7CanonicalTriangle,
            TaoSection7TopLeftWitness.triangle] using hj) (by
          simpa [w, taoSection7CanonicalTriangle,
            TaoSection7TopLeftWitness.triangle] using hl)
      exact
        (taoSection7SourceWhitePoint_iff_not_geometryBlack n xi epsilon q).1
          hwhite (taoSection7SourceBlackInDomain_geometryBlack hqBlack)
    · exact taoSection7CanonicalClaimStar_case2 hxi hscalar p q hqNear hj
        (lt_of_not_ge hl)
  · exact taoSection7CanonicalClaimStar_case3 hxi hscalar p q hqNear
      (lt_of_not_ge hj)

end

end Tao
end Erdos1135
