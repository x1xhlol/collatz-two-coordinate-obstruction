/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Lemma74CanonicalClaimStar

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Point

@[simp] theorem distSq_right_self (p : TaoSection7Point) :
    p.right.distSq p = 1 := by
  simp [distSq, jReal, lReal, right]

@[simp] theorem distSq_down_self (p : TaoSection7Point) :
    p.down.distSq p = 1 := by
  simp [distSq, jReal, lReal, down]

end TaoSection7Point

namespace TaoSection7Triangle.ClaimStar

theorem black_unitNeighbor_mem
    {black : TaoSection7Point → Prop} {rho : ℝ}
    {Delta : TaoSection7Triangle}
    (hstar : Delta.ClaimStar black rho) (hunit : (1 : ℝ) ≤ rho ^ 2)
    {p q : TaoSection7Point} (hq : Delta.Mem q) (hpblack : black p)
    (hdist : p.distSq q = 1) :
    Delta.Mem p := by
  exact hstar.black_near_mem hpblack ⟨q, hq, hdist.trans_le hunit⟩

theorem mem_of_nat_path
    {black : TaoSection7Point → Prop} {rho : ℝ}
    {Delta : TaoSection7Triangle}
    (hstar : Delta.ClaimStar black rho)
    (path : ℕ → TaoSection7Point) (m : ℕ)
    (hstart : Delta.Mem (path 0))
    (hstep : ∀ k < m,
      black (path (k + 1)) ∧
        (path (k + 1)).distSq (path k) ≤ rho ^ 2) :
    Delta.Mem (path m) := by
  induction m with
  | zero => simpa using hstart
  | succ m ih =>
      have hprev : Delta.Mem (path m) :=
        ih (fun k hk => hstep k (by omega))
      exact hstar.black_near_mem (hstep m (by omega)).1
        ⟨path m, hprev, (hstep m (by omega)).2⟩

end TaoSection7Triangle.ClaimStar

namespace TaoSection7TopLeftWitness

theorem source_mem_of_claimStar
    {black : TaoSection7Point → Prop} {p : TaoSection7Point}
    (w : TaoSection7TopLeftWitness black p) {size rho : ℝ}
    (hsize : 0 ≤ size) (hunit : (1 : ℝ) ≤ rho ^ 2)
    (hstar : (w.triangle size).ClaimStar black rho) :
    (w.triangle size).Mem p := by
  let H := taoSection7SoutheastH w.topLeft p
  let V := taoSection7SoutheastV w.topLeft p
  have hjNat : (w.topLeft.j : ℕ) ≤ (p.j : ℕ) := by
    exact_mod_cast w.topLeft_j_le
  have hVCast : (V : ℤ) = w.topLeft.l - p.l := by
    exact taoSection7SoutheastV_intCast w.topLeft p w.source_l_le_topLeft_l
  have htopMem : (w.triangle size).Mem w.topLeft :=
    w.triangle_topLeft_mem hsize
  have hrowBlack : ∀ k, k ≤ H → black (w.topLeft.rightN k) := by
    intro k hk
    apply w.horizontal_black
    · change (w.topLeft.j : ℕ) ≤ ((w.topLeft.rightN k).j : ℕ)
      simp
    · change ((w.topLeft.rightN k).j : ℕ) ≤ (p.j : ℕ)
      rw [TaoSection7Point.rightN_j]
      dsimp [H, taoSection7SoutheastH] at hk
      omega
    · simp
  have hrowMem : (w.triangle size).Mem (w.topLeft.rightN H) := by
    apply hstar.mem_of_nat_path (fun k => w.topLeft.rightN k) H
    · simpa using htopMem
    · intro k hk
      constructor
      · exact hrowBlack (k + 1) (by omega)
      · rw [TaoSection7Point.rightN_succ]
        simpa using hunit
  have hrowEnd : w.topLeft.rightN H = w.columnTop := by
    apply TaoSection7Point.ext'
    · apply Subtype.ext
      calc
        ((w.topLeft.rightN H).j : ℕ) = (w.topLeft.j : ℕ) + H :=
          TaoSection7Point.rightN_j w.topLeft H
        _ = (w.columnTop.j : ℕ) := by
          dsimp [H, taoSection7SoutheastH, columnTop]
          omega
    · simp [columnTop]
  have hcolumnTopMem : (w.triangle size).Mem w.columnTop := by
    rw [← hrowEnd]
    exact hrowMem
  have hcolumnBlack : ∀ k, k ≤ V → black (w.columnTop.downN k) := by
    intro k hk
    apply w.vertical_black
    · rfl
    · have hkInt : (k : ℤ) ≤ (V : ℤ) := by exact_mod_cast hk
      simp [columnTop, TaoSection7Point.downN]
      omega
    · simp [columnTop, TaoSection7Point.downN]
  have hsourcePathMem : (w.triangle size).Mem (w.columnTop.downN V) := by
    apply hstar.mem_of_nat_path (fun k => w.columnTop.downN k) V
    · simpa using hcolumnTopMem
    · intro k hk
      constructor
      · exact hcolumnBlack (k + 1) (by omega)
      · rw [TaoSection7Point.downN_succ]
        simpa using hunit
  have hsourceEnd : w.columnTop.downN V = p := by
    apply TaoSection7Point.ext'
    · rfl
    · simp [columnTop, TaoSection7Point.downN, hVCast]
  simpa only [hsourceEnd] using hsourcePathMem

end TaoSection7TopLeftWitness

theorem taoSection7CanonicalTriangle_source_mem
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p : TaoSection7CanonicalBlackPoint n xi epsilon) :
    (taoSection7CanonicalTriangle hxi hscalar p).Mem p.1 := by
  let w := taoSection7CanonicalTopLeftWitness hxi hscalar p
  let size := taoSection7CanonicalTriangleSize hxi hscalar p
  let rho := taoSection7TriangleSeparation epsilon
  have hsize : 0 ≤ size := by
    simpa [size] using taoSection7CanonicalTriangleSize_nonneg hxi hscalar p
  have hunit : (1 : ℝ) ≤ rho ^ 2 := by
    have hrho : 1 ≤ rho := by simpa [rho] using hscalar.separation_one
    nlinarith [sq_nonneg rho]
  have hstar : (w.triangle size).ClaimStar
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) rho := by
    simpa [w, size, rho, taoSection7CanonicalTriangle] using
      taoSection7CanonicalTriangle_claimStar hxi hscalar p
  change (w.triangle size).Mem p.1
  exact w.source_mem_of_claimStar hsize hunit hstar

end

end Tao

end Erdos1135Predecessor
