/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Lemma74CanonicalSourceMem

/-!
# Lemma 7.4 Canonical Selector Coherence

This leaf proves that every domain-black member of a canonical triangle
reconstructs the same vertical and horizontal selectors, hence the same
canonical triangle.  It stops before overlap uniqueness and family assembly.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Triangle

/-- Triangle membership is closed under moving northwest while remaining in
the southeast quadrant of the top-left corner. -/
theorem mem_northwest_of_mem
    {Delta : TaoSection7Triangle} {p q : TaoSection7Point}
    (hp : Delta.Mem p)
    (hjLeft : Delta.cornerJ ≤ q.j) (hjRight : q.j ≤ p.j)
    (hlLower : p.l ≤ q.l) (hlUpper : q.l ≤ Delta.cornerL) :
    Delta.Mem q := by
  have hpj : Delta.cornerJ ≤ p.j := hp.1
  have hpl : p.l ≤ Delta.cornerL := hp.2.1
  have hpWeight :
      taoSection7SoutheastWeight Delta.topLeft p ≤ Delta.size :=
    (taoSection7Triangle_mem_iff_southeastWeight_le
      Delta p hpj hpl).1 hp
  have hjReal : q.jReal ≤ p.jReal := by
    change (((q.j : ℕ) : ℝ)) ≤ (((p.j : ℕ) : ℝ))
    exact_mod_cast hjRight
  have hlReal : p.lReal ≤ q.lReal := by
    change ((p.l : ℤ) : ℝ) ≤ ((q.l : ℤ) : ℝ)
    exact_mod_cast hlLower
  have hlog9 : 0 ≤ Real.log (9 : ℝ) := (Real.log_pos (by norm_num)).le
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hjTerm :
      (q.jReal - Delta.topLeft.jReal) * Real.log 9 ≤
        (p.jReal - Delta.topLeft.jReal) * Real.log 9 :=
    mul_le_mul_of_nonneg_right (by linarith) hlog9
  have hlTerm :
      (Delta.topLeft.lReal - q.lReal) * Real.log 2 ≤
        (Delta.topLeft.lReal - p.lReal) * Real.log 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hlog2
  have hqjNat : (Delta.topLeft.j : ℕ) ≤ (q.j : ℕ) := by
    exact_mod_cast hjLeft
  have hpjNat : (Delta.topLeft.j : ℕ) ≤ (p.j : ℕ) := by
    exact_mod_cast hpj
  rw [taoSection7SoutheastWeight_eq_coordinates
      Delta.topLeft p hpjNat hpl] at hpWeight
  apply (taoSection7Triangle_mem_iff_southeastWeight_le
    Delta q hjLeft hlUpper).2
  rw [taoSection7SoutheastWeight_eq_coordinates
    Delta.topLeft q hqjNat hlUpper]
  linarith

theorem not_mem_above_corner
    (Delta : TaoSection7Triangle) (j : ℕ+) :
    ¬ Delta.Mem ⟨j, Delta.cornerL + 1⟩ := by
  intro h
  have := TaoSection7Triangle.mem_height_le h
  simp at this

end TaoSection7Triangle

theorem taoSection7CanonicalLStar_eq_of_mem
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p q : TaoSection7CanonicalBlackPoint n xi epsilon)
    (hq : (taoSection7CanonicalTriangle hxi hscalar p).Mem q.1) :
    taoSection7CanonicalLStar hxi hscalar q =
      taoSection7CanonicalLStar hxi hscalar p := by
  let Delta := taoSection7CanonicalTriangle hxi hscalar p
  let Lp := taoSection7CanonicalLStar hxi hscalar p
  let rho := taoSection7TriangleSeparation epsilon
  let top : TaoSection7Point := ⟨q.1.j, Lp⟩
  let above : TaoSection7Point := ⟨q.1.j, Lp + 1⟩
  have hcornerL : Delta.cornerL = Lp := by rfl
  have hqLower : q.1.l ≤ Lp := by
    simpa [hcornerL] using TaoSection7Triangle.mem_height_le hq
  have htopMem : Delta.Mem top := by
    apply TaoSection7Triangle.mem_northwest_of_mem hq
    · simpa [top] using hq.1
    · rfl
    · exact hqLower
    · exact hcornerL.symm.le
  have haboveOut : ¬ Delta.Mem above := by
    simpa [above, hcornerL] using
      TaoSection7Triangle.not_mem_above_corner Delta q.1.j
  have hunit : (1 : ℝ) ≤ rho ^ 2 := by
    have hrho : 1 ≤ rho := by simpa [rho] using hscalar.separation_one
    nlinarith [sq_nonneg rho]
  have hstar : Delta.ClaimStar
      (taoSection7SourceBlackInDomain n xi epsilon (n / 2)) rho := by
    simpa [Delta, rho] using
      taoSection7CanonicalTriangle_claimStar hxi hscalar p
  have haboveDist : above.distSq top = 1 := by
    simp [above, top, TaoSection7Point.distSq,
      TaoSection7Point.jReal, TaoSection7Point.lReal]
  have haboveNotDomain :
      ¬ taoSection7SourceBlackInDomain n xi epsilon (n / 2) above := by
    intro haboveBlack
    have haboveMem := hstar.black_unitNeighbor_mem hunit htopMem
      haboveBlack haboveDist
    exact haboveOut haboveMem
  have haboveDomain : taoSection7SourcePointInDomain (n / 2) above := by
    simpa [above, taoSection7SourcePointInDomain] using q.2.1
  have haboveWhite : taoSection7SourceWhitePoint n xi epsilon above := by
    apply (taoSection7SourceWhitePoint_iff_not_geometryBlack
      n xi epsilon above).2
    intro haboveGeom
    apply haboveNotDomain
    exact ⟨haboveDomain,
      (taoSection7SourceBlackPoint_iff_geometryBlack
        n xi epsilon above).2 haboveGeom⟩
  have hblackOn := taoSection7CanonicalTriangle_blackOn hxi hscalar p
  have hvertical : ∀ r : TaoSection7Point,
      r.j = q.1.j → q.1.l ≤ r.l → r.l ≤ Lp →
        taoSection7SourceBlackPoint n xi epsilon r := by
    intro r hrj hrl hru
    have hrMem : Delta.Mem r := by
      apply TaoSection7Triangle.mem_northwest_of_mem hq
      · simpa [hrj] using hq.1
      · simp [hrj]
      · exact hrl
      · simpa [hcornerL] using hru
    exact (hblackOn r (by simpa [Delta] using hrMem)).2
  have hunique := taoSection7CanonicalLStar_unique
    hxi hscalar q Lp hqLower hvertical (by simpa [above] using haboveWhite)
  exact hunique.symm

theorem taoSection7CanonicalJStart_eq_of_mem
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p q : TaoSection7CanonicalBlackPoint n xi epsilon)
    (hq : (taoSection7CanonicalTriangle hxi hscalar p).Mem q.1) :
    taoSection7CanonicalJStart hxi hscalar q =
      taoSection7CanonicalJStart hxi hscalar p := by
  let Delta := taoSection7CanonicalTriangle hxi hscalar p
  let Lp := taoSection7CanonicalLStar hxi hscalar p
  let Lq := taoSection7CanonicalLStar hxi hscalar q
  let a := taoSection7CanonicalJStart hxi hscalar p
  let black := taoSection7SourceBlackInDomain n xi epsilon (n / 2)
  have hL : Lq = Lp := by
    simpa [Lq, Lp] using taoSection7CanonicalLStar_eq_of_mem
      hxi hscalar p q hq
  have hcornerL : Delta.cornerL = Lp := by rfl
  have hcornerJNat : (Delta.cornerJ : ℕ) = a := by rfl
  have haPos : 1 ≤ a := by
    exact (taoSection7CanonicalJStart_spec hxi hscalar p).1
  have haEnd : a ≤ (q.1.j : ℕ) := by
    have hcorner := hq.1
    exact_mod_cast (show Delta.cornerJ ≤ q.1.j from hcorner)
  have hqLower : q.1.l ≤ Lp := by
    simpa [hcornerL] using TaoSection7Triangle.mem_height_le hq
  have hsuffix : taoSection7BlackSuffix black q.1.j Lq a := by
    intro r hleft hright
    let x : TaoSection7Point := ⟨r, Lq⟩
    have hxMem : Delta.Mem x := by
      apply TaoSection7Triangle.mem_northwest_of_mem hq
      · change Delta.cornerJ ≤ r
        exact_mod_cast (show a ≤ (r : ℕ) from hleft)
      · exact hright
      · dsimp [x]
        rw [hL]
        exact hqLower
      · dsimp [x]
        rw [hL, hcornerL]
    have hblackOn := taoSection7CanonicalTriangle_blackOn hxi hscalar p
    exact hblackOn x (by simpa [Delta] using hxMem)
  have hboundary : a = 1 ∨
      ∃ h : 1 < a, ¬ black ⟨⟨a - 1, by omega⟩, Lq⟩ := by
    rcases taoSection7CanonicalJStart_boundary hxi hscalar p with hOne | hpred
    · exact Or.inl hOne
    · right
      rcases hpred with ⟨h, hnot⟩
      refine ⟨h, ?_⟩
      simpa [black, a, Lq, hL, Lp] using hnot
  have hqEnd := taoSection7CanonicalLStar_blackInDomain hxi hscalar q
  have hunique := taoSection7TerminalBlackRunStart_unique
    black q.1.j Lq hqEnd a haPos haEnd hsuffix hboundary
  have hcanon : a = taoSection7CanonicalJStart hxi hscalar q := by
    simpa [taoSection7CanonicalJStart, black, Lq] using hunique
  exact hcanon.symm

theorem taoSection7CanonicalJStar_eq_of_mem
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p q : TaoSection7CanonicalBlackPoint n xi epsilon)
    (hq : (taoSection7CanonicalTriangle hxi hscalar p).Mem q.1) :
    taoSection7CanonicalJStar hxi hscalar q =
      taoSection7CanonicalJStar hxi hscalar p := by
  apply Subtype.ext
  exact taoSection7CanonicalJStart_eq_of_mem hxi hscalar p q hq

theorem taoSection7CanonicalTopLeft_eq_of_mem
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p q : TaoSection7CanonicalBlackPoint n xi epsilon)
    (hq : (taoSection7CanonicalTriangle hxi hscalar p).Mem q.1) :
    (taoSection7CanonicalTopLeftWitness hxi hscalar q).topLeft =
      (taoSection7CanonicalTopLeftWitness hxi hscalar p).topLeft := by
  apply TaoSection7Point.ext'
  · simpa [taoSection7CanonicalTopLeftWitness] using
      taoSection7CanonicalJStar_eq_of_mem hxi hscalar p q hq
  · simpa [taoSection7CanonicalTopLeftWitness] using
      taoSection7CanonicalLStar_eq_of_mem hxi hscalar p q hq

theorem taoSection7CanonicalTriangle_eq_of_mem
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi)
    (hscalar : TaoSection7ClaimStarScalarPacket epsilon)
    (p q : TaoSection7CanonicalBlackPoint n xi epsilon)
    (hq : (taoSection7CanonicalTriangle hxi hscalar p).Mem q.1) :
    taoSection7CanonicalTriangle hxi hscalar q =
      taoSection7CanonicalTriangle hxi hscalar p := by
  have htop := taoSection7CanonicalTopLeft_eq_of_mem hxi hscalar p q hq
  have hsize : taoSection7CanonicalTriangleSize hxi hscalar q =
      taoSection7CanonicalTriangleSize hxi hscalar p := by
    unfold taoSection7CanonicalTriangleSize
    rw [htop]
  unfold taoSection7CanonicalTriangle TaoSection7TopLeftWitness.triangle
  congr 1
  · exact congrArg (fun x : TaoSection7Point => x.j) htop
  · exact congrArg (fun x : TaoSection7Point => x.l) htop

end

end Tao
end Erdos1135SecondScale
