import Erdos1135.ND.Band.A5AnalyticTube
import Erdos1135.ND.Band.A5RawMass

/-!
# A5 First-Shift Source Ingress

This endpoint-shaped leaf constructs the analytic packet at physical phase
`A + 1` directly inside the original same-width padded carrier.  The auxiliary
denominator `M / 2` is proof-local: every public conclusion retains the
original `M`, tube constant `C`, and physical window `J3`.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- A point in the first shifted intrinsic tube lies in the original padded
physical window.  This is the source-facing distinction from the widened
carrier-neutral shifted analytic packet. -/
private theorem ndA5FullTube_add_one_shift_mem_paddedBandWindow_of_sourceGuards
    {B j nu : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C) (hM : 0 < M)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hnu : nu ∈ ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M + 1)
      (ndA5TubeWidth B C)) :
    nu + Tao.taoSection5M0 B ∈
      ndA5PaddedBandWindow B branch C j := by
  let z := ndA5BandLower B branch j
  let A := ndA5PhysicalPhase z M
  let Mr := M / 2
  let W := ndA5TubeWidth B C
  let S := (4 / 25 : ℝ) * W + Real.log 2
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hYpos : 0 < Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos hBpos _
  have hz : 0 < z := by
    dsimp [z]
    unfold ndA5BandLower
    positivity
  have hMr : 0 < Mr := by
    dsimp [Mr]
    positivity
  have hphase : ndA5PhysicalPhase z Mr = A + 1 := by
    simpa [A, Mr] using ndA5PhysicalPhase_div_two hz hM
  have hshiftMrEq :
      ndA5InteriorShift B Mr =
        ndA5InteriorShift B M - Real.log 2 := by
    simpa [Mr] using ndA5InteriorShift_div_two (B := B) hM
  have hlogTwoPos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hshiftMr : |ndA5InteriorShift B Mr| ≤ S := by
    rw [hshiftMrEq]
    calc
      |ndA5InteriorShift B M - Real.log 2| ≤
          |ndA5InteriorShift B M| + |Real.log 2| := abs_sub _ _
      _ ≤ (4 / 25 : ℝ) * W + Real.log 2 := by
        rw [abs_of_pos hlogTwoPos]
        simpa [W] using
          add_le_add hshift (le_refl (Real.log 2))
      _ = S := by rfl
  have hmargin :
      S / ndA5LogFourThirds + (W + 1) / ndA5PhaseDelta ≤
        3 * W := by
    simpa [S, W] using ndA5FirstShiftContainmentMargin hC hlogB
  have hnu' : nu ∈ ndA5FullTube (A + 1) W := by
    simpa [A, W, z] using hnu
  have hnuMr : nu ∈ ndA5FullTube (ndA5PhysicalPhase z Mr) W := by
    rw [hphase]
    exact hnu'
  apply ndA5FullTube_shift_mem_paddedBandWindow_of_crossWidthMargin
    (B := B) (j := j) (nu := nu) (branch := branch)
    (C := C) (Cpad := C) (M := Mr) (S := S)
    hB hMr hshiftMr hmargin
  simpa [z, W] using hnuMr

/-- The first neighboring analytic packet under the original v10 source
guards.  No widened tube constant or widened physical carrier occurs in the
result. -/
theorem ndA5AnalyticTubeFacts_add_one_of_sourceGuards
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C) (hM : 0 < M)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hj : j < ndA5BandCount B branch) :
    NDA5AnalyticTubeFacts B C
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M + 1) := by
  let z := ndA5BandLower B branch j
  let A := ndA5PhysicalPhase z M
  let Mr := M / 2
  let W := ndA5TubeWidth B C
  let S := (4 / 25 : ℝ) * W + Real.log 2
  let N := Real.log (z / (B : ℝ)) / ndA5LogFourThirds
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hYpos : 0 < Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos hBpos _
  have hz : 0 < z := by
    dsimp [z]
    unfold ndA5BandLower
    positivity
  have hMr : 0 < Mr := by
    dsimp [Mr]
    positivity
  have hphase : ndA5PhysicalPhase z Mr = A + 1 := by
    simpa [A, Mr] using ndA5PhysicalPhase_div_two hz hM
  have hshiftMrEq :
      ndA5InteriorShift B Mr =
        ndA5InteriorShift B M - Real.log 2 := by
    simpa [Mr] using ndA5InteriorShift_div_two (B := B) hM
  have hlogTwoPos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  have hW : (142 : ℝ) ≤ W := by
    simpa [W] using
      ndA5TubeWidth_ge_one_hundred_forty_two hC hlogB
  have hWpos : 0 < W := by linarith
  have hWone : 1 < W := by linarith
  have hshiftMr : |ndA5InteriorShift B Mr| ≤ S := by
    rw [hshiftMrEq]
    calc
      |ndA5InteriorShift B M - Real.log 2| ≤
          |ndA5InteriorShift B M| + |Real.log 2| := abs_sub _ _
      _ ≤ (4 / 25 : ℝ) * W + Real.log 2 := by
        rw [abs_of_pos hlogTwoPos]
        simpa [W] using
          add_le_add hshift (le_refl (Real.log 2))
      _ = S := by rfl
  have hmargin :
      S / ndA5LogFourThirds + (W + 1) / ndA5PhaseDelta ≤
        3 * W := by
    simpa [S, W] using ndA5FirstShiftContainmentMargin hC hlogB
  have hroom := ndA5PaddedBandLower_sub_m0_lower_of_guards
    (C := C) hB hlogB hpadding hj
  have hscale :
      (1020 : ℝ) ≤ (340 / 100000 : ℝ) * Real.log B := by
    nlinarith
  have hroom' :
      (1020 : ℝ) ≤ N - 3 * W - (Tao.taoSection5M0 B : ℝ) := by
    have h := hscale.trans hroom
    simpa [ndA5PaddedBandLower, N, z, W] using h
  have hroundPos : 0 < (W + 1) / ndA5PhaseDelta :=
    div_pos (by linarith) ndA5PhaseDelta_mem_Ioo.1
  have hSdiv : S / ndA5LogFourThirds < 3 * W := by
    linarith
  have hshiftMrUpper : ndA5InteriorShift B Mr ≤ S :=
    (le_abs_self _).trans hshiftMr
  have hshiftMrDiv :
      ndA5InteriorShift B Mr / ndA5LogFourThirds < 3 * W :=
    (div_le_div_of_nonneg_right hshiftMrUpper
      ndA5LogFourThirds_pos.le).trans_lt hSdiv
  have hcenterPos :
      0 < N - (Tao.taoSection5M0 B : ℝ) -
        ndA5InteriorShift B Mr / ndA5LogFourThirds := by
    linarith
  have hcenterEq :=
    ndA5PhysicalPhase_sub_phaseDelta_mul_eq_centered
      (B := B) (j := j) (nu := 0) (branch := branch) (M := Mr) hB hMr
  have hphaseEq :
      ndA5PhysicalPhase z Mr =
        ndA5PhaseDelta *
          (N - (Tao.taoSection5M0 B : ℝ) -
            ndA5InteriorShift B Mr / ndA5LogFourThirds) := by
    simpa [z, N] using hcenterEq
  have hphasePos : 0 < ndA5PhysicalPhase z Mr := by
    rw [hphaseEq]
    exact mul_pos ndA5PhaseDelta_mem_Ioo.1 hcenterPos
  have hAonePos : 0 < A + 1 := by
    rw [← hphase]
    exact hphasePos
  have hne : (ndA5FullTube (A + 1) W).Nonempty :=
    ndA5FullTube_nonempty_of_phase_pos hAonePos hWone
  refine
    { one_half_le_C := hC
      nonempty := by simpa [A, W, z] using hne
      pointwise := ?_ }
  intro nu hnu
  have hnu' : nu ∈ ndA5FullTube (A + 1) W := by
    simpa [A, W, z] using hnu
  have hcarrier :
      nu + Tao.taoSection5M0 B ∈
        ndA5PaddedBandWindow B branch C j :=
    ndA5FullTube_add_one_shift_mem_paddedBandWindow_of_sourceGuards
      hB hlogB hC hM hshift hnu
  have ht2 : NDA5T2ScaleFacts B
      (nu + Tao.taoSection5M0 B) C :=
    ndA5PaddedBandWindow_t2_of_guards
      hB hlogB hpadding hj hcarrier
  have hsub :
      nu + Tao.taoSection5M0 B - Tao.taoSection5M0 B = nu := by
    omega
  have hnuPos := ht2.nu_pos
  rw [hsub] at hnuPos
  have hWle := ht2.width_le_nu_div_eight
  rw [hsub] at hWle
  have hlevel : NDA5PhysicalLevelFacts (A + 1) nu :=
    ndA5PhysicalLevelFacts_of_mem_fullTube hnuPos
      (by simpa [W] using hWle) hnu'
  exact
    { t2 := ht2
      level := by simpa [A, z] using hlevel }

/-- The first shifted intrinsic tube is explicitly admissible in the original
positive physical source carrier.  Only subset is claimed: the padded carrier
is generally larger. -/
theorem ndA5FullTube_add_one_subset_physicalNuWindow_of_sourceGuards
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hC : (1 / 2 : ℝ) ≤ C) (hM : 0 < M)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hj : j < ndA5BandCount B branch) :
    ndA5FullTube
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M + 1)
        (ndA5TubeWidth B C) ⊆
      ndA5PhysicalNuWindow B branch C j := by
  intro nu hnu
  have hTube1 := ndA5AnalyticTubeFacts_add_one_of_sourceGuards
    hB hlogB hC hM hpadding hshift hj
  have hcell := hTube1.pointwise nu hnu
  have hsub :
      nu + Tao.taoSection5M0 B - Tao.taoSection5M0 B = nu := by
    omega
  have hnuPos := hcell.t2.nu_pos
  rw [hsub] at hnuPos
  have hcarrier :
      nu + Tao.taoSection5M0 B ∈
        ndA5PaddedBandWindow B branch C j :=
    ndA5FullTube_add_one_shift_mem_paddedBandWindow_of_sourceGuards
      hB hlogB hC hM hshift hnu
  exact mem_ndA5PhysicalNuWindow_iff.mpr ⟨hnuPos, hcarrier⟩

end

end ND
end Erdos1135
