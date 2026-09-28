import Erdos1135.ND.Band.A5Physical
import Erdos1135.Tao.Section5.AffineSourceScale

/-!
# A5 Exact Affine Correction

This leaf bounds the exact affine offset before the nominal A5 level profile
is used.  The source identity involves `M - F`, not `M`; the resulting
position correction is therefore retained explicitly and charged once at the
later strip-boundary consumer.

The exponent arithmetic is local to the actual `(t2)` range:
`nu <= 0.0105 log B` and `log 3 < 1.1` give `F <= B^0.01155`, while an
interior endpoint has `M >= B^0.999`.  Thus `F / M <= B^-0.98745`, which
is strong enough to make the logarithmic correction at most `B^-0.9`.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- A rational upper bound for `log 3`, proved from the positive-term
Taylor lower bound for the exponential. -/
theorem ndA5_log_three_lt_eleven_tenths :
    Real.log (3 : ℝ) < 11 / 10 := by
  have hsum :
      (3 : ℝ) < ∑ i ∈ Finset.range 6,
        (11 / 10 : ℝ) ^ i / Nat.factorial i := by
    norm_num [Finset.sum_range_succ]
  have hle := Real.sum_le_exp_of_nonneg
    (by norm_num : (0 : ℝ) ≤ 11 / 10) 6
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)).2
    (hsum.trans_le hle)

/-- The visible interior-shift and padding guards place every consumed
endpoint above `B^0.999`.  This intentionally uses only the lower endpoint
information; no `EPrime` or probability hypothesis is involved. -/
theorem ndA5_rpow_999_div_1000_le_endpoint
    {B : ℕ} {C M : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B) (hM : 0 < M)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C) :
    (B : ℝ) ^ (999 / 1000 : ℝ) ≤ M := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hlogB0 : 0 ≤ Real.log B := by linarith
  have hwidth : ndA5TubeWidth B C ≤
      (11 / 500000 : ℝ) * Real.log B := by
    linarith
  have hshiftLower := (abs_le.mp hshift).1
  have hm0term :
      0 ≤ (Tao.taoSection5M0 B : ℝ) * ndA5LogFourThirds :=
    mul_nonneg (Nat.cast_nonneg _) ndA5LogFourThirds_pos.le
  have hlogM :
      (999 / 1000 : ℝ) * Real.log B ≤ Real.log M := by
    unfold ndA5InteriorShift at hshiftLower
    nlinarith
  rw [Real.rpow_def_of_pos hBpos, ← Real.exp_log hM]
  exact Real.exp_monotone (by simpa [mul_comm] using hlogM)

/-- Source-facing endpoint lower bound.  Membership in the checked Section 5
target already places `M` above the canonical lost-window lower endpoint, so
the affine-source packet removes every band, padding, and interior-shift
assumption from this adapter. -/
theorem ndA5_rpow_999_div_1000_le_ePrime_endpoint
    {B M : ℕ} {E : Set ℕ}
    (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    (hM : M ∈ Tao.taoSection5EPrime B E) :
    (B : ℝ) ^ (999 / 1000 : ℝ) ≤ (M : ℝ) := by
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast facts.schedule.one_le_B
  have hBOne : (1 : ℝ) ≤ B := by
    exact_mod_cast facts.schedule.one_le_B
  have hexpOne :
      1 ≤ Real.exp (2 * Real.log 2 * Tao.taoSection5TypicalSlack B) := by
    apply Real.one_le_exp
    have hslack : 0 ≤ Tao.taoSection5TypicalSlack B := by
      unfold Tao.taoSection5TypicalSlack
      exact Real.rpow_nonneg (Real.log_nonneg hBOne) _
    positivity
  have hBmain :
      (B : ℝ) ≤
        Real.exp (2 * Real.log 2 * Tao.taoSection5TypicalSlack B) * B := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hexpOne hBpos.le
  have hBlower :
      (B : ℝ) < Tao.taoSection5CanonicalLostLower B :=
    hBmain.trans_lt
      ((le_add_of_nonneg_right (by positivity :
          0 ≤ (3 : ℝ) ^ Tao.taoSection5N0 B)).trans_lt facts.reverseBudget)
  have hMlower :
      Tao.taoSection5CanonicalLostLower B ≤ (M : ℝ) :=
    Nat.ceil_le.mp (Tao.mem_taoSection5EPrime_iff.mp hM).1
  have hpow :
      (B : ℝ) ^ (999 / 1000 : ℝ) ≤ (B : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hBOne (by norm_num)
  have hpow' : (B : ℝ) ^ (999 / 1000 : ℝ) ≤ (B : ℝ) := by
    simpa only [Real.rpow_one] using hpow
  exact hpow'.trans (hBlower.le.trans hMlower)

/-- The coarse affine offset has the exact local exponent needed by the
once-only denominator correction. -/
theorem ndA5_affineOffset_le_rpow_231_div_20000
    {B nu : ℕ} {as : List ℕ+}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hlen : as.length = nu)
    (hnu : (nu : ℝ) ≤ (105 / 10000 : ℝ) * Real.log B) :
    (Tao.taoOffsetList as : ℝ) ≤
      (B : ℝ) ^ (231 / 20000 : ℝ) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hlogB0 : 0 ≤ Real.log B := by linarith
  have hlogThree0 : 0 ≤ Real.log (3 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hmul :
      (nu : ℝ) * Real.log 3 ≤
        ((105 / 10000 : ℝ) * Real.log B) * (11 / 10 : ℝ) :=
    mul_le_mul hnu ndA5_log_three_lt_eleven_tenths.le
      hlogThree0 (mul_nonneg (by norm_num) hlogB0)
  have hexponent :
      (nu : ℝ) * Real.log 3 ≤
        (231 / 20000 : ℝ) * Real.log B := by
    nlinarith
  have hoffsetQ := Tao.taoOffsetList_le_three_pow_length as
  have hoffsetR :
      (Tao.taoOffsetList as : ℝ) ≤ (3 : ℝ) ^ as.length := by
    exact_mod_cast hoffsetQ
  rw [hlen] at hoffsetR
  calc
    (Tao.taoOffsetList as : ℝ) ≤ (3 : ℝ) ^ nu := hoffsetR
    _ = Real.exp ((nu : ℝ) * Real.log 3) := by
      calc
        (3 : ℝ) ^ nu = (3 : ℝ) ^ (nu : ℝ) :=
          (Real.rpow_natCast (3 : ℝ) nu).symm
        _ = Real.exp (Real.log 3 * (nu : ℝ)) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
        _ = Real.exp ((nu : ℝ) * Real.log 3) := by ring_nf
    _ ≤ Real.exp ((231 / 20000 : ℝ) * Real.log B) :=
      Real.exp_monotone hexponent
    _ = (B : ℝ) ^ (231 / 20000 : ℝ) := by
      rw [Real.rpow_def_of_pos hBpos]
      ring_nf

/-- Quantitative affine ratio at the actual A5 scale.  This is stronger than
the global Section 5 `B^(-4/5)` denominator ratio because it retains the
local passage length `nu` instead of replacing it by `n0`. -/
theorem ndA5_affineOffset_div_endpoint_le_rpow_neg_19749_div_20000
    {B nu : ℕ} {C M : ℝ} {as : List ℕ+}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B) (hM : 0 < M)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hlen : as.length = nu)
    (hnu : (nu : ℝ) ≤ (105 / 10000 : ℝ) * Real.log B) :
    0 ≤ (Tao.taoOffsetList as : ℝ) / M ∧
      (Tao.taoOffsetList as : ℝ) / M ≤
        (B : ℝ) ^ (-(19749 / 20000 : ℝ)) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hoffset0 : 0 ≤ (Tao.taoOffsetList as : ℝ) :=
    Rat.cast_nonneg.mpr (Tao.taoOffsetList_nonneg as)
  have hoffset := ndA5_affineOffset_le_rpow_231_div_20000
    hB hlogB hlen hnu
  have hendpoint := ndA5_rpow_999_div_1000_le_endpoint
    hB hlogB hM hpadding hshift
  refine ⟨div_nonneg hoffset0 hM.le, ?_⟩
  calc
    (Tao.taoOffsetList as : ℝ) / M ≤
        (B : ℝ) ^ (231 / 20000 : ℝ) / M :=
      div_le_div_of_nonneg_right hoffset hM.le
    _ ≤ (B : ℝ) ^ (231 / 20000 : ℝ) /
        (B : ℝ) ^ (999 / 1000 : ℝ) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hBpos.le _)
        (Real.rpow_pos_of_pos hBpos _) hendpoint
    _ = (B : ℝ) ^ (-(19749 / 20000 : ℝ)) := by
      rw [← Real.rpow_sub hBpos]
      norm_num

/-- Source-facing local affine ratio.  The `EPrime` endpoint packet supplies
the denominator scale, while the checked `(t2)` packet supplies the actual
passage length rather than the much larger global `n0`. -/
theorem ndA5_affineOffset_div_ePrime_le_rpow_neg_19749_div_20000
    {B n M : ℕ} {C : ℝ} {E : Set ℕ} {as : List ℕ+}
    (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hM : M ∈ Tao.taoSection5EPrime B E)
    (ht2 : NDA5T2ScaleFacts B n C)
    (hlen : as.length = n - Tao.taoSection5M0 B) :
    0 ≤ (Tao.taoOffsetList as : ℝ) / (M : ℝ) ∧
      (Tao.taoOffsetList as : ℝ) / (M : ℝ) ≤
        (B : ℝ) ^ (-(19749 / 20000 : ℝ)) := by
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast facts.schedule.one_le_B
  have hMposNat : 0 < M :=
    Odd.pos (Tao.mem_taoSection5EPrime_iff.mp hM).2.2.1
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hMposNat
  have hoffset0 : 0 ≤ (Tao.taoOffsetList as : ℝ) :=
    Rat.cast_nonneg.mpr (Tao.taoOffsetList_nonneg as)
  have hoffset := ndA5_affineOffset_le_rpow_231_div_20000
    facts.schedule.one_le_B hlogB hlen ht2.nu_upper
  have hendpoint := ndA5_rpow_999_div_1000_le_ePrime_endpoint facts hM
  refine ⟨div_nonneg hoffset0 hMpos.le, ?_⟩
  calc
    (Tao.taoOffsetList as : ℝ) / (M : ℝ) ≤
        (B : ℝ) ^ (231 / 20000 : ℝ) / (M : ℝ) :=
      div_le_div_of_nonneg_right hoffset hMpos.le
    _ ≤ (B : ℝ) ^ (231 / 20000 : ℝ) /
        (B : ℝ) ^ (999 / 1000 : ℝ) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hBpos.le _)
        (Real.rpow_pos_of_pos hBpos _) hendpoint
    _ = (B : ℝ) ^ (-(19749 / 20000 : ℝ)) := by
      rw [← Real.rpow_sub hBpos]
      norm_num

/-- Scalar logarithmic correction once a local affine-ratio bound has been
established.  Keeping this adapter separate lets both the physical-interior
and the checked `EPrime` routes consume the same once-only logarithmic charge. -/
theorem ndA5_logCorrection_packet_of_ratio_bound
    {B : ℕ} {r : ℝ}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hr0 : 0 ≤ r)
    (hrStrong : r ≤ (B : ℝ) ^ (-(19749 / 20000 : ℝ))) :
    0 < 1 - r ∧
      0 ≤ -Real.log (1 - r) ∧
      -Real.log (1 - r) ≤ (B : ℝ) ^ (-(9 / 10 : ℝ)) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hBOne : (1 : ℝ) ≤ B := by exact_mod_cast hB
  let strong : ℝ := (B : ℝ) ^ (-(19749 / 20000 : ℝ))
  let weak : ℝ := (B : ℝ) ^ (-(9 / 10 : ℝ))
  have hrStrong' : r ≤ strong := by simpa [strong] using hrStrong
  have hlogTwo : Real.log (2 : ℝ) < 1 :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hgapLog :
      Real.log (2 : ℝ) ≤ (1749 / 20000 : ℝ) * Real.log B := by
    nlinarith
  have htwoGap :
      (2 : ℝ) ≤ (B : ℝ) ^ (1749 / 20000 : ℝ) := by
    rw [Real.rpow_def_of_pos hBpos,
      ← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_monotone (by simpa [mul_comm] using hgapLog)
  have htwoStrong : 2 * strong ≤ weak := by
    calc
      2 * strong ≤
          (B : ℝ) ^ (1749 / 20000 : ℝ) * strong :=
        mul_le_mul_of_nonneg_right htwoGap
          (Real.rpow_nonneg hBpos.le _)
      _ = weak := by
        rw [show strong = (B : ℝ) ^ (-(19749 / 20000 : ℝ)) by rfl,
          ← Real.rpow_add hBpos]
        congr 1
        norm_num [weak]
  have hweakOne : weak ≤ 1 := by
    simpa [weak] using
      Real.rpow_le_one_of_one_le_of_nonpos hBOne
        (by norm_num : (-(9 / 10 : ℝ)) ≤ 0)
  have hrHalf : r ≤ 1 / 2 := by
    nlinarith
  have hdenPos : 0 < 1 - r := by linarith
  have hlogNonpos : Real.log (1 - r) ≤ 0 :=
    Real.log_nonpos hdenPos.le (by linarith)
  have hlogLower := Real.one_sub_inv_le_log_of_pos hdenPos
  have hnegLogDiv : -Real.log (1 - r) ≤ r / (1 - r) := by
    rw [show r / (1 - r) = (1 - r)⁻¹ - 1 by
      field_simp [hdenPos.ne']
      ring_nf]
    linarith
  have hdivTwo : r / (1 - r) ≤ 2 * r := by
    apply (div_le_iff₀ hdenPos).2
    nlinarith [mul_nonneg hr0 (by linarith : 0 ≤ 1 - 2 * r)]
  have hrTwoStrong : 2 * r ≤ 2 * strong :=
    mul_le_mul_of_nonneg_left hrStrong' (by norm_num)
  refine ⟨hdenPos, ?_, ?_⟩
  · linarith
  · exact hnegLogDiv.trans
      (hdivTwo.trans (hrTwoStrong.trans htwoStrong))

/-- The exact affine denominator stays positive, and its logarithmic
position correction is nonnegative and at most `B^-0.9`. -/
theorem ndA5_exactAffineCorrection_packet
    {B nu : ℕ} {C M : ℝ} {as : List ℕ+}
    (hB : 1 ≤ B) (hlogB : (300000 : ℝ) ≤ Real.log B) (hM : 0 < M)
    (hpadding : 3 * ndA5TubeWidth B C ≤
      (33 / 500000 : ℝ) * Real.log B)
    (hshift : |ndA5InteriorShift B M| ≤
      (4 / 25 : ℝ) * ndA5TubeWidth B C)
    (hlen : as.length = nu)
    (hnu : (nu : ℝ) ≤ (105 / 10000 : ℝ) * Real.log B) :
    let r := (Tao.taoOffsetList as : ℝ) / M
    0 ≤ r ∧
      r ≤ (B : ℝ) ^ (-(19749 / 20000 : ℝ)) ∧
      0 < 1 - r ∧
      0 ≤ -Real.log (1 - r) ∧
      -Real.log (1 - r) ≤ (B : ℝ) ^ (-(9 / 10 : ℝ)) := by
  dsimp only
  let r : ℝ := (Tao.taoOffsetList as : ℝ) / M
  have hratio := ndA5_affineOffset_div_endpoint_le_rpow_neg_19749_div_20000
    hB hlogB hM hpadding hshift hlen hnu
  have hr0 : 0 ≤ r := by simpa [r] using hratio.1
  have hrStrong : r ≤ (B : ℝ) ^ (-(19749 / 20000 : ℝ)) := by
    simpa [r] using hratio.2
  have hcorrection := ndA5_logCorrection_packet_of_ratio_bound
    hB hlogB hr0 hrStrong
  exact ⟨hr0, hrStrong, hcorrection.1, hcorrection.2.1,
    hcorrection.2.2⟩

/-- Exact source-facing correction packet for the affine atom route.
`EPrime` supplies the endpoint lower bound; the ND band/tube consumer must
separately supply `(t2)`, of which only the local `nu_upper` field is used. -/
theorem ndA5_exactAffineCorrection_ePrime_packet
    {B n M : ℕ} {C : ℝ} {E : Set ℕ} {as : List ℕ+}
    (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hM : M ∈ Tao.taoSection5EPrime B E)
    (ht2 : NDA5T2ScaleFacts B n C)
    (hlen : as.length = n - Tao.taoSection5M0 B) :
    let r := (Tao.taoOffsetList as : ℝ) / (M : ℝ)
    0 ≤ r ∧
      r ≤ (B : ℝ) ^ (-(19749 / 20000 : ℝ)) ∧
      0 < 1 - r ∧
      0 ≤ -Real.log (1 - r) ∧
      -Real.log (1 - r) ≤ (B : ℝ) ^ (-(9 / 10 : ℝ)) := by
  dsimp only
  let r : ℝ := (Tao.taoOffsetList as : ℝ) / (M : ℝ)
  have hratio := ndA5_affineOffset_div_ePrime_le_rpow_neg_19749_div_20000
    facts hlogB hM ht2 hlen
  have hr0 : 0 ≤ r := by simpa [r] using hratio.1
  have hrStrong : r ≤ (B : ℝ) ^ (-(19749 / 20000 : ℝ)) := by
    simpa [r] using hratio.2
  have hcorrection := ndA5_logCorrection_packet_of_ratio_bound
    facts.schedule.one_le_B hlogB hr0 hrStrong
  exact ⟨hr0, hrStrong, hcorrection.1, hcorrection.2.1,
    hcorrection.2.2⟩

end

end ND
end Erdos1135
