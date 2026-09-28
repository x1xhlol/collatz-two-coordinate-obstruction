/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.ExplicitNumericalSyracuseMixing
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreSummedVariation

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

theorem explicitReferencePrefixFamily_rate {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt A C) :
    ∀ {ι : Type} [Fintype ι] (q k ell : ℕ)
      (word : ι → List ℕ+) (hlen : ∀ i, (word i).length ≤ q)
      (hk : ∀ i, k ≤ q - (word i).length) (hell : ell ≤ q),
      1 ≤ k → 1 ≤ ell →
      (∀ i j, i ≠ j → ∀ full : List ℕ+,
        full.take (word i).length = word i → full.take (word j).length = word j → False) →
      ndTernaryUniformMean q (fun y =>
        |(∑ i, ndReferencePrefixTransportAt q (word i) (hlen i)
            (fun z => ndSyracuseUnitReferenceDensity k
              (Tao.taoZModThreeProjection (hk i) z)) y) -
          ndSyracuseUnitReferenceDensity ell (Tao.taoZModThreeProjection hell y)|) ≤
        (2 / 3 : ℝ) * (C / (k : ℝ) ^ A + C / (ell : ℝ) ^ A +
          Tao.taoGatedRejectedMass (Tao.geom2PNatListPMF q)
            (fun full => ∃ i, full.take (word i).length = word i)
            (Tao.taoSection7OffsetZMod q)) := by
  intro ι _ q k ell word hlen hk hell hkpos hellpos hdisjoint
  exact referencePrefixFamily_lowerTail_fullL1_le q k ell word hlen hk hell hdisjoint
    (C / (k : ℝ) ^ A) (C / (ell : ℝ) ^ A) (div_nonneg hC (by positivity))
    (fun i => hmix _ k hkpos (hk i)) (hmix q ell hellpos hell)

private theorem explicitCore_sum_wordFilter {b m K : ℕ}
    (f : ndShiftedReferenceSelectedWords b (ndGeom2ShiftedWideSymmetricShiftRadius b) K → ℝ) :
    (∑ w, ndRootCoreWordFilter b m w.val * f w) =
      ∑ w : ndRootCoreSelectedWords b m K, f ⟨w.val, (Finset.mem_filter.mp w.property).1⟩ := by
  classical
  let e : ndRootCoreSelectedWords b m K →
      ndShiftedReferenceSelectedWords b (ndGeom2ShiftedWideSymmetricShiftRadius b) K :=
    fun w => ⟨w.val, (Finset.mem_filter.mp w.property).1⟩
  have he : Function.Injective e := by
    intro w v h
    have hv : w.val = v.val := congrArg (fun z => z.val) h
    exact Subtype.ext hv
  symm
  apply Fintype.sum_of_injective e he
  · intro w hw
    have hn : ¬(b ≤ w.val.length + m ∧ w.val.length ≤ b + m) := by
      intro hh
      exact hw ⟨⟨w.val, Finset.mem_filter.mpr ⟨w.property, hh⟩⟩, rfl⟩
    simp only [ndRootCoreWordFilter, hn, if_false, zero_mul]
  · intro w
    have hh := (Finset.mem_filter.mp w.property).2
    simp [e, ndRootCoreWordFilter, hh]

theorem explicitCoreFilteredKernel_rate {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt A C) :
    ∀ b m K k ell : ℕ,
      200 ≤ b → 16 ≤ m → m ≤ ndGeom2ShiftedWideSymmetricWidth b →
      1 ≤ k → 1 ≤ ell →
      ∀ hell : ell ≤ ndGeom2ShiftedWideSymmetricHorizon b + k,
      ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + k) (fun y =>
        |ndRootCoreFilteredKernel b (ndGeom2ShiftedWideSymmetricShiftRadius b) K k
          (ndRootCoreWordFilter b m) (ndSyracuseUnitReferenceDensity k) y -
          ndSyracuseUnitReferenceDensity ell (Tao.taoZModThreeProjection hell y)|) ≤
        (2 / 3 : ℝ) * (C / (k : ℝ) ^ A + C / (ell : ℝ) ^ A +
          (4 * (b : ℝ) + 4) * Real.exp (-((m : ℝ) ^ 2 / (576 * (b : ℝ)))) +
          (1 / 2 : ℝ) ^ (K + 1)) := by
  classical
  intro b m K k ell hb hm hmw hk hellpos hell
  let S := ndRootCoreSelectedWords b m K
  have hlen (w : S) : w.val.length ≤ ndGeom2ShiftedWideSymmetricHorizon b :=
    shiftedReferenceSelectedWords_length_le_horizon b _ K ⟨w.val, (Finset.mem_filter.mp w.property).1⟩
  have hdis (w v : S) (hne : w ≠ v) (full : List ℕ+)
      (hw : full.take w.val.length = w.val) (hv : full.take v.val.length = v.val) : False := by
    apply shiftedReferenceSelectedWords_prefix_disjoint b _ K
      ⟨w.val, (Finset.mem_filter.mp w.property).1⟩ ⟨v.val, (Finset.mem_filter.mp v.property).1⟩ _ full hw hv
    intro h
    exact hne (Subtype.ext (congrArg (fun z => z.val) h))
  have hr := explicitReferencePrefixFamily_rate hC hmix (ι := S)
    (ndGeom2ShiftedWideSymmetricHorizon b + k) k ell
    (fun w : S => w.val)
    (fun w => by change w.val.length ≤ ndGeom2ShiftedWideSymmetricHorizon b + k; have h := hlen w; omega)
    (fun w => by change k ≤ ndGeom2ShiftedWideSymmetricHorizon b + k - w.val.length; have h := hlen w; omega)
    hell hk hellpos hdis
  have he := rootCore_rejectedMass_le_exp_add_tail (K := K) hb hm hmw
    (by omega : ndGeom2ShiftedWideSymmetricHorizon b ≤ ndGeom2ShiftedWideSymmetricHorizon b + k)
  have heq (y : ZMod (3 ^ (ndGeom2ShiftedWideSymmetricHorizon b + k))) :
      ndRootCoreFilteredKernel b (ndGeom2ShiftedWideSymmetricShiftRadius b) K k
        (ndRootCoreWordFilter b m) (ndSyracuseUnitReferenceDensity k) y =
      ∑ w : S, ndReferencePrefixTransportAt (ndGeom2ShiftedWideSymmetricHorizon b + k) w.val
        (by have h := hlen w; omega) (fun z => ndSyracuseUnitReferenceDensity k
          (Tao.taoZModThreeProjection (by have h := hlen w; omega) z)) y := by
    unfold ndRootCoreFilteredKernel
    rw [explicitCore_sum_wordFilter]
    rfl
  simp_rw [heq]
  exact hr.trans (by dsimp only [S] at he ⊢; linarith only [he])

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem explicit_coreMarkedMass_increment_rate {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt A C) :
    ∀ (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
      (cap width : ℕ → ℕ) (n k ell : ℕ),
      let b := (U.forwardIterate cap n).floor;
      16 ≤ width b → width b ≤ ndGeom2ShiftedWideSymmetricWidth b →
      1 ≤ k → 1 ≤ ell →
      ndGeom2ShiftedWideSymmetricHorizon b + k ≤ 2 * b →
      ell ≤ ndGeom2ShiftedWideSymmetricHorizon b + k →
      |U.forwardCoreMarkedMass cap width (n + 1) k (fun _ => 1) -
        U.forwardCoreMarkedMass cap width n ell (fun _ => 1)| ≤
      U.coreCapacityBudget cap width n * ((2 / 3 : ℝ) *
        (C / (k : ℝ) ^ A + C / (ell : ℝ) ^ A +
          (4 * (b : ℝ) + 4) * Real.exp (-((width b : ℝ) ^ 2 / (576 * (b : ℝ)))) +
          (1 / 2 : ℝ) ^ (cap n + 1))) := by
  have hrate := explicitCoreFilteredKernel_rate hC hmix
  intro U cap width n k ell b hm hmw hk hellpos hq hell
  rw [U.forwardCoreMarkedMass_increment_eq_histogram cap width n k ell hk hell]
  apply (U.abs_coreHistogram_pairing_le_capacity_fullL1 cap width n _ hq _).trans
  exact mul_le_mul_of_nonneg_left
    (hrate b (width b) (cap n) k ell (U.forwardIterate cap n).floor_twoHundred hm hmw hk hellpos hell)
    (U.coreCapacityBudget_nonneg cap width n)

theorem explicit_quarter_coreMarkedSequence_increment_rate {A : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt A C) :
    ∀ (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
      (cap width : ℕ → ℕ) (n : ℕ),
      let b := (U.forwardIterate cap n).floor;
      16 ≤ width b → width b ≤ ndGeom2ShiftedWideSymmetricWidth b →
      |U.coreMarkedSequence cap width (n + 1) - U.coreMarkedSequence cap width n| ≤
        U.coreCapacityBudget cap width n * ((2 / 3 : ℝ) *
          (C / (((b + b / 100) / 4 : ℕ) : ℝ) ^ A + C / ((b / 4 : ℕ) : ℝ) ^ A +
            (4 * (b : ℝ) + 4) * Real.exp (-((width b : ℝ) ^ 2 / (576 * (b : ℝ)))) +
            (1 / 2 : ℝ) ^ (cap n + 1))) := by
  have hrate := explicit_coreMarkedMass_increment_rate hC hmix
  intro U cap width n b hm hmw
  have hb : 200 ≤ b := (U.forwardIterate cap n).floor_twoHundred
  have hr := hrate U cap width n ((b + b / 100) / 4) (b / 4) hm hmw
    (by omega) (by omega) (shiftedReference_quarter_next_conductor_le_two_mul b) (by omega)
  unfold coreMarkedSequence
  rw [U.forwardIterate_succ_eq_next cap n]
  exact hr

theorem explicit_core_increment_le_majorant {C : ℝ}
    (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt 6 C) :
    ∀ (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
      (_hb : 32 ^ 5 ≤ U.floor) (cap : ℕ → ℕ) (L K0 : ℕ),
      (∀ n, cap n ≤ L * (n + 1)) → (∀ n, K0 + n / 100 ≤ cap n) → ∀ n,
      |U.coreMarkedSequence cap ndRootCoreWidth (n + 1) - U.coreMarkedSequence cap ndRootCoreWidth n| ≤
        U.denominator * ndRootCoreVariationMajorant U.floor L K0 C n := by
  have hrate := explicit_quarter_coreMarkedSequence_increment_rate hC hmix
  intro U hb cap L K0 hcap hcaplo n
  let b := (U.forwardIterate cap n).floor
  have hm := U.forward_core_width_guard hb cap n
  have hr := hrate U cap ndRootCoreWidth n hm.1 hm.2
  have hbudget := U.coreCapacityBudget_le_geometric cap L hcap n
  have he := rootCore_quarter_error_le (b := b) (U.forwardIterate cap n).floor_twoHundred hC
  have hi : 1 / (b : ℝ) ^ 6 ≤ (1 / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (b : ℝ))
      (U.core_inverse_floor_le_geometric cap n) 6
    simpa only [div_pow, one_pow, mul_pow, ← pow_mul, Nat.mul_comm] using hh
  have hp : 0 ≤ 2 * C * 8 ^ 6 + ndRootCoreStripConstant := by
    unfold ndRootCoreStripConstant
    positivity
  have herror := mul_le_mul_of_nonneg_left hi hp
  have hct := rootCore_cap_failure_le_geometric cap K0 hcaplo n
  have hD : 0 ≤ U.denominator := by
    letI := U.state.labelFintype
    exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  have herr : C / (((b + b / 100) / 4 : ℕ) : ℝ) ^ 6 + C / ((b / 4 : ℕ) : ℝ) ^ 6 +
      (4 * (b : ℝ) + 4) * Real.exp (-((ndRootCoreWidth b : ℝ) ^ 2 / (576 * (b : ℝ)))) +
      (1 / 2 : ℝ) ^ (cap n + 1) ≤
      ((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (U.floor : ℝ) ^ 6) *
        ((200 / 201 : ℝ) ^ 6) ^ n +
        (1 / 2 : ℝ) ^ K0 * ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n := by
    rw [mul_one_div] at herror
    have hh : (2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (b : ℝ) ^ 6 ≤
        ((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (U.floor : ℝ) ^ 6) * ((200 / 201 : ℝ) ^ 6) ^ n := by
      convert herror using 1; ring
    linarith
  calc
    _ ≤ U.coreCapacityBudget cap ndRootCoreWidth n * ((2 / 3 : ℝ) *
        (((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (U.floor : ℝ) ^ 6) *
          ((200 / 201 : ℝ) ^ 6) ^ n +
          (1 / 2 : ℝ) ^ K0 * ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n)) :=
      hr.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left herr (by norm_num))
        (U.coreCapacityBudget_nonneg cap ndRootCoreWidth n))
    _ ≤ (U.denominator * ((4 * (U.floor : ℝ) ^ (3 / 5 : ℝ) + 1) * (L + 5) *
        ((2 : ℝ) ^ (U.floor + 1) + (16 : ℝ) ^ U.floor)) *
        ((n + 1 : ℕ) : ℝ) ^ 3 * ndRootCoreGrowth ^ n) * ((2 / 3 : ℝ) *
        (((2 * C * 8 ^ 6 + ndRootCoreStripConstant) / (U.floor : ℝ) ^ 6) *
          ((200 / 201 : ℝ) ^ 6) ^ n +
          (1 / 2 : ℝ) ^ K0 * ((1 / 2 : ℝ) ^ (1 / 100 : ℝ)) ^ n)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = _ := by unfold ndRootCoreVariationMajorant; rw [mul_pow, mul_pow]; ring

theorem explicit_core_marked_difference
    {C : ℝ} (hC : 0 ≤ C) (hmix : Tao.syracFineScaleMixingAt 6 C)
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (hb : 32 ^ 5 ≤ U.floor) (cap : ℕ → ℕ) (L K0 : ℕ)
    (hcap : ∀ n, cap n ≤ L * (n + 1)) (hcaplo : ∀ n, K0 + n / 100 ≤ cap n)
    {N n : ℕ} (hNn : N ≤ n) :
    |U.coreMarkedSequence cap ndRootCoreWidth n - U.coreMarkedSequence cap ndRootCoreWidth N| ≤
      U.denominator * ndRootCoreVariationTail U.floor L K0 C N := by
  let f := U.coreMarkedSequence cap ndRootCoreWidth
  let B := ndRootCoreVariationMajorant U.floor L K0 C
  have hD : 0 ≤ U.denominator := by
    letI := U.state.labelFintype
    exact Finset.sum_nonneg fun i _ => U.state.weight_nonneg i
  have hinc := explicit_core_increment_le_majorant hC hmix U hb cap L K0 hcap hcaplo
  have hpartial (J : ℕ) : |f (N + J) - f N| ≤
      U.denominator * ∑ j ∈ Finset.range J, B (N + j) := by
    induction J with
    | zero => simp
    | succ J ih =>
      rw [Finset.sum_range_succ]
      calc
        _ ≤ |f (N + (J + 1)) - f (N + J)| + |f (N + J) - f N| :=
          abs_sub_le _ _ _
        _ ≤ U.denominator * B (N + J) +
            U.denominator * ∑ j ∈ Finset.range J, B (N + j) :=
          add_le_add (by simpa only [Nat.add_assoc] using hinc (N + J)) ih
        _ = _ := by ring
  have hs : Summable (fun j => B (N + j)) := by
    simpa only [Nat.add_comm N] using
      (summable_nat_add_iff N).mpr (summable_rootCoreVariationMajorant U.floor L K0 C)
  have hsum : (∑ j ∈ Finset.range (n - N), B (N + j)) ≤ ∑' j, B (N + j) :=
    hs.sum_le_tsum _ (fun j _ => rootCoreVariationMajorant_nonneg _ _ _ _ hC)
  have h := (hpartial (n - N)).trans (mul_le_mul_of_nonneg_left hsum hD)
  simpa only [Nat.add_sub_of_le hNn] using h

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
