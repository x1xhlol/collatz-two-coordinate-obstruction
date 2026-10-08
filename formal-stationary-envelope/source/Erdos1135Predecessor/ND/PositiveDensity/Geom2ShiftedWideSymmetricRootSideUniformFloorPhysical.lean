/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideKilledLiftHighExitPhysical

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

set_option maxRecDepth 4096

theorem four_mul_threePow_mul_sixteenPow_oneHundredth_le_fourPow
    {b : ℕ} (hb : 200 ≤ b) :
    4 * 3 ^ b * 16 ^ (b / 100) ≤ 4 ^ b := by
  let c := ndBalancedTotal b
  have hthree : 3 ^ b ≤ 2 ^ c := by
    simpa only [c] using three_pow_le_two_pow_ndBalancedTotal b
  have hc := five_mul_ndBalancedTotal_le_eight_mul_add_five b
  have hdiv := Nat.div_mul_le_self b 100
  have hexp : 2 + c + 4 * (b / 100) ≤ 2 * b := by
    dsimp only [c] at hc ⊢
    omega
  calc
    4 * 3 ^ b * 16 ^ (b / 100) ≤
        4 * 2 ^ c * 16 ^ (b / 100) := by gcongr
    _ = 2 ^ (2 + c + 4 * (b / 100)) := by
      norm_num only [pow_add, pow_mul]
    _ ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right (by norm_num) hexp
    _ = 4 ^ b := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]

abbrev NDGeom2PredictableRootSideUniformFloorIncidence
    (Label : Type*) (root : Label → ℕ) (b K : ℕ) :=
  NDGeom2PredictableRootSideBoundedOvershootIncidence
    Label root (fun _ => b)
      (fun _ => ndGeom2ShiftedWideSymmetricShiftRadius b) K

theorem
    ndGeom2PredictableRootSideUniformFloorIncidence_sixteenPow_actualBase_add_oneHundredth_le_source
    {Label : Type*} {root rootBase : Label → ℕ} {b K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 200 ≤ b)
    (hfloor : ∀ i, b ≤ rootBase i)
    (hrootLower : ∀ i, 16 ^ rootBase i ≤ root i)
    (z : NDGeom2PredictableRootSideUniformFloorIncidence Label root b K) :
    16 ^
        (rootBase
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) +
          b / 100) ≤
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z := by
  let i := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z
  let q := rootBase i
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  let M := root i
  let source := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  have hpacketRootLower : ∀ j, 16 ^ b ≤ root j := by
    intro j
    exact
      (Nat.pow_le_pow_right (by norm_num) (hfloor j)).trans
        (hrootLower j)
  have hshell :=
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_shell
      hrootOdd (fun _ => by omega) hpacketRootLower z
  have hscale :
      4 * 2 ^ r * 3 ^ b * 16 ^ (q + b / 100) ≤
        2 ^ r * 4 ^ b * 16 ^ q := by
    calc
      4 * 2 ^ r * 3 ^ b * 16 ^ (q + b / 100) =
          2 ^ r * 16 ^ q * (4 * 3 ^ b * 16 ^ (b / 100)) := by
        rw [pow_add]
        ring
      _ ≤ 2 ^ r * 16 ^ q * 4 ^ b := by
        gcongr
        exact four_mul_threePow_mul_sixteenPow_oneHundredth_le_fourPow hb
      _ = 2 ^ r * 4 ^ b * 16 ^ q := by ring
  have hnumLower :
      2 ^ r * 4 ^ b * 16 ^ q ≤ 2 ^ r * 4 ^ b * M := by
    gcongr
    exact hrootLower i
  have hcross :
      4 * 2 ^ r * 3 ^ b * 16 ^ (q + b / 100) ≤
        4 * 2 ^ r * 3 ^ b * source :=
    hscale.trans (hnumLower.trans (by
      simpa only [i, q, r, M, source] using hshell.1))
  have hdenPos : 0 < 4 * 2 ^ r * 3 ^ b := by positivity
  have hcancel := Nat.le_of_mul_le_mul_left hcross hdenPos
  simpa only [i, q, source] using hcancel

theorem
    ndGeom2PredictableRootSideUniformFloorIncidence_actualBase_add_oneHundredth_le_sourceBase
    {Label : Type*} {root rootBase : Label → ℕ} {b K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 200 ≤ b)
    (hfloor : ∀ i, b ≤ rootBase i)
    (hrootLower : ∀ i, 16 ^ rootBase i ≤ root i)
    (z : NDGeom2PredictableRootSideUniformFloorIncidence Label root b K) :
    rootBase (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) +
          b / 100 ≤
      ndA5QOneRootDyadicBase
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) := by
  let q := rootBase
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
  let source := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  have hsource :=
    ndGeom2PredictableRootSideUniformFloorIncidence_sixteenPow_actualBase_add_oneHundredth_le_source
      hrootOdd hb hfloor hrootLower z
  have hpow : 2 ^ (4 * (q + b / 100)) ≤ source := by
    calc
      2 ^ (4 * (q + b / 100)) = 16 ^ (q + b / 100) := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, pow_mul]
      _ ≤ source := by simpa only [q, source] using hsource
  have hlog : 4 * (q + b / 100) ≤ Nat.log 2 source :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  unfold ndA5QOneRootDyadicBase
  dsimp only [q, source] at hlog ⊢
  omega

theorem
    ndGeom2PredictableRootSideUniformFloorIncidence_floor_add_oneHundredth_le_sourceBase
    {Label : Type*} {root rootBase : Label → ℕ} {b K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 200 ≤ b)
    (hfloor : ∀ i, b ≤ rootBase i)
    (hrootLower : ∀ i, 16 ^ rootBase i ≤ root i)
    (z : NDGeom2PredictableRootSideUniformFloorIncidence Label root b K) :
    b + b / 100 ≤
      ndA5QOneRootDyadicBase
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) := by
  exact (Nat.add_le_add_right
      (hfloor
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      (b / 100)).trans
    (ndGeom2PredictableRootSideUniformFloorIncidence_actualBase_add_oneHundredth_le_sourceBase
      hrootOdd hb hfloor hrootLower z)

theorem shiftedWideUniformFloorPhysicalEdgeDepth_cast_le_twoHundredFifty_mul_logGap
    {b q depth root source : ℕ}
    (hb : 200 ≤ b)
    (hdepthCap : depth ≤ 2 * b + 1)
    (hrootPos : 0 < root)
    (hrootUpper : root < 16 ^ (q + 1))
    (hsourceLower : 16 ^ (q + b / 100) ≤ source) :
    (depth : ℝ) ≤
      250 * (Real.log (source : ℝ) - Real.log (root : ℝ)) := by
  let inc := b / 100
  have hinc : 2 ≤ inc := by
    dsimp only [inc]
    omega
  have harithNat : 3 * depth ≤ 2000 * (inc - 1) := by omega
  have harithReal :
      (3 : ℝ) * (depth : ℝ) ≤ 2000 * ((inc : ℝ) - 1) := by
    have hcast :
        ((3 * depth : ℕ) : ℝ) ≤ ((2000 * (inc - 1) : ℕ) : ℝ) := by
      exact_mod_cast harithNat
    norm_num only [Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_sub (by omega : 1 ≤ inc)] at hcast
    exact hcast
  have hlogTwo : (2 / 3 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlogSixteen : (8 / 3 : ℝ) < Real.log 16 := by
    calc
      (8 / 3 : ℝ) = 4 * (2 / 3 : ℝ) := by ring
      _ < 4 * Real.log 2 :=
        mul_lt_mul_of_pos_left hlogTwo (by norm_num)
      _ = Real.log 16 := by
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
        norm_num
  have hincSubNonneg : (0 : ℝ) ≤ (inc : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast (show 1 ≤ inc by omega))
  have hdepthScale :
      (depth : ℝ) ≤ 250 * ((inc : ℝ) - 1) * Real.log 16 := by
    calc
      (depth : ℝ) ≤ 250 * ((inc : ℝ) - 1) * (8 / 3 : ℝ) := by
        nlinarith
      _ ≤ 250 * ((inc : ℝ) - 1) * Real.log 16 := by
        exact mul_le_mul_of_nonneg_left hlogSixteen.le
          (mul_nonneg (by norm_num) hincSubNonneg)
  have hsourcePos : 0 < source :=
    lt_of_lt_of_le (by positivity) hsourceLower
  have hrootLog :
      Real.log (root : ℝ) ≤ ((q + 1 : ℕ) : ℝ) * Real.log 16 := by
    have hmono :
        Real.log (root : ℝ) ≤
          Real.log (((16 ^ (q + 1) : ℕ) : ℝ)) :=
      Real.strictMonoOn_log.monotoneOn
        (by
          change (0 : ℝ) < (root : ℝ)
          exact_mod_cast hrootPos)
        (by
          change (0 : ℝ) < ((16 ^ (q + 1) : ℕ) : ℝ)
          positivity)
        (by exact_mod_cast hrootUpper.le)
    norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hmono
    rw [Real.log_pow] at hmono
    exact hmono
  have hsourceLog :
      ((q + inc : ℕ) : ℝ) * Real.log 16 ≤ Real.log (source : ℝ) := by
    have hmono :
        Real.log (((16 ^ (q + inc) : ℕ) : ℝ)) ≤
          Real.log (source : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (by
          change (0 : ℝ) < ((16 ^ (q + inc) : ℕ) : ℝ)
          positivity)
        (by
          change (0 : ℝ) < (source : ℝ)
          exact_mod_cast hsourcePos)
        (by
          dsimp only [inc]
          exact_mod_cast hsourceLower)
    norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hmono
    rw [Real.log_pow] at hmono
    exact hmono
  have hgap :
      ((inc : ℝ) - 1) * Real.log 16 ≤
        Real.log (source : ℝ) - Real.log (root : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hrootLog hsourceLog
    nlinarith
  calc
    (depth : ℝ) ≤ 250 * ((inc : ℝ) - 1) * Real.log 16 := hdepthScale
    _ = 250 * (((inc : ℝ) - 1) * Real.log 16) := by ring
    _ ≤ 250 * (Real.log (source : ℝ) - Real.log (root : ℝ)) :=
      mul_le_mul_of_nonneg_left hgap (by norm_num)

theorem
    ndGeom2PredictableRootSideUniformFloorIncidenceDepth_cast_le_twoHundredFifty_mul_log_source_sub_log_root
    {Label : Type*} {root rootBase : Label → ℕ} {b K : ℕ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 200 ≤ b)
    (hfloor : ∀ i, b ≤ rootBase i)
    (hrootLower : ∀ i, 16 ^ rootBase i ≤ root i)
    (hrootUpper : ∀ i, root i < 16 ^ (rootBase i + 1))
    (z : NDGeom2PredictableRootSideUniformFloorIncidence Label root b K) :
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z : ℝ) ≤
      250 *
        (Real.log
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) -
          Real.log
            (root
              (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) :
              ℝ)) := by
  let i := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z
  let q := rootBase i
  let depth := ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z
  let source := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  have hdepthCap : depth ≤ 2 * b + 1 := by
    simpa only [depth, i] using
      ndGeom2ShiftedWideSymmetricSelectedDepth_le_two_mul_add_one
        (ndGeom2PredictableRootSideBoundedOvershootIncidence_depth_mem z)
  have hrootPos : 0 < root i :=
    lt_of_lt_of_le (by positivity) (hrootLower i)
  have hsourceLower : 16 ^ (q + b / 100) ≤ source := by
    simpa only [i, q, source] using
      (ndGeom2PredictableRootSideUniformFloorIncidence_sixteenPow_actualBase_add_oneHundredth_le_source
        hrootOdd hb hfloor hrootLower z)
  simpa only [depth, source, i, q] using
    (shiftedWideUniformFloorPhysicalEdgeDepth_cast_le_twoHundredFifty_mul_logGap
      hb hdepthCap hrootPos (hrootUpper i) hsourceLower)

private theorem uniformFloorPhysicalEdgeSource_mem_same_target
    {root source depth : ℕ} {C : ℝ}
    (hC : 250 ≤ C)
    (hrootTarget : root ∈ oddSyracuseLogTimeOneSet C)
    (hsourceOdd : Odd source)
    (hrootSource : root ≤ source)
    (hdepth :
      (depth : ℝ) ≤
        250 * (Real.log (source : ℝ) - Real.log (root : ℝ)))
    (hiterate : (Tao.syracuse^[depth]) source = root) :
    source ∈ oddSyracuseLogTimeOneSet C := by
  have hsourcePos : 0 < source := Odd.pos hsourceOdd
  rcases hrootTarget with ⟨hrootPos, _hrootOdd, m, hmClock, hmOne⟩
  have hlogRootSource :
      Real.log (root : ℝ) ≤ Real.log (source : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by
        change (0 : ℝ) < (root : ℝ)
        exact_mod_cast hrootPos)
      (by
        change (0 : ℝ) < (source : ℝ)
        exact_mod_cast hsourcePos)
      (by exact_mod_cast hrootSource)
  have hCSub : 0 ≤ C - 250 := sub_nonneg.mpr hC
  refine ⟨hsourcePos, hsourceOdd, depth + m, ?_, ?_⟩
  · rw [Nat.cast_add]
    calc
      (depth : ℝ) + (m : ℝ) ≤
          250 * (Real.log (source : ℝ) - Real.log (root : ℝ)) +
            C * Real.log (root : ℝ) := add_le_add hdepth hmClock
      _ = 250 * Real.log (source : ℝ) +
          (C - 250) * Real.log (root : ℝ) := by ring
      _ ≤ 250 * Real.log (source : ℝ) +
          (C - 250) * Real.log (source : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hlogRootSource hCSub
        linarith
      _ = C * Real.log (source : ℝ) := by ring
  · rw [Nat.add_comm, Function.iterate_add_apply, hiterate, hmOne]

theorem
    ndGeom2PredictableRootSideUniformFloorIncidenceSource_mem_same_oddSyracuseLogTimeOneSet
    {Label : Type*} {root rootBase : Label → ℕ} {b K : ℕ} {C : ℝ}
    (hrootOdd : ∀ i, Odd (root i))
    (hb : 200 ≤ b)
    (hfloor : ∀ i, b ≤ rootBase i)
    (hrootLower : ∀ i, 16 ^ rootBase i ≤ root i)
    (hrootUpper : ∀ i, root i < 16 ^ (rootBase i + 1))
    (hC : 250 ≤ C)
    (hrootTarget : ∀ i, root i ∈ oddSyracuseLogTimeOneSet C)
    (z : NDGeom2PredictableRootSideUniformFloorIncidence Label root b K) :
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z ∈
      oddSyracuseLogTimeOneSet C := by
  let i := ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z
  let q := rootBase i
  let source := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z
  have hinc : 2 ≤ b / 100 := by omega
  have hsourceLower : 16 ^ (q + b / 100) ≤ source := by
    simpa only [i, q, source] using
      (ndGeom2PredictableRootSideUniformFloorIncidence_sixteenPow_actualBase_add_oneHundredth_le_source
        hrootOdd hb hfloor hrootLower z)
  have hrootSource : root i ≤ source := by
    calc
      root i ≤ 16 ^ (q + 1) := by
        simpa only [q] using (hrootUpper i).le
      _ ≤ 16 ^ (q + b / 100) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ source := hsourceLower
  have hdepth :=
    ndGeom2PredictableRootSideUniformFloorIncidenceDepth_cast_le_twoHundredFifty_mul_log_source_sub_log_root
      hrootOdd hb hfloor hrootLower hrootUpper z
  have hpacketRootLower : ∀ j, 16 ^ b ≤ root j := by
    intro j
    exact
      (Nat.pow_le_pow_right (by norm_num) (hfloor j)).trans
        (hrootLower j)
  have hsourceOdd : Odd source := by
    simpa only [source] using
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd
        hrootOdd (fun _ => by omega) hpacketRootLower z
  have hiterate :
      (Tao.syracuse^[ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z])
          source = root i := by
    simpa only [source, i] using
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_iterate
        hrootOdd (fun _ => by omega) hpacketRootLower z)
  exact uniformFloorPhysicalEdgeSource_mem_same_target
    hC (hrootTarget i) hsourceOdd hrootSource
    (by simpa only [source, i] using hdepth) hiterate

end

end PositiveDensity

end ND

end Erdos1135Predecessor
