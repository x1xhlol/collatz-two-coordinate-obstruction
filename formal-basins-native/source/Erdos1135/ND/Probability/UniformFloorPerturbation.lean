import Erdos1135.ND.Conventions
import Erdos1135.Tao.Probability.Finite
import Erdos1135.Tao.Probability.LogWindowEventualMassLower
import Erdos1135.Tao.Probability.LogWindowFloorPerturbation

/-!
# Uniform real/floor source perturbation

This neutral leaf compares the exact inclusive uniform source blocks at a
real scale `x` and its natural floor.  Harmonic mass is used only to certify
raw cardinality; the resulting probability estimate is a cardinal one.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

local instance uniformFloorPerturbationDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- If every positive atom of a finite set is at most `U`, its cardinality is
at most `U` times its reciprocal mass. -/
theorem card_cast_le_mul_logFinsetMass_of_mem_le
    {S : Finset ℕ} {U : ℝ}
    (hmem : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ U) :
    (S.card : ℝ) ≤ U * Tao.logFinsetMass S := by
  rw [Tao.logFinsetMass, Finset.mul_sum]
  calc
    (S.card : ℝ) = ∑ n ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ n ∈ S, U * Tao.logNatWeight n := by
      apply Finset.sum_le_sum
      intro n hn
      rcases hmem n hn with ⟨hnpos, hnU⟩
      rw [Tao.logNatWeight_eq_one_div_of_pos hnpos]
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnpos
      calc
        (1 : ℝ) = (n : ℝ) / (n : ℝ) := by field_simp
        _ ≤ U / (n : ℝ) :=
          div_le_div_of_nonneg_right hnU hnreal.le
        _ = U * (1 / (n : ℝ)) := by ring

/-- If every atom is at least a positive lower endpoint `L`, multiplying its
reciprocal mass by `L` is at most the raw cardinality. -/
theorem mul_logFinsetMass_le_card_cast_of_mem_ge
    {S : Finset ℕ} {L : ℝ} (hL : 0 < L)
    (hmem : ∀ n ∈ S, L ≤ (n : ℝ)) :
    L * Tao.logFinsetMass S ≤ (S.card : ℝ) := by
  rw [Tao.logFinsetMass, Finset.mul_sum]
  calc
    (∑ n ∈ S, L * Tao.logNatWeight n) ≤
        ∑ _n ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnreal : 0 < (n : ℝ) := hL.trans_le (hmem n hn)
      have hnpos : 0 < n := by exact_mod_cast hnreal
      rw [Tao.logNatWeight_eq_one_div_of_pos hnpos]
      calc
        L * (1 / (n : ℝ)) ≤ (n : ℝ) * (1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (hmem n hn)
            (one_div_nonneg.mpr hnreal.le)
        _ = 1 := by field_simp
    _ = (S.card : ℝ) := by simp

private theorem abs_normalized_card_sub_le_two_mul_div
    {a b s t d m : ℝ}
    (hm : 0 < m) (hma : m ≤ a) (hmb : m ≤ b)
    (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) (hsa : s ≤ a) (htb : t ≤ b)
    (hst : |s - t| ≤ d) (hab : |a - b| ≤ d) :
    |s / a - t / b| ≤ 2 * d / m := by
  have ha : 0 < a := hm.trans_le hma
  have hb : 0 < b := hm.trans_le hmb
  have hd : 0 ≤ d := (abs_nonneg (s - t)).trans hst
  have hstUpper : s - t ≤ d := (abs_le.mp hst).2
  have htsUpper : t - s ≤ d := by
    have h := (abs_le.mp hst).1
    linarith
  have habUpper : a - b ≤ d := (abs_le.mp hab).2
  have hbaUpper : b - a ≤ d := by
    have h := (abs_le.mp hab).1
    linarith
  have hforwardRewrite :
      s / a - t / b = ((s - t) * b + t * (b - a)) / (a * b) := by
    field_simp [ha.ne', hb.ne']
    ring
  have hreverseRewrite :
      t / b - s / a = ((t - s) * a + s * (a - b)) / (a * b) := by
    field_simp [ha.ne', hb.ne']
    ring
  have hforwardNumerator :
      (s - t) * b + t * (b - a) ≤ 2 * d * b := by
    calc
      (s - t) * b + t * (b - a) ≤ d * b + t * d :=
        add_le_add
          (mul_le_mul_of_nonneg_right hstUpper hb.le)
          (mul_le_mul_of_nonneg_left hbaUpper ht0)
      _ ≤ d * b + b * d :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right htb hd)
      _ = 2 * d * b := by ring
  have hreverseNumerator :
      (t - s) * a + s * (a - b) ≤ 2 * d * a := by
    calc
      (t - s) * a + s * (a - b) ≤ d * a + s * d :=
        add_le_add
          (mul_le_mul_of_nonneg_right htsUpper ha.le)
          (mul_le_mul_of_nonneg_left habUpper hs0)
      _ ≤ d * a + a * d :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hsa hd)
      _ = 2 * d * a := by ring
  have hforward : s / a - t / b ≤ 2 * d / m := by
    rw [hforwardRewrite]
    calc
      ((s - t) * b + t * (b - a)) / (a * b) ≤
          (2 * d * b) / (a * b) :=
        div_le_div_of_nonneg_right hforwardNumerator (mul_pos ha hb).le
      _ = 2 * d / a := by field_simp [ha.ne', hb.ne']
      _ ≤ 2 * d / m :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hd) hm hma
  have hreverse : t / b - s / a ≤ 2 * d / m := by
    rw [hreverseRewrite]
    calc
      ((t - s) * a + s * (a - b)) / (a * b) ≤
          (2 * d * a) / (a * b) :=
        div_le_div_of_nonneg_right hreverseNumerator (mul_pos ha hb).le
      _ = 2 * d / b := by field_simp [ha.ne', hb.ne']
      _ ≤ 2 * d / m :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hd) hm hmb
  rw [abs_le]
  constructor <;> linarith

private theorem abs_card_cast_sub_le_symmDiffCard
    {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    |(S.card : ℝ) - (T.card : ℝ)| ≤
      ((S \ T).card : ℝ) + ((T \ S).card : ℝ) := by
  have hS :
      (S.card : ℝ) = ((S \ T).card : ℝ) + ((S ∩ T).card : ℝ) := by
    exact_mod_cast (Finset.card_sdiff_add_card_inter S T).symm
  have hT :
      (T.card : ℝ) = ((T \ S).card : ℝ) + ((S ∩ T).card : ℝ) := by
    simpa only [Finset.inter_comm] using
      (show (T.card : ℝ) =
          ((T \ S).card : ℝ) + ((T ∩ S).card : ℝ) by
        exact_mod_cast (Finset.card_sdiff_add_card_inter T S).symm)
  rw [hS, hT, abs_le]
  have hleft : 0 ≤ ((S \ T).card : ℝ) := by positivity
  have hright : 0 ≤ ((T \ S).card : ℝ) := by positivity
  constructor <;> linarith

private theorem abs_card_filter_cast_sub_le_symmDiffCard
    {ι : Type*} [DecidableEq ι]
    (S T : Finset ι) (E : Set ι) :
    |((S.filter fun a => a ∈ E).card : ℝ) -
        ((T.filter fun a => a ∈ E).card : ℝ)| ≤
      ((S \ T).card : ℝ) + ((T \ S).card : ℝ) := by
  classical
  have hleft :
      (S.filter fun a => a ∈ E) \ (T.filter fun a => a ∈ E) ⊆ S \ T := by
    intro a ha
    simp only [Finset.mem_sdiff, Finset.mem_filter] at ha ⊢
    exact ⟨ha.1.1, fun haT => ha.2 ⟨haT, ha.1.2⟩⟩
  have hright :
      (T.filter fun a => a ∈ E) \ (S.filter fun a => a ∈ E) ⊆ T \ S := by
    intro a ha
    simp only [Finset.mem_sdiff, Finset.mem_filter] at ha ⊢
    exact ⟨ha.1.1, fun haS => ha.2 ⟨haS, ha.1.2⟩⟩
  calc
    |((S.filter fun a => a ∈ E).card : ℝ) -
        ((T.filter fun a => a ∈ E).card : ℝ)| ≤
        ((((S.filter fun a => a ∈ E) \
            (T.filter fun a => a ∈ E)).card : ℝ) +
          (((T.filter fun a => a ∈ E) \
            (S.filter fun a => a ∈ E)).card : ℝ)) :=
      abs_card_cast_sub_le_symmDiffCard _ _
    _ ≤ ((S \ T).card : ℝ) + ((T \ S).card : ℝ) := by
      exact add_le_add
        (by exact_mod_cast Finset.card_le_card hleft)
        (by exact_mod_cast Finset.card_le_card hright)

/-- Safe normalized cardinal perturbation for arbitrary ambient events. The
factor two pays once for the numerator and once for normalization. -/
theorem abs_cardFilterRatio_sub_le_two_symmDiffCard_div_min
    {ι : Type*} [DecidableEq ι]
    (S T : Finset ι) (E : Set ι)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    |((S.filter fun a => a ∈ E).card : ℝ) / (S.card : ℝ) -
        ((T.filter fun a => a ∈ E).card : ℝ) / (T.card : ℝ)| ≤
      2 * (((S \ T).card : ℝ) + ((T \ S).card : ℝ)) /
        min (S.card : ℝ) (T.card : ℝ) := by
  classical
  let s := ((S.filter fun a => a ∈ E).card : ℝ)
  let t := ((T.filter fun a => a ∈ E).card : ℝ)
  let a := (S.card : ℝ)
  let b := (T.card : ℝ)
  let d := ((S \ T).card : ℝ) + ((T \ S).card : ℝ)
  have ha : 0 < a := by
    change 0 < (S.card : ℝ)
    exact_mod_cast (Finset.card_pos.mpr hS)
  have hb : 0 < b := by
    change 0 < (T.card : ℝ)
    exact_mod_cast (Finset.card_pos.mpr hT)
  have hm : 0 < min a b := lt_min ha hb
  have hs0 : 0 ≤ s := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hsa : s ≤ a := by
    change ((S.filter fun a => a ∈ E).card : ℝ) ≤ (S.card : ℝ)
    exact_mod_cast Finset.card_filter_le S (fun a => a ∈ E)
  have htb : t ≤ b := by
    change ((T.filter fun a => a ∈ E).card : ℝ) ≤ (T.card : ℝ)
    exact_mod_cast Finset.card_filter_le T (fun a => a ∈ E)
  have hst : |s - t| ≤ d :=
    abs_card_filter_cast_sub_le_symmDiffCard S T E
  have hab : |a - b| ≤ d := abs_card_cast_sub_le_symmDiffCard S T
  exact abs_normalized_card_sub_le_two_mul_div
    hm (min_le_left _ _) (min_le_right _ _)
      hs0 ht0 hsa htb hst hab

private def uniformFinsetEventCarrierEquiv
    (S : Finset ℕ) (E : Set ℕ) :
    {N : {n : ℕ // n ∈ S} // N.val ∈ E} ≃
      {n : ℕ // n ∈ S.filter fun n => n ∈ E} where
  toFun N := ⟨N.val.val, by
    classical
    exact Finset.mem_filter.mpr ⟨N.val.property, N.property⟩⟩
  invFun n := ⟨⟨n.1, by
    classical
    exact (Finset.mem_filter.mp n.2).1⟩, by
      classical
      exact (Finset.mem_filter.mp n.2).2⟩
  left_inv N := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv n := by apply Subtype.ext; rfl

/-- Exact ambient-event formula for a uniform finite block law. -/
theorem pmfProb_uniformOddBlockPMF_eq_card_filter_div
    (y : ℝ) (hwindow : (oddBlock y).Nonempty) (E : Set ℕ) :
    Tao.pmfProb (uniformOddBlockPMF y hwindow) {N | N.1 ∈ E} =
      (((oddBlock y).filter fun n => n ∈ E).card : ℝ) /
        ((oddBlock y).card : ℝ) := by
  classical
  letI : Nonempty {n : ℕ // n ∈ oddBlock y} :=
    ⟨⟨hwindow.choose, hwindow.choose_spec⟩⟩
  change Tao.pmfProb
      (PMF.uniformOfFintype {n : ℕ // n ∈ oddBlock y})
      {N | N.1 ∈ E} = _
  rw [Tao.pmfProb_uniformOfFintype]
  have hcard :
      Fintype.card ↑({N : {n : ℕ // n ∈ oddBlock y} | (N : ℕ) ∈ E}) =
        ((oddBlock y).filter fun n => n ∈ E).card := by
    calc
      Fintype.card ↑({N : {n : ℕ // n ∈ oddBlock y} | (N : ℕ) ∈ E}) =
          Fintype.card
            {N : {n : ℕ // n ∈ oddBlock y} // N.val ∈ E} := rfl
      _ = Fintype.card
          {n : ℕ // n ∈ (oddBlock y).filter fun n => n ∈ E} :=
        Fintype.card_congr (uniformFinsetEventCarrierEquiv (oddBlock y) E)
      _ = _ := Fintype.card_coe _
  rw [hcard]
  simp only [Fintype.card_coe]

/-- The checked weighted movement theorem, in the ND branch/source notation. -/
theorem logFinsetSymmDiffMass_oddBlock_floor_transport_le_six_div
    {x : ℝ} (hx : 1 ≤ x) (branch : Tao.TaoSection5SourceBranch) :
    let B := Nat.floor x
    let S := oddBlock (Tao.taoSection5SourceY B branch)
    let T := oddBlock (transportSourceY x branch)
    Tao.logFinsetSymmDiffMass S T ≤ 6 / (B : ℝ) := by
  cases branch with
  | alpha =>
      simpa [oddBlock, transportSourceY, Tao.taoSection5SourceY, alpha] using
        Tao.logFinsetSymmDiffMass_taoNyOddWindow_floor_taoAlpha_le_six_div hx
  | alphaSq =>
      simpa [oddBlock, transportSourceY, Tao.taoSection5SourceY, alpha] using
        Tao.logFinsetSymmDiffMass_taoNyOddWindow_floor_taoAlpha_sq_le_six_div hx

private theorem oddBlock_floor_rpow_card_packet
    {x beta : ℝ} (facts : Tao.TaoProp111RealFloorWindowMassFacts x)
    (hbeta : 1 ≤ beta)
    (hmassFloor :
      Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
        Tao.logFinsetMass
          (oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta)))
    (hmassReal :
      Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 ≤
        Tao.logFinsetMass (oddBlock (x ^ beta))) :
    let B := Nat.floor x
    let S := oddBlock ((B : ℝ) ^ beta)
    let T := oddBlock (x ^ beta)
    S.Nonempty ∧ T.Nonempty ∧
      (B : ℝ) ≤ (S.card : ℝ) ∧ (B : ℝ) ≤ (T.card : ℝ) := by
  dsimp only
  have hx0 : 0 ≤ x := zero_le_one.trans facts.one_le_x
  have hxpos : 0 < x := zero_lt_one.trans_le facts.one_le_x
  have hB : 1 ≤ Nat.floor x :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using facts.one_le_x)
  have hBpos : 0 < ((Nat.floor x : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < Nat.floor x by omega)
  have hmassOne :
      (1 : ℝ) ≤ Real.log ((Nat.floor x : ℕ) : ℝ) / 8000 := by
    linarith [facts.log_floor_large]
  have hfloorLower :
      ((Nat.floor x : ℕ) : ℝ) *
          Tao.logFinsetMass
            (oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta)) ≤
        ((oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta)).card : ℝ) := by
    apply mul_logFinsetMass_le_card_cast_of_mem_ge hBpos
    intro n hn
    have hn' : n ∈ Tao.taoNyOddWindow
        (((Nat.floor x : ℕ) : ℝ) ^ beta) Tao.taoAlpha := by
      simpa only [oddBlock, alpha] using hn
    have hnLower :=
      (Tao.taoNyOddWindow_mem
        (Real.rpow_nonneg (Nat.cast_nonneg _) beta)).mp hn'
    exact (Real.self_le_rpow_of_one_le
      (by exact_mod_cast hB : (1 : ℝ) ≤ Nat.floor x) hbeta).trans hnLower.1
  have hrealLower :
      ((Nat.floor x : ℕ) : ℝ) *
          Tao.logFinsetMass (oddBlock (x ^ beta)) ≤
        ((oddBlock (x ^ beta)).card : ℝ) := by
    apply mul_logFinsetMass_le_card_cast_of_mem_ge hBpos
    intro n hn
    have hn' : n ∈ Tao.taoNyOddWindow (x ^ beta) Tao.taoAlpha := by
      simpa only [oddBlock, alpha] using hn
    have hnLower :=
      (Tao.taoNyOddWindow_mem (Real.rpow_nonneg hx0 beta)).mp hn'
    exact (Nat.floor_le hx0).trans
      ((Real.self_le_rpow_of_one_le facts.one_le_x hbeta).trans hnLower.1)
  have hfloorCard :
      ((Nat.floor x : ℕ) : ℝ) ≤
        ((oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta)).card : ℝ) := by
    calc
      ((Nat.floor x : ℕ) : ℝ) =
          ((Nat.floor x : ℕ) : ℝ) * 1 := by ring
      _ ≤ ((Nat.floor x : ℕ) : ℝ) *
          Tao.logFinsetMass
            (oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta)) :=
        mul_le_mul_of_nonneg_left (hmassOne.trans hmassFloor) hBpos.le
      _ ≤ _ := hfloorLower
  have hrealCard :
      ((Nat.floor x : ℕ) : ℝ) ≤
        ((oddBlock (x ^ beta)).card : ℝ) := by
    calc
      ((Nat.floor x : ℕ) : ℝ) =
          ((Nat.floor x : ℕ) : ℝ) * 1 := by ring
      _ ≤ ((Nat.floor x : ℕ) : ℝ) *
          Tao.logFinsetMass (oddBlock (x ^ beta)) :=
        mul_le_mul_of_nonneg_left (hmassOne.trans hmassReal) hBpos.le
      _ ≤ _ := hrealLower
  have hfloorNonempty :
      (oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta)).Nonempty := by
    have hcardPos :
        0 < ((oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta)).card : ℝ) :=
      hBpos.trans_le hfloorCard
    exact Finset.card_pos.mp (by exact_mod_cast hcardPos)
  have hrealNonempty : (oddBlock (x ^ beta)).Nonempty := by
    have hcardPos : 0 < ((oddBlock (x ^ beta)).card : ℝ) :=
      hBpos.trans_le hrealCard
    exact Finset.card_pos.mp (by exact_mod_cast hcardPos)
  exact ⟨hfloorNonempty, hrealNonempty, hfloorCard, hrealCard⟩

/-- The eventual harmonic mass packet certifies raw cardinalities for both
exact inclusive uniform source blocks. -/
theorem oddBlock_floor_transport_card_packet
    {x : ℝ} (facts : Tao.TaoProp111RealFloorWindowMassFacts x)
    (branch : Tao.TaoSection5SourceBranch) :
    let B := Nat.floor x
    let S := oddBlock (Tao.taoSection5SourceY B branch)
    let T := oddBlock (transportSourceY x branch)
    S.Nonempty ∧ T.Nonempty ∧
      (B : ℝ) ≤ (S.card : ℝ) ∧ (B : ℝ) ≤ (T.card : ℝ) := by
  cases branch with
  | alpha =>
      simpa [Tao.taoSection5SourceY, transportSourceY, alpha] using
        oddBlock_floor_rpow_card_packet facts
          (show (1 : ℝ) ≤ Tao.taoAlpha by norm_num [Tao.taoAlpha])
          (by simpa [oddBlock, alpha] using facts.alpha_floor)
          (by simpa [oddBlock, alpha] using facts.alpha_real)
  | alphaSq =>
      simpa [Tao.taoSection5SourceY, transportSourceY, alpha] using
        oddBlock_floor_rpow_card_packet facts
          (show (1 : ℝ) ≤ Tao.taoAlpha ^ 2 by norm_num [Tao.taoAlpha])
          (by simpa [oddBlock, alpha] using facts.alphaSq_floor)
          (by simpa [oddBlock, alpha] using facts.alphaSq_real)

private theorem oddBlock_floor_rpow_symmDiffCard_le
    {x beta : ℝ} (hx : 1 ≤ x)
    (hbetaOne : 1 ≤ beta) (hbetaTwo : beta ≤ 2)
    (hprodOne : 1 ≤ beta * alpha) (hprodTwo : beta * alpha ≤ 2) :
    let B := Nat.floor x
    let S := oddBlock ((B : ℝ) ^ beta)
    let T := oddBlock (x ^ beta)
    let U := (x ^ beta) ^ alpha
    ((S \ T).card : ℝ) + ((T \ S).card : ℝ) ≤
      6 * U / (B : ℝ) := by
  dsimp only
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hB : 1 ≤ Nat.floor x :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hx)
  have hBpos : 0 < ((Nat.floor x : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < Nat.floor x by omega)
  have hbetaNonneg : 0 ≤ beta := zero_le_one.trans hbetaOne
  have halphaNonneg : 0 ≤ alpha := by norm_num [alpha, Tao.taoAlpha]
  have hinner :
      ((Nat.floor x : ℕ) : ℝ) ^ beta ≤ x ^ beta :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx0) hbetaNonneg
  have houter :
      (((Nat.floor x : ℕ) : ℝ) ^ beta) ^ alpha ≤
        (x ^ beta) ^ alpha :=
    Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) beta)
      hinner halphaNonneg
  have hleft :
      (((oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta) \
          oddBlock (x ^ beta)).card : ℝ)) ≤
        ((x ^ beta) ^ alpha) *
          Tao.logFinsetMass
            (oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta) \
              oddBlock (x ^ beta)) := by
    apply card_cast_le_mul_logFinsetMass_of_mem_le
    intro n hn
    have hnS := (Finset.mem_sdiff.mp hn).1
    have hn' : n ∈ Tao.taoNyOddWindow
        (((Nat.floor x : ℕ) : ℝ) ^ beta) Tao.taoAlpha := by
      simpa only [oddBlock, alpha] using hnS
    have hnMem :=
      (Tao.taoNyOddWindow_mem
        (Real.rpow_nonneg (Nat.cast_nonneg _) beta)).mp hn'
    have hnpos : 0 < n := by omega
    exact ⟨hnpos, hnMem.2.1.trans houter⟩
  have hright :
      (((oddBlock (x ^ beta) \
          oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta)).card : ℝ)) ≤
        ((x ^ beta) ^ alpha) *
          Tao.logFinsetMass
            (oddBlock (x ^ beta) \
              oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta)) := by
    apply card_cast_le_mul_logFinsetMass_of_mem_le
    intro n hn
    have hnT := (Finset.mem_sdiff.mp hn).1
    have hn' : n ∈ Tao.taoNyOddWindow (x ^ beta) Tao.taoAlpha := by
      simpa only [oddBlock, alpha] using hnT
    have hnMem :=
      (Tao.taoNyOddWindow_mem (Real.rpow_nonneg hx0 beta)).mp hn'
    have hnpos : 0 < n := by omega
    exact ⟨hnpos, hnMem.2.1⟩
  have hmass :=
    Tao.logFinsetSymmDiffMass_taoNyOddWindow_floor_rpow_le_six_div
      hx hbetaOne hbetaTwo halphaNonneg hprodOne hprodTwo
  have hU : 0 ≤ (x ^ beta) ^ alpha :=
    Real.rpow_nonneg (Real.rpow_nonneg hx0 beta) alpha
  calc
    (((oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta) \
          oddBlock (x ^ beta)).card : ℝ)) +
        (((oddBlock (x ^ beta) \
          oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta)).card : ℝ)) ≤
      ((x ^ beta) ^ alpha) *
          Tao.logFinsetMass
            (oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta) \
              oddBlock (x ^ beta)) +
        ((x ^ beta) ^ alpha) *
          Tao.logFinsetMass
            (oddBlock (x ^ beta) \
              oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta)) :=
      add_le_add hleft hright
    _ = ((x ^ beta) ^ alpha) *
        Tao.logFinsetSymmDiffMass
          (oddBlock (((Nat.floor x : ℕ) : ℝ) ^ beta))
          (oddBlock (x ^ beta)) := by
      unfold Tao.logFinsetSymmDiffMass
      ring
    _ ≤ ((x ^ beta) ^ alpha) * (6 / ((Nat.floor x : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [oddBlock, alpha] using hmass) hU
    _ = 6 * ((x ^ beta) ^ alpha) /
        ((Nat.floor x : ℕ) : ℝ) := by ring

/-- Raw symmetric-difference cardinality for both real/floor source branches. -/
theorem oddBlock_floor_transport_symmDiffCard_le
    {x : ℝ} (facts : Tao.TaoProp111RealFloorWindowMassFacts x)
    (branch : Tao.TaoSection5SourceBranch) :
    let B := Nat.floor x
    let S := oddBlock (Tao.taoSection5SourceY B branch)
    let T := oddBlock (transportSourceY x branch)
    let U := (transportSourceY x branch) ^ alpha
    ((S \ T).card : ℝ) + ((T \ S).card : ℝ) ≤
      6 * U / (B : ℝ) := by
  cases branch with
  | alpha =>
      simpa [Tao.taoSection5SourceY, transportSourceY, alpha] using
        oddBlock_floor_rpow_symmDiffCard_le facts.one_le_x
          (beta := Tao.taoAlpha)
          (by norm_num [Tao.taoAlpha]) (by norm_num [Tao.taoAlpha])
          (by norm_num [alpha, Tao.taoAlpha])
          (by norm_num [alpha, Tao.taoAlpha])
  | alphaSq =>
      simpa [Tao.taoSection5SourceY, transportSourceY, alpha] using
        oddBlock_floor_rpow_symmDiffCard_le facts.one_le_x
          (beta := Tao.taoAlpha ^ 2)
          (by norm_num [Tao.taoAlpha]) (by norm_num [Tao.taoAlpha])
          (by norm_num [alpha, Tao.taoAlpha])
          (by norm_num [alpha, Tao.taoAlpha])

/-- Pointwise normalized uniform source perturbation before real-rate
absorption. -/
theorem abs_pmfProb_uniformOddBlock_floor_transport_sub_le
    {x : ℝ} (facts : Tao.TaoProp111RealFloorWindowMassFacts x)
    (branch : Tao.TaoSection5SourceBranch)
    (hFloor :
      (oddBlock (Tao.taoSection5SourceY (Nat.floor x) branch)).Nonempty)
    (hReal : (oddBlock (transportSourceY x branch)).Nonempty)
    (E : Set ℕ) :
    let B := Nat.floor x
    let U := (transportSourceY x branch) ^ alpha
    |Tao.pmfProb
        (uniformOddBlockPMF (Tao.taoSection5SourceY B branch) hFloor)
          {N | N.1 ∈ E} -
      Tao.pmfProb (uniformOddBlockPMF
        (transportSourceY x branch) hReal) {N | N.1 ∈ E}| ≤
      12 * U / (B : ℝ) ^ 2 := by
  dsimp only
  let B := Nat.floor x
  let S := oddBlock (Tao.taoSection5SourceY B branch)
  let T := oddBlock (transportSourceY x branch)
  let U := (transportSourceY x branch) ^ alpha
  have hpacket := oddBlock_floor_transport_card_packet facts branch
  have hdelta := oddBlock_floor_transport_symmDiffCard_le facts branch
  dsimp only at hpacket hdelta
  have hBpos : 0 < (B : ℝ) := by
    have hB : 1 ≤ B :=
      Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using facts.one_le_x)
    exact_mod_cast (show 0 < B by omega)
  have hmin : (B : ℝ) ≤ min (S.card : ℝ) (T.card : ℝ) :=
    le_min hpacket.2.2.1 hpacket.2.2.2
  have hminPos : 0 < min (S.card : ℝ) (T.card : ℝ) :=
    hBpos.trans_le hmin
  have hsourceNonneg : 0 ≤ transportSourceY x branch := by
    cases branch <;>
      simp only [transportSourceY] <;>
      exact Real.rpow_nonneg (zero_le_one.trans facts.one_le_x) _
  have hUNonneg : 0 ≤ U := Real.rpow_nonneg hsourceNonneg alpha
  rw [pmfProb_uniformOddBlockPMF_eq_card_filter_div,
    pmfProb_uniformOddBlockPMF_eq_card_filter_div]
  calc
    |(((S.filter fun n => n ∈ E).card : ℝ) / (S.card : ℝ)) -
        (((T.filter fun n => n ∈ E).card : ℝ) / (T.card : ℝ))| ≤
        2 * (((S \ T).card : ℝ) + ((T \ S).card : ℝ)) /
          min (S.card : ℝ) (T.card : ℝ) :=
      abs_cardFilterRatio_sub_le_two_symmDiffCard_div_min
        S T E hpacket.1 hpacket.2.1
    _ ≤ (2 * (6 * U / (B : ℝ))) /
        min (S.card : ℝ) (T.card : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdelta (by norm_num)) hminPos.le
    _ ≤ (2 * (6 * U / (B : ℝ))) / (B : ℝ) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num)
          (div_nonneg (mul_nonneg (by norm_num) hUNonneg)
            hBpos.le)) hBpos hmin
    _ = 12 * U / (B : ℝ) ^ 2 := by
      field_simp [hBpos.ne']
      ring

private theorem transportSourceOuter_le_rpow
    {x : ℝ} (hx : 1 ≤ x) (branch : Tao.TaoSection5SourceBranch) :
    (transportSourceY x branch) ^ alpha ≤ x ^ (101 / 100 : ℝ) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  cases branch with
  | alpha =>
      simp only [transportSourceY]
      change (x ^ Tao.taoAlpha) ^ Tao.taoAlpha ≤ x ^ (101 / 100 : ℝ)
      rw [← Real.rpow_mul hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx
        (by norm_num [alpha, Tao.taoAlpha])
  | alphaSq =>
      simp only [transportSourceY]
      change (x ^ (Tao.taoAlpha ^ 2)) ^ Tao.taoAlpha ≤
        x ^ (101 / 100 : ℝ)
      rw [← Real.rpow_mul hx0]
      exact Real.rpow_le_rpow_of_exponent_le hx
        (by norm_num [alpha, Tao.taoAlpha])

/-- The two exact inclusive uniform source windows differ by at most the
stable polynomial envelope `96*x^(-99/100)`, uniformly over ambient events. -/
theorem eventually_abs_pmfProb_uniformOddBlock_floor_transport_sub_le :
    ∀ᶠ x : ℝ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch)
        (hFloor :
          (oddBlock
            (Tao.taoSection5SourceY (Nat.floor x) branch)).Nonempty)
        (hReal : (oddBlock (transportSourceY x branch)).Nonempty)
        (E : Set ℕ),
        |Tao.pmfProb
            (uniformOddBlockPMF
              (Tao.taoSection5SourceY (Nat.floor x) branch) hFloor)
              {N | N.1 ∈ E} -
          Tao.pmfProb
            (uniformOddBlockPMF (transportSourceY x branch) hReal)
              {N | N.1 ∈ E}| ≤
          96 * x ^ (-(99 / 100 : ℝ)) := by
  filter_upwards
      [Tao.eventually_taoProp111RealFloorWindowMassFacts,
        eventually_ge_atTop (2 : ℝ)]
      with x facts hx
  intro branch hFloor hReal E
  let B := Nat.floor x
  let U := (transportSourceY x branch) ^ alpha
  have hpoint :=
    abs_pmfProb_uniformOddBlock_floor_transport_sub_le
      facts branch hFloor hReal E
  have hxpos : 0 < x := by linarith
  have hBpos : 0 < (B : ℝ) := by
    have hB : 1 ≤ B :=
      Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by
        norm_num
        exact facts.one_le_x)
    exact_mod_cast (show 0 < B by omega)
  have hhalf : x / 2 ≤ (B : ℝ) := by
    have hfloor := Nat.lt_floor_add_one x
    dsimp only [B]
    push_cast at hfloor
    linarith
  have hsqHalf : (x / 2) ^ 2 ≤ (B : ℝ) ^ 2 :=
    by simpa only [pow_two] using
      mul_self_le_mul_self (by positivity) hhalf
  have hsq : x ^ 2 ≤ 4 * (B : ℝ) ^ 2 := by nlinarith
  have hU : 0 ≤ U := by
    dsimp only [U]
    apply Real.rpow_nonneg
    cases branch <;>
      simp only [transportSourceY] <;>
      exact Real.rpow_nonneg hxpos.le _
  have hdenom :
      12 * U / (B : ℝ) ^ 2 ≤ 48 * U / x ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hBpos) (sq_pos_of_pos hxpos)]
    calc
      (12 * U) * x ^ 2 ≤ (12 * U) * (4 * (B : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num) hU)
      _ = (48 * U) * (B : ℝ) ^ 2 := by ring
  have houter := transportSourceOuter_le_rpow facts.one_le_x branch
  calc
    |Tao.pmfProb
          (uniformOddBlockPMF
            (Tao.taoSection5SourceY (Nat.floor x) branch) hFloor)
            {N | N.1 ∈ E} -
        Tao.pmfProb
          (uniformOddBlockPMF (transportSourceY x branch) hReal)
            {N | N.1 ∈ E}| ≤
        12 * U / (B : ℝ) ^ 2 := hpoint
    _ ≤ 48 * U / x ^ 2 := hdenom
    _ ≤ 48 * x ^ (101 / 100 : ℝ) / x ^ 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left houter (by norm_num)) (sq_nonneg x)
    _ = 48 * (x ^ (101 / 100 : ℝ) / x ^ (2 : ℝ)) := by
      rw [Real.rpow_two]
      ring
    _ = 48 * x ^ ((101 / 100 : ℝ) - 2) := by
      rw [Real.rpow_sub hxpos]
    _ = 48 * x ^ (-(99 / 100 : ℝ)) := by norm_num
    _ ≤ 96 * x ^ (-(99 / 100 : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (by norm_num)
        (Real.rpow_nonneg hxpos.le _)

end
end ND
end Erdos1135
