import Erdos1135.ND.PhaseGap
import Mathlib.Data.Finset.Max
import Mathlib.Data.Int.Interval
import Mathlib.Order.Interval.Finset.Nat

/-!
# A5 Strict Affine Unit Sweep

This neutral leaf isolates the signed no-skipping sweep used in frozen v10
A5.  The source component's symbolic ceiling is the strict lift
`floor x + 1`; ordinary integer ceiling would be one too small at integral
phase.

The declarations below do not choose the physical tube, band indices, or
normalizer.  A later representation-frozen consumer must supply the endpoint
crossings before using the central-hit cardinality theorem.
-/

namespace Erdos1135
namespace ND

/-- The positive A5 decrement `2 - log_2 3`. -/
noncomputable def ndA5PhaseDelta : ℝ :=
  2 - logTwoThree

/-- The strict signed affine selector underlying the A5 band sweep.

The added `1` is intentional even when the affine phase is integral. -/
noncomputable def ndA5StrictAffineSweep (A : ℝ) (nu : ℕ) : ℤ :=
  Int.floor (A - ndA5PhaseDelta * (nu : ℝ)) + 1

private theorem one_lt_logTwoThree :
    1 < logTwoThree := by
  unfold logTwoThree
  apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  simpa only [one_mul] using
    (Real.log_lt_log (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) < 3))

private theorem logTwoThree_lt_two :
    logTwoThree < 2 := by
  unfold logTwoThree
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  calc
    Real.log 3 < Real.log 4 :=
      Real.log_lt_log (by norm_num : (0 : ℝ) < 3)
        (by norm_num : (3 : ℝ) < 4)
    _ = Real.log (2 * 2) := by norm_num
    _ = Real.log 2 + Real.log 2 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0)]
    _ = 2 * Real.log 2 := by ring

private theorem ndA5PhaseDelta_pos :
    0 < ndA5PhaseDelta := by
  unfold ndA5PhaseDelta
  linarith [logTwoThree_lt_two]

private theorem ndA5PhaseDelta_lt_one :
    ndA5PhaseDelta < 1 := by
  unfold ndA5PhaseDelta
  linarith [one_lt_logTwoThree]

/-- The A5 phase decrement is strictly between zero and one. -/
theorem ndA5PhaseDelta_mem_Ioo :
    ndA5PhaseDelta ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨ndA5PhaseDelta_pos, ndA5PhaseDelta_lt_one⟩

/-- The strict affine selector lies in the half-open unit interval immediately
above its underlying real phase.  The lower endpoint is strict because the
selector is `floor x + 1`, including at integral `x`. -/
theorem ndA5StrictAffineSweep_sub_affine_mem_Ioc (A : ℝ) (nu : ℕ) :
    0 < (ndA5StrictAffineSweep A nu : ℝ) -
          (A - ndA5PhaseDelta * (nu : ℝ)) ∧
      (ndA5StrictAffineSweep A nu : ℝ) -
          (A - ndA5PhaseDelta * (nu : ℝ)) ≤ 1 := by
  unfold ndA5StrictAffineSweep
  constructor
  · have h := Int.lt_floor_add_one
        (A - ndA5PhaseDelta * (nu : ℝ))
    push_cast at h ⊢
    linarith
  · have h := Int.floor_le
        (A - ndA5PhaseDelta * (nu : ℝ))
    push_cast at h ⊢
    linarith

private theorem intFloor_sub_unitInterval
    {x delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    Int.floor (x - delta) = Int.floor x ∨
      Int.floor (x - delta) = Int.floor x - 1 := by
  have hupper := Int.floor_mono (by linarith : x - delta ≤ x)
  have hfloorDelta : Int.floor delta = 0 := by
    rw [Int.floor_eq_iff]
    norm_num
    exact ⟨hdelta0.le, hdelta1⟩
  have hlower := Int.le_floor_add_floor (x - delta) delta
  have hsum : x - delta + delta = x := by ring
  rw [hsum, hfloorDelta, add_zero] at hlower
  omega

/-- Advancing the affine parameter either preserves the strict selector or
drops it by exactly one. -/
theorem ndA5StrictAffineSweep_succ (A : ℝ) (nu : ℕ) :
    ndA5StrictAffineSweep A (nu + 1) = ndA5StrictAffineSweep A nu ∨
      ndA5StrictAffineSweep A (nu + 1) =
        ndA5StrictAffineSweep A nu - 1 := by
  unfold ndA5StrictAffineSweep
  have harg :
      A - ndA5PhaseDelta * ((nu + 1 : ℕ) : ℝ) =
        (A - ndA5PhaseDelta * (nu : ℝ)) - ndA5PhaseDelta := by
    push_cast
    ring
  rw [harg]
  rcases intFloor_sub_unitInterval
      (x := A - ndA5PhaseDelta * (nu : ℝ))
      (delta := ndA5PhaseDelta)
      ndA5PhaseDelta_pos ndA5PhaseDelta_lt_one with h | h
  · left
    omega
  · right
    omega

/-- The strict affine selector is antitone in its natural index. -/
theorem ndA5StrictAffineSweep_antitone (A : ℝ) :
    Antitone (ndA5StrictAffineSweep A) := by
  apply antitone_nat_of_succ_le
  intro nu
  rcases ndA5StrictAffineSweep_succ A nu with h | h <;> omega

/-- A finite integer-valued sweep with only zero or unit downward steps hits
every integer level lying between its two endpoint values. -/
theorem exists_eq_of_unit_down_sweep
    {d : ℕ → ℤ} {a b : ℕ} (hab : a ≤ b)
    (hstep : ∀ nu, a ≤ nu → nu < b →
      d (nu + 1) = d nu ∨ d (nu + 1) = d nu - 1)
    {k : ℤ} (hupper : k ≤ d a) (hlower : d b ≤ k) :
    ∃ nu ∈ Finset.Icc a b, d nu = k := by
  classical
  let F := (Finset.Icc a b).filter (fun nu => d nu ≤ k)
  have hbF : b ∈ F := by
    simp [F, hab, hlower]
  have hF : F.Nonempty := ⟨b, hbF⟩
  let nu := F.min' hF
  have hnuF : nu ∈ F := by
    dsimp [nu]
    exact F.min'_mem hF
  have hnuIcc := (Finset.mem_filter.mp hnuF).1
  have hdnu := (Finset.mem_filter.mp hnuF).2
  by_cases hnua : nu = a
  · refine ⟨nu, hnuIcc, ?_⟩
    rw [hnua] at hdnu
    rw [hnua]
    exact le_antisymm hdnu hupper
  · have hanu : a < nu := by
      have := (Finset.mem_Icc.mp hnuIcc).1
      omega
    let p := nu - 1
    have hpnu : p + 1 = nu := by
      dsimp [p]
      omega
    have hp_lt_nu : p < nu := by omega
    have hpIcc : p ∈ Finset.Icc a b := by
      apply Finset.mem_Icc.mpr
      exact ⟨Nat.le_sub_one_of_lt hanu,
        (Nat.sub_le nu 1).trans (Finset.mem_Icc.mp hnuIcc).2⟩
    have hpnotF : p ∉ F := by
      intro hpF
      have hmin : nu ≤ p := by
        dsimp [nu]
        exact F.min'_le p hpF
      exact (not_lt_of_ge hmin) hp_lt_nu
    have hdp : k < d p := by
      have hnle : ¬ d p ≤ k := by
        intro hle
        apply hpnotF
        exact Finset.mem_filter.mpr ⟨hpIcc, hle⟩
      omega
    have hp_lt_b : p < b :=
      hp_lt_nu.trans_le (Finset.mem_Icc.mp hnuIcc).2
    have hs := hstep p (Finset.mem_Icc.mp hpIcc).1 hp_lt_b
    rw [hpnu] at hs
    refine ⟨nu, hnuIcc, ?_⟩
    rcases hs with hs | hs <;> omega

private theorem central_hits_card_of_cover
    (d : ℕ → ℤ) (a b s : ℕ)
    (hcover : ∀ k ∈ Finset.Icc (-(s : ℤ)) (s : ℤ),
      ∃ nu ∈ Finset.Icc a b, d nu = k) :
    2 * s + 1 ≤
      ((Finset.Icc a b).filter
        (fun nu => Int.natAbs (d nu) ≤ s)).card := by
  classical
  let K : Finset ℤ := Finset.Icc (-(s : ℤ)) (s : ℤ)
  let F : Finset ℕ :=
    (Finset.Icc a b).filter (fun nu => Int.natAbs (d nu) ≤ s)
  have hsubset : K ⊆ F.image d := by
    intro k hk
    have hk' : k ∈ Finset.Icc (-(s : ℤ)) (s : ℤ) := by
      simpa [K] using hk
    obtain ⟨nu, hnu, hd⟩ := hcover k hk'
    have hkBounds := Finset.mem_Icc.mp hk'
    have hkabs : Int.natAbs k ≤ s := by
      rcases le_total 0 k with hk0 | hk0
      · have hle : (Int.natAbs k : ℤ) ≤ (s : ℤ) := by
          rw [Int.natAbs_of_nonneg hk0]
          exact hkBounds.2
        exact_mod_cast hle
      · have hle : (Int.natAbs k : ℤ) ≤ (s : ℤ) := by
          rw [Int.ofNat_natAbs_of_nonpos hk0]
          omega
        exact_mod_cast hle
    have hnuF : nu ∈ F := by
      apply Finset.mem_filter.mpr
      exact ⟨hnu, by simpa [hd] using hkabs⟩
    exact Finset.mem_image.mpr ⟨nu, hnuF, hd⟩
  have hKcardInt : (K.card : ℤ) = (s : ℤ) + 1 - (-(s : ℤ)) := by
    simpa [K] using
      (Int.card_Icc_of_le (a := -(s : ℤ)) (b := (s : ℤ)) (by omega))
  have hKcardInt' : (K.card : ℤ) = ((2 * s + 1 : ℕ) : ℤ) := by
    rw [hKcardInt]
    push_cast
    ring
  have hKcard : K.card = 2 * s + 1 := by
    exact_mod_cast hKcardInt'
  calc
    2 * s + 1 = K.card := hKcard.symm
    _ ≤ (F.image d).card := Finset.card_le_card hsubset
    _ ≤ F.card := Finset.card_image_le
    _ = ((Finset.Icc a b).filter
        (fun nu => Int.natAbs (d nu) ≤ s)).card := rfl

/-- If a unit-down sweep crosses both signed endpoints `s` and `-s`, at
least `2*s+1` indices lie in its central integer window.  Plateaus are allowed:
the proof counts the image rather than selecting injective witnesses. -/
theorem two_mul_add_one_le_card_centralHits_of_unit_down_sweep
    {d : ℕ → ℤ} {a b s : ℕ} (hab : a ≤ b)
    (hstep : ∀ nu, a ≤ nu → nu < b →
      d (nu + 1) = d nu ∨ d (nu + 1) = d nu - 1)
    (hupper : (s : ℤ) ≤ d a)
    (hlower : d b ≤ -(s : ℤ)) :
    2 * s + 1 ≤
      ((Finset.Icc a b).filter
        (fun nu => Int.natAbs (d nu) ≤ s)).card := by
  apply central_hits_card_of_cover d a b s
  intro k hk
  have hkBounds := Finset.mem_Icc.mp hk
  exact exists_eq_of_unit_down_sweep hab hstep
    (hkBounds.2.trans hupper) (hlower.trans hkBounds.1)

/-- The physical strict selector, after subtracting the signed drift `2*nu`,
is the neutral affine sweep.  This is an integer shift, not natural
subtraction. -/
theorem intFloor_add_logTwoThree_add_one_sub_two_mul_eq_strictAffineSweep
    (A : ℝ) (nu : ℕ) :
    Int.floor (A + (nu : ℝ) * logTwoThree) + 1 -
        2 * (nu : ℤ) =
      ndA5StrictAffineSweep A nu := by
  unfold ndA5StrictAffineSweep ndA5PhaseDelta
  calc
    Int.floor (A + (nu : ℝ) * logTwoThree) + 1 - 2 * (nu : ℤ) =
        (Int.floor (A + (nu : ℝ) * logTwoThree) -
          2 * (nu : ℤ)) + 1 := by ring
    _ = Int.floor
          ((A + (nu : ℝ) * logTwoThree) -
            ((2 * (nu : ℤ) : ℤ) : ℝ)) + 1 := by
      rw [Int.floor_sub_intCast]
    _ = Int.floor
          (A - (2 - logTwoThree) * (nu : ℝ)) + 1 := by
      congr 2
      push_cast
      ring

end ND
end Erdos1135
