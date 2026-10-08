/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.ND.Band.A5Tube
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A6 Strict-Level Multiplicity

This neutral A6 leaf counts the actual natural-index fibers of the literal
`floor + 1` sweep.  Under the already frozen unclipped-tube hypothesis, each
integer level has the exact difference-of-floors multiplicity.  Consecutive
level errors therefore have discrepancy at most one, and finite summation by
parts turns that prefix bound into the endpoint-shaped Abel estimate needed
by the later Gaussian comparison.
-/

namespace Erdos1135
namespace ND

/-- The multiplicity of one signed integer level inside the full strict A5
tube.  The definition retains natural-index multiplicity. -/
noncomputable def ndA6StrictLevelMultiplicity (A W : ℝ) (d : ℤ) : ℕ :=
  ((ndA5FullTube A W).filter
    (fun nu => ndA5StrictAffineSweep A nu = d)).card

/-- Membership in one level of the strict `floor + 1` sweep, with the
load-bearing strict lower and weak upper endpoints. -/
theorem ndA5StrictAffineSweep_eq_iff (A : ℝ) (nu : ℕ) (d : ℤ) :
    ndA5StrictAffineSweep A nu = d ↔
      (A - (d : ℝ)) / ndA5PhaseDelta < (nu : ℝ) ∧
        (nu : ℝ) ≤ (A - (d : ℝ) + 1) / ndA5PhaseDelta := by
  unfold ndA5StrictAffineSweep
  constructor
  · intro h
    have hfloor : Int.floor (A - ndA5PhaseDelta * (nu : ℝ)) = d - 1 := by
      omega
    have hbounds := Int.floor_eq_iff.mp hfloor
    constructor
    · apply (div_lt_iff₀ ndA5PhaseDelta_mem_Ioo.1).2
      push_cast at hbounds ⊢
      linarith
    · apply (le_div_iff₀ ndA5PhaseDelta_mem_Ioo.1).2
      push_cast at hbounds ⊢
      linarith
  · rintro ⟨hlower, hupper⟩
    have hlower' := (div_lt_iff₀ ndA5PhaseDelta_mem_Ioo.1).mp hlower
    have hupper' := (le_div_iff₀ ndA5PhaseDelta_mem_Ioo.1).mp hupper
    have hfloor : Int.floor (A - ndA5PhaseDelta * (nu : ℝ)) = d - 1 := by
      rw [Int.floor_eq_iff]
      push_cast at hlower' hupper' ⊢
      constructor <;> linarith
    omega

private theorem ndA5TubeRadius_lt {W : ℝ} (hW : 0 < W) :
    (ndA5TubeRadius W : ℝ) < W := by
  have hceil : 0 < Nat.ceil W := Nat.ceil_pos.mpr hW
  have hradius : ndA5TubeRadius W + 1 = Nat.ceil W := by
    unfold ndA5TubeRadius
    omega
  have h := Nat.ceil_lt_add_one hW.le
  rw [← hradius] at h
  push_cast at h
  linarith

/-- On an unclipped full tube, the actual natural fiber multiplicity is the
exact difference of its weak upper and strict lower floors. -/
theorem ndA6StrictLevelMultiplicity_eq_floor_sub_floor
    {A W : ℝ} (hW : 0 < W)
    (hlo : 0 < ndA5TubeLo A W) {d : ℤ}
    (hd : d ∈ Finset.Icc (-(ndA5TubeRadius W : ℤ))
      (ndA5TubeRadius W : ℤ)) :
    (ndA6StrictLevelMultiplicity A W d : ℤ) =
      Int.floor ((A - (d : ℝ) + 1) / ndA5PhaseDelta) -
        Int.floor ((A - (d : ℝ)) / ndA5PhaseDelta) := by
  let lower : ℝ := (A - (d : ℝ)) / ndA5PhaseDelta
  let upper : ℝ := (A - (d : ℝ) + 1) / ndA5PhaseDelta
  have hdBounds := Finset.mem_Icc.mp hd
  have hbaseFloorNonneg :
      0 ≤ Int.floor ((A - (ndA5TubeRadius W : ℝ)) /
        ndA5PhaseDelta) := by
    unfold ndA5TubeLo at hlo
    have hpos := Int.pos_iff_toNat_pos.mpr hlo
    omega
  have hbaseLeLower :
      (A - (ndA5TubeRadius W : ℝ)) / ndA5PhaseDelta ≤ lower := by
    apply (div_le_div_iff_of_pos_right ndA5PhaseDelta_mem_Ioo.1).2
    dsimp [lower]
    have hdUpper : (d : ℝ) ≤ (ndA5TubeRadius W : ℝ) := by
      exact_mod_cast hdBounds.2
    linarith
  have hfloorLowerNonneg : 0 ≤ Int.floor lower :=
    hbaseFloorNonneg.trans (Int.floor_mono hbaseLeLower)
  have hlowerUpper : lower ≤ upper := by
    dsimp [lower, upper]
    apply (div_le_div_iff_of_pos_right ndA5PhaseDelta_mem_Ioo.1).2
    linarith
  have hfloorLowerUpper : Int.floor lower ≤ Int.floor upper :=
    Int.floor_mono hlowerUpper
  have hfloorUpperNonneg : 0 ≤ Int.floor upper :=
    hfloorLowerNonneg.trans hfloorLowerUpper
  have hdAbs : |(d : ℝ)| < W := by
    have hdLower : -((ndA5TubeRadius W : ℝ)) ≤ (d : ℝ) := by
      exact_mod_cast hdBounds.1
    have hdUpper : (d : ℝ) ≤ (ndA5TubeRadius W : ℝ) := by
      exact_mod_cast hdBounds.2
    rw [abs_lt]
    constructor <;> linarith [ndA5TubeRadius_lt hW]
  have hfiber :
      (ndA5FullTube A W).filter
          (fun nu => ndA5StrictAffineSweep A nu = d) =
        Finset.Ioc (Int.floor lower).toNat (Int.floor upper).toNat := by
    ext nu
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨_, hlevel⟩
      have hbounds := (ndA5StrictAffineSweep_eq_iff A nu d).mp hlevel
      change lower < (nu : ℝ) ∧ (nu : ℝ) ≤ upper at hbounds
      constructor
      · have hz : Int.floor lower < (nu : ℤ) := Int.floor_lt.mpr hbounds.1
        have hz' : ((Int.floor lower).toNat : ℤ) < (nu : ℤ) := by
          rw [Int.toNat_of_nonneg hfloorLowerNonneg]
          exact hz
        exact_mod_cast hz'
      · have hz : (nu : ℤ) ≤ Int.floor upper := Int.le_floor.mpr hbounds.2
        have hz' : (nu : ℤ) ≤ ((Int.floor upper).toNat : ℤ) := by
          rw [Int.toNat_of_nonneg hfloorUpperNonneg]
          exact hz
        exact_mod_cast hz'
    · rintro ⟨hlowerNat, hupperNat⟩
      have hlowerZ : ((Int.floor lower).toNat : ℤ) < (nu : ℤ) := by
        exact_mod_cast hlowerNat
      have hupperZ : (nu : ℤ) ≤ ((Int.floor upper).toNat : ℤ) := by
        exact_mod_cast hupperNat
      rw [Int.toNat_of_nonneg hfloorLowerNonneg] at hlowerZ
      rw [Int.toNat_of_nonneg hfloorUpperNonneg] at hupperZ
      have hbounds : lower < (nu : ℝ) ∧ (nu : ℝ) ≤ upper :=
        ⟨Int.floor_lt.mp hlowerZ, Int.le_floor.mp hupperZ⟩
      have hlevel : ndA5StrictAffineSweep A nu = d := by
        apply (ndA5StrictAffineSweep_eq_iff A nu d).mpr
        exact hbounds
      constructor
      · apply (mem_ndA5FullTube_iff hW A nu).mpr
        rw [hlevel]
        exact hdAbs
      · exact hlevel
  have hNatLe : (Int.floor lower).toNat ≤ (Int.floor upper).toNat := by
    omega
  unfold ndA6StrictLevelMultiplicity
  rw [hfiber, Nat.card_Ioc]
  rw [Int.ofNat_sub hNatLe]
  rw [Int.toNat_of_nonneg hfloorUpperNonneg,
    Int.toNat_of_nonneg hfloorLowerNonneg]

/-- The signed error of the actual strict-level multiplicity from its mean
spacing `1 / delta`. -/
noncomputable def ndA6StrictMultiplicityError
    (A W : ℝ) (d : ℤ) : ℝ :=
  (ndA6StrictLevelMultiplicity A W d : ℝ) -
    1 / ndA5PhaseDelta

private theorem abs_intFloor_sub_intFloor_sub_sub_le_one
    (upper lower : ℝ) :
    |((Int.floor upper : ℝ) - (Int.floor lower : ℝ)) -
        (upper - lower)| ≤ 1 := by
  have hUpperFloor := Int.floor_le upper
  have hUpperCeil := Int.lt_floor_add_one upper
  have hLowerFloor := Int.floor_le lower
  have hLowerCeil := Int.lt_floor_add_one lower
  push_cast at hUpperFloor hUpperCeil hLowerFloor hLowerCeil
  rw [abs_le]
  constructor <;> linarith

/-- Every initial segment of the signed tube levels has multiplicity
discrepancy at most one from the mean spacing `1 / delta`.  The levels are
enumerated from `-R` upward and the theorem includes the singleton `R = 0`
case. -/
theorem abs_sum_range_ndA6StrictMultiplicityError_le_one
    {A W : ℝ} (hW : 0 < W)
    (hlo : 0 < ndA5TubeLo A W) {m : ℕ}
    (hm : m ≤ 2 * ndA5TubeRadius W + 1) :
    |∑ i ∈ Finset.range m,
        ndA6StrictMultiplicityError A W
          (-(ndA5TubeRadius W : ℤ) + (i : ℤ))| ≤ 1 := by
  let R : ℕ := ndA5TubeRadius W
  let x : ℕ → ℝ := fun i =>
    (A + (R : ℝ) + 1 - (i : ℝ)) / ndA5PhaseDelta
  let F : ℕ → ℝ := fun i => (Int.floor (x i) : ℝ)
  have herror (i : ℕ) (hi : i ∈ Finset.range m) :
      ndA6StrictMultiplicityError A W (-(R : ℤ) + (i : ℤ)) =
        F i - F (i + 1) - 1 / ndA5PhaseDelta := by
    have hiLt : i < m := Finset.mem_range.mp hi
    have hiLe : i ≤ 2 * R := by
      dsimp [R] at hm ⊢
      omega
    have hd : -(R : ℤ) + (i : ℤ) ∈
        Finset.Icc (-(ndA5TubeRadius W : ℤ))
          (ndA5TubeRadius W : ℤ) := by
      apply Finset.mem_Icc.mpr
      dsimp [R] at hiLe ⊢
      constructor
      · omega
      · have hiLeZ : (i : ℤ) ≤ 2 * (ndA5TubeRadius W : ℤ) := by
          exact_mod_cast hiLe
        omega
    have hmultZ :=
      ndA6StrictLevelMultiplicity_eq_floor_sub_floor hW hlo hd
    have hmult :
        (ndA6StrictLevelMultiplicity A W (-(R : ℤ) + (i : ℤ)) : ℝ) =
          (Int.floor
              ((A - ((-(R : ℤ) + (i : ℤ) : ℤ) : ℝ) + 1) /
                ndA5PhaseDelta) : ℝ) -
            (Int.floor
              ((A - ((-(R : ℤ) + (i : ℤ) : ℤ) : ℝ)) /
                ndA5PhaseDelta) : ℝ) := by
      exact_mod_cast hmultZ
    have hupperArg :
        (A - ((-(R : ℤ) + (i : ℤ) : ℤ) : ℝ) + 1) /
            ndA5PhaseDelta = x i := by
      dsimp [x]
      push_cast
      ring
    have hlowerArg :
        (A - ((-(R : ℤ) + (i : ℤ) : ℤ) : ℝ)) /
            ndA5PhaseDelta = x (i + 1) := by
      dsimp [x]
      push_cast
      ring
    unfold ndA6StrictMultiplicityError
    rw [hmult, hupperArg, hlowerArg]
  have hsum :
      (∑ i ∈ Finset.range m,
          ndA6StrictMultiplicityError A W (-(R : ℤ) + (i : ℤ))) =
        (F 0 - F m) - (m : ℝ) / ndA5PhaseDelta := by
    calc
      (∑ i ∈ Finset.range m,
          ndA6StrictMultiplicityError A W (-(R : ℤ) + (i : ℤ))) =
          ∑ i ∈ Finset.range m,
            (F i - F (i + 1) - 1 / ndA5PhaseDelta) := by
              apply Finset.sum_congr rfl
              exact herror
      _ = (F 0 - F m) - (m : ℝ) / ndA5PhaseDelta := by
        rw [Finset.sum_sub_distrib, Finset.sum_range_sub']
        simp
        ring
  rw [hsum]
  have hx : x 0 - x m = (m : ℝ) / ndA5PhaseDelta := by
    dsimp [x]
    ring
  simpa only [F, hx] using
    (abs_intFloor_sub_intFloor_sub_sub_le_one (x 0) (x m))

/-- Every index in the full strict tube maps to one of its signed integer
levels. -/
theorem ndA5StrictAffineSweep_mem_Icc_of_mem_fullTube
    {A W : ℝ} (hW : 0 < W) {nu : ℕ}
    (hnu : nu ∈ ndA5FullTube A W) :
    ndA5StrictAffineSweep A nu ∈
      Finset.Icc (-(ndA5TubeRadius W : ℤ))
        (ndA5TubeRadius W : ℤ) := by
  let d := ndA5StrictAffineSweep A nu
  have hdTube : |(d : ℝ)| < W := by
    dsimp [d]
    exact (mem_ndA5FullTube_iff hW A nu).mp hnu
  have hnatReal : (Int.natAbs d : ℝ) < W := by
    calc
      (Int.natAbs d : ℝ) = |(d : ℝ)| := by
        rw [Nat.cast_natAbs]
        norm_cast
      _ < W := hdTube
  have hnatCeil : Int.natAbs d < Nat.ceil W :=
    Nat.lt_ceil.mpr hnatReal
  have hceil : 0 < Nat.ceil W := Nat.ceil_pos.mpr hW
  have hradius : ndA5TubeRadius W + 1 = Nat.ceil W := by
    unfold ndA5TubeRadius
    omega
  have hnatRadius : Int.natAbs d ≤ ndA5TubeRadius W := by
    omega
  have hdAbs : |d| ≤ (ndA5TubeRadius W : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnatRadius
  exact Finset.mem_Icc.mpr (abs_le.mp hdAbs)

/-- Regrouping the actual full-tube sum by signed strict-sweep level preserves
the complete natural-index multiplicity. -/
theorem sum_ndA5FullTube_eq_sum_ndA6StrictLevelMultiplicity
    {A W : ℝ} (hW : 0 < W) (phi : ℤ → ℝ) :
    ∑ nu ∈ ndA5FullTube A W, phi (ndA5StrictAffineSweep A nu) =
      ∑ d ∈ Finset.Icc (-(ndA5TubeRadius W : ℤ))
          (ndA5TubeRadius W : ℤ),
        (ndA6StrictLevelMultiplicity A W d : ℝ) * phi d := by
  classical
  have hmaps : ∀ nu ∈ ndA5FullTube A W,
      ndA5StrictAffineSweep A nu ∈
        Finset.Icc (-(ndA5TubeRadius W : ℤ))
          (ndA5TubeRadius W : ℤ) := by
    intro nu hnu
    exact ndA5StrictAffineSweep_mem_Icc_of_mem_fullTube hW hnu
  symm
  simpa only [ndA6StrictLevelMultiplicity, Finset.sum_const,
    nsmul_eq_mul, Nat.cast_ofNat] using
    (Finset.sum_fiberwise_of_maps_to' hmaps phi)

/-- The unweighted Abel bracket appropriate for a coefficient sequence whose
every anchored prefix has absolute value at most one. -/
noncomputable def ndA6AbelVariation (w : ℕ → ℝ) (V : ℕ) : ℝ :=
  |w (V - 1)| +
    ∑ i ∈ Finset.range (V - 1), |w i - w (i + 1)|

/-- Finite summation by parts with unit control on every anchored prefix.
Unlike the A5 localization bracket, this estimate has no length weight. -/
theorem abs_sum_range_mul_le_ndA6AbelVariation
    (e w : ℕ → ℝ) (V : ℕ)
    (hp : ∀ m, m ≤ V → |∑ i ∈ Finset.range m, e i| ≤ 1) :
    |∑ i ∈ Finset.range V, w i * e i| ≤
      ndA6AbelVariation w V := by
  have hAbel :
      (∑ i ∈ Finset.range V, w i * e i) =
        w (V - 1) * (∑ i ∈ Finset.range V, e i) -
          ∑ i ∈ Finset.range (V - 1),
            (w (i + 1) - w i) *
              (∑ j ∈ Finset.range (i + 1), e j) := by
    simpa only [smul_eq_mul] using
      (Finset.sum_range_by_parts w e V)
  have hTerminal :
      |w (V - 1) * (∑ i ∈ Finset.range V, e i)| ≤
        |w (V - 1)| := by
    rw [abs_mul]
    calc
      |w (V - 1)| * |∑ i ∈ Finset.range V, e i| ≤
          |w (V - 1)| * 1 :=
        mul_le_mul_of_nonneg_left (hp V le_rfl) (abs_nonneg _)
      _ = |w (V - 1)| := mul_one _
  have hIncrement (i : ℕ) (hi : i ∈ Finset.range (V - 1)) :
      |(w (i + 1) - w i) *
          (∑ j ∈ Finset.range (i + 1), e j)| ≤
        |w i - w (i + 1)| := by
    have himV : i + 1 ≤ V := by
      have hiLt : i < V - 1 := Finset.mem_range.mp hi
      omega
    rw [abs_mul, abs_sub_comm (w (i + 1)) (w i)]
    calc
      |w i - w (i + 1)| *
          |∑ j ∈ Finset.range (i + 1), e j| ≤
          |w i - w (i + 1)| * 1 :=
        mul_le_mul_of_nonneg_left (hp (i + 1) himV) (abs_nonneg _)
      _ = |w i - w (i + 1)| := mul_one _
  have hBulk :
      |∑ i ∈ Finset.range (V - 1),
          (w (i + 1) - w i) *
            (∑ j ∈ Finset.range (i + 1), e j)| ≤
        ∑ i ∈ Finset.range (V - 1), |w i - w (i + 1)| := by
    calc
      |∑ i ∈ Finset.range (V - 1),
          (w (i + 1) - w i) *
            (∑ j ∈ Finset.range (i + 1), e j)| ≤
          ∑ i ∈ Finset.range (V - 1),
            |(w (i + 1) - w i) *
              (∑ j ∈ Finset.range (i + 1), e j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (V - 1),
          |w i - w (i + 1)| := Finset.sum_le_sum hIncrement
  rw [hAbel]
  unfold ndA6AbelVariation
  exact (abs_sub _ _).trans (add_le_add hTerminal hBulk)

/-- The Abel bracket of a nonnegative sequence increasing to the middle
index and decreasing thereafter is at most twice its peak.  The proof also
covers the singleton `R = 0` case. -/
theorem ndA6AbelVariation_centered_le_two
    (w : ℕ → ℝ) (R : ℕ)
    (h0 : 0 ≤ w 0) (hend : 0 ≤ w (2 * R))
    (hup : ∀ i, i < R → w i ≤ w (i + 1))
    (hdown : ∀ i, R ≤ i → i < 2 * R → w (i + 1) ≤ w i) :
    ndA6AbelVariation w (2 * R + 1) ≤ 2 * w R := by
  have hleft :
      (∑ i ∈ Finset.range R, |w i - w (i + 1)|) =
        w R - w 0 := by
    calc
      (∑ i ∈ Finset.range R, |w i - w (i + 1)|) =
          ∑ i ∈ Finset.range R, (w (i + 1) - w i) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hle : w i - w (i + 1) ≤ 0 :=
              sub_nonpos.mpr (hup i (Finset.mem_range.mp hi))
            rw [abs_of_nonpos hle]
            ring
      _ = -(∑ i ∈ Finset.range R, (w i - w (i + 1))) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = -(w 0 - w R) := by rw [Finset.sum_range_sub']
      _ = w R - w 0 := by ring
  have hright :
      (∑ i ∈ Finset.range R,
          |w (R + i) - w (R + i + 1)|) =
        w R - w (2 * R) := by
    calc
      (∑ i ∈ Finset.range R,
          |w (R + i) - w (R + i + 1)|) =
          ∑ i ∈ Finset.range R,
            (w (R + i) - w (R + i + 1)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [abs_of_nonneg]
              apply sub_nonneg.mpr
              apply hdown
              · omega
              · have hiLt := Finset.mem_range.mp hi
                omega
      _ = w (R + 0) - w (R + R) := by
        simpa only [Nat.add_assoc] using
          (Finset.sum_range_sub' (f := fun i => w (R + i)) R)
      _ = w R - w (2 * R) := by
        congr 2; omega
  unfold ndA6AbelVariation
  rw [show 2 * R + 1 - 1 = 2 * R by omega]
  rw [abs_of_nonneg hend]
  rw [show 2 * R = R + R by omega, Finset.sum_range_add]
  rw [hleft, hright]
  rw [show R + R = 2 * R by omega]
  linarith

/-- A centered-unimodal weight sees at most twice its peak against the actual
strict-level multiplicity errors.  There is no tube-radius or `1 / delta`
loss in this error term. -/
theorem abs_sum_range_mul_ndA6StrictMultiplicityError_le_two_center
    {A W : ℝ} (hW : 0 < W)
    (hlo : 0 < ndA5TubeLo A W) (omega : ℕ → ℝ)
    (h0 : 0 ≤ omega 0)
    (hend : 0 ≤ omega (2 * ndA5TubeRadius W))
    (hup : ∀ i, i < ndA5TubeRadius W → omega i ≤ omega (i + 1))
    (hdown : ∀ i, ndA5TubeRadius W ≤ i →
      i < 2 * ndA5TubeRadius W → omega (i + 1) ≤ omega i) :
    |∑ i ∈ Finset.range (2 * ndA5TubeRadius W + 1),
        omega i * ndA6StrictMultiplicityError A W
          (-(ndA5TubeRadius W : ℤ) + (i : ℤ))| ≤
      2 * omega (ndA5TubeRadius W) := by
  let R : ℕ := ndA5TubeRadius W
  let e : ℕ → ℝ := fun i =>
    ndA6StrictMultiplicityError A W (-(R : ℤ) + (i : ℤ))
  change |∑ i ∈ Finset.range (2 * R + 1), omega i * e i| ≤
    2 * omega R
  calc
    |∑ i ∈ Finset.range (2 * R + 1), omega i * e i| ≤
        ndA6AbelVariation omega (2 * R + 1) := by
      apply abs_sum_range_mul_le_ndA6AbelVariation
      intro m hm
      dsimp [e, R] at hm ⊢
      exact abs_sum_range_ndA6StrictMultiplicityError_le_one hW hlo hm
    _ ≤ 2 * omega R := by
      apply ndA6AbelVariation_centered_le_two
      · exact h0
      · simpa only [R] using hend
      · intro i hi
        apply hup
        simpa only [R] using hi
      · intro i hiR hi
        apply hdown
        · simpa only [R] using hiR
        · simpa only [R] using hi

/-- Endpoint-shaped finite Abel control for the strict-level multiplicity
errors across the complete signed tube.  A later centered-unimodal Gaussian
specialization bounds the displayed variation bracket by twice its peak. -/
theorem abs_sum_range_mul_ndA6StrictMultiplicityError_le_abel
    {A W : ℝ} (hW : 0 < W)
    (hlo : 0 < ndA5TubeLo A W) (omega : ℕ → ℝ) :
    |∑ i ∈ Finset.range (2 * ndA5TubeRadius W + 1),
        omega i * ndA6StrictMultiplicityError A W
          (-(ndA5TubeRadius W : ℤ) + (i : ℤ))| ≤
      |omega (2 * ndA5TubeRadius W)| +
        ∑ i ∈ Finset.range (2 * ndA5TubeRadius W),
          |omega (i + 1) - omega i| := by
  let V : ℕ := 2 * ndA5TubeRadius W + 1
  let B : ℕ → ℝ := fun i =>
    ndA6StrictMultiplicityError A W
      (-(ndA5TubeRadius W : ℤ) + (i : ℤ))
  have hV : 0 < V := by
    dsimp [V]
    omega
  have hPrefix (m : ℕ) (hm : m ≤ V) :
      |∑ i ∈ Finset.range m, B i| ≤ 1 := by
    dsimp [B, V] at hm ⊢
    exact abs_sum_range_ndA6StrictMultiplicityError_le_one hW hlo hm
  have hAbel :
      (∑ i ∈ Finset.range V, omega i * B i) =
        omega (V - 1) * (∑ i ∈ Finset.range V, B i) -
          ∑ i ∈ Finset.range (V - 1),
            (omega (i + 1) - omega i) *
              (∑ j ∈ Finset.range (i + 1), B j) := by
    simpa only [smul_eq_mul] using
      (Finset.sum_range_by_parts omega B V)
  have hTerminal :
      |omega (V - 1) * (∑ i ∈ Finset.range V, B i)| ≤
        |omega (V - 1)| := by
    rw [abs_mul]
    calc
      |omega (V - 1)| * |∑ i ∈ Finset.range V, B i| ≤
          |omega (V - 1)| * 1 :=
        mul_le_mul_of_nonneg_left (hPrefix V le_rfl) (abs_nonneg _)
      _ = |omega (V - 1)| := mul_one _
  have hIncrement (i : ℕ) (hi : i ∈ Finset.range (V - 1)) :
      |(omega (i + 1) - omega i) *
          (∑ j ∈ Finset.range (i + 1), B j)| ≤
        |omega (i + 1) - omega i| := by
    have himV : i + 1 ≤ V := by
      have hiLt : i < V - 1 := Finset.mem_range.mp hi
      omega
    rw [abs_mul]
    calc
      |omega (i + 1) - omega i| *
          |∑ j ∈ Finset.range (i + 1), B j| ≤
          |omega (i + 1) - omega i| * 1 :=
        mul_le_mul_of_nonneg_left (hPrefix (i + 1) himV) (abs_nonneg _)
      _ = |omega (i + 1) - omega i| := mul_one _
  have hBulk :
      |∑ i ∈ Finset.range (V - 1),
          (omega (i + 1) - omega i) *
            (∑ j ∈ Finset.range (i + 1), B j)| ≤
        ∑ i ∈ Finset.range (V - 1),
          |omega (i + 1) - omega i| := by
    calc
      |∑ i ∈ Finset.range (V - 1),
          (omega (i + 1) - omega i) *
            (∑ j ∈ Finset.range (i + 1), B j)| ≤
          ∑ i ∈ Finset.range (V - 1),
            |(omega (i + 1) - omega i) *
              (∑ j ∈ Finset.range (i + 1), B j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (V - 1),
          |omega (i + 1) - omega i| :=
        Finset.sum_le_sum hIncrement
  rw [hAbel]
  calc
    |omega (V - 1) * (∑ i ∈ Finset.range V, B i) -
        ∑ i ∈ Finset.range (V - 1),
          (omega (i + 1) - omega i) *
            (∑ j ∈ Finset.range (i + 1), B j)| ≤
      |omega (V - 1) * (∑ i ∈ Finset.range V, B i)| +
        |∑ i ∈ Finset.range (V - 1),
          (omega (i + 1) - omega i) *
            (∑ j ∈ Finset.range (i + 1), B j)| := abs_sub _ _
    _ ≤ |omega (V - 1)| +
        ∑ i ∈ Finset.range (V - 1),
          |omega (i + 1) - omega i| := add_le_add hTerminal hBulk
    _ = |omega (2 * ndA5TubeRadius W)| +
        ∑ i ∈ Finset.range (2 * ndA5TubeRadius W),
          |omega (i + 1) - omega i| := by
      dsimp [V]

end ND
end Erdos1135
