import Erdos1135.ND.Band.A5Sweep

/-!
# A5 Full Strict Tube

This leaf freezes the literal finite natural-index tube for the strict A5
affine selector.  It deliberately defines the full tube before any physical
band interval is imposed.  The radius is `ceil W - 1`, so integral widths use
the source's strict endpoint convention.
-/

namespace Erdos1135
namespace ND

/-- The largest natural absolute value strictly below the real tube width. -/
noncomputable def ndA5TubeRadius (W : ℝ) : ℕ :=
  Nat.ceil W - 1

/-- The strict integer radius loses less than one from a positive real
width.  This is the scalar form of the `ceil W - 1` convention. -/
theorem ndA5TubeWidth_sub_one_le_radius
    {W : ℝ} (hW : 0 < W) :
    W - 1 ≤ (ndA5TubeRadius W : ℝ) := by
  have hceil : 0 < Nat.ceil W := Nat.ceil_pos.mpr hW
  have hradius : ndA5TubeRadius W + 1 = Nat.ceil W := by
    unfold ndA5TubeRadius
    omega
  have hceilLower : W ≤ (Nat.ceil W : ℝ) := Nat.le_ceil W
  rw [← hradius] at hceilLower
  push_cast at hceilLower
  linarith

/-- Above width two, the strict integer radius retains at least half of the
real width. -/
theorem ndA5TubeWidth_div_two_le_radius
    {W : ℝ} (hW : 2 ≤ W) :
    W / 2 ≤ (ndA5TubeRadius W : ℝ) := by
  calc
    W / 2 ≤ W - 1 := by linarith
    _ ≤ (ndA5TubeRadius W : ℝ) :=
      ndA5TubeWidth_sub_one_le_radius (by linarith)

/-- A finite upper cap for all natural indices in the strict affine tube. -/
noncomputable def ndA5TubeUpperCap (A W : ℝ) : ℕ :=
  (Int.floor ((A + (ndA5TubeRadius W : ℝ) + 1) /
    ndA5PhaseDelta)).toNat

/-- The natural lower endpoint obtained from the strict lower real bound.
Negative signed endpoints are clipped to zero by `Int.toNat`. -/
noncomputable def ndA5TubeLo (A W : ℝ) : ℕ :=
  (Int.floor ((A - (ndA5TubeRadius W : ℝ)) /
    ndA5PhaseDelta) + 1).toNat

/-- The natural upper endpoint obtained from the weak upper real bound. -/
noncomputable def ndA5TubeHi (A W : ℝ) : ℕ :=
  ndA5TubeUpperCap A W

/-- The full finite natural-index tube for the strict affine selector. -/
noncomputable def ndA5FullTube (A W : ℝ) : Finset ℕ :=
  (Finset.range (ndA5TubeUpperCap A W + 1)).filter
    (fun nu => |(ndA5StrictAffineSweep A nu : ℝ)| < W)

private theorem intCast_abs_lt_iff_natAbs_le_tubeRadius
    {W : ℝ} (hW : 0 < W) (d : ℤ) :
    |(d : ℝ)| < W ↔ Int.natAbs d ≤ ndA5TubeRadius W := by
  have hceil : 0 < Nat.ceil W := Nat.ceil_pos.mpr hW
  have hradius : ndA5TubeRadius W + 1 = Nat.ceil W := by
    unfold ndA5TubeRadius
    omega
  calc
    |(d : ℝ)| < W ↔ (Int.natAbs d : ℝ) < W := by
      rw [Nat.cast_natAbs]
      norm_cast
    _ ↔ Int.natAbs d < Nat.ceil W := Nat.lt_ceil.symm
    _ ↔ Int.natAbs d ≤ ndA5TubeRadius W := by omega

private theorem natAbs_le_iff_signed_bounds (d : ℤ) (r : ℕ) :
    Int.natAbs d ≤ r ↔ -(r : ℤ) ≤ d ∧ d ≤ (r : ℤ) := by
  rw [← Int.ofNat_le, Int.natCast_natAbs]
  exact abs_le

/-- The strict integer tube is exactly the asymmetric pair of affine real
bounds dictated by `floor x + 1`. -/
theorem ndA5StrictAffineSweep_abs_lt_iff_affine
    {W : ℝ} (hW : 0 < W) (A : ℝ) (nu : ℕ) :
    |(ndA5StrictAffineSweep A nu : ℝ)| < W ↔
      (A - (ndA5TubeRadius W : ℝ)) / ndA5PhaseDelta < (nu : ℝ) ∧
        (nu : ℝ) ≤
          (A + (ndA5TubeRadius W : ℝ) + 1) / ndA5PhaseDelta := by
  rw [intCast_abs_lt_iff_natAbs_le_tubeRadius hW]
  rw [natAbs_le_iff_signed_bounds]
  unfold ndA5StrictAffineSweep
  constructor
  · rintro ⟨hlower, hupper⟩
    have hlowerFloor : -((ndA5TubeRadius W : ℤ)) - 1 ≤
        Int.floor (A - ndA5PhaseDelta * (nu : ℝ)) := by
      omega
    have hupperFloor :
        Int.floor (A - ndA5PhaseDelta * (nu : ℝ)) <
          (ndA5TubeRadius W : ℤ) := by
      omega
    have hlowerReal := Int.le_floor.mp hlowerFloor
    have hupperReal := Int.floor_lt.mp hupperFloor
    constructor
    · apply (div_lt_iff₀ ndA5PhaseDelta_mem_Ioo.1).2
      push_cast at hupperReal ⊢
      linarith
    · apply (le_div_iff₀ ndA5PhaseDelta_mem_Ioo.1).2
      push_cast at hlowerReal ⊢
      linarith
  · rintro ⟨hlower, hupper⟩
    have hupperReal : A - ndA5PhaseDelta * (nu : ℝ) <
        (ndA5TubeRadius W : ℤ) := by
      have h := (div_lt_iff₀ ndA5PhaseDelta_mem_Ioo.1).mp hlower
      push_cast at h ⊢
      linarith
    have hlowerReal : (-((ndA5TubeRadius W : ℤ)) - 1 : ℤ) ≤
        A - ndA5PhaseDelta * (nu : ℝ) := by
      have h := (le_div_iff₀ ndA5PhaseDelta_mem_Ioo.1).mp hupper
      push_cast at h ⊢
      linarith
    have hupperFloor :
        Int.floor (A - ndA5PhaseDelta * (nu : ℝ)) <
          (ndA5TubeRadius W : ℤ) :=
      Int.floor_lt.mpr hupperReal
    have hlowerFloor : -((ndA5TubeRadius W : ℤ)) - 1 ≤
        Int.floor (A - ndA5PhaseDelta * (nu : ℝ)) :=
      Int.le_floor.mpr hlowerReal
    constructor <;> omega

/-- The explicit range cap is total but does not remove any point satisfying
the strict tube predicate. -/
theorem mem_ndA5FullTube_iff {W : ℝ} (hW : 0 < W) (A : ℝ) (nu : ℕ) :
    nu ∈ ndA5FullTube A W ↔
      |(ndA5StrictAffineSweep A nu : ℝ)| < W := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro htube
    have hbounds :=
      (ndA5StrictAffineSweep_abs_lt_iff_affine hW A nu).mp htube
    have hnuFloor : (nu : ℤ) ≤
        Int.floor ((A + (ndA5TubeRadius W : ℝ) + 1) /
          ndA5PhaseDelta) :=
      Int.le_floor.mpr hbounds.2
    have hfloor : 0 ≤
        Int.floor ((A + (ndA5TubeRadius W : ℝ) + 1) /
          ndA5PhaseDelta) := by
      omega
    have hnuCap : nu ≤ ndA5TubeUpperCap A W := by
      unfold ndA5TubeUpperCap
      exact (Int.le_toNat hfloor).mpr hnuFloor
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hnuCap), htube⟩

/-- Every positive affine phase has a natural point in a strict tube whose
width is larger than the unit strict-selector witness. -/
theorem ndA5FullTube_nonempty_of_phase_pos
    {A W : ℝ} (hA : 0 < A) (hW : 1 < W) :
    (ndA5FullTube A W).Nonempty := by
  have hWpos : 0 < W := by linarith
  let q := Nat.floor (A / ndA5PhaseDelta)
  have hcenterNonneg : 0 ≤ A / ndA5PhaseDelta :=
    (div_pos hA ndA5PhaseDelta_mem_Ioo.1).le
  have hqLower : (q : ℝ) ≤ A / ndA5PhaseDelta := by
    dsimp [q]
    exact Nat.floor_le hcenterNonneg
  have hqUpper : A / ndA5PhaseDelta < (q : ℝ) + 1 := by
    dsimp [q]
    simpa using Nat.lt_floor_add_one (A / ndA5PhaseDelta)
  have hqLowerMul : ndA5PhaseDelta * (q : ℝ) ≤ A := by
    simpa [mul_comm] using
      (le_div_iff₀ ndA5PhaseDelta_mem_Ioo.1).mp hqLower
  have hqUpperMul :
      A < ndA5PhaseDelta * ((q : ℝ) + 1) := by
    simpa [mul_comm] using
      (div_lt_iff₀ ndA5PhaseDelta_mem_Ioo.1).mp hqUpper
  have hremainderLower :
      0 ≤ A - ndA5PhaseDelta * (q : ℝ) := by
    linarith
  have hremainderUpper :
      A - ndA5PhaseDelta * (q : ℝ) < ndA5PhaseDelta := by
    nlinarith
  have hfloor :
      Int.floor (A - ndA5PhaseDelta * (q : ℝ)) = 0 := by
    rw [Int.floor_eq_iff]
    constructor
    · simpa using hremainderLower
    · simpa using hremainderUpper.trans ndA5PhaseDelta_mem_Ioo.2
  have hsweep : ndA5StrictAffineSweep A q = 1 := by
    unfold ndA5StrictAffineSweep
    rw [hfloor]
    omega
  refine ⟨q, (mem_ndA5FullTube_iff hWpos A q).mpr ?_⟩
  rw [hsweep]
  norm_num
  exact hW

/-- A nonempty full strict tube is the exact natural interval between the
strict lower and weak upper affine endpoints. -/
theorem ndA5FullTube_eq_Icc {A W : ℝ} (hW : 0 < W)
    (hne : (ndA5FullTube A W).Nonempty) :
    ndA5FullTube A W = Finset.Icc (ndA5TubeLo A W) (ndA5TubeHi A W) := by
  obtain ⟨nu₀, hnu₀⟩ := hne
  have hbounds₀ :=
    (ndA5StrictAffineSweep_abs_lt_iff_affine hW A nu₀).mp
      ((mem_ndA5FullTube_iff hW A nu₀).mp hnu₀)
  have hnu₀Floor : (nu₀ : ℤ) ≤
      Int.floor ((A + (ndA5TubeRadius W : ℝ) + 1) /
        ndA5PhaseDelta) :=
    Int.le_floor.mpr hbounds₀.2
  have hfloor : 0 ≤
      Int.floor ((A + (ndA5TubeRadius W : ℝ) + 1) /
        ndA5PhaseDelta) := by
    omega
  ext nu
  rw [mem_ndA5FullTube_iff hW]
  rw [Finset.mem_Icc]
  constructor
  · intro htube
    have hbounds :=
      (ndA5StrictAffineSweep_abs_lt_iff_affine hW A nu).mp htube
    constructor
    · unfold ndA5TubeLo
      apply Int.toNat_le.mpr
      have hfloorLower :
          Int.floor ((A - (ndA5TubeRadius W : ℝ)) /
            ndA5PhaseDelta) < (nu : ℤ) :=
        Int.floor_lt.mpr hbounds.1
      omega
    · unfold ndA5TubeHi ndA5TubeUpperCap
      apply (Int.le_toNat hfloor).mpr
      exact Int.le_floor.mpr hbounds.2
  · rintro ⟨hlower, hupper⟩
    apply (ndA5StrictAffineSweep_abs_lt_iff_affine hW A nu).mpr
    constructor
    · unfold ndA5TubeLo at hlower
      have hlowerZ := Int.toNat_le.mp hlower
      apply Int.floor_lt.mp
      omega
    · unfold ndA5TubeHi ndA5TubeUpperCap at hupper
      have hupperZ := (Int.le_toNat hfloor).mp hupper
      exact Int.le_floor.mp hupperZ

private theorem card_ndA5FullTube_eq_intFloor_sub_intFloor
    {A W : ℝ} (hW : 0 < W)
    (hne : (ndA5FullTube A W).Nonempty) (hlo : 0 < ndA5TubeLo A W) :
    ((ndA5FullTube A W).card : ℝ) =
      (Int.floor ((A + (ndA5TubeRadius W : ℝ) + 1) /
          ndA5PhaseDelta) : ℝ) -
        (Int.floor ((A - (ndA5TubeRadius W : ℝ)) /
          ndA5PhaseDelta) : ℝ) := by
  have hEq := ndA5FullTube_eq_Icc hW hne
  have hlohi : ndA5TubeLo A W ≤ ndA5TubeHi A W := by
    rw [← Finset.nonempty_Icc]
    rw [← hEq]
    exact hne
  have hloFloorNonneg : 0 ≤
      Int.floor ((A - (ndA5TubeRadius W : ℝ)) /
        ndA5PhaseDelta) + 1 := by
    unfold ndA5TubeLo at hlo
    exact (Int.pos_iff_toNat_pos.mpr hlo).le
  have hloInt : (ndA5TubeLo A W : ℤ) =
      Int.floor ((A - (ndA5TubeRadius W : ℝ)) /
        ndA5PhaseDelta) + 1 := by
    unfold ndA5TubeLo
    exact Int.toNat_of_nonneg hloFloorNonneg
  have hhiPos : 0 < ndA5TubeHi A W := hlo.trans_le hlohi
  have hhiFloorNonneg : 0 ≤
      Int.floor ((A + (ndA5TubeRadius W : ℝ) + 1) /
        ndA5PhaseDelta) := by
    unfold ndA5TubeHi ndA5TubeUpperCap at hhiPos
    exact (Int.pos_iff_toNat_pos.mpr hhiPos).le
  have hhiInt : (ndA5TubeHi A W : ℤ) =
      Int.floor ((A + (ndA5TubeRadius W : ℝ) + 1) /
        ndA5PhaseDelta) := by
    unfold ndA5TubeHi ndA5TubeUpperCap
    exact Int.toNat_of_nonneg hhiFloorNonneg
  have hcardInt : ((ndA5FullTube A W).card : ℤ) =
      Int.floor ((A + (ndA5TubeRadius W : ℝ) + 1) /
        ndA5PhaseDelta) -
      Int.floor ((A - (ndA5TubeRadius W : ℝ)) /
        ndA5PhaseDelta) := by
    rw [hEq, Nat.card_Icc]
    rw [Int.ofNat_sub
      (by omega : ndA5TubeLo A W ≤ ndA5TubeHi A W + 1)]
    push_cast
    rw [hloInt, hhiInt]
    ring
  norm_cast

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

/-- The cardinality of an unclipped full strict tube has the frozen v10
`K_I = 2 + 1 / delta` error.  The positive lower endpoint is load-bearing:
without it, natural-index clipping can lose order `W` points. -/
theorem ndA5FullTube_card_error {A W : ℝ} (hW : 0 < W)
    (hne : (ndA5FullTube A W).Nonempty) (hlo : 0 < ndA5TubeLo A W) :
    |((ndA5FullTube A W).card : ℝ) -
        2 * W / ndA5PhaseDelta| ≤
      2 + 1 / ndA5PhaseDelta := by
  have hcard :=
    card_ndA5FullTube_eq_intFloor_sub_intFloor hW hne hlo
  have hceil : 0 < Nat.ceil W := Nat.ceil_pos.mpr hW
  have hradius : ndA5TubeRadius W + 1 = Nat.ceil W := by
    unfold ndA5TubeRadius
    omega
  have hradiusLt : (ndA5TubeRadius W : ℝ) < W := by
    have h := Nat.ceil_lt_add_one hW.le
    rw [← hradius] at h
    push_cast at h
    linarith
  have hWLeRadiusAddOne : W ≤ (ndA5TubeRadius W : ℝ) + 1 := by
    have h := Nat.le_ceil W
    rw [← hradius] at h
    push_cast at h
    linarith
  have hradiusError :
      |(2 * (ndA5TubeRadius W : ℝ) + 1) - 2 * W| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hdelta : 0 < ndA5PhaseDelta := ndA5PhaseDelta_mem_Ioo.1
  have hwidthError :
      |(2 * (ndA5TubeRadius W : ℝ) + 1) / ndA5PhaseDelta -
          2 * W / ndA5PhaseDelta| ≤ 1 / ndA5PhaseDelta := by
    rw [← sub_div, abs_div, abs_of_pos hdelta]
    exact (div_le_div_iff_of_pos_right hdelta).mpr hradiusError
  let lower : ℝ :=
    (A - (ndA5TubeRadius W : ℝ)) / ndA5PhaseDelta
  let upper : ℝ :=
    (A + (ndA5TubeRadius W : ℝ) + 1) / ndA5PhaseDelta
  have hspan : upper - lower =
      (2 * (ndA5TubeRadius W : ℝ) + 1) / ndA5PhaseDelta := by
    dsimp [upper, lower]
    ring
  have hfloorError :
      |((Int.floor upper : ℝ) - (Int.floor lower : ℝ)) -
          (upper - lower)| ≤ 1 :=
    abs_intFloor_sub_intFloor_sub_sub_le_one upper lower
  have hspanError :
      |(upper - lower) - 2 * W / ndA5PhaseDelta| ≤
        1 / ndA5PhaseDelta := by
    rw [hspan]
    exact hwidthError
  rw [hcard]
  change |((Int.floor upper : ℝ) - (Int.floor lower : ℝ)) -
      2 * W / ndA5PhaseDelta| ≤ 2 + 1 / ndA5PhaseDelta
  calc
    |((Int.floor upper : ℝ) - (Int.floor lower : ℝ)) -
        2 * W / ndA5PhaseDelta| =
        |(((Int.floor upper : ℝ) - (Int.floor lower : ℝ)) -
          (upper - lower)) +
          ((upper - lower) - 2 * W / ndA5PhaseDelta)| := by
            congr 1
            ring
    _ ≤ |((Int.floor upper : ℝ) - (Int.floor lower : ℝ)) -
          (upper - lower)| +
        |(upper - lower) - 2 * W / ndA5PhaseDelta| := abs_add_le _ _
    _ ≤ 1 + 1 / ndA5PhaseDelta :=
      add_le_add hfloorError hspanError
    _ ≤ 2 + 1 / ndA5PhaseDelta := by linarith

/-- If the nonempty full tube is not clipped at zero on the left, its two
natural endpoints attain the exact signed radius values. -/
theorem ndA5FullTube_endpoint_crossings {A W : ℝ} (hW : 0 < W)
    (hne : (ndA5FullTube A W).Nonempty) (hlo : 0 < ndA5TubeLo A W) :
    ndA5StrictAffineSweep A (ndA5TubeLo A W) =
        (ndA5TubeRadius W : ℤ) ∧
      ndA5StrictAffineSweep A (ndA5TubeHi A W) =
        -(ndA5TubeRadius W : ℤ) := by
  have hEq := ndA5FullTube_eq_Icc hW hne
  have hlohi : ndA5TubeLo A W ≤ ndA5TubeHi A W := by
    rw [← Finset.nonempty_Icc]
    rw [← hEq]
    exact hne
  have hloMem : ndA5TubeLo A W ∈ ndA5FullTube A W := by
    rw [hEq]
    exact Finset.left_mem_Icc.mpr hlohi
  have hhiMem : ndA5TubeHi A W ∈ ndA5FullTube A W := by
    rw [hEq]
    exact Finset.right_mem_Icc.mpr hlohi
  have hsigned (nu : ℕ) (hnu : nu ∈ ndA5FullTube A W) :
      -(ndA5TubeRadius W : ℤ) ≤ ndA5StrictAffineSweep A nu ∧
        ndA5StrictAffineSweep A nu ≤ (ndA5TubeRadius W : ℤ) := by
    apply (natAbs_le_iff_signed_bounds _ _).mp
    apply (intCast_abs_lt_iff_natAbs_le_tubeRadius hW _).mp
    exact (mem_ndA5FullTube_iff hW A nu).mp hnu
  have hloBounds := hsigned (ndA5TubeLo A W) hloMem
  have hhiBounds := hsigned (ndA5TubeHi A W) hhiMem
  let p := ndA5TubeLo A W - 1
  have hpSucc : p + 1 = ndA5TubeLo A W := by
    dsimp [p]
    omega
  have hpNot : p ∉ ndA5FullTube A W := by
    intro hp
    rw [hEq] at hp
    have hpLower := (Finset.mem_Icc.mp hp).1
    dsimp [p] at hpLower
    omega
  have hpOutside :
      ndA5StrictAffineSweep A p < -(ndA5TubeRadius W : ℤ) ∨
        (ndA5TubeRadius W : ℤ) < ndA5StrictAffineSweep A p := by
    by_contra h
    push Not at h
    apply hpNot
    apply (mem_ndA5FullTube_iff hW A p).mpr
    apply (intCast_abs_lt_iff_natAbs_le_tubeRadius hW _).mpr
    apply (natAbs_le_iff_signed_bounds _ _).mpr
    exact h
  have hpStep := ndA5StrictAffineSweep_succ A p
  rw [hpSucc] at hpStep
  have hloExact : ndA5StrictAffineSweep A (ndA5TubeLo A W) =
      (ndA5TubeRadius W : ℤ) := by
    rcases hpStep with hpStep | hpStep <;> omega
  let q := ndA5TubeHi A W + 1
  have hqNot : q ∉ ndA5FullTube A W := by
    intro hq
    rw [hEq] at hq
    have hqUpper := (Finset.mem_Icc.mp hq).2
    dsimp [q] at hqUpper
    omega
  have hqOutside :
      ndA5StrictAffineSweep A q < -(ndA5TubeRadius W : ℤ) ∨
        (ndA5TubeRadius W : ℤ) < ndA5StrictAffineSweep A q := by
    by_contra h
    push Not at h
    apply hqNot
    apply (mem_ndA5FullTube_iff hW A q).mpr
    apply (intCast_abs_lt_iff_natAbs_le_tubeRadius hW _).mpr
    apply (natAbs_le_iff_signed_bounds _ _).mpr
    exact h
  have hhiStep := ndA5StrictAffineSweep_succ A (ndA5TubeHi A W)
  change ndA5StrictAffineSweep A q =
        ndA5StrictAffineSweep A (ndA5TubeHi A W) ∨
      ndA5StrictAffineSweep A q =
        ndA5StrictAffineSweep A (ndA5TubeHi A W) - 1 at hhiStep
  have hhiExact : ndA5StrictAffineSweep A (ndA5TubeHi A W) =
      -(ndA5TubeRadius W : ℤ) := by
    rcases hhiStep with hhiStep | hhiStep <;> omega
  exact ⟨hloExact, hhiExact⟩

end ND
end Erdos1135
