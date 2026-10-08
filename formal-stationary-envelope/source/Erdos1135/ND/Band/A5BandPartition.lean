import Erdos1135.ND.Band.A5BandNormalizer
import Mathlib.Data.Finset.Pairwise

/-!
# Exact A5 Band Partition

The frozen v10 bands partition the positive odd values in the half-open real
interval `[y, y^alpha)`.  The checked ND source block is inclusive at its
upper real endpoint, so this leaf keeps the possible terminal odd natural as
a separate at-most-singleton component.  It never declares that component
unconditionally empty.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- The possible odd natural lying exactly at a real endpoint. -/
noncomputable def oddRealEndpoint (u : ℝ) : Finset ℕ :=
  (Finset.Icc (Nat.ceil u) (Nat.floor u)).filter (fun N => N % 2 = 1)

/-- Exact membership in the terminal real-endpoint component. -/
theorem mem_oddRealEndpoint {u : ℝ} {N : ℕ} :
    N ∈ oddRealEndpoint u ↔ (N : ℝ) = u ∧ N % 2 = 1 := by
  by_cases hu : 0 ≤ u
  · simp only [oddRealEndpoint, Finset.mem_filter, Finset.mem_Icc,
      Nat.ceil_le, Nat.le_floor_iff hu]
    constructor
    · rintro ⟨⟨huN, hNu⟩, hodd⟩
      exact ⟨le_antisymm hNu huN, hodd⟩
    · rintro ⟨hNu, hodd⟩
      exact ⟨⟨hNu.ge, hNu.le⟩, hodd⟩
  · have hunonpos : u ≤ 0 := (lt_of_not_ge hu).le
    rw [oddRealEndpoint, Finset.mem_filter, Finset.mem_Icc,
      Nat.floor_of_nonpos hunonpos]
    constructor
    · rintro ⟨⟨_, hNzero⟩, hodd⟩
      have : N = 0 := by omega
      subst N
      norm_num at hodd
    · rintro ⟨hNu, _⟩
      have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      exact (hu (hNu ▸ hNnonneg)).elim

/-- A real endpoint contributes at most one odd natural. -/
theorem card_oddRealEndpoint_le_one (u : ℝ) :
    (oddRealEndpoint u).card ≤ 1 := by
  calc
    (oddRealEndpoint u).card ≤
        (Finset.Icc (Nat.ceil u) (Nat.floor u)).card :=
      Finset.card_filter_le _ _
    _ = Nat.floor u + 1 - Nat.ceil u := Nat.card_Icc _ _
    _ ≤ 1 := by
      have := Nat.floor_le_ceil u
      omega

/-- The terminal component is empty or a genuine singleton. -/
theorem oddRealEndpoint_eq_empty_or_singleton (u : ℝ) :
    oddRealEndpoint u = ∅ ∨
      ∃ N : ℕ, oddRealEndpoint u = {N} := by
  by_cases h : (oddRealEndpoint u).Nonempty
  · right
    rcases h with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    ext M
    simp only [Finset.mem_singleton]
    constructor
    · intro hM
      exact (Finset.card_le_one.mp (card_oddRealEndpoint_le_one u))
        M hM N hN
    · rintro rfl
      exact hN
  · left
    exact Finset.not_nonempty_iff_eq_empty.mp h

/-- Singleton criterion for the terminal component. -/
theorem oddRealEndpoint_eq_singleton_iff
    {u : ℝ} {N : ℕ} :
    oddRealEndpoint u = {N} ↔ (N : ℝ) = u ∧ N % 2 = 1 := by
  constructor
  · intro h
    apply mem_oddRealEndpoint.mp
    rw [h]
    simp
  · intro hN
    ext M
    simp only [Finset.mem_singleton]
    constructor
    · intro hM
      have hM' := mem_oddRealEndpoint.mp hM
      exact_mod_cast hM'.1.trans hN.1.symm
    · rintro rfl
      exact mem_oddRealEndpoint.mpr hN

/-- Exact logarithmic mass of the possible terminal endpoint. -/
theorem logFinsetMass_oddRealEndpoint (u : ℝ) :
    Tao.logFinsetMass (oddRealEndpoint u) =
      ((oddRealEndpoint u).card : ℝ) / u := by
  unfold Tao.logFinsetMass
  calc
    (∑ N ∈ oddRealEndpoint u, Tao.logNatWeight N) =
        ∑ N ∈ oddRealEndpoint u, 1 / u := by
      apply Finset.sum_congr rfl
      intro N hN
      have hend := mem_oddRealEndpoint.mp hN
      have hNpos : 0 < N := by
        have hmod := Nat.mod_lt N (by omega : 0 < 2)
        omega
      rw [Tao.logNatWeight_eq_one_div_of_pos hNpos, hend.1]
    _ = ((oddRealEndpoint u).card : ℝ) / u := by
      simp [div_eq_mul_inv]

/-- The possible terminal endpoint has mass at most `1/u` when `u>0`. -/
theorem logFinsetMass_oddRealEndpoint_le_one_div
    {u : ℝ} (hu : 0 < u) :
    Tao.logFinsetMass (oddRealEndpoint u) ≤ 1 / u := by
  rw [logFinsetMass_oddRealEndpoint]
  apply (div_le_div_iff_of_pos_right hu).2
  exact_mod_cast card_oddRealEndpoint_le_one u

/-- A half-open carrier is disjoint from its terminal endpoint. -/
theorem oddHalfOpenRealWindow_disjoint_oddRealEndpoint
    {y u : ℝ} :
    Disjoint (oddHalfOpenRealWindow y u) (oddRealEndpoint u) := by
  apply Finset.disjoint_left.mpr
  intro N hhalf hend
  have hlt := (mem_oddHalfOpenRealWindow.mp hhalf).2.1
  have heq := (mem_oddRealEndpoint.mp hend).1
  linarith

/-- Restore the inclusive natural upper endpoint to a half-open real window. -/
theorem oddLogWindow_ceil_floor_eq_halfOpen_union_endpoint
    {y u : ℝ} (hyu : y ≤ u) :
    Tao.oddLogWindow (Nat.ceil y) (Nat.floor u) =
      oddHalfOpenRealWindow y u ∪ oddRealEndpoint u := by
  by_cases hu : 0 ≤ u
  · ext N
    rw [Tao.oddLogWindow_mem, Finset.mem_union,
      mem_oddHalfOpenRealWindow, mem_oddRealEndpoint,
      Nat.ceil_le, Nat.le_floor_iff hu]
    constructor
    · rintro ⟨hyN, hNu, hodd⟩
      rcases lt_or_eq_of_le hNu with hlt | heq
      · exact Or.inl ⟨hyN, hlt, hodd⟩
      · exact Or.inr ⟨heq, hodd⟩
    · rintro (hhalf | hend)
      · exact ⟨hhalf.1, hhalf.2.1.le, hhalf.2.2⟩
      · exact ⟨hyu.trans_eq hend.1.symm, hend.1.le, hend.2⟩
  · have hunonpos : u ≤ 0 := (lt_of_not_ge hu).le
    ext N
    rw [Tao.oddLogWindow_mem, Finset.mem_union,
      mem_oddHalfOpenRealWindow, mem_oddRealEndpoint,
      Nat.floor_of_nonpos hunonpos]
    constructor
    · rintro ⟨_, hNzero, hodd⟩
      have : N = 0 := by omega
      subst N
      norm_num at hodd
    · rintro (hhalf | hend)
      · have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        linarith [hhalf.2.1]
      · have hNnonneg : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        exact (hu (hend.1 ▸ hNnonneg)).elim

/-- Union-oriented form of the half-open/inclusive endpoint bridge. -/
theorem oddHalfOpenRealWindow_union_oddRealEndpoint
    {z u : ℝ} (hzu : z ≤ u) :
    oddHalfOpenRealWindow z u ∪ oddRealEndpoint u =
      Tao.oddLogWindow (Nat.ceil z) (Nat.floor u) :=
  (oddLogWindow_ceil_floor_eq_halfOpen_union_endpoint hzu).symm

/-- The checked inclusive ND block is its frozen half-open source interval
plus the possible odd terminal endpoint. -/
theorem oddBlock_eq_halfOpen_union_endpoint
    {y : ℝ} (hy : 1 ≤ y) :
    oddBlock y =
      oddHalfOpenRealWindow y (Real.rpow y alpha) ∪
        oddRealEndpoint (Real.rpow y alpha) := by
  change Tao.oddLogWindow (Nat.ceil y) (Nat.floor (Real.rpow y alpha)) = _
  apply oddLogWindow_ceil_floor_eq_halfOpen_union_endpoint
  exact Real.self_le_rpow_of_one_le hy (by
    norm_num [alpha, Tao.taoAlpha])

/-- The last consecutive A5 lower endpoint is exactly `y^alpha`. -/
theorem ndA5BandLower_count_eq_rpow
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch}
    (hcount : 0 < ndA5BandCount B branch) :
    ndA5BandLower B branch (ndA5BandCount B branch) =
      Real.rpow (Tao.taoSection5SourceY B branch) alpha := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hYpos : 0 < Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos hBpos _
  have hexponent :
      (ndA5BandCount B branch : ℝ) * ndA5BandBeta B branch =
        (alpha - 1) * Real.log (Tao.taoSection5SourceY B branch) := by
    calc
      (ndA5BandCount B branch : ℝ) * ndA5BandBeta B branch =
          ndA5BandBeta B branch * (ndA5BandCount B branch : ℝ) :=
        mul_comm _ _
      _ = ndA5BandLogWidth B branch :=
        ndA5BandBeta_mul_count hcount
      _ = (alpha - 1) *
          Real.log (Tao.taoSection5SourceY B branch) := rfl
  unfold ndA5BandLower
  rw [hexponent]
  calc
    Tao.taoSection5SourceY B branch *
        Real.exp ((alpha - 1) *
          Real.log (Tao.taoSection5SourceY B branch)) =
      Real.exp (Real.log (Tao.taoSection5SourceY B branch)) *
        Real.exp ((alpha - 1) *
          Real.log (Tao.taoSection5SourceY B branch)) := by
        rw [Real.exp_log hYpos]
    _ = Real.exp
        (Real.log (Tao.taoSection5SourceY B branch) +
          (alpha - 1) *
            Real.log (Tao.taoSection5SourceY B branch)) := by
      rw [Real.exp_add]
    _ = Real.exp
        (Real.log (Tao.taoSection5SourceY B branch) * alpha) := by
      congr 1
      ring
    _ = Real.rpow (Tao.taoSection5SourceY B branch) alpha :=
      (Real.rpow_def_of_pos hYpos alpha).symm

/-- Exact A5 lower endpoints are monotone, independently of whether the
partition has positive band count. -/
theorem monotone_ndA5BandLower
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch) :
    Monotone (ndA5BandLower B branch) := by
  intro i j hij
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hYpos : 0 < Tao.taoSection5SourceY B branch := by
    rw [Tao.taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos hBpos _
  have hbeta := ndA5BandBeta_nonneg hB branch
  unfold ndA5BandLower
  apply mul_le_mul_of_nonneg_left _ hYpos.le
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hbeta

private theorem oddHalfOpenRealWindow_union_consecutive
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    oddHalfOpenRealWindow a b ∪ oddHalfOpenRealWindow b c =
      oddHalfOpenRealWindow a c := by
  unfold oddHalfOpenRealWindow
  rw [← Finset.filter_union,
    Finset.Ico_union_Ico_eq_Ico (Nat.ceil_mono hab) (Nat.ceil_mono hbc)]

private theorem biUnion_range_oddHalfOpenRealWindow
    (z : ℕ → ℝ) (hz : Monotone z) (J : ℕ) :
    (Finset.range J).biUnion
        (fun j => oddHalfOpenRealWindow (z j) (z (j + 1))) =
      oddHalfOpenRealWindow (z 0) (z J) := by
  induction J with
  | zero => simp [oddHalfOpenRealWindow]
  | succ J ih =>
      rw [Finset.range_add_one, Finset.biUnion_insert, ih, Finset.union_comm]
      exact oddHalfOpenRealWindow_union_consecutive
        (hz (Nat.zero_le J)) (hz (Nat.le_succ J))

/-- The finite union of exact A5 bands telescopes to the full half-open
source interval. -/
theorem biUnion_range_ndA5OddBand
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (K : ℕ) :
    (Finset.range K).biUnion
        (ndA5OddBand B branch) =
      oddHalfOpenRealWindow (Tao.taoSection5SourceY B branch)
        (ndA5BandLower B branch K) := by
  have h := biUnion_range_oddHalfOpenRealWindow
    (ndA5BandLower B branch)
    (monotone_ndA5BandLower hB branch) K
  simpa only [ndA5OddBand, ndA5BandLower_zero] using h

/-- Endpoint-rewritten form of the exact half-open A5 partition. -/
theorem biUnion_range_ndA5OddBand_eq_source_rpow
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch}
    (hcount : 0 < ndA5BandCount B branch) :
    (Finset.range (ndA5BandCount B branch)).biUnion
        (ndA5OddBand B branch) =
      oddHalfOpenRealWindow (Tao.taoSection5SourceY B branch)
        (Real.rpow (Tao.taoSection5SourceY B branch) alpha) := by
  rw [biUnion_range_ndA5OddBand hB branch (ndA5BandCount B branch),
    ndA5BandLower_count_eq_rpow hB hcount]

/-- Distinct exact A5 bands are pairwise disjoint. -/
theorem ndA5OddBand_pairwiseDisjoint
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (K : ℕ) :
    Set.PairwiseDisjoint
      (↑(Finset.range K) : Set ℕ)
      (ndA5OddBand B branch) := by
  intro i _hi j _hj hij
  apply Finset.disjoint_left.mpr
  intro N hNi hNj
  have hi := mem_ndA5OddBand.mp hNi
  have hj := mem_ndA5OddBand.mp hNj
  have hmono := monotone_ndA5BandLower hB branch
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hstep : i + 1 ≤ j := by omega
    have := (hmono hstep).trans hj.1
    exact (not_lt_of_ge this) hi.2.1
  · have hstep : j + 1 ≤ i := by omega
    have := (hmono hstep).trans hi.1
    exact (not_lt_of_ge this) hj.2.1

/-- Source-facing name for the possible odd natural at `sourceY^alpha`. -/
noncomputable def ndA5OddTopEndpoint
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) : Finset ℕ :=
  oddRealEndpoint
    (Real.rpow (Tao.taoSection5SourceY B branch) alpha)

/-- Exact logarithmic mass of the source-facing top component. -/
theorem logFinsetMass_ndA5OddTopEndpoint
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch) :
    Tao.logFinsetMass (ndA5OddTopEndpoint B branch) =
      ((ndA5OddTopEndpoint B branch).card : ℝ) /
        Real.rpow (Tao.taoSection5SourceY B branch) alpha := by
  unfold ndA5OddTopEndpoint
  exact logFinsetMass_oddRealEndpoint _

/-- The A5 half-open union is disjoint from the possible terminal endpoint. -/
theorem ndA5Bands_disjoint_oddRealEndpoint
    {B : ℕ} (hB : 1 ≤ B) {branch : Tao.TaoSection5SourceBranch}
    (hcount : 0 < ndA5BandCount B branch) :
    Disjoint
      ((Finset.range (ndA5BandCount B branch)).biUnion
        (ndA5OddBand B branch))
      (ndA5OddTopEndpoint B branch) := by
  unfold ndA5OddTopEndpoint
  rw [biUnion_range_ndA5OddBand_eq_source_rpow hB hcount]
  exact oddHalfOpenRealWindow_disjoint_oddRealEndpoint

private theorem one_le_taoSection5SourceY
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch) :
    (1 : ℝ) ≤ Tao.taoSection5SourceY B branch := by
  have hBreal : (1 : ℝ) ≤ B := by exact_mod_cast hB
  rw [Tao.taoSection5SourceY_eq_branch_rpow]
  exact hBreal.trans (Real.self_le_rpow_of_one_le hBreal (by
    cases branch <;>
      norm_num [Tao.taoSection5BranchExponent, Tao.taoAlpha]))

/-- Endpoint-honest exact partition of the checked inclusive ND source block. -/
theorem oddBlock_sourceY_eq_biUnion_ndA5OddBand_union_endpoint
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) :
    oddBlock (Tao.taoSection5SourceY B branch) =
      (Finset.range (ndA5BandCount B branch)).biUnion
          (ndA5OddBand B branch) ∪
        ndA5OddTopEndpoint B branch := by
  unfold ndA5OddTopEndpoint
  rw [oddBlock_eq_halfOpen_union_endpoint
      (one_le_taoSection5SourceY hB branch),
    ← biUnion_range_ndA5OddBand_eq_source_rpow hB hcount]

/-- Exact natural-count decomposition of the inclusive ND source block. -/
theorem card_oddBlock_sourceY_eq_sum_ndA5OddBand_add_endpoint
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) :
    (oddBlock (Tao.taoSection5SourceY B branch)).card =
      (∑ j ∈ Finset.range (ndA5BandCount B branch),
        (ndA5OddBand B branch j).card) +
      (ndA5OddTopEndpoint B branch).card := by
  rw [oddBlock_sourceY_eq_biUnion_ndA5OddBand_union_endpoint
      hB branch hcount,
    Finset.card_union_of_disjoint
      (ndA5Bands_disjoint_oddRealEndpoint hB hcount),
    Finset.card_biUnion (ndA5OddBand_pairwiseDisjoint hB branch
      (ndA5BandCount B branch))]

/-- Exact logarithmic-mass decomposition of the inclusive ND source block. -/
theorem logFinsetMass_oddBlock_sourceY_eq_sum_ndA5OddBand_add_endpoint
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) :
    Tao.logFinsetMass (oddBlock (Tao.taoSection5SourceY B branch)) =
      (∑ j ∈ Finset.range (ndA5BandCount B branch),
        Tao.logFinsetMass (ndA5OddBand B branch j)) +
      Tao.logFinsetMass (ndA5OddTopEndpoint B branch) := by
  rw [oddBlock_sourceY_eq_biUnion_ndA5OddBand_union_endpoint
      hB branch hcount]
  unfold Tao.logFinsetMass
  rw [Finset.sum_union (ndA5Bands_disjoint_oddRealEndpoint hB hcount),
    Finset.sum_biUnion (ndA5OddBand_pairwiseDisjoint hB branch
      (ndA5BandCount B branch))]

end

end ND
end Erdos1135
