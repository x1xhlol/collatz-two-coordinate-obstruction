import Erdos1135.Tao.Density.LogDensity
import Mathlib.Tactic

/-!
# Finite Log-Count Algebra

This module contains finite algebraic adapters for `logCount`.  These lemmas
are intentionally independent of Syracuse and of Tao's logarithmic windows.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

theorem logCount_eq_of_subset_Iic_of_le {s : Set ℕ} {X N : ℕ}
    (hsub : s ⊆ Set.Iic X) (hXN : X ≤ N) :
    logCount s N = logCount s X := by
  classical
  unfold logCount
  symm
  refine Finset.sum_subset ?hsubset ?hzero
  · intro i hi
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hXN)
  · intro i _hiN hiNotX
    have hXi : X ≤ i := le_of_not_gt fun hiX => hiNotX (Finset.mem_range.mpr hiX)
    have hnot : i + 1 ∉ s := by
      intro hs
      have hleX : i + 1 ≤ X := hsub hs
      omega
    simp [hnot]

theorem logCount_inter_lower_bound_lift_of_subset_Iic
    {W LocalGood : Set ℕ} {H X : ℕ} {κ : ℝ}
    (hW : W ⊆ Set.Iic H) (hHX : H ≤ X)
    (hlower : κ * logCount W H ≤ logCount (W ∩ LocalGood) H) :
    κ * logCount W X ≤ logCount (W ∩ LocalGood) X := by
  rw [logCount_eq_of_subset_Iic_of_le hW hHX,
    logCount_eq_of_subset_Iic_of_le (Set.Subset.trans Set.inter_subset_left hW) hHX]
  exact hlower

theorem logCount_inter_le_mul_of_ratio_le {bad window : Set ℕ} {η : ℝ} {N : ℕ}
    (hratio : logCount (bad ∩ window) N / logCount window N ≤ η) :
    logCount (bad ∩ window) N ≤ η * logCount window N := by
  by_cases hpos : 0 < logCount window N
  · exact (div_le_iff₀ hpos).mp hratio
  · have hwin_nonneg : 0 ≤ logCount window N := logCount_nonneg window N
    have hwin_eq : logCount window N = 0 :=
      le_antisymm (le_of_not_gt hpos) hwin_nonneg
    have hinter_le : logCount (bad ∩ window) N ≤ logCount window N :=
      logCount_mono Set.inter_subset_right N
    have hinter_eq : logCount (bad ∩ window) N = 0 := by
      exact le_antisymm (by simpa [hwin_eq] using hinter_le)
        (logCount_nonneg (bad ∩ window) N)
    simp [hwin_eq, hinter_eq]

theorem logCount_window_diff_ge_of_bad_inter_le {bad window : Set ℕ} {η : ℝ} {N : ℕ}
    (hbad : logCount (bad ∩ window) N ≤ η * logCount window N) :
    (1 - η) * logCount window N ≤ logCount (window \ bad) N := by
  have hsub : bad ∩ window ⊆ window := by
    intro n hn
    exact hn.2
  have hdiff_set : window \ (bad ∩ window) = window \ bad := by
    ext n
    constructor
    · intro hn
      exact ⟨hn.1, fun hbadn => hn.2 ⟨hbadn, hn.1⟩⟩
    · intro hn
      exact ⟨hn.1, fun hbadwin => hn.2 hbadwin.1⟩
  have hcount :
      logCount (window \ bad) N = logCount window N - logCount (bad ∩ window) N := by
    simpa [hdiff_set] using logCount_diff_of_subset hsub N
  calc
    (1 - η) * logCount window N =
        logCount window N - η * logCount window N := by ring
    _ ≤ logCount window N - logCount (bad ∩ window) N := by
        exact sub_le_sub_left hbad (logCount window N)
    _ = logCount (window \ bad) N := hcount.symm

theorem logCount_biUnion_of_pairwise_disjoint {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Set ℕ)
    (hdisj : ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j → Disjoint (A i) (A j))
    (N : ℕ) :
    logCount (⋃ i ∈ I, A i) N = ∑ i ∈ I, logCount (A i) N := by
  classical
  revert hdisj
  refine Finset.induction_on I ?base ?step
  · intro _hdisj
    simp
  · intro a I ha ih hdisj
    have hrest_disj :
        ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j → Disjoint (A i) (A j) := by
      intro i hi j hj hij
      exact hdisj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
    have ha_disj : Disjoint (A a) (⋃ i ∈ I, A i) := by
      rw [Set.disjoint_left]
      intro n hna hnrest
      rcases Set.mem_iUnion.mp hnrest with ⟨i, hiUnion⟩
      rcases Set.mem_iUnion.mp hiUnion with ⟨hiI, hnAi⟩
      have hne : a ≠ i := by
        intro h
        subst i
        exact ha hiI
      exact (Set.disjoint_left.mp
        (hdisj (Finset.mem_insert_self a I) (Finset.mem_insert_of_mem hiI) hne) hna) hnAi
    have hunion : (⋃ i ∈ insert a I, A i) = A a ∪ ⋃ i ∈ I, A i := by
      ext n
      constructor
      · intro hn
        rcases Set.mem_iUnion.mp hn with ⟨i, hiUnion⟩
        rcases Set.mem_iUnion.mp hiUnion with ⟨hiIns, hnAi⟩
        rcases Finset.mem_insert.mp hiIns with rfl | hiI
        · exact Or.inl hnAi
        · exact Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hiI, hnAi⟩⟩)
      · intro hn
        rcases hn with hna | hnrest
        · exact Set.mem_iUnion.mpr
            ⟨a, Set.mem_iUnion.mpr ⟨Finset.mem_insert_self a I, hna⟩⟩
        · rcases Set.mem_iUnion.mp hnrest with ⟨i, hiUnion⟩
          rcases Set.mem_iUnion.mp hiUnion with ⟨hiI, hnAi⟩
          exact Set.mem_iUnion.mpr
            ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hiI, hnAi⟩⟩
    rw [hunion, logCount_union_of_disjoint ha_disj N, ih hrest_disj, Finset.sum_insert ha]

theorem logCountingRatio_ge_of_logCount_ge_mul_logMass {s : Set ℕ} {c : ℝ} {N : ℕ}
    (hN : 0 < N) (h : c * logMass N ≤ logCount s N) :
    c ≤ logCountingRatio s N := by
  rw [logCountingRatio]
  exact (le_div_iff₀ (logMass_pos hN)).mpr h

theorem logCountingRatio_ge_of_window_inter_lower_bounds
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (W : ι → Set ℕ) (LocalGood : ι → Set ℕ)
    (Good : Set ℕ) (X : ℕ) (κ ρ c : ℝ)
    (hX : 0 < X)
    (hκ : 0 ≤ κ)
    (hpairW : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (W i) (W j))
    (hlocal : ∀ i ∈ I, W i ∩ LocalGood i ⊆ Good)
    (hlower : ∀ i ∈ I,
      κ * logCount (W i) X ≤ logCount (W i ∩ LocalGood i) X)
    (hcover : ρ * logMass X ≤ ∑ i ∈ I, logCount (W i) X)
    (hc : c ≤ κ * ρ) :
    c ≤ logCountingRatio Good X := by
  classical
  have hpairLocal :
      ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j →
        Disjoint (W i ∩ LocalGood i) (W j ∩ LocalGood j) := by
    intro i hi j hj hij
    rw [Set.disjoint_left]
    intro n hni hnj
    exact (Set.disjoint_left.mp (hpairW i hi j hj hij)) hni.1 hnj.1
  have hsubset : (⋃ i ∈ I, W i ∩ LocalGood i) ⊆ Good := by
    intro n hn
    rcases Set.mem_iUnion.mp hn with ⟨i, hiUnion⟩
    rcases Set.mem_iUnion.mp hiUnion with ⟨hiI, hnLocal⟩
    exact hlocal i hiI hnLocal
  have hsumLocal :
      κ * (∑ i ∈ I, logCount (W i) X) ≤
        ∑ i ∈ I, logCount (W i ∩ LocalGood i) X := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hlower i hi
  have hGoodLower :
      κ * (∑ i ∈ I, logCount (W i) X) ≤ logCount Good X := by
    calc
      κ * (∑ i ∈ I, logCount (W i) X) ≤
          ∑ i ∈ I, logCount (W i ∩ LocalGood i) X := hsumLocal
      _ = logCount (⋃ i ∈ I, W i ∩ LocalGood i) X := by
          exact (logCount_biUnion_of_pairwise_disjoint I
            (fun i => W i ∩ LocalGood i) hpairLocal X).symm
      _ ≤ logCount Good X := logCount_mono hsubset X
  have hcoverScaled :
      κ * (ρ * logMass X) ≤ κ * (∑ i ∈ I, logCount (W i) X) :=
    mul_le_mul_of_nonneg_left hcover hκ
  have hcScaled : c * logMass X ≤ (κ * ρ) * logMass X :=
    mul_le_mul_of_nonneg_right hc (le_of_lt (logMass_pos hX))
  have hlowerTotal : c * logMass X ≤ logCount Good X := by
    calc
      c * logMass X ≤ (κ * ρ) * logMass X := hcScaled
      _ = κ * (ρ * logMass X) := by ring
      _ ≤ κ * (∑ i ∈ I, logCount (W i) X) := hcoverScaled
      _ ≤ logCount Good X := hGoodLower
  exact logCountingRatio_ge_of_logCount_ge_mul_logMass hX hlowerTotal

theorem logCountingRatio_ge_of_endpoint_window_inter_lower_bounds
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (W : ι → Set ℕ) (hi : ι → ℕ)
    (LocalGood : ι → Set ℕ) (Good : Set ℕ) (X : ℕ) (κ ρ c : ℝ)
    (hX : 0 < X)
    (hκ : 0 ≤ κ)
    (hsupport : ∀ i ∈ I, W i ⊆ Set.Iic (hi i))
    (hhiX : ∀ i ∈ I, hi i ≤ X)
    (hpairW : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (W i) (W j))
    (hlocal : ∀ i ∈ I, W i ∩ LocalGood i ⊆ Good)
    (hlower_endpoint : ∀ i ∈ I,
      κ * logCount (W i) (hi i) ≤ logCount (W i ∩ LocalGood i) (hi i))
    (hcover : ρ * logMass X ≤ ∑ i ∈ I, logCount (W i) X)
    (hc : c ≤ κ * ρ) :
    c ≤ logCountingRatio Good X := by
  exact logCountingRatio_ge_of_window_inter_lower_bounds
    I W LocalGood Good X κ ρ c hX hκ hpairW hlocal
    (fun i hiI =>
      logCount_inter_lower_bound_lift_of_subset_Iic
        (hsupport i hiI) (hhiX i hiI) (hlower_endpoint i hiI))
    hcover hc

theorem logCount_good_ge_window_sum_of_bad_inter_le {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (W : ι → Set ℕ) (Bad Good : Set ℕ) (N : ℕ) (δ : ℝ)
    (hpairW : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (W i) (W j))
    (hgood : ∀ i ∈ I, W i \ Bad ⊆ Good)
    (hbad : ∀ i ∈ I, logCount (W i ∩ Bad) N ≤ δ * logCount (W i) N) :
    (1 - δ) * (∑ i ∈ I, logCount (W i) N) ≤ logCount Good N := by
  classical
  have hsum :
      (1 - δ) * (∑ i ∈ I, logCount (W i) N) ≤
        ∑ i ∈ I, logCount (W i \ Bad) N := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => by
      exact logCount_window_diff_ge_of_bad_inter_le
        (bad := Bad) (window := W i) (η := δ) (N := N) (by
          simpa [Set.inter_comm] using hbad i hi)
  have hpairDiff :
      ∀ ⦃i⦄, i ∈ I → ∀ ⦃j⦄, j ∈ I → i ≠ j →
        Disjoint (W i \ Bad) (W j \ Bad) := by
    intro i hi j hj hij
    rw [Set.disjoint_left]
    intro n hni hnj
    exact (Set.disjoint_left.mp (hpairW i hi j hj hij)) hni.1 hnj.1
  have hsubset : (⋃ i ∈ I, W i \ Bad) ⊆ Good := by
    intro n hn
    rcases Set.mem_iUnion.mp hn with ⟨i, hiUnion⟩
    rcases Set.mem_iUnion.mp hiUnion with ⟨hiI, hnWi⟩
    exact hgood i hiI hnWi
  calc
    (1 - δ) * (∑ i ∈ I, logCount (W i) N) ≤
        ∑ i ∈ I, logCount (W i \ Bad) N := hsum
    _ = logCount (⋃ i ∈ I, W i \ Bad) N := by
        exact (logCount_biUnion_of_pairwise_disjoint I (fun i => W i \ Bad) hpairDiff N).symm
    _ ≤ logCount Good N := logCount_mono hsubset N

theorem logCountingRatio_good_ge_of_window_cover {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (W : ι → Set ℕ) (Bad Good : Set ℕ) (N : ℕ)
    (δ ρ c : ℝ)
    (hN : 0 < N)
    (hδ : 0 ≤ 1 - δ)
    (hpairW : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (W i) (W j))
    (hgood : ∀ i ∈ I, W i \ Bad ⊆ Good)
    (hbad : ∀ i ∈ I, logCount (W i ∩ Bad) N ≤ δ * logCount (W i) N)
    (hcover : ρ * logMass N ≤ ∑ i ∈ I, logCount (W i) N)
    (hc : c ≤ (1 - δ) * ρ) :
    c ≤ logCountingRatio Good N := by
  have hwindow := logCount_good_ge_window_sum_of_bad_inter_le
    I W Bad Good N δ hpairW hgood hbad
  have hcoverScaled :
      (1 - δ) * (ρ * logMass N) ≤
        (1 - δ) * (∑ i ∈ I, logCount (W i) N) :=
    mul_le_mul_of_nonneg_left hcover hδ
  have hcScaled :
      c * logMass N ≤ ((1 - δ) * ρ) * logMass N :=
    mul_le_mul_of_nonneg_right hc (le_of_lt (logMass_pos hN))
  have hlower : c * logMass N ≤ logCount Good N := by
    calc
      c * logMass N ≤ ((1 - δ) * ρ) * logMass N := hcScaled
      _ = (1 - δ) * (ρ * logMass N) := by ring
      _ ≤ (1 - δ) * (∑ i ∈ I, logCount (W i) N) := hcoverScaled
      _ ≤ logCount Good N := hwindow
  exact logCountingRatio_ge_of_logCount_ge_mul_logMass hN hlower

theorem finite_telescope_lower_bound (p err : ℕ → ℝ) (baseErr : ℝ)
    (hbase : 1 - baseErr ≤ p 0)
    (hstep : ∀ j : ℕ, p j - err j ≤ p (j + 1)) :
    ∀ J : ℕ,
      1 - (baseErr + ∑ j ∈ Finset.range J, err j) ≤ p J := by
  intro J
  induction J with
  | zero =>
      simpa using hbase
  | succ J ih =>
      calc
        1 - (baseErr + ∑ j ∈ Finset.range (J + 1), err j) =
            (1 - (baseErr + ∑ j ∈ Finset.range J, err j)) - err J := by
          rw [Finset.sum_range_succ]
          ring
        _ ≤ p J - err J := sub_le_sub_right ih (err J)
        _ ≤ p (J + 1) := hstep J

/-- Finite telescope whose recurrence is required only on the consumed
prefix.  In particular, a length-`Jmax` trace does not certify the unused
step from `Jmax` to `Jmax + 1`. -/
theorem finite_telescope_lower_bound_bounded
    (p err : ℕ → ℝ) (baseErr : ℝ) (Jmax : ℕ)
    (hbase : 1 - baseErr ≤ p 0)
    (hstep : ∀ j : ℕ, j < Jmax → p j - err j ≤ p (j + 1)) :
    ∀ J : ℕ, J ≤ Jmax →
      1 - (baseErr + ∑ j ∈ Finset.range J, err j) ≤ p J := by
  intro J
  induction J with
  | zero =>
      intro _
      simpa using hbase
  | succ J ih =>
      intro hJ
      have hJlt : J < Jmax := Nat.lt_of_succ_le hJ
      calc
        1 - (baseErr + ∑ j ∈ Finset.range (J + 1), err j) =
            (1 - (baseErr + ∑ j ∈ Finset.range J, err j)) - err J := by
          rw [Finset.sum_range_succ]
          ring
        _ ≤ p J - err J := sub_le_sub_right (ih hJlt.le) (err J)
        _ ≤ p (J + 1) := hstep J hJlt

theorem finite_telescope_lower_bound_exact (p err : ℕ → ℝ) (baseErr : ℝ)
    (hbase : 1 - baseErr ≤ p 0)
    (hstep : ∀ j : ℕ, p j - err j ≤ p (j + 1)) :
    ∀ J : ℕ,
      1 - (baseErr + ∑ j ∈ Finset.range J, err j) ≤ p J :=
  finite_telescope_lower_bound p err baseErr hbase hstep

theorem finite_telescope_lower_bound_of_sum_le
    (p err : ℕ → ℝ) (baseErr budget : ℝ) (J : ℕ)
    (hbase : 1 - baseErr ≤ p 0)
    (hstep : ∀ j : ℕ, p j - err j ≤ p (j + 1))
    (hbudget : (∑ j ∈ Finset.range J, err j) ≤ budget) :
    1 - (baseErr + budget) ≤ p J := by
  have h := finite_telescope_lower_bound_exact p err baseErr hbase hstep J
  linarith

end Tao
end Erdos1135
