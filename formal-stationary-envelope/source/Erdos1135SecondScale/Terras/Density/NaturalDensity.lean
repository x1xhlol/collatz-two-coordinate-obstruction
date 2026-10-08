/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Topology.Order.Basic

/-!
# Natural Density For Terras/Everett

This module defines the project-local natural-density predicate used by the Terras/Everett route
and proves the first residue-class density theorem.
-/

namespace Erdos1135SecondScale
namespace Terras

open Filter
open scoped Topology

theorem nat_count_eq_count_classical (p : ℕ → Prop) [DecidablePred p] (N : ℕ) :
    @Nat.count p (fun n => Classical.propDecidable (p n)) N = Nat.count p N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.count_succ, Nat.count_succ, ih]
      by_cases h : p N <;> simp [h]

noncomputable def natCount (s : Set ℕ) (N : ℕ) : ℕ :=
  @Nat.count (fun n => n ∈ s) (fun n => Classical.propDecidable (n ∈ s)) N

noncomputable def natCountingRatio (s : Set ℕ) (N : ℕ) : ℝ :=
  (natCount s N : ℝ) / (N : ℝ)

def HasNatDensity (s : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => natCountingRatio s N) atTop (nhds d)

theorem natCount_eq_count (s : Set ℕ) (N : ℕ) [DecidablePred (fun n => n ∈ s)] :
    natCount s N = N.count (fun n => n ∈ s) := by
  exact nat_count_eq_count_classical (fun n => n ∈ s) N

theorem natCount_modEq {m : ℕ} (hm : 0 < m) (r N : ℕ) :
    natCount {n : ℕ | n ≡ r [MOD m]} N =
      N / m + if r % m < N % m then 1 else 0 := by
  rw [natCount_eq_count]
  exact Nat.count_modEq_card N hm r

theorem tendsto_nat_div_const_ratio {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ((N / m : ℕ) : ℝ) / (N : ℝ)) atTop
      (nhds (1 / (m : ℝ))) := by
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have harg : Tendsto (fun N : ℕ => (N : ℝ) / (m : ℝ)) atTop atTop := by
    exact Filter.Tendsto.atTop_div_const hm_real_pos tendsto_natCast_atTop_atTop
  have hfloor :
      Tendsto (fun N : ℕ => ((N / m : ℕ) : ℝ) / ((N : ℝ) / (m : ℝ))) atTop
        (nhds (1 : ℝ)) := by
    convert (tendsto_nat_floor_div_atTop (R := ℝ)).comp harg using 1
    ext N
    simp [Nat.floor_div_eq_div]
  have hprod :
      Tendsto (fun N : ℕ => (m : ℝ) * (((N / m : ℕ) : ℝ) / (N : ℝ))) atTop
        (nhds (1 : ℝ)) := by
    refine hfloor.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp [hNreal, hm_real_pos.ne']
  have hscaled :
      Tendsto
        (fun N : ℕ =>
          (1 / (m : ℝ)) * ((m : ℝ) * (((N / m : ℕ) : ℝ) / (N : ℝ))))
        atTop (nhds ((1 / (m : ℝ)) * 1)) := hprod.const_mul (1 / (m : ℝ))
  have hscaled' :
      Tendsto
        (fun N : ℕ =>
          (1 / (m : ℝ)) * ((m : ℝ) * (((N / m : ℕ) : ℝ) / (N : ℝ))))
        atTop (nhds (1 / (m : ℝ))) := by
    simpa [hm_real_pos.ne'] using hscaled
  refine hscaled'.congr' ?_
  filter_upwards with N
  field_simp [hm_real_pos.ne']

theorem tendsto_modEq_error {m r : ℕ} :
    Tendsto
      (fun N : ℕ => (((if r % m < N % m then 1 else 0 : ℕ) : ℝ) / (N : ℝ)))
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have herr_le_one : (((if r % m < N % m then 1 else 0 : ℕ) : ℝ) : ℝ) ≤ 1 := by
      split <;> norm_num
    exact div_le_div₀ (by norm_num) herr_le_one hNpos le_rfl

theorem hasNatDensity_modEq {m : ℕ} (hm : 0 < m) (r : ℕ) :
    HasNatDensity {n : ℕ | n ≡ r [MOD m]} (1 / (m : ℝ)) := by
  unfold HasNatDensity natCountingRatio
  have hbase := tendsto_nat_div_const_ratio hm
  have herr := tendsto_modEq_error (m := m) (r := r)
  have hsum :
      Tendsto
        (fun N : ℕ =>
          ((N / m : ℕ) : ℝ) / (N : ℝ) +
            (((if r % m < N % m then 1 else 0 : ℕ) : ℝ) / (N : ℝ)))
        atTop (nhds (1 / (m : ℝ) + 0)) := hbase.add herr
  have hsum' :
      Tendsto
        (fun N : ℕ =>
          ((N / m : ℕ) : ℝ) / (N : ℝ) +
            (((if r % m < N % m then 1 else 0 : ℕ) : ℝ) / (N : ℝ)))
        atTop (nhds (1 / (m : ℝ))) := by
    simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards with N
  rw [natCount_modEq hm]
  rw [Nat.cast_add]
  ring

noncomputable def finsetSetUnion {ι : Type*} (I : Finset ι) (A : ι → Set ℕ) : Set ℕ :=
  {n | ∃ i, i ∈ I ∧ n ∈ A i}

theorem finsetSetUnion_empty {ι : Type*} (A : ι → Set ℕ) :
    finsetSetUnion (∅ : Finset ι) A = ∅ := by
  ext n
  simp [finsetSetUnion]

theorem finsetSetUnion_insert {ι : Type*} [DecidableEq ι] {I : Finset ι} {a : ι}
    (ha : a ∉ I) (A : ι → Set ℕ) :
    finsetSetUnion (insert a I) A = A a ∪ finsetSetUnion I A := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨i, hi, hAi⟩
    rw [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · exact Or.inl hAi
    · exact Or.inr ⟨i, hi, hAi⟩
  · intro hn
    rcases hn with hA | hU
    · exact ⟨a, by simp, hA⟩
    · rcases hU with ⟨i, hi, hAi⟩
      exact ⟨i, by simp [hi], hAi⟩

theorem hasNatDensity_empty : HasNatDensity (∅ : Set ℕ) 0 := by
  simp [HasNatDensity, natCountingRatio, natCount]

theorem natCount_union_of_disjoint {s t : Set ℕ} (hdisj : Disjoint s t) (N : ℕ) :
    natCount (s ∪ t) N = natCount s N + natCount t N := by
  induction N with
  | zero => simp [natCount]
  | succ N ih =>
      unfold natCount at ih ⊢
      repeat rw [Nat.count_succ]
      rw [ih]
      have hnot : ¬(N ∈ s ∧ N ∈ t) := by
        intro h
        exact Set.disjoint_left.mp hdisj h.1 h.2
      by_cases hs : N ∈ s <;> by_cases ht : N ∈ t
      · exact (hnot ⟨hs, ht⟩).elim
      · simp [hs, ht]
        omega
      · simp [hs, ht]
        omega
      · simp [hs, ht]

theorem HasNatDensity.union_of_disjoint {s t : Set ℕ} {a b : ℝ}
    (hs : HasNatDensity s a) (ht : HasNatDensity t b) (hdisj : Disjoint s t) :
    HasNatDensity (s ∪ t) (a + b) := by
  unfold HasNatDensity natCountingRatio at hs ht ⊢
  have hsum := hs.add ht
  refine hsum.congr' ?_
  filter_upwards with N
  rw [natCount_union_of_disjoint hdisj]
  rw [Nat.cast_add]
  ring

theorem HasNatDensity.finsetSetUnion_of_pairwise_disjoint {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Set ℕ) (d : ι → ℝ)
    (hdens : ∀ i ∈ I, HasNatDensity (A i) (d i))
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j)) :
    HasNatDensity (finsetSetUnion I A) (∑ i ∈ I, d i) := by
  induction I using Finset.induction_on with
  | empty =>
      simpa [finsetSetUnion_empty] using hasNatDensity_empty
  | insert a I ha ih =>
      have hdens_tail : ∀ i ∈ I, HasNatDensity (A i) (d i) := by
        intro i hi
        exact hdens i (by simp [hi])
      have hdisj_tail : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j) := by
        intro i hi j hj hij
        exact hdisj i (by simp [hi]) j (by simp [hj]) hij
      have htail := ih hdens_tail hdisj_tail
      have hhead : HasNatDensity (A a) (d a) := hdens a (by simp)
      have hhead_tail_disj : Disjoint (A a) (finsetSetUnion I A) := by
        rw [Set.disjoint_left]
        intro n hA hU
        rcases hU with ⟨j, hj, hAj⟩
        have haj : a ≠ j := by
          intro heq
          exact ha (heq ▸ hj)
        exact Set.disjoint_left.mp (hdisj a (by simp) j (by simp [hj]) haj) hA hAj
      have hunion := hhead.union_of_disjoint htail hhead_tail_disj
      rw [finsetSetUnion_insert ha]
      simpa [Finset.sum_insert ha] using hunion

theorem natCount_mono {s t : Set ℕ} (hsub : s ⊆ t) (N : ℕ) :
    natCount s N ≤ natCount t N := by
  unfold natCount
  exact @Nat.count_mono_left (fun n => n ∈ s) (fun n => Classical.propDecidable (n ∈ s))
    (fun n => n ∈ t) (fun n => Classical.propDecidable (n ∈ t)) N
    (fun _k _hk hks => hsub hks)

theorem natCount_le (s : Set ℕ) (N : ℕ) : natCount s N ≤ N := by
  unfold natCount
  exact @Nat.count_le (fun n => n ∈ s) (fun n => Classical.propDecidable (n ∈ s)) N

theorem natCountingRatio_mono_eventually {s t : Set ℕ} (hsub : s ⊆ t) :
    ∀ᶠ N in atTop, natCountingRatio s N ≤ natCountingRatio t N := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hcount : (natCount s N : ℝ) ≤ (natCount t N : ℝ) := by
    exact_mod_cast natCount_mono hsub N
  have hN_nonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  exact div_le_div_of_nonneg_right hcount hN_nonneg

theorem natCountingRatio_le_one_eventually (s : Set ℕ) :
    ∀ᶠ N in atTop, natCountingRatio s N ≤ 1 := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hcount : (natCount s N : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast natCount_le s N
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hratio :
      (natCount s N : ℝ) / (N : ℝ) ≤ (N : ℝ) / (N : ℝ) :=
    div_le_div_of_nonneg_right hcount hN_pos.le
  simpa [natCountingRatio, hN_pos.ne'] using hratio

theorem HasNatDensity.of_superset_of_tendsto_one {A : ℕ → Set ℕ} {S : Set ℕ} {d : ℕ → ℝ}
    (hsub : ∀ k, A k ⊆ S)
    (hA : ∀ k, HasNatDensity (A k) (d k))
    (hd : Tendsto d atTop (nhds 1)) :
    HasNatDensity S 1 := by
  unfold HasNatDensity
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    rcases ((tendsto_order.1 hd).1 b hb).exists with ⟨k, hk⟩
    have hlower : ∀ᶠ N in atTop, b < natCountingRatio (A k) N :=
      (tendsto_order.1 (hA k)).1 b hk
    have hmono : ∀ᶠ N in atTop, natCountingRatio (A k) N ≤ natCountingRatio S N :=
      natCountingRatio_mono_eventually (hsub k)
    filter_upwards [hlower, hmono] with N hlow hle
    exact lt_of_lt_of_le hlow hle
  · intro b hb
    filter_upwards [natCountingRatio_le_one_eventually S] with N hle
    exact lt_of_le_of_lt hle hb

theorem nat_count_lt_le (B N : ℕ) : Nat.count (fun n => n < B) N ≤ B := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.count_succ]
      by_cases h : N < B
      · have hcount_le : Nat.count (fun n => n < B) N ≤ N := Nat.count_le (fun n => n < B)
        simp [h]
        omega
      · simp [h]
        exact ih

theorem natCount_Iio_le (B N : ℕ) : natCount {n : ℕ | n < B} N ≤ B := by
  rw [natCount_eq_count]
  exact nat_count_lt_le B N

theorem natCount_le_of_subset_Iio {s : Set ℕ} {B : ℕ}
    (hsub : s ⊆ {n : ℕ | n < B}) (N : ℕ) :
    natCount s N ≤ B :=
  (natCount_mono hsub N).trans (natCount_Iio_le B N)

theorem hasNatDensity_zero_of_subset_Iio {s : Set ℕ} {B : ℕ}
    (hsub : s ⊆ {n : ℕ | n < B}) :
    HasNatDensity s 0 := by
  unfold HasNatDensity natCountingRatio
  refine squeeze_zero' ?_ ?_ (tendsto_const_div_atTop_nhds_zero_nat (B : ℝ))
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hnum : (natCount s N : ℝ) ≤ (B : ℝ) := by
      exact_mod_cast natCount_le_of_subset_Iio hsub N
    exact div_le_div₀ (by positivity) hnum hNpos le_rfl

theorem HasNatDensity.inter_Ici {s : Set ℕ} {d : ℝ} (hs : HasNatDensity s d) (B : ℕ) :
    HasNatDensity {n : ℕ | n ∈ s ∧ B ≤ n} d := by
  let low : Set ℕ := {n | n ∈ s ∧ n < B}
  let high : Set ℕ := {n | n ∈ s ∧ B ≤ n}
  have hlow_density : HasNatDensity low 0 := by
    apply hasNatDensity_zero_of_subset_Iio (B := B)
    intro _n hn
    exact hn.2
  have hcount : ∀ N, natCount s N = natCount low N + natCount high N := by
    intro N
    have hcover : s = low ∪ high := by
      ext n
      constructor
      · intro hs_mem
        by_cases hn : n < B
        · exact Or.inl ⟨hs_mem, hn⟩
        · exact Or.inr ⟨hs_mem, le_of_not_gt hn⟩
      · intro h
        rcases h with hlow | hhigh
        · exact hlow.1
        · exact hhigh.1
    have hdisj : Disjoint low high := by
      rw [Set.disjoint_left]
      intro _n hlow hhigh
      exact (not_lt_of_ge hhigh.2) hlow.2
    rw [hcover]
    exact natCount_union_of_disjoint hdisj N
  unfold HasNatDensity natCountingRatio at hs hlow_density ⊢
  have hdiff := hs.sub hlow_density
  have hdiff' :
      Tendsto
        (fun N : ℕ => (natCount s N : ℝ) / (N : ℝ) - (natCount low N : ℝ) / (N : ℝ))
        atTop (nhds d) := by
    simpa using hdiff
  refine hdiff'.congr' ?_
  filter_upwards with N
  have hc : (natCount s N : ℝ) = (natCount low N : ℝ) + (natCount high N : ℝ) := by
    exact_mod_cast hcount N
  change (natCount s N : ℝ) / (N : ℝ) - (natCount low N : ℝ) / (N : ℝ) =
    (natCount high N : ℝ) / (N : ℝ)
  rw [hc]
  ring

noncomputable def residueSet (m : ℕ) (R : Finset (ZMod m)) : Set ℕ :=
  {n | (n : ZMod m) ∈ R}

theorem modEqResidueClass_disjoint_of_ne {m : ℕ} (hm : 0 < m) {a b : ZMod m}
    (hab : a ≠ b) :
    Disjoint {n : ℕ | n ≡ a.val [MOD m]} {n : ℕ | n ≡ b.val [MOD m]} := by
  rw [Set.disjoint_left]
  intro n ha hb
  haveI : NeZero m := ⟨hm.ne'⟩
  have hna : (n : ZMod m) = (a.val : ZMod m) :=
    (ZMod.natCast_eq_natCast_iff n a.val m).2 ha
  have hnb : (n : ZMod m) = (b.val : ZMod m) :=
    (ZMod.natCast_eq_natCast_iff n b.val m).2 hb
  have hab_eq : a = b := by
    rw [ZMod.natCast_zmod_val a] at hna
    rw [ZMod.natCast_zmod_val b] at hnb
    exact hna.symm.trans hnb
  exact hab hab_eq

theorem residueSet_eq_finsetSetUnion_val_modEq {m : ℕ} (hm : 0 < m)
    (R : Finset (ZMod m)) :
    residueSet m R = finsetSetUnion R (fun z : ZMod m => {n : ℕ | n ≡ z.val [MOD m]}) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  ext n
  constructor
  · intro hn
    refine ⟨(n : ZMod m), hn, ?_⟩
    change n ≡ (n : ZMod m).val [MOD m]
    rw [← ZMod.natCast_eq_natCast_iff]
    exact (ZMod.natCast_zmod_val (n : ZMod m)).symm
  · intro hn
    rcases hn with ⟨z, hz, hmod⟩
    change (n : ZMod m) ∈ R
    have hcast : (n : ZMod m) = (z.val : ZMod m) :=
      (ZMod.natCast_eq_natCast_iff n z.val m).2 hmod
    rw [ZMod.natCast_zmod_val z] at hcast
    exact hcast.symm ▸ hz

theorem hasNatDensity_residueSet {m : ℕ} (hm : 0 < m) (R : Finset (ZMod m)) :
    HasNatDensity (residueSet m R) ((R.card : ℝ) / (m : ℝ)) := by
  have hfinite := HasNatDensity.finsetSetUnion_of_pairwise_disjoint R
    (fun z : ZMod m => {n : ℕ | n ≡ z.val [MOD m]})
    (fun _ : ZMod m => (1 : ℝ) / (m : ℝ))
    (by
      intro z _hz
      exact hasNatDensity_modEq hm z.val)
    (by
      intro _a _ha _b _hb hab
      exact modEqResidueClass_disjoint_of_ne hm hab)
  have hsum : (∑ z ∈ R, (1 : ℝ) / (m : ℝ)) = (R.card : ℝ) / (m : ℝ) := by
    simp [div_eq_mul_inv]
  rw [residueSet_eq_finsetSetUnion_val_modEq hm]
  simpa [hsum] using hfinite

theorem hasNatDensity_residueSet_Ici {m : ℕ} (hm : 0 < m) (R : Finset (ZMod m)) (B : ℕ) :
    HasNatDensity {n : ℕ | n ∈ residueSet m R ∧ B ≤ n} ((R.card : ℝ) / (m : ℝ)) :=
  (hasNatDensity_residueSet hm R).inter_Ici B

theorem hasNatDensity_residueSet_ge {m : ℕ} (hm : 0 < m) (R : Finset (ZMod m)) (B : ℕ) :
    HasNatDensity {n : ℕ | B ≤ n ∧ (n : ZMod m) ∈ R} ((R.card : ℝ) / (m : ℝ)) := by
  simpa [residueSet, and_comm, and_left_comm, and_assoc] using
    hasNatDensity_residueSet_Ici hm R B

end Terras
end Erdos1135SecondScale
