import Erdos1135.ND.Fourier.FixedTotalBars

/-!
# Fixed-Total Without-Replacement Concentration

This leaf begins the T3 interface with the exact integer double count behind
the factorial moments of a uniform fixed-cardinality subset.  The raw theorem
keeps all infeasible and endpoint cases visible: no probability normalization,
division, or exponential estimate is used here.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

/-- The carrier of `K`-subsets of an `N`-element population. -/
abbrev NDUniformKSubset (N K : ℕ) :=
  Set.powersetCard (Fin N) K

/-- The number of selected elements in the strict zero-based prefix
`{0, ..., q - 1}`.  When `q > N`, this is the whole selected subset. -/
def ndUniformPrefixCount {N K : ℕ}
    (S : NDUniformKSubset N K) (q : ℕ) : ℕ :=
  (S.1.filter fun i : Fin N => (i : ℕ) < q).card

private def ndPowersetCardSupersetEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Finset α) (K : ℕ) (hRK : R.card ≤ K) :
    {S : Set.powersetCard α K // R ⊆ S.1} ≃
      {T : Finset α //
        T ∈ (Finset.univ \ R).powersetCard (K - R.card)} where
  toFun S := ⟨S.1.1 \ R, by
    rw [Finset.mem_powersetCard]
    constructor
    · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (by rfl)
    · rw [Finset.card_sdiff_of_subset S.2, S.1.2]⟩
  invFun T := ⟨⟨R ∪ T.1, by
    have hT := Finset.mem_powersetCard.mp T.2
    have hdisjoint : Disjoint R T.1 :=
      ((Finset.subset_sdiff.mp hT.1).2).symm
    rw [Set.powersetCard.mem_iff]
    rw [Finset.card_union_of_disjoint hdisjoint, hT.2,
      Nat.add_sub_of_le hRK]⟩, Finset.subset_union_left⟩
  left_inv S := by
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.union_sdiff_of_subset S.2
  right_inv T := by
    have hT := Finset.mem_powersetCard.mp T.2
    have hdisjoint : Disjoint R T.1 :=
      ((Finset.subset_sdiff.mp hT.1).2).symm
    apply Subtype.ext
    exact Finset.union_sdiff_cancel_left hdisjoint

private theorem sum_indicator_powersetCard_superset
    {α : Type*} [Fintype α] [DecidableEq α]
    (R : Finset α) (K : ℕ) (hRK : R.card ≤ K) :
    (∑ S : Set.powersetCard α K, if R ⊆ S.1 then 1 else 0) =
      Nat.choose (Fintype.card α - R.card) (K - R.card) := by
  classical
  calc
    (∑ S : Set.powersetCard α K, if R ⊆ S.1 then 1 else 0) =
        Fintype.card {S : Set.powersetCard α K // R ⊆ S.1} := by
      rw [Finset.sum_boole]
      exact (Fintype.card_subtype _).symm
    _ = Fintype.card {T : Finset α //
          T ∈ (Finset.univ \ R).powersetCard (K - R.card)} :=
      Fintype.card_congr (ndPowersetCardSupersetEquiv R K hRK)
    _ = ((Finset.univ \ R).powersetCard (K - R.card)).card :=
      Fintype.card_coe _
    _ = Nat.choose (Fintype.card α - R.card) (K - R.card) := by
      rw [Finset.card_powersetCard,
        Finset.card_sdiff_of_subset (Finset.subset_univ R),
        Finset.card_univ]

private theorem choose_ndUniformPrefixCount_eq_incidence_sum
    {N K q r : ℕ} (S : NDUniformKSubset N K) :
    Nat.choose (ndUniformPrefixCount S q) r =
      ∑ R ∈
        (Finset.univ.filter fun i : Fin N => (i : ℕ) < q).powersetCard r,
        if R ⊆ S.1 then 1 else 0 := by
  classical
  let Q : Finset (Fin N) :=
    Finset.univ.filter fun i : Fin N => (i : ℕ) < q
  calc
    Nat.choose (ndUniformPrefixCount S q) r =
        ((S.1.filter fun i : Fin N => (i : ℕ) < q).powersetCard r).card := by
      rw [Finset.card_powersetCard]
      rfl
    _ = ((Q.powersetCard r).filter fun R => R ⊆ S.1).card := by
      congr 1
      ext R
      simp only [Finset.mem_powersetCard, Finset.mem_filter]
      constructor
      · rintro ⟨hR, hcard⟩
        refine ⟨⟨?_, hcard⟩, ?_⟩
        · intro i hi
          have hiFilter := hR hi
          simp only [Finset.mem_filter] at hiFilter
          simpa only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
            using hiFilter.2
        · intro i hi
          exact (Finset.mem_filter.mp (hR hi)).1
      · rintro ⟨⟨hRQ, hcard⟩, hRS⟩
        refine ⟨?_, hcard⟩
        intro i hi
        rw [Finset.mem_filter]
        refine ⟨hRS hi, ?_⟩
        have hiQ := hRQ hi
        simpa only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
          using hiQ
    _ = ∑ R ∈ Q.powersetCard r,
          if R ⊆ S.1 then 1 else 0 := by
      symm
      exact Finset.sum_boole (fun R => R ⊆ S.1) (Q.powersetCard r)
    _ = ∑ R ∈
        (Finset.univ.filter fun i : Fin N => (i : ℕ) < q).powersetCard r,
        if R ⊆ S.1 then 1 else 0 := rfl

/-- Guarded factorial-moment double count for a uniform fixed-cardinality
subset.  The guard is essential with natural truncated subtraction when
`r > K`; `min N q` is essential when the requested prefix passes the end of
the population. -/
theorem sum_choose_ndUniformPrefixCount_guarded
    (N K q r : ℕ) :
    (∑ S : NDUniformKSubset N K,
      Nat.choose (ndUniformPrefixCount S q) r) =
      if r ≤ K then
        Nat.choose (min N q) r *
          Nat.choose (N - r) (K - r)
      else 0 := by
  classical
  by_cases hrK : r ≤ K
  · rw [if_pos hrK]
    let Q : Finset (Fin N) :=
      Finset.univ.filter fun i : Fin N => (i : ℕ) < q
    have hQcard : Q.card = min N q := by
      simpa only [Q] using
        (Fin.card_filter_val_lt (n := N) (m := q))
    calc
      (∑ S : NDUniformKSubset N K,
          Nat.choose (ndUniformPrefixCount S q) r) =
          ∑ S : NDUniformKSubset N K,
            ∑ R ∈ Q.powersetCard r,
              if R ⊆ S.1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro S _hS
        exact choose_ndUniformPrefixCount_eq_incidence_sum S
      _ = ∑ R ∈ Q.powersetCard r,
            ∑ S : NDUniformKSubset N K,
              if R ⊆ S.1 then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ _R ∈ Q.powersetCard r,
            Nat.choose (N - r) (K - r) := by
        apply Finset.sum_congr rfl
        intro R hR
        have hRcard : R.card = r :=
          (Finset.mem_powersetCard.mp hR).2
        have hRleK : R.card ≤ K := by
          simpa only [hRcard] using hrK
        rw [sum_indicator_powersetCard_superset R K hRleK]
        simp only [Fintype.card_fin, hRcard]
      _ = (Q.powersetCard r).card *
            Nat.choose (N - r) (K - r) := by simp
      _ = Nat.choose Q.card r *
            Nat.choose (N - r) (K - r) := by
        rw [Finset.card_powersetCard]
      _ = Nat.choose (min N q) r *
            Nat.choose (N - r) (K - r) := by
        rw [hQcard]
  · rw [if_neg hrK]
    apply Finset.sum_eq_zero
    intro S _hS
    apply Nat.choose_eq_zero_of_lt
    calc
      ndUniformPrefixCount S q ≤ S.1.card :=
        Finset.card_filter_le _ _
      _ = K := S.2
      _ < r := Nat.lt_of_not_ge hrK

/-- The consumed form of the factorial-moment count when the prefix is inside
the population and the marked subconfiguration size is supported. -/
theorem sum_choose_ndUniformPrefixCount_of_le
    (N K q r : ℕ) (hqN : q ≤ N) (hrK : r ≤ K) :
    (∑ S : NDUniformKSubset N K,
      Nat.choose (ndUniformPrefixCount S q) r) =
      Nat.choose q r * Nat.choose (N - r) (K - r) := by
  rw [sum_choose_ndUniformPrefixCount_guarded, if_pos hrK,
    min_eq_right hqN]

/-- Cross-multiplied factorial moment, still valid for infeasible carriers and
unsupported marked-subset sizes.  Multiplication by `choose N r` removes the
truncated completion term; binomial zeros close the `r > K` branch. -/
theorem choose_mul_sum_choose_ndUniformPrefixCount
    (N K q r : ℕ) :
    Nat.choose N r *
        (∑ S : NDUniformKSubset N K,
          Nat.choose (ndUniformPrefixCount S q) r) =
      Nat.choose N K *
        Nat.choose (min N q) r * Nat.choose K r := by
  by_cases hrK : r ≤ K
  · rw [sum_choose_ndUniformPrefixCount_guarded, if_pos hrK]
    calc
      Nat.choose N r *
          (Nat.choose (min N q) r *
            Nat.choose (N - r) (K - r)) =
          Nat.choose (min N q) r *
            (Nat.choose N r *
              Nat.choose (N - r) (K - r)) := by
        ac_rfl
      _ = Nat.choose (min N q) r *
            (Nat.choose N K * Nat.choose K r) := by
        rw [← Nat.choose_mul hrK]
      _ = Nat.choose N K *
            Nat.choose (min N q) r * Nat.choose K r := by
        ac_rfl
  · rw [sum_choose_ndUniformPrefixCount_guarded, if_neg hrK,
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hrK)]
    simp

/-- Literal-prefix specialization of the cross-multiplied factorial moment.
No feasibility or marked-subset support hypothesis is needed. -/
theorem choose_mul_sum_choose_ndUniformPrefixCount_of_le
    (N K q r : ℕ) (hqN : q ≤ N) :
    Nat.choose N r *
        (∑ S : NDUniformKSubset N K,
          Nat.choose (ndUniformPrefixCount S q) r) =
      Nat.choose N K * Nat.choose q r * Nat.choose K r := by
  simpa only [min_eq_right hqN] using
    choose_mul_sum_choose_ndUniformPrefixCount N K q r

/-- Division-free factorial moment of the checked fixed-total bars PMF.  The
only cancelled factor is the nonzero cardinality of the feasible bars
carrier; the marked-subset coefficient `choose (L - 1) r` is retained. -/
theorem choose_mul_ndFixedTotalBarsPMF_expectation_choose_prefixCount
    (n L q r : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    (Nat.choose (L - 1) r : ℝ) *
        Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
          (fun B =>
            (Nat.choose (ndBarsPrefixCount B.1 q) r : ℝ)) =
      (Nat.choose (min (L - 1) q) r : ℝ) *
        (Nat.choose (n - 1) r : ℝ) := by
  classical
  have hnormalizer :
      (Nat.choose (L - 1) (n - 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (Nat.choose_ne_zero (Nat.sub_le_sub_right hL 1))
  have hcross :
      (Nat.choose (L - 1) r : ℝ) *
          (∑ B : NDFixedTotalBars n L,
            (Nat.choose (ndBarsPrefixCount B.1 q) r : ℝ)) =
        (Nat.choose (L - 1) (n - 1) : ℝ) *
          (Nat.choose (min (L - 1) q) r : ℝ) *
            (Nat.choose (n - 1) r : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_sum,
      ndUniformPrefixCount, ndBarsPrefixCount] using
      congrArg (fun z : ℕ => (z : ℝ))
        (choose_mul_sum_choose_ndUniformPrefixCount
          (L - 1) (n - 1) q r)
  unfold Tao.pmfExpectation
  simp_rw [ndFixedTotalBarsPMF_apply_toReal n L hn hL,
    one_div_mul_eq_div]
  rw [← Finset.sum_div, ← mul_div_assoc,
    div_eq_iff hnormalizer, hcross]
  ac_rfl

/-- The genuine factorial-moment coefficient ratio on the supported range.
The guard makes `choose (L - 1) r` nonzero; no support condition relative to
the selected-set size `n - 1` is needed. -/
theorem ndFixedTotalBarsPMF_expectation_choose_prefixCount_eq
    (n L q r : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (hrL : r ≤ L - 1) :
    Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
      (fun B =>
        (Nat.choose (ndBarsPrefixCount B.1 q) r : ℝ)) =
      (Nat.choose (min (L - 1) q) r : ℝ) *
        ((Nat.choose (n - 1) r : ℝ) /
          (Nat.choose (L - 1) r : ℝ)) := by
  have hden : (Nat.choose (L - 1) r : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hrL)
  rw [← mul_div_assoc, eq_div_iff hden, mul_comm]
  exact choose_mul_ndFixedTotalBarsPMF_expectation_choose_prefixCount
    n L q r hn hL

private theorem ndNat_mul_tsub_le_mul_tsub
    (N K r : ℕ) (hKN : K ≤ N) :
    N * (K - r) ≤ K * (N - r) := by
  calc
    N * (K - r) = N * K - N * r :=
      Nat.mul_sub_left_distrib N K r
    _ ≤ N * K - K * r :=
      Nat.sub_le_sub_left (Nat.mul_le_mul_right r hKN) (N * K)
    _ = K * (N - r) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_comm K N]

/-- Division-free and zero-safe comparison of the binomial coefficient
ratio with the corresponding power ratio. -/
private theorem ndNat_pow_mul_choose_le_pow_mul_choose
    (N K r : ℕ) (hKN : K ≤ N) :
    N ^ r * Nat.choose K r ≤ K ^ r * Nat.choose N r := by
  induction r with
  | zero => simp
  | succ r ih =>
      refine Nat.le_of_mul_le_mul_right ?_ (Nat.succ_pos r)
      calc
        (N ^ (r + 1) * Nat.choose K (r + 1)) * (r + 1) =
            N ^ (r + 1) *
              (Nat.choose K (r + 1) * (r + 1)) := by
                rw [mul_assoc]
        _ = N ^ (r + 1) * (Nat.choose K r * (K - r)) := by
              rw [Nat.choose_succ_right_eq]
        _ = (N * (K - r)) * (N ^ r * Nat.choose K r) := by
              rw [pow_succ]
              ac_rfl
        _ ≤ (K * (N - r)) * (K ^ r * Nat.choose N r) :=
              Nat.mul_le_mul (ndNat_mul_tsub_le_mul_tsub N K r hKN) ih
        _ = K ^ (r + 1) * (Nat.choose N r * (N - r)) := by
              rw [pow_succ]
              ac_rfl
        _ = K ^ (r + 1) *
              (Nat.choose N (r + 1) * (r + 1)) := by
                rw [Nat.choose_succ_right_eq]
        _ = (K ^ (r + 1) * Nat.choose N (r + 1)) * (r + 1) := by
              rw [mul_assoc]

/-- The cancellation-free coefficient comparison needed by the
without-replacement T3 moment bound.  Unsupported binomial coefficients and
all zero endpoints remain part of the public statement. -/
theorem ndChooseRatio_cross_le
    (N K r : ℕ) (hKN : K ≤ N) :
    (N : ℝ) ^ r * (Nat.choose K r : ℝ) ≤
      (K : ℝ) ^ r * (Nat.choose N r : ℝ) := by
  exact_mod_cast ndNat_pow_mul_choose_le_pow_mul_choose N K r hKN

/-- The actual fixed-bars factorial moment is bounded by the corresponding
with-replacement binomial coefficient.  No support condition relative to the
selected-set size `n - 1` is imposed. -/
theorem ndFixedTotalBarsPMF_expectation_choose_prefixCount_le
    (n L q r : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (hL1 : 1 < L) (hqL : q ≤ L - 1) (hrq : r ≤ q) :
    Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
      (fun B =>
        (Nat.choose (ndBarsPrefixCount B.1 q) r : ℝ)) ≤
      (Nat.choose q r : ℝ) *
        (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) ^ r := by
  have hKN : n - 1 ≤ L - 1 := Nat.sub_le_sub_right hL 1
  have hN : 0 < L - 1 := Nat.sub_pos_iff_lt.mpr hL1
  have hrL : r ≤ L - 1 := hrq.trans hqL
  have hchoosePos : 0 < (Nat.choose (L - 1) r : ℝ) :=
    Nat.cast_pos.2 (Nat.choose_pos hrL)
  have hNpowPos : 0 < ((L - 1 : ℕ) : ℝ) ^ r :=
    pow_pos (Nat.cast_pos.2 hN) r
  have hratio :
      (Nat.choose (n - 1) r : ℝ) /
          (Nat.choose (L - 1) r : ℝ) ≤
        (((n - 1 : ℕ) : ℝ) /
          ((L - 1 : ℕ) : ℝ)) ^ r := by
    rw [div_pow]
    apply (div_le_div_iff₀ hchoosePos hNpowPos).2
    simpa only [mul_comm] using
      ndChooseRatio_cross_le (L - 1) (n - 1) r hKN
  calc
    Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
        (fun B =>
          (Nat.choose (ndBarsPrefixCount B.1 q) r : ℝ)) =
        (Nat.choose q r : ℝ) *
          ((Nat.choose (n - 1) r : ℝ) /
            (Nat.choose (L - 1) r : ℝ)) := by
      simpa only [min_eq_right hqL] using
        ndFixedTotalBarsPMF_expectation_choose_prefixCount_eq
          n L q r hn hL hrL
    _ ≤ (Nat.choose q r : ℝ) *
          (((n - 1 : ℕ) : ℝ) /
            ((L - 1 : ℕ) : ℝ)) ^ r :=
      mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg _)

end ND
end Erdos1135
