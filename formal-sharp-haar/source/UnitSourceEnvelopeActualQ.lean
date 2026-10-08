import UnitSourcePairExpectation
import Erdos1135.Tao.Fourier.Section7PairExpectation
import Erdos1135.Tao.Fourier.Section7SourceDomain
import Erdos1135.Tao.Renewal.HoldExpectation
import Erdos1135.Tao.Renewal.SourceCutoffStabilization
import Erdos1135.Tao.Renewal.SourceRegeneration

/-!
# Native full-pair envelope to the actual renewal Q

This leaf transports the checked raw-Pascal expectation through finite Hold
source histories, averages each realized QFinite tail, and only then applies
source cutoff stabilization. It adapts the envelope portion and private
helpers of native `Section7SChiActualQ`, without introducing a new Fourier
law or a new renewal assumption.
-/

open scoped BigOperators Topology

namespace Erdos1135
namespace Tao

private theorem taoSection7HoldPointOfPrefix_length_eq_sourceHitPoint
    (pre : List ℕ) :
    taoSection7HoldPointOfPrefix pre.length pre =
      taoSection7SourceHitPoint (1 : ℕ+) 0 pre := by
  ext
  · apply Subtype.ext
    simp [taoSection7HoldPointOfPrefix, taoSection7SourceHitPoint,
      taoSection7ShiftIndex]
    omega
  · simp [taoSection7HoldPointOfPrefix, taoSection7HoldTerminalSum,
      taoSection7SourceHitPoint]

private theorem taoSection7HoldPointOfPrefix_length_eq_increment
    (pre : List ℕ) :
    taoSection7HoldPointOfPrefix pre.length pre =
      taoSection7HoldIncrementOfPrefix pre := by
  ext
  · apply Subtype.ext
    simp [taoSection7HoldPointOfPrefix, taoSection7HoldIncrementOfPrefix,
      taoSection7ShiftIndex]
    omega
  · simp [taoSection7HoldPointOfPrefix, taoSection7HoldTerminalSum,
      taoSection7HoldIncrementOfPrefix]

private theorem taoSection7HoldSourcePrefixPMF_toReal_ne_zero_support
    {m : ℕ} {pre : List ℕ}
    (h : (taoSection7HoldSourcePrefixPMF (m, pre)).toReal ≠ 0) :
    m = pre.length ∧ taoSection7NoThree pre := by
  have hinner :
      (taoSection7PascalPrimeSourceListPMF m pre).toReal ≠ 0 := by
    intro hzero
    rw [taoSection7HoldSourcePrefixPMF_apply_toReal, hzero, mul_zero] at h
    exact h rfl
  have hpmf : taoSection7PascalPrimeSourceListPMF m pre ≠ 0 := by
    intro hzero
    rw [hzero] at hinner
    exact hinner rfl
  have hlen : m = pre.length := by
    by_contra hne
    exact hpmf (taoSection7PascalPrimeSourceListPMF_apply_eq_zero_of_length_ne
      m pre (fun hlen => hne hlen.symm))
  exact ⟨hlen,
    taoSection7PascalPrimeSourceListPMF_apply_ne_zero_noThree hpmf⟩

private theorem taoSection7HoldSourcePrefixListPMF_toReal_ne_zero_support
    {N : ℕ} {xs : List (ℕ × List ℕ)}
    (h : (taoSection7HoldSourcePrefixListPMF N xs).toReal ≠ 0) :
    xs.length = N ∧
      ∀ x ∈ xs, x.1 = x.2.length ∧ taoSection7NoThree x.2 := by
  have hlen : xs.length = N := by
    by_contra hne
    have hzero := taoSection7HoldSourcePrefixListPMF_apply_eq_zero_of_length_ne
      N xs hne
    rw [hzero] at h
    exact h rfl
  refine ⟨hlen, ?_⟩
  induction N generalizing xs with
  | zero =>
      have hnil : xs = [] := by simpa using hlen
      subst xs
      simp
  | succ N ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          have hprod :
              (taoSection7HoldSourcePrefixPMF x).toReal *
                  (taoSection7HoldSourcePrefixListPMF N xs).toReal ≠ 0 := by
            simpa [taoSection7HoldSourcePrefixListPMF_succ_apply_cons,
              ENNReal.toReal_mul] using h
          have hhead : (taoSection7HoldSourcePrefixPMF x).toReal ≠ 0 := by
            intro hzero
            exact hprod (by rw [hzero, zero_mul])
          have htail :
              (taoSection7HoldSourcePrefixListPMF N xs).toReal ≠ 0 := by
            intro hzero
            exact hprod (by rw [hzero, mul_zero])
          have hlenTail : xs.length = N := by simpa using hlen
          have hsTail := ih htail hlenTail
          intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact taoSection7HoldSourcePrefixPMF_toReal_ne_zero_support hhead
          · exact hsTail y hy

private theorem taoSection7HoldPoint_map_eq_increments_of_supported
    (xs : List (ℕ × List ℕ))
    (hsupp : ∀ x ∈ xs, x.1 = x.2.length) :
    xs.map (fun x => taoSection7HoldPointOfPrefix x.1 x.2) =
      taoSection7HoldIncrementsOfPrefixes (xs.map Prod.snd) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := hsupp x (by simp)
      have htail : ∀ y ∈ xs, y.1 = y.2.length := by
        intro y hy
        exact hsupp y (by simp [hy])
      rw [List.map_cons, taoSection7HoldIncrementsOfPrefixes]
      simp only [List.map_cons]
      rw [ih htail]
      congr 1
      rcases x with ⟨m, pre⟩
      rw [hx]
      exact taoSection7HoldPointOfPrefix_length_eq_increment pre

private noncomputable def taoSection7RealizedHoldListQFinite
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop) :
    List TaoSection7RenewalPoint → ℝ
  | [] => 0
  | p :: hs => taoSection7QFinite epsilon W p hs

private theorem taoSection7RealizedHoldListQFinite_nonneg
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop) :
    ∀ hs, 0 ≤ taoSection7RealizedHoldListQFinite epsilon W hs
  | [] => by simp [taoSection7RealizedHoldListQFinite]
  | p :: hs => taoSection7QFinite_nonneg epsilon W p hs

private theorem taoSection7RealizedHoldListQFinite_le_one
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop) :
    ∀ hs, taoSection7RealizedHoldListQFinite epsilon W hs ≤ 1
  | [] => by simp [taoSection7RealizedHoldListQFinite]
  | p :: hs => taoSection7QFinite_le_one hepsilon W p hs

private theorem taoSection7PascalExpectation_eq_sourceHistoryExpectation
    (n : ℕ) (xi : ZMod (3 ^ n)) :
    (∑' bs : List ℕ,
      (taoSection7PascalSourceListPMF (n / 2) bs).toReal *
        taoSection7FactorProduct
          (taoSection7SourceFThreeFactor n xi) bs) =
      ∑' xs : List (ℕ × List ℕ),
        (taoSection7HoldSourcePrefixListPMF (n / 2) xs).toReal *
          taoSection7FactorProduct
            (taoSection7SourceFThreeFactor n xi)
            (taoSection7RawPrefixOfHoldBlocks (n / 2) xs) := by
  have htransport := pmf_map_weighted_tsum_toReal_eq_of_bounded01
    (taoSection7HoldSourcePrefixListPMF (n / 2))
    (taoSection7RawPrefixOfHoldBlocks (n / 2))
    (taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi))
    (fun bs => taoSection7FactorProductFrom_nonneg
      (taoSection7SourceFThreeFactor_nonneg n xi) 1 0 bs)
    (fun bs => taoSection7FactorProduct_le_one
      (taoSection7SourceFThreeFactor_nonneg n xi)
      (taoSection7SourceFThreeFactor_le_one n xi) bs)
  rw [taoSection7HoldSourcePrefixListPMF_map_rawPrefix_self] at htransport
  exact htransport.2.2

private theorem taoSection7SourceHistory_weighted_factor_le_realizedQFinite
    (n : ℕ) (xi : ZMod (3 ^ n)) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hJ : 0 < n / 2) (xs : List (ℕ × List ℕ)) :
    (taoSection7HoldSourcePrefixListPMF (n / 2) xs).toReal *
        taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi)
          (taoSection7RawPrefixOfHoldBlocks (n / 2) xs) ≤
      (taoSection7HoldSourcePrefixListPMF (n / 2) xs).toReal *
        taoSection7RealizedHoldListQFinite epsilon
          (taoSection7SourceActualW n xi epsilon)
          (xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2) := by
  by_cases hmass :
      (taoSection7HoldSourcePrefixListPMF (n / 2) xs).toReal = 0
  · simp [hmass]
  · have hsupp :=
      taoSection7HoldSourcePrefixListPMF_toReal_ne_zero_support hmass
    cases xs with
    | nil =>
        have hzero : n / 2 = 0 := by simpa using hsupp.1.symm
        exact (Nat.ne_of_gt hJ hzero).elim
    | cons x tail =>
        rcases x with ⟨m, pre⟩
        have hhead := hsupp.2 (m, pre) (by simp)
        have htail :
            ∀ y ∈ tail, y.1 = y.2.length ∧ taoSection7NoThree y.2 := by
          intro y hy
          exact hsupp.2 y (by simp [hy])
        have hmap :
            tail.map (fun y => taoSection7HoldPointOfPrefix y.1 y.2) =
              taoSection7HoldIncrementsOfPrefixes (tail.map Prod.snd) := by
          exact taoSection7HoldPoint_map_eq_increments_of_supported tail
            (fun y hy => (htail y hy).1)
        have hm : m = pre.length := by simpa using hhead.1
        subst m
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        change
          taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi)
              ((taoSection7SourceBlocks
                (pre :: tail.map Prod.snd)).take (n / 2)) ≤ _
        simp only [List.map_cons, taoSection7RealizedHoldListQFinite]
        rw [taoSection7HoldPointOfPrefix_length_eq_sourceHitPoint pre, hmap]
        exact
          taoSection7SourceFThreeFactorProduct_take_sourceBlocks_le_qfinite_cutoff
            n xi (n / 2) hepsilon0 hepsilon1 pre (tail.map Prod.snd)
            hhead.2 (by
              intro q hq
              rcases List.mem_map.mp hq with ⟨y, hy, rfl⟩
              exact (htail y hy).2)

private theorem taoSection7SourceHistoryExpectation_le_holdListQFinite
    (n : ℕ) (xi : ZMod (3 ^ n)) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hJ : 0 < n / 2) :
    (∑' xs : List (ℕ × List ℕ),
      (taoSection7HoldSourcePrefixListPMF (n / 2) xs).toReal *
        taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi)
          (taoSection7RawPrefixOfHoldBlocks (n / 2) xs)) ≤
      ∑' hs : List TaoSection7RenewalPoint,
        (taoSection7HoldListPMF (n / 2) hs).toReal *
          taoSection7RealizedHoldListQFinite epsilon
            (taoSection7SourceActualW n xi epsilon) hs := by
  have hraw := pmf_map_weighted_tsum_toReal_eq_of_bounded01
    (taoSection7HoldSourcePrefixListPMF (n / 2))
    (taoSection7RawPrefixOfHoldBlocks (n / 2))
    (taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi))
    (fun bs => taoSection7FactorProductFrom_nonneg
      (taoSection7SourceFThreeFactor_nonneg n xi) 1 0 bs)
    (fun bs => taoSection7FactorProduct_le_one
      (taoSection7SourceFThreeFactor_nonneg n xi)
      (taoSection7SourceFThreeFactor_le_one n xi) bs)
  rw [taoSection7HoldSourcePrefixListPMF_map_rawPrefix_self] at hraw
  have hhold := pmf_map_weighted_tsum_toReal_eq_of_bounded01
    (taoSection7HoldSourcePrefixListPMF (n / 2))
    (fun xs => xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2)
    (taoSection7RealizedHoldListQFinite epsilon
      (taoSection7SourceActualW n xi epsilon))
    (taoSection7RealizedHoldListQFinite_nonneg epsilon _)
    (taoSection7RealizedHoldListQFinite_le_one hepsilon0 _)
  rw [taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq] at hhold
  calc
    _ ≤ ∑' xs : List (ℕ × List ℕ),
        (taoSection7HoldSourcePrefixListPMF (n / 2) xs).toReal *
          taoSection7RealizedHoldListQFinite epsilon
            (taoSection7SourceActualW n xi epsilon)
            (xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2) :=
      hraw.2.1.tsum_le_tsum
        (taoSection7SourceHistory_weighted_factor_le_realizedQFinite
          n xi hepsilon0 hepsilon1 hJ) hhold.2.1
    _ = _ := hhold.2.2.symm

private theorem taoSection7HoldListRealizedQFiniteExpectation_eq_terminalApprox
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (K : ℕ)
    (W : TaoSection7RenewalPoint → Prop) :
    (∑' hs : List TaoSection7RenewalPoint,
      (taoSection7HoldListPMF (K + 1) hs).toReal *
        taoSection7RealizedHoldListQFinite epsilon W hs) =
      taoSection7HoldExpectationFull
        (fun p => taoSection7QFiniteTerminalOneApprox K epsilon W p) := by
  have hnil :
      (taoSection7HoldListPMF (K + 1) ([] : List TaoSection7RenewalPoint)).toReal *
          taoSection7RealizedHoldListQFinite epsilon W [] = 0 := by
    simp [taoSection7RealizedHoldListQFinite]
  have hmass :
      Summable fun x : TaoSection7RenewalPoint × List TaoSection7RenewalPoint =>
        (taoSection7HoldPMF x.1).toReal *
          (taoSection7HoldListPMF K x.2).toReal :=
    taoSection7HoldPMF_mul_holdListPMF_summable_toReal K
  have hsum :
      Summable fun x : TaoSection7RenewalPoint × List TaoSection7RenewalPoint =>
        (taoSection7HoldPMF x.1).toReal *
          (taoSection7HoldListPMF K x.2).toReal *
          taoSection7QFinite epsilon W x.1 x.2 := by
    refine Summable.of_norm_bounded hmass ?_
    intro x
    have hm0 : 0 ≤ (taoSection7HoldPMF x.1).toReal *
        (taoSection7HoldListPMF K x.2).toReal :=
      mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have hq0 : 0 ≤ taoSection7QFinite epsilon W x.1 x.2 :=
      taoSection7QFinite_nonneg epsilon W x.1 x.2
    have hq1 : taoSection7QFinite epsilon W x.1 x.2 ≤ 1 :=
      taoSection7QFinite_le_one hepsilon W x.1 x.2
    have hqabs : |taoSection7QFinite epsilon W x.1 x.2| ≤ 1 := by
      rw [abs_of_nonneg hq0]
      exact hq1
    calc
      ‖(taoSection7HoldPMF x.1).toReal *
          (taoSection7HoldListPMF K x.2).toReal *
          taoSection7QFinite epsilon W x.1 x.2‖ =
          ((taoSection7HoldPMF x.1).toReal *
            (taoSection7HoldListPMF K x.2).toReal) *
            |taoSection7QFinite epsilon W x.1 x.2| := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hm0]
      _ ≤ ((taoSection7HoldPMF x.1).toReal *
            (taoSection7HoldListPMF K x.2).toReal) * 1 := by
              exact mul_le_mul_of_nonneg_left hqabs hm0
      _ = (taoSection7HoldPMF x.1).toReal *
            (taoSection7HoldListPMF K x.2).toReal := by ring
  have hfiber :
      ∀ p : TaoSection7RenewalPoint,
        Summable fun hs : List TaoSection7RenewalPoint =>
          (taoSection7HoldPMF p).toReal *
            (taoSection7HoldListPMF K hs).toReal *
            taoSection7QFinite epsilon W p hs := by
    intro p
    have hinner := taoSection7QFiniteTerminalOneApprox_summable
      (K := K) hepsilon W p
    simpa [mul_assoc] using hinner.mul_left (taoSection7HoldPMF p).toReal
  calc
    (∑' hs : List TaoSection7RenewalPoint,
      (taoSection7HoldListPMF (K + 1) hs).toReal *
        taoSection7RealizedHoldListQFinite epsilon W hs) =
        ∑' x : TaoSection7RenewalPoint × List TaoSection7RenewalPoint,
          (taoSection7HoldListPMF (K + 1) (x.1 :: x.2)).toReal *
            taoSection7RealizedHoldListQFinite epsilon W (x.1 :: x.2) := by
          exact taoSection7_tsum_list_eq_tsum_cons_of_nil_zero hnil
    _ = ∑' x : TaoSection7RenewalPoint × List TaoSection7RenewalPoint,
        (taoSection7HoldPMF x.1).toReal *
          (taoSection7HoldListPMF K x.2).toReal *
          taoSection7QFinite epsilon W x.1 x.2 := by
          apply tsum_congr
          intro x
          rw [taoSection7HoldListPMF_succ_apply_cons, ENNReal.toReal_mul]
          rfl
    _ = ∑' p : TaoSection7RenewalPoint,
        (taoSection7HoldPMF p).toReal *
          (∑' hs : List TaoSection7RenewalPoint,
            (taoSection7HoldListPMF K hs).toReal *
              taoSection7QFinite epsilon W p hs) := by
          rw [Summable.tsum_prod' hsum hfiber]
          apply tsum_congr
          intro p
          simpa [mul_assoc] using
            (tsum_mul_left
              (a := (taoSection7HoldPMF p).toReal)
              (f := fun hs : List TaoSection7RenewalPoint =>
                (taoSection7HoldListPMF K hs).toReal *
                  taoSection7QFinite epsilon W p hs))
    _ = taoSection7HoldExpectationFull
        (fun p => taoSection7QFiniteTerminalOneApprox K epsilon W p) := rfl

/-- The native raw Pascal envelope-to-renewal transport, exposed independently
of the canonical offset character so terminal phases can reuse it. The
transport proof below follows the native Section7SChiActualQ leaf. -/
theorem unitSourceFullEnvelope_le_actualQ
    (n : ℕ) (xi : ZMod (3 ^ n))
    {epsilon : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    taoSection7PairSourceEnvelope n xi (n / 2) 1 0 ≤
      taoSection7HoldExpectationFull
        (taoSection7SourceActualQ n xi epsilon) := by
  change (∑' bs : List ℕ,
    (taoSection7PascalSourceListPMF (n / 2) bs).toReal *
      taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi) bs) ≤ _
  by_cases hJ0 : n / 2 = 0
  · have hraw :
        (∑' bs : List ℕ,
          (taoSection7PascalSourceListPMF (n / 2) bs).toReal *
            taoSection7FactorProduct
              (taoSection7SourceFThreeFactor n xi) bs) = 1 := by
      rw [hJ0, tsum_eq_single ([] : List ℕ)]
      · simp [taoSection7PascalSourceListPMF,
          taoSection7FactorProduct, taoSection7FactorProductFrom]
      · intro bs hbs
        cases bs with
        | nil => exact (hbs rfl).elim
        | cons b bs =>
            simp [taoSection7PascalSourceListPMF]
    have hQ :
        taoSection7SourceActualQ n xi epsilon =
          fun _p : TaoSection7RenewalPoint => 1 := by
      funext p
      apply taoSection7SourceActualQ_eq_one_of_cutoff_lt hepsilon0
      rw [hJ0]
      exact p.j.property
    rw [hraw, hQ]
    unfold taoSection7HoldExpectationFull
    simpa using (le_of_eq taoSection7HoldPMF_tsum_toReal.symm)
  · have hJ : 0 < n / 2 := Nat.pos_of_ne_zero hJ0
    obtain ⟨K, hK⟩ := Nat.exists_eq_succ_of_ne_zero hJ0
    calc
      (∑' bs : List ℕ,
          (taoSection7PascalSourceListPMF (n / 2) bs).toReal *
            taoSection7FactorProduct
              (taoSection7SourceFThreeFactor n xi) bs) =
          ∑' xs : List (ℕ × List ℕ),
            (taoSection7HoldSourcePrefixListPMF (n / 2) xs).toReal *
              taoSection7FactorProduct
                (taoSection7SourceFThreeFactor n xi)
                (taoSection7RawPrefixOfHoldBlocks (n / 2) xs) :=
        taoSection7PascalExpectation_eq_sourceHistoryExpectation n xi
      _ ≤ ∑' hs : List TaoSection7RenewalPoint,
            (taoSection7HoldListPMF (n / 2) hs).toReal *
              taoSection7RealizedHoldListQFinite epsilon
                (taoSection7SourceActualW n xi epsilon) hs :=
        taoSection7SourceHistoryExpectation_le_holdListQFinite
          n xi hepsilon0 hepsilon1 hJ
      _ = taoSection7HoldExpectationFull
            (fun p =>
              taoSection7QFiniteTerminalOneApprox K epsilon
                (taoSection7SourceActualW n xi epsilon) p) := by
        rw [hK]
        exact taoSection7HoldListRealizedQFiniteExpectation_eq_terminalApprox
          hepsilon0 K (taoSection7SourceActualW n xi epsilon)
      _ = taoSection7HoldExpectationFull
            (taoSection7SourceActualQ n xi epsilon) := by
        unfold taoSection7HoldExpectationFull
        apply tsum_congr
        intro p
        rw [taoSection7SourceActualQ_eq_terminalOneApprox_of_le
          hepsilon0 p K (by
            calc
              n / 2 = K + 1 := hK
              _ ≤ (p.j : ℕ) + K := by
                simpa [Nat.add_comm] using
                  Nat.add_le_add_right p.j.property K)]

end Tao
end Erdos1135
