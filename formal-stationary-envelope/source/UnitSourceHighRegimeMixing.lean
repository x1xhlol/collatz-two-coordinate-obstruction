import UnitSourceFixedSlice
import UnitSourceMappedAggregation
import Erdos1135.Tao.Section6.HighRegimeMixing

/-!
# Seed-uniform near-diagonal oscillation

The arbitrary-output source aggregation retains the native length-n source
and charges its global exceptional event once. Summing the seeded fixed
slices gives polynomial oscillation when 0.9n <= m <= n, uniformly in the
finite-modulus seed. This packet asserts no low-regime mixing theorem, Haar
density identification, integer-descendant estimate, or Collatz conclusion.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao

/-- Exact identification of the generic mapped fixed slice and the seeded
head-tail slice. The source length predicate is automatic on PMF support. -/
theorem unitSourceMappedSlice_eq_seededGatedSubmass
    (CA : ℝ) (T k l : ℕ) (z : ZMod (3 ^ (T + (k + 1))))
    (x : ZMod (3 ^ (T + (k + 1)))) :
    unitSourceMappedSlice CA (T + (k + 1)) k l
        (unitSourceLengthNMap (T + (k + 1)) z) x =
      unitSourceGatedSubmass CA T k l z x := by
  have hpmf : taoGatedOptionPMF (geom2PNatListPMF (T + (k + 1)))
      (taoSection6FixedAmbientGate CA (T + (k + 1)) k l)
      (unitSourceLengthNMap (T + (k + 1)) z) = unitSourceGatedPMF CA T k l z := by
    apply PMF.ext
    intro y
    unfold unitSourceGatedPMF taoGatedOptionPMF
    rw [PMF.map_apply, PMF.map_apply]
    apply tsum_congr
    intro full
    by_cases hlength : full.length = T + (k + 1)
    · by_cases hgate : taoSection6HeadGate CA (T + (k + 1)) k l (full.take (k + 1))
      · simp [taoSection6FixedAmbientGate, taoGatedOptionKey, hlength, hgate]
      · simp [taoSection6FixedAmbientGate, taoGatedOptionKey, hlength, hgate]
    · have hzero := geom2PNatListPMF_apply_eq_zero_of_length_ne (T + (k + 1)) full hlength
      simp [hzero]
  unfold unitSourceMappedSlice unitSourceGatedSubmass
  rw [hpmf]

theorem exists_unitSourceFixedAmbientOscillation_le
    (CA : ℝ) (hCA : 17 ≤ CA) (A : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N0 : ℕ, ∀ n k l m : ℕ,
      ∀ z : ZMod (3 ^ n), N0 ≤ n → k + 1 ≤ n → m ≤ n → 9 * n ≤ 10 * m →
      taoZModPowOscillation m n
          (unitSourceMappedSlice CA n k l (unitSourceLengthNMap n z)) ≤
        D / (n : ℝ) ^ (A + 3) := by
  obtain ⟨D, hD, N0, hslice⟩ := exists_unitSourceFixedSliceOscillation_le CA hCA A
  refine ⟨D, hD, N0, ?_⟩
  intro n k l m z hn hk hmn hm
  let T := n - (k + 1)
  have hambient : T + (k + 1) = n := Nat.sub_add_cancel hk
  clear_value T
  subst n
  have hbound := hslice T k l m z hn hmn hm
  have hsource : unitSourceMappedSlice CA (T + (k + 1)) k l
      (unitSourceLengthNMap (T + (k + 1)) z) = unitSourceGatedSubmass CA T k l z := by
    funext x
    exact unitSourceMappedSlice_eq_seededGatedSubmass CA T k l z x
  rw [hsource]
  exact hbound

noncomputable def unitSourceFineScaleOscillation
    (m n : ℕ) (z : ZMod (3 ^ n)) : ℝ :=
  taoZModPowOscillation m n (fun x => (unitSourceAffinePMF n (n - 1) z x).toReal)

/-- Seed-uniform Section 6 near-diagonal oscillation at every sufficiently
large conductor. The n-1-step law is the literal affine geometric PMF. -/
theorem exists_unitSourceFineScaleOscillation_le_highRegime_large
    (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ n m : ℕ, N0 ≤ n → m ≤ n → 9 * n ≤ 10 * m →
        ∀ z : ZMod (3 ^ n), unitSourceFineScaleOscillation m n z ≤ C / (n : ℝ) ^ (A + 1) := by
  let CA : ℝ := 8 * ((A : ℝ) + 4)
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hCA : (17 : ℝ) ≤ CA := by dsimp [CA]; nlinarith
  obtain ⟨D, hD, Nslice, hslice⟩ := exists_unitSourceFixedAmbientOscillation_le CA hCA A
  obtain ⟨Nevent, hNevent, hevent⟩ :=
    exists_unitSourceMappedOscillation_le_slice_sum_add_globalFailure CA hCA
  refine ⟨2 * D + 2, by nlinarith, max Nslice Nevent,
    hNevent.trans (le_max_right _ _), ?_⟩
  intro n m hn hmn hhigh z
  have hnSlice : Nslice ≤ n := (le_max_left _ _).trans hn
  have hnEvent : Nevent ≤ n := (le_max_right _ _).trans hn
  have hnTwo : 2 ≤ n := hNevent.trans hnEvent
  have hnOne : 1 ≤ n := by omega
  have hslices :
      (∑ k : Fin n, ∑ l : Fin (2 * n),
        taoZModPowOscillation m n
          (unitSourceMappedSlice CA n k l (unitSourceLengthNMap n z))) ≤
        (2 * D) / (n : ℝ) ^ (A + 1) := by
    calc
      _ ≤ ∑ _k : Fin n, ∑ _l : Fin (2 * n), D / (n : ℝ) ^ (A + 3) := by
        apply Finset.sum_le_sum
        intro k _hk
        apply Finset.sum_le_sum
        intro l _hl
        exact hslice n k l m z hnSlice (by omega) hmn hhigh
      _ = (((n * (2 * n) : ℕ) : ℝ) * (D / (n : ℝ) ^ (A + 3))) := by
        simp [Nat.cast_mul]
        ring
      _ = _ := taoSection6_box_mul_div_pow_eq A n D hnOne
  have hfailure : 2 * taoSection6GlobalFailureMass CA n ≤ 2 / (n : ℝ) ^ (A + 1) := by
    have h := taoSection6GlobalFailureMass_le_inv_pow A hnTwo
    dsimp [CA]
    calc
      _ ≤ 2 * (1 / (n : ℝ) ^ (A + 1)) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by ring
  have hevent' := hevent n hnEvent m hmn (unitSourceLengthNMap n z)
  rw [unitSourceLengthNMap_pmf_eq] at hevent'
  calc
    unitSourceFineScaleOscillation m n z ≤
      (∑ k : Fin n, ∑ l : Fin (2 * n),
        taoZModPowOscillation m n
          (unitSourceMappedSlice CA n k l (unitSourceLengthNMap n z))) +
        2 * taoSection6GlobalFailureMass CA n := hevent'
    _ ≤ (2 * D) / (n : ℝ) ^ (A + 1) + 2 / (n : ℝ) ^ (A + 1) :=
      add_le_add hslices hfailure
    _ = _ := by ring

/-- The fallback bound uses only that the literal affine image is a PMF. -/
theorem unitSourceFineScaleOscillation_le_two
    {m n : ℕ} (hmn : m ≤ n) (z : ZMod (3 ^ n)) :
    unitSourceFineScaleOscillation m n z ≤ 2 := by
  have hmass : (∑ x : ZMod (3 ^ n), |(unitSourceAffinePMF n (n - 1) z x).toReal|) = 1 := by
    simp only [abs_of_nonneg ENNReal.toReal_nonneg]
    exact pmf_sum_toReal _
  exact (taoZModPowOscillation_le_two_mul_sum_abs hmn _).trans_eq (by rw [hmass, mul_one])

/-- Uniform polynomial near-diagonal oscillation, including the finitely many
small conductors by the PMF mass bound. -/
theorem exists_unitSourceFineScaleOscillation_le_highRegime
    (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n m : ℕ, 1 ≤ n → m ≤ n → 9 * n ≤ 10 * m →
      ∀ z : ZMod (3 ^ n), unitSourceFineScaleOscillation m n z ≤ C / (n : ℝ) ^ A := by
  obtain ⟨D, hD, N0, hN0, hlarge⟩ :=
    exists_unitSourceFineScaleOscillation_le_highRegime_large A
  let C := D + 2 * (N0 : ℝ) ^ A
  have hC : 0 ≤ C := add_nonneg hD (by positivity)
  refine ⟨C, hC, ?_⟩
  intro n m hn hmn hhigh z
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  by_cases hbig : N0 ≤ n
  · calc
      _ ≤ D / (n : ℝ) ^ (A + 1) := hlarge n m hbig hmn hhigh z
      _ ≤ D / (n : ℝ) ^ A := by
        apply div_le_div_of_nonneg_left hD (by positivity)
        exact pow_le_pow_right₀ hnR (by omega)
      _ ≤ C / (n : ℝ) ^ A :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  · have hnN : (n : ℝ) ≤ N0 := by exact_mod_cast (le_of_not_ge hbig)
    have hpow : (n : ℝ) ^ A ≤ (N0 : ℝ) ^ A := by gcongr
    have hsmall : 2 ≤ C / (n : ℝ) ^ A := by
      apply (le_div_iff₀ (pow_pos hnpos A)).2
      dsimp [C]
      nlinarith
    exact (unitSourceFineScaleOscillation_le_two hmn z).trans hsmall

#print axioms exists_unitSourceFineScaleOscillation_le_highRegime

end Erdos1135.Tao
