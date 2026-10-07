import ActualPathSupport

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Preorder Filter Topology

namespace CollatzCylinderPacking.Arithmetic.InverseDoob

abbrev PrefixIndex (k : ℕ) := Finset.Iic k → ℕ

def prefixExtend (k : ℕ) (p : PrefixIndex k) (i : ℕ) : ℕ :=
  if hi : i ≤ k then p ⟨i, Finset.mem_Iic.mpr hi⟩ else 0

theorem prefixExtend_apply {k i : ℕ} (p : PrefixIndex k) (hi : i ≤ k) :
    prefixExtend k p i = p ⟨i, Finset.mem_Iic.mpr hi⟩ := dif_pos hi

theorem restrict_prefixExtend (k : ℕ) (p : PrefixIndex k) :
    frestrictLe (π := fun _ : ℕ => ℕ) k (prefixExtend k p) = p := by
  funext i
  exact prefixExtend_apply p (Finset.mem_Iic.mp i.2)

theorem ValidPrefix.congr {n k : ℕ} {x y : ℕ → ℕ} (hx : ValidPrefix n k x)
    (he : ∀ i ≤ k, x i = y i) : ValidPrefix n k y := by
  refine ⟨(he 0 (Nat.zero_le k)).symm.trans hx.1, ?_, ?_⟩
  · intro i hi
    simpa only [← he i hi] using hx.2.1 i hi
  · intro i hi
    obtain ⟨a, ha, hxnext⟩ := hx.2.2 i hi
    refine ⟨a, ?_, ?_⟩
    · simpa only [← he i (by omega)] using ha
    · simpa only [← he i (by omega), ← he (i + 1) (by omega)] using hxnext

noncomputable def finitePrefixPMF (n k : ℕ) : PMF (PrefixIndex k) := by
  let μ := (pathLaw n).map (frestrictLe (π := fun _ : ℕ => ℕ) k)
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (measurable_frestrictLe k).aemeasurable
  exact μ.toPMF

theorem finitePrefixPMF_apply (n k : ℕ) (p : PrefixIndex k) :
    finitePrefixPMF n k p = pathLaw n (prefixSet k (prefixExtend k p)) := by
  change (pathLaw n).map (frestrictLe (π := fun _ : ℕ => ℕ) k) {p} = _
  rw [Measure.map_apply (measurable_frestrictLe k) (measurableSet_singleton _),
    prefixSet_eq_preimage, restrict_prefixExtend]

theorem finitePrefixPMF_eq_zero_of_invalid {n k : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (p : PrefixIndex k) (hbad : ¬ ValidPrefix n k (prefixExtend k p)) :
    finitePrefixPMF n k p = 0 := by
  rw [finitePrefixPMF_apply]
  have hnull : pathLaw n {x | ¬ ValidPrefix n k x} = 0 :=
    ae_iff.mp (pathLaw_validPrefix_ae hn hu k)
  apply measure_mono_null _ hnull
  intro x hx hgood
  exact hbad (hgood.congr hx)

theorem finitePrefixPMF_toReal_summable (n k : ℕ) :
    Summable (fun p => (finitePrefixPMF n k p).toReal) :=
  ENNReal.summable_toReal (finitePrefixPMF n k).tsum_coe_ne_top

theorem finitePrefixPMF_toReal_tsum (n k : ℕ) :
    ∑' p, (finitePrefixPMF n k p).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq (fun p => (finitePrefixPMF n k).apply_ne_top p),
    (finitePrefixPMF n k).tsum_coe, ENNReal.toReal_one]

end CollatzCylinderPacking.Arithmetic.InverseDoob
