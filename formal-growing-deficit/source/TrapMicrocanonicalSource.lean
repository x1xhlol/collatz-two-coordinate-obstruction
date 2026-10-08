import UnitSourceAffinePMF

/-! The actual geometric source conditioned on its total exponent. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace Erdos1135.Tao

noncomputable def unitSourceExponentMass (k s : ℕ) : ℝ :=
  (((geom2PNatListPMF k).map taoTupleWeight) s).toReal

theorem unitSourceExponentMass_nonneg (k s : ℕ) :
    0 ≤ unitSourceExponentMass k s := ENNReal.toReal_nonneg

theorem unitSourceExponentMass_eq_tsum (k s : ℕ) :
    unitSourceExponentMass k s =
      ∑' as : List ℕ+, if taoTupleWeight as = s then
        (geom2PNatListPMF k as).toReal else 0 := by
  rw [unitSourceExponentMass, pmf_map_apply_toReal_tsum]
  apply tsum_congr
  intro as
  simp only [eq_comm]

theorem unitSourceExponentMass_pos_support (k s : ℕ)
    (h : 0 < unitSourceExponentMass k s) :
    ∃ as ∈ {as : List ℕ+ | taoTupleWeight as = s},
      as ∈ (geom2PNatListPMF k).support := by
  have hm : s ∈ ((geom2PNatListPMF k).map taoTupleWeight).support := by
    rw [PMF.mem_support_iff]
    intro hz
    simp [unitSourceExponentMass, hz] at h
  obtain ⟨as, has, hs⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  exact ⟨as, hs, has⟩

noncomputable def unitSourceConditionedListPMF (k s : ℕ)
    (h : 0 < unitSourceExponentMass k s) : PMF (List ℕ+) :=
  (geom2PNatListPMF k).filter {as | taoTupleWeight as = s}
    (unitSourceExponentMass_pos_support k s h)

theorem unitSourceConditionedListPMF_apply_toReal (k s : ℕ)
    (h : 0 < unitSourceExponentMass k s) (as : List ℕ+) :
    (unitSourceConditionedListPMF k s h as).toReal =
      if taoTupleWeight as = s then
        (geom2PNatListPMF k as).toReal / unitSourceExponentMass k s else 0 := by
  classical
  have hmass :
      (∑' xs : List ℕ+,
        ({xs : List ℕ+ | taoTupleWeight xs = s}.indicator
          (geom2PNatListPMF k)) xs) =
        ((geom2PNatListPMF k).map taoTupleWeight) s := by
    rw [PMF.map_apply]
    apply tsum_congr
    intro xs
    simp [Set.indicator_apply, eq_comm]
  rw [unitSourceConditionedListPMF, PMF.filter_apply, hmass,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  by_cases hs : taoTupleWeight as = s <;>
    simp [hs, unitSourceExponentMass, div_eq_mul_inv]

noncomputable def unitSourceConditionedAffinePMF
    (N k s : ℕ) (z : ZMod (3 ^ N))
    (h : 0 < unitSourceExponentMass k s) : PMF (ZMod (3 ^ N)) :=
  (unitSourceConditionedListPMF k s h).map (unitSourceAffineOffset N k z)

noncomputable def unitSourceSliceFourierMass
    (N k : ℕ) (xi z : ZMod (3 ^ N)) (s : ℕ) : ℂ :=
  ∑' as : List ℕ+, if taoTupleWeight as = s then
    ((geom2PNatListPMF k as).toReal : ℂ) *
      taoForwardDFTKernel (unitSourceAffineOffset N k z as) xi else 0

theorem unitSourceConditionedAffinePMF_dft_eq_normalized
    (N k s : ℕ) (xi z : ZMod (3 ^ N))
    (h : 0 < unitSourceExponentMass k s) :
    ZMod.dft (pmfComplexMass (unitSourceConditionedAffinePMF N k s z h)) xi =
      unitSourceSliceFourierMass N k xi z s / (unitSourceExponentMass k s : ℂ) := by
  unfold unitSourceConditionedAffinePMF
  rw [tao_dft_pmfComplexMass_map_apply]
  unfold unitSourceSliceFourierMass
  rw [← tsum_div_const]
  apply tsum_congr
  intro as
  rw [unitSourceConditionedListPMF_apply_toReal]
  by_cases hs : taoTupleWeight as = s
  · simp [hs]
    ring
  · simp [hs]

noncomputable def unitSourceAffineTwistedExpectation
    (N k : ℕ) (xi z : ZMod (3 ^ N)) (tau : UnitSourceTerminalPhase) : ℂ :=
  ∑' as : List ℕ+, ((geom2PNatListPMF k as).toReal : ℂ) *
    taoForwardDFTKernel (unitSourceAffineOffset N k z as) xi * tau.1 (taoTupleWeight as)

noncomputable def unitSourceTerminalPhaseMul
    (tau sigma : UnitSourceTerminalPhase) : UnitSourceTerminalPhase :=
  ⟨fun s => tau.1 s * sigma.1 s, fun s => by rw [norm_mul, tau.2, sigma.2, one_mul]⟩

theorem unitSourceAffineTwistedExpectation_eq_pairExpectation
    (N k : ℕ) (xi z : ZMod (3 ^ N)) (tau : UnitSourceTerminalPhase) :
    unitSourceAffineTwistedExpectation N k xi z tau =
      unitSourcePairExpectation N xi
        (unitSourceTerminalPhaseMul (unitSourceSeedPhase N k xi z) tau) k 1 0 := by
  unfold unitSourceAffineTwistedExpectation unitSourcePairExpectation
  apply tsum_congr
  intro as
  by_cases hlen : as.length = k
  · rw [unitSourceAffine_kernel_eq_twistedPairExpansion N k xi z as hlen]
    simp only [unitSourcePairExpansionFrom_eq_original_mul_terminal,
      Nat.zero_add, unitSourceTerminalPhaseMul]
    ring
  · rw [geom2PNatListPMF_apply_eq_zero_of_length_ne k as hlen]
    simp

theorem unitSourceAffineTwistedExpectation_summable
    (N k : ℕ) (xi z : ZMod (3 ^ N)) (tau : UnitSourceTerminalPhase) :
    Summable fun as : List ℕ+ => ((geom2PNatListPMF k as).toReal : ℂ) *
      taoForwardDFTKernel (unitSourceAffineOffset N k z as) xi * tau.1 (taoTupleWeight as) := by
  refine Summable.of_norm_bounded (pmf_summable_toReal (geom2PNatListPMF k)) ?_
  intro as
  rw [norm_mul, norm_mul, norm_taoForwardDFTKernel_eq_one, tau.2]
  simp

def unitSourceConstantPhase : UnitSourceTerminalPhase := ⟨fun _ => 1, by simp⟩

noncomputable def unitSourceSliceSign (s : ℕ) : UnitSourceTerminalPhase :=
  ⟨fun t => if t = s then 1 else -1, fun t => by dsimp; split <;> simp⟩

theorem unitSourceSliceFourierMass_eq_two_phases
    (N k : ℕ) (xi z : ZMod (3 ^ N)) (s : ℕ) :
    unitSourceSliceFourierMass N k xi z s =
      (unitSourceAffineTwistedExpectation N k xi z unitSourceConstantPhase +
        unitSourceAffineTwistedExpectation N k xi z (unitSourceSliceSign s)) / 2 := by
  unfold unitSourceAffineTwistedExpectation
  rw [← (unitSourceAffineTwistedExpectation_summable N k xi z unitSourceConstantPhase).tsum_add
    (unitSourceAffineTwistedExpectation_summable N k xi z (unitSourceSliceSign s)),
    ← tsum_div_const]
  unfold unitSourceSliceFourierMass
  apply tsum_congr
  intro as
  by_cases hs : taoTupleWeight as = s <;>
    simp [unitSourceConstantPhase, unitSourceSliceSign, hs]

end Erdos1135.Tao

#print axioms Erdos1135.Tao.unitSourceConditionedAffinePMF_dft_eq_normalized
#print axioms Erdos1135.Tao.unitSourceSliceFourierMass_eq_two_phases
