import Erdos1135.Tao.Probability.AntitoneResidueSums
import Erdos1135.Tao.Probability.FullL1
import Erdos1135.Tao.Probability.LogWindowMassLower
import Erdos1135.Tao.Syracuse.Prop19Laws
import Lean.Elab.Tactic.Omega

/-!
# Logarithmic Window Residue Laws

This module compares the finite logarithmic source-index law with the uniform
law on odd residue classes.  It keeps Tao's real endpoint schedule and the
Section 5 output packet out of the finite harmonic argument.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators ZMod

/-- The logarithmic source-index law reduced modulo a positive natural modulus. -/
noncomputable def oddLogSourceIndexResidueLaw
    (lo hi : ℕ) (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (Q : ℕ) (hQ : 0 < Q) : PMF (Fin Q) :=
  (oddLogSourceIndexPMF lo hi hmass).map fun i =>
    ⟨i.1 % Q, Nat.mod_lt i.1 hQ⟩

/-- The uniform law on a positive finite residue carrier, with positivity kept
as explicit data rather than a global typeclass assumption. -/
noncomputable def positiveFinUniformPMF (Q : ℕ) (hQ : 0 < Q) : PMF (Fin Q) := by
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  exact PMF.uniformOfFintype (Fin Q)

/-- Each source-index residue atom is its harmonic fiber sum divided by the
total odd-window mass. -/
theorem oddLogSourceIndexResidueLaw_apply_toReal
    {lo hi Q : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) (hQ : 0 < Q)
    (r : Fin Q) :
    (oddLogSourceIndexResidueLaw lo hi hmass Q hQ r).toReal =
      antitoneResidueClassSum (lo / 2) ((hi - 1) / 2) Q
          (fun i => logNatWeight (oddLogSourceIndexToValue i)) r /
        logFinsetMass (oddLogWindow lo hi) := by
  classical
  rw [oddLogSourceIndexResidueLaw, taoPMF_map_apply_toReal_tsum, tsum_fintype]
  rw [show (Finset.univ :
      Finset {i : ℕ // i ∈ oddLogSourceIndexWindow lo hi}) =
    (oddLogSourceIndexWindow lo hi).attach by
      exact Finset.univ_eq_attach _]
  calc
    (∑ i ∈ (oddLogSourceIndexWindow lo hi).attach,
        if r = ⟨i.1 % Q, Nat.mod_lt i.1 hQ⟩ then
          (oddLogSourceIndexPMF lo hi hmass i).toReal else 0) =
        ∑ i ∈ (oddLogSourceIndexWindow lo hi).attach,
          if i.1 % Q = r.1 then
            logNatWeight (oddLogSourceIndexToValue i.1) /
              logFinsetMass (oddLogWindow lo hi) else 0 := by
          apply Finset.sum_congr rfl
          intro i hiS
          rw [oddLogSourceIndexPMF_apply_toReal]
          by_cases hir : i.1 % Q = r.1
          · simp [hir]
          · have hne : r ≠ ⟨i.1 % Q, Nat.mod_lt i.1 hQ⟩ := by
              intro h
              exact hir (Fin.ext_iff.mp h.symm)
            simp [hir, hne]
    _ =
        ∑ i ∈ oddLogSourceIndexWindow lo hi,
          if i % Q = r.1 then
              logNatWeight (oddLogSourceIndexToValue i) /
              logFinsetMass (oddLogWindow lo hi) else 0 := by
          simpa using
            (Finset.sum_attach (oddLogSourceIndexWindow lo hi)
              (fun i : ℕ => if i % Q = r.1 then
                logNatWeight (oddLogSourceIndexToValue i) /
                  logFinsetMass (oddLogWindow lo hi) else (0 : ℝ)))
    _ = (∑ i ∈ (oddLogSourceIndexWindow lo hi).filter
            (fun i => i % Q = r.1),
          logNatWeight (oddLogSourceIndexToValue i)) /
        logFinsetMass (oddLogWindow lo hi) := by
          rw [Finset.sum_filter, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i hiS
          by_cases hir : i % Q = r.1 <;> simp [hir]
    _ = antitoneResidueClassSum (lo / 2) ((hi - 1) / 2) Q
          (fun i => logNatWeight (oddLogSourceIndexToValue i)) r /
        logFinsetMass (oddLogWindow lo hi) := by
          rw [oddLogSourceIndexWindow_eq_Icc hlo hlohi]
          rfl

/-- Full-L1 discrepancy of logarithmic source-index residues from the uniform
law on `Fin Q`. -/
theorem taoTV_oddLogSourceIndexResidueLaw_uniform_le
    {lo hi Q : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) (hQ : 0 < Q) :
    taoTV (oddLogSourceIndexResidueLaw lo hi hmass Q hQ)
        (positiveFinUniformPMF Q hQ) ≤
      (Q : ℝ) /
        ((lo : ℝ) * logFinsetMass (oddLogWindow lo hi)) := by
  let w : ℕ → ℝ := fun i => logNatWeight (oddLogSourceIndexToValue i)
  let A := lo / 2
  let B := (hi - 1) / 2
  let Z : ℝ := ∑ r : Fin Q, antitoneResidueClassSum A B Q w r
  letI : NeZero Q := ⟨Nat.ne_of_gt hQ⟩
  have hZ : 0 < Z := by
    dsimp [Z]
    rw [sum_antitoneResidueClassSum hQ]
    exact (sum_oddLogSourceIndexWeight_eq_logFinsetMass hlo hlohi).symm ▸ hmass
  have hraw := antitoneResidueClassSum_fullL1_le hQ w
    oddLogSourceIndexWeight_antitone oddLogSourceIndexWeight_nonneg hZ
  have hweight : w A ≤ 1 / (lo : ℝ) :=
    oddLogSourceIndexWeight_lo_div_two_le hlo
  change (∑ r : Fin Q,
      |(oddLogSourceIndexResidueLaw lo hi hmass Q hQ r).toReal -
        (positiveFinUniformPMF Q hQ r).toReal|) ≤
    (Q : ℝ) / ((lo : ℝ) * logFinsetMass (oddLogWindow lo hi))
  simp_rw [oddLogSourceIndexResidueLaw_apply_toReal hlo hlohi hmass hQ]
  have huniform (r : Fin Q) :
      (positiveFinUniformPMF Q hQ r).toReal = 1 / (Q : ℝ) := by
    simp [positiveFinUniformPMF, PMF.uniformOfFintype_apply,
      Fintype.card_fin, ENNReal.toReal_inv]
  simp_rw [huniform]
  have hZeq : Z = logFinsetMass (oddLogWindow lo hi) := by
    dsimp [Z]
    rw [sum_antitoneResidueClassSum hQ]
    exact sum_oddLogSourceIndexWeight_eq_logFinsetMass hlo hlohi
  rw [← hZeq]
  exact calc
      (∑ r : Fin Q,
          |antitoneResidueClassSum A B Q w r / Z - 1 / (Q : ℝ)|) ≤
          (Q : ℝ) * w A / Z := hraw
      _ ≤ (Q : ℝ) * (1 / (lo : ℝ)) / Z := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hweight (Nat.cast_nonneg Q)) hZ.le
      _ = (Q : ℝ) / ((lo : ℝ) * Z) := by
        field_simp

/-- The odd residue represented by a source-index residue modulo `2^K`. -/
def oddPowTwoCoordinate (K : ℕ) (j : Fin (2 ^ K)) :
    ZMod (2 ^ (K + 1)) :=
  (2 * j.1 + 1 : ℕ)

@[simp]
theorem oddPowTwoCoordinate_val (K : ℕ) (j : Fin (2 ^ K)) :
    (oddPowTwoCoordinate K j).val = 2 * j.1 + 1 := by
  apply ZMod.val_natCast_of_lt
  rw [pow_succ]
  omega

theorem oddPowTwoCoordinate_val_odd (K : ℕ) (j : Fin (2 ^ K)) :
    Odd (oddPowTwoCoordinate K j).val := by
  rw [oddPowTwoCoordinate_val]
  exact ⟨j.1, by omega⟩

/-- Numeric odd coordinates parameterize all odd residues modulo `2^(K+1)`. -/
noncomputable def oddPowTwoCoordinateEquiv (K : ℕ) :
    Fin (2 ^ K) ≃ {r : ZMod (2 ^ (K + 1)) // Odd r.val} where
  toFun j := ⟨oddPowTwoCoordinate K j, oddPowTwoCoordinate_val_odd K j⟩
  invFun r := ⟨(r.1.val - 1) / 2, by
    have hodd : r.1.val % 2 = 1 := Nat.odd_iff.mp r.2
    have hlt := r.1.val_lt
    have hpow : 2 ^ (K + 1) = 2 ^ K * 2 := by rw [pow_succ]
    omega⟩
  left_inv j := by
    apply Fin.ext
    change ((oddPowTwoCoordinate K j).val - 1) / 2 = j.1
    rw [oddPowTwoCoordinate_val]
    omega
  right_inv r := by
    apply Subtype.ext
    change ((2 * ((r.1.val - 1) / 2) + 1 : ℕ) :
        ZMod (2 ^ (K + 1))) = r.1
    have hodd : r.1.val % 2 = 1 := Nat.odd_iff.mp r.2
    rw [show 2 * ((r.1.val - 1) / 2) + 1 = r.1.val by omega]
    exact ZMod.natCast_zmod_val r.1

/-- Uniform finite laws are invariant under relabeling by an equivalence. -/
private theorem uniformOfFintype_map_equiv
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro a hne
    have hmiss : b ≠ e a := by
      intro h
      apply hne
      exact e.injective (by simpa using h.symm)
    simp [hmiss]

/-- The arithmetic odd-coordinate uniform law is the canonical odd-residue
law used by Proposition 1.9. -/
theorem positiveFinUniformPMF_map_oddPowTwoCoordinate
    (K : ℕ) :
    (positiveFinUniformPMF (2 ^ K) (pow_pos (by omega) K)).map
        (oddPowTwoCoordinate K) =
      taoUniformOddResiduePMF K := by
  let e : Fin (2 ^ K) ≃ HeadTrueParityWords K :=
    (oddPowTwoCoordinateEquiv K).trans
      (oddResiduesEquivHeadTrueParityWords K)
  have he (j : Fin (2 ^ K)) :
      headTrueParityWordResidue K (e j) = oddPowTwoCoordinate K j := by
    let r : {r : ZMod (2 ^ (K + 1)) // Odd r.val} :=
      oddPowTwoCoordinateEquiv K j
    have h := congrArg Subtype.val
      ((oddResiduesEquivHeadTrueParityWords K).symm_apply_apply r)
    exact h
  letI : NeZero (2 ^ K) := ⟨ne_of_gt (pow_pos (by omega) K)⟩
  rw [taoUniformOddResiduePMF]
  change (PMF.uniformOfFintype (Fin (2 ^ K))).map
      (oddPowTwoCoordinate K) =
    (PMF.uniformOfFintype (HeadTrueParityWords K)).map
      (headTrueParityWordResidue K)
  rw [← uniformOfFintype_map_equiv e, PMF.map_comp]
  apply congrArg (fun f => (PMF.uniformOfFintype (Fin (2 ^ K))).map f)
  funext j
  exact (he j).symm

/-- Convert an odd-window value to the neutral odd source type. -/
def oddLogWindowValueToOddNat {lo hi : ℕ} :
    {N : ℕ // N ∈ oddLogWindow lo hi} → TaoOddNat :=
  fun N => ⟨N.1, Nat.odd_iff.mpr (oddLogWindow_mem.mp N.2).2.2⟩

/-- Odd-value logarithmic window PMF on the neutral Proposition 1.9 source. -/
noncomputable def oddLogWindowOddNatPMF (lo hi : ℕ)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) : PMF TaoOddNat :=
  (oddLogWindowPMF lo hi hmass).map oddLogWindowValueToOddNat

/-- Convert a source index directly to its represented odd source value. -/
def oddLogSourceIndexToOddNat {lo hi : ℕ} :
    {i : ℕ // i ∈ oddLogSourceIndexWindow lo hi} → TaoOddNat :=
  fun i => ⟨oddLogSourceIndexToValue i.1, by
    exact Nat.odd_iff.mpr (oddLogSourceIndexToValue_mod_two i.1)⟩

theorem oddLogSourceIndexPMF_map_oddNat_eq_oddLogWindowOddNatPMF
    {lo hi : ℕ} (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) :
    (oddLogSourceIndexPMF lo hi hmass).map oddLogSourceIndexToOddNat =
      oddLogWindowOddNatPMF lo hi hmass := by
  rw [oddLogWindowOddNatPMF,
    ← oddLogSourceIndexPMF_map_value_eq_oddLogWindowPMF hmass,
    PMF.map_comp]
  apply congrArg
    (fun f => (oddLogSourceIndexPMF lo hi hmass).map f)
  funext i
  apply Subtype.ext
  rfl

/-- Reducing a source index modulo `2^K` and then taking its odd coordinate
agrees with reducing the represented odd value modulo `2^(K+1)`. -/
theorem oddPowTwoCoordinate_mod_sourceIndex (K i : ℕ) :
    oddPowTwoCoordinate K
        ⟨i % (2 ^ K), Nat.mod_lt i (pow_pos (by omega) K)⟩ =
      ((oddLogSourceIndexToValue i : ℕ) : ZMod (2 ^ (K + 1))) := by
  apply (ZMod.natCast_eq_natCast_iff
    (2 * (i % (2 ^ K)) + 1) (oddLogSourceIndexToValue i)
    (2 ^ (K + 1))).mpr
  have hmod := (Nat.mod_modEq i (2 ^ K)).mul_left' 2
  have hadd := hmod.add_right 1
  simpa [oddLogSourceIndexToValue, pow_succ, Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc] using hadd

/-- The low source-index residue law pushes to the Proposition 1.9 source
residue law through the same odd coordinate. -/
theorem oddLogSourceIndexResidueLaw_map_oddPowTwoCoordinate
    {lo hi : ℕ} (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) (K : ℕ) :
    (oddLogSourceIndexResidueLaw lo hi hmass (2 ^ K)
        (pow_pos (by omega) K)).map (oddPowTwoCoordinate K) =
      taoProp19SourceResidueLaw (oddLogWindowOddNatPMF lo hi hmass) (K + 1) := by
  rw [← oddLogSourceIndexPMF_map_oddNat_eq_oddLogWindowOddNatPMF hmass]
  unfold oddLogSourceIndexResidueLaw taoProp19SourceResidueLaw
  rw [PMF.map_comp, PMF.map_comp]
  apply congrArg
    (fun f => (oddLogSourceIndexPMF lo hi hmass).map f)
  funext i
  exact oddPowTwoCoordinate_mod_sourceIndex K i.1

theorem positiveFinUniformPMF_map_oddPowTwoCoordinate_eq_canonical
    (K : ℕ) :
    (positiveFinUniformPMF (2 ^ K) (pow_pos (by omega) K)).map
        (oddPowTwoCoordinate K) =
      taoCanonicalUniformOddResiduePMF (K + 1) := by
  simpa [taoCanonicalUniformOddResiduePMF] using
    positiveFinUniformPMF_map_oddPowTwoCoordinate K

/-- Finite logarithmic odd windows are close to the canonical odd-residue law
whenever the reciprocal lower endpoint is small compared with their total
harmonic mass.  The distance is Tao's full L1 convention. -/
theorem taoTV_oddLogWindow_sourceResidue_canonical_le
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) (K : ℕ) :
    taoTV
        (taoProp19SourceResidueLaw
          (oddLogWindowOddNatPMF lo hi hmass) (K + 1))
        (taoCanonicalUniformOddResiduePMF (K + 1)) ≤
      ((2 ^ K : ℕ) : ℝ) /
        ((lo : ℝ) * logFinsetMass (oddLogWindow lo hi)) := by
  let hQ : 0 < 2 ^ K := pow_pos (by omega) K
  have hmap := taoTV_map_le
    (oddLogSourceIndexResidueLaw lo hi hmass (2 ^ K) hQ)
    (positiveFinUniformPMF (2 ^ K) hQ)
    (oddPowTwoCoordinate K)
  rw [oddLogSourceIndexResidueLaw_map_oddPowTwoCoordinate,
    positiveFinUniformPMF_map_oddPowTwoCoordinate_eq_canonical] at hmap
  exact hmap.trans
    (taoTV_oddLogSourceIndexResidueLaw_uniform_le hlo hlohi hmass hQ)

example :
    oddLogSourceIndexWindow 1 1 = Finset.Icc 0 0 := by
  decide

example :
    oddLogSourceIndexWindow 2 6 = Finset.Icc 1 2 := by
  decide

example :
    oddLogSourceIndexWindow 3 4 = Finset.Icc 1 1 := by
  decide

example :
    (oddPowTwoCoordinate 0 ⟨0, by decide⟩).val = 1 := by
  decide

end Tao
end Erdos1135
