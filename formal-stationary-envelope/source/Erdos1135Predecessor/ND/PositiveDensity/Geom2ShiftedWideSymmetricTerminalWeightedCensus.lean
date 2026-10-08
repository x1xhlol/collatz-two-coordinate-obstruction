/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalCapOneCompression

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

theorem terminal_source_residue_sum_le
    (S : Finset ℕ) (q : ℕ) (X : ℝ) (hX : 0 < X)
    (hQ : ((3 ^ q : ℕ) : ℝ) ≤ X)
    (hS : ∀ x ∈ S, (x : ℝ) < 32 * X)
    (psi : ZMod (3 ^ q) → ℝ) (hp : ∀ y, 0 ≤ psi y) :
    (∑ x ∈ S, psi (x : ZMod (3 ^ q))) ≤
      33 * X * ndTernaryUniformMean q psi := by
  classical
  let Q := 3 ^ q
  let N := Nat.ceil (32 * X / (Q : ℝ))
  let cell : ℕ → ℕ × ZMod Q := fun x => (x / Q, (x : ZMod Q))
  have hQpos : (0 : ℝ) < Q := by dsimp [Q]; positivity
  have hinj : Function.Injective cell := by
    intro x y h
    have hd : x / Q = y / Q := congrArg Prod.fst h
    have hm : x % Q = y % Q := by
      have hv := congrArg (fun p : ℕ × ZMod Q => p.2.val) h
      simpa [cell, ZMod.val_natCast] using hv
    calc
      x = x % Q + Q * (x / Q) := (Nat.mod_add_div x Q).symm
      _ = y % Q + Q * (y / Q) := by rw [hm, hd]
      _ = y := Nat.mod_add_div y Q
  have hsub : S.image cell ⊆ (Finset.range N).product Finset.univ := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr ?_, Finset.mem_univ _⟩
    apply Nat.lt_ceil.mpr
    apply (lt_div_iff₀ hQpos).2
    have hd : ((x / Q : ℕ) : ℝ) * (Q : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self x Q
    exact hd.trans_lt (hS x hx)
  have hsum : 0 ≤ ∑ y, psi y := Finset.sum_nonneg fun y _ => hp y
  have hN : (N : ℝ) ≤ 32 * X / (Q : ℝ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  calc
    _ = ∑ c ∈ S.image cell, psi c.2 := by
      rw [Finset.sum_image]
      exact fun x _ y _ h => hinj h
    _ ≤ ∑ c ∈ (Finset.range N).product Finset.univ, psi c.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c _ _ => hp c.2)
    _ = (N : ℝ) * ∑ y, psi y := by
      calc
        _ = ∑ _x ∈ Finset.range N, ∑ y : ZMod Q, psi y := Finset.sum_product _ _ _
        _ = _ := by simp [Q]
    _ ≤ (32 * X / (Q : ℝ) + 1) * ∑ y, psi y := mul_le_mul_of_nonneg_right hN hsum
    _ ≤ (33 * X / (Q : ℝ)) * ∑ y, psi y := by
      apply mul_le_mul_of_nonneg_right _ hsum
      apply (le_div_iff₀ hQpos).2
      rw [add_mul, div_mul_cancel₀ _ hQpos.ne', one_mul]
      change (Q : ℝ) ≤ X at hQ
      nlinarith
    _ = _ := by unfold ndTernaryUniformMean ndTernaryUniformScale; dsimp [Q]; ring

def ndTerminalResidueFan (q j : ℕ) (y : ZMod (3 ^ q)) : ZMod (3 ^ q) :=
  ((fun z : ZMod (3 ^ q) => 4 * z + 1)^[j]) y

theorem terminalResidueFan_natCast (q j x : ℕ) :
    ndTerminalResidueFan q j (x : ZMod (3 ^ q)) =
      (ndTerminalSourceFan j x : ZMod (3 ^ q)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [ndTerminalResidueFan, ndTerminalSourceFan,
      Function.iterate_succ_apply', Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at ih ⊢
    rw [ih]
    simp

theorem terminalResidueFan_bijective (q j : ℕ) :
    Function.Bijective (ndTerminalResidueFan q j) := by
  have h4 : IsUnit (4 : ZMod (3 ^ q)) := by
    have h := (Tao.taoCor63TwoPowUnit q 2).isUnit
    norm_num [Tao.taoCor63TwoPowUnit_coe] at h
    exact h
  have hstep : Function.Bijective (fun z : ZMod (3 ^ q) => 4 * z + 1) := by
    have hinj : Function.Injective (fun z : ZMod (3 ^ q) => 4 * z + 1) := by
      intro x y h
      exact h4.mul_left_cancel (add_right_cancel h)
    exact ⟨hinj, Finite.surjective_of_injective hinj⟩
  exact hstep.iterate j

theorem terminalResidueFan_fullMean (q j : ℕ) (f : ZMod (3 ^ q) → ℝ) :
    ndTernaryUniformMean q (fun y => f (ndTerminalResidueFan q j y)) =
      ndTernaryUniformMean q f := by
  unfold ndTernaryUniformMean
  rw [(terminalResidueFan_bijective q j).sum_comp f]

theorem terminal_fan_coeff_sum_le (J : ℕ) :
    (∑ j : Fin J, (1 / 4 : ℝ) ^ j.val) ≤ 4 / 3 := by
  rw [Fin.sum_univ_eq_sum_range]
  have h := geom_sum_mul_of_le_one (show (1 / 4 : ℝ) ≤ 1 by norm_num) J
  have hp : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ J := by positivity
  nlinarith

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem fullTerminal_weighted_source_charge
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (hseedNeOne : ∀ i, U.state.root i ≠ 1)
    (hseedHitsOne : ∀ i, ∃ m : ℕ, (Tao.syracuse^[m]) (U.state.root i) = 1)
    (X : ℝ) (hX : 0 < X)
    (hsource : ∀ z : U.FullTerminalAt cap n shift K,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ))
    (psi : ℕ → ℝ) (hp : ∀ x, 0 ≤ psi x) :
    letI := (U.forwardIterate cap n).state.labelFintype
    (∑ z : U.FullTerminalAt cap n shift K,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
        (U.forwardIterate cap n).state.outerWeight z *
        psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)) ≤
      (U.parentSourcePotential / X) *
        ∑ x ∈ U.fullTerminalSources cap n shift K, psi x := by
  classical
  letI := U.state.labelFintype
  letI := (U.forwardIterate cap n).state.labelFintype
  let W := fun z : U.FullTerminalAt cap n shift K =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
      (U.forwardIterate cap n).state.outerWeight z
  let P := fun i : U.state.Label => (U.state.root i : ℝ) * U.state.outerWeight i
  let cell := fun z : U.FullTerminalAt cap n shift K =>
    (fullTerminalAncestor z, ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)
  let sources := U.fullTerminalSources cap n shift K
  have hinj : Function.Injective cell := by
    intro z w h
    exact fullTerminal_eq_of_successfulSeed_ancestor_source_eq hseedNeOne hseedHitsOne
      (congrArg Prod.fst h) (congrArg Prod.snd h)
  have hsub : Finset.univ.image cell ⊆ Finset.univ.product sources := by
    intro c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  have hmul : X * (∑ z, W z * psi (cell z).2) ≤
      U.parentSourcePotential * ∑ x ∈ sources, psi x := by
    calc
      _ = ∑ z, (X * W z) * psi (cell z).2 := by rw [Finset.mul_sum]; simp [mul_assoc]
      _ ≤ ∑ z, P (cell z).1 * psi (cell z).2 := by
        apply Finset.sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_right _ (hp _)
        exact (mul_le_mul_of_nonneg_right (hsource z)
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg _
            (U.forwardIterate cap n).state.weight_nonneg z)).trans
          (U.fullTerminal_source_mul_weight_le_frozenOwner cap n shift K z)
      _ = ∑ c ∈ Finset.univ.image cell, P c.1 * psi c.2 := by
        rw [Finset.sum_image]; exact fun a _ b _ h => hinj h
      _ ≤ ∑ c ∈ Finset.univ.product sources, P c.1 * psi c.2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro c _ _
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (U.state.weight_nonneg c.1)) (hp _)
      _ = _ := by
        calc
          _ = ∑ i : U.state.Label, ∑ x ∈ sources, P i * psi x := Finset.sum_product _ _ _
          _ = _ := by
            simp only [← Finset.mul_sum, ← Finset.sum_mul]
            unfold parentSourcePotential ndGeom2PredictableRootSideParentSourcePotential
              NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorAllLabels
            rfl
  have hdiv := (le_div_iff₀ hX).2 (by simpa [mul_comm] using hmul)
  simpa [W, cell, sources, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

theorem fullTerminal_weighted_residue_census
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (hseedNeOne : ∀ i, U.state.root i ≠ 1)
    (hseedHitsOne : ∀ i, ∃ m : ℕ, (Tao.syracuse^[m]) (U.state.root i) = 1)
    (q : ℕ) (X : ℝ) (hX : 0 < X) (hQ : ((3 ^ q : ℕ) : ℝ) ≤ X)
    (hsource : ∀ z : U.FullTerminalAt cap n shift K,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) ∧
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X)
    (psi : ZMod (3 ^ q) → ℝ) (hp : ∀ y, 0 ≤ psi y) :
    letI := (U.forwardIterate cap n).state.labelFintype
    (∑ z : U.FullTerminalAt cap n shift K,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
        (U.forwardIterate cap n).state.outerWeight z *
        psi (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ZMod (3 ^ q))) ≤
      33 * U.parentSourcePotential * ndTernaryUniformMean q psi := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  have hc := U.fullTerminal_weighted_source_charge cap n shift K hseedNeOne hseedHitsOne
    X hX (fun z => (hsource z).1) (fun x => psi (x : ZMod (3 ^ q))) (fun x => hp _)
  have hs := terminal_source_residue_sum_le (U.fullTerminalSources cap n shift K) q X hX hQ
    (fun x hx => by obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx; exact (hsource z).2) psi hp
  calc
    _ ≤ _ := hc
    _ ≤ (U.parentSourcePotential / X) * (33 * X * ndTernaryUniformMean q psi) :=
      mul_le_mul_of_nonneg_left hs (div_nonneg U.frozenSourcePotential_nonneg hX.le)
    _ = _ := by field_simp

theorem terminal_conductor_room_of_pos_mark
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k : ℕ) (hk : k ≤ (U.forwardIterate cap n).floor)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i))
    (hT : 0 < U.forwardCoreTerminalUnitMass cap width n K k X hX hi) :
    ((3 ^ k : ℕ) : ℝ) < X := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  have hfan := U.forwardCoreTerminalUnitMass_le_full_cap_one_fan cap width n K k X hX hi
  obtain ⟨z⟩ : Nonempty (V.FullTerminalIncidence X hX hi) := by
    by_contra h
    haveI : IsEmpty (V.FullTerminalIncidence X hX hi) := not_nonempty_iff.mp h
    have hz : U.forwardCoreTerminalUnitMass cap width n K k X hX hi ≤ 0 := by
      simpa using hfan
    linarith
  have hb := V.floor_twoHundred
  have hr : ∀ i, 16 ^ V.floor ≤ V.state.root i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (V.floor_le_base i)).trans (V.state.rootLower i)
  have hbound := ndGeom2RootSideCommonFloor_capOne_source_bounds V.state.root_odd
    (by omega) hr z
  have hshift := V.fullTerminalShift_spec X hX hi
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
  have hupper : (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) < 32 * X := by
    nlinarith [hbound.2, hshift.2.2]
  have hlower : 16 ^ V.floor ≤ ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z :=
    (Nat.pow_le_pow_right (by norm_num) (show V.floor ≤
      V.state.base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) + V.floor / 100 by
        have := V.floor_le_base (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z); omega)).trans
      (ndGeom2RootSideCommonFloorShifted_sourceLower V.state.root_odd hb
        V.floor_le_base V.state.rootLower z)
  have h32 : 32 ≤ 2 ^ V.floor := by
    have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show 5 ≤ V.floor by omega)
    simpa using h
  have hpower : 32 * 3 ^ k ≤ 16 ^ V.floor := by
    calc
      _ ≤ 2 ^ V.floor * 3 ^ V.floor := Nat.mul_le_mul h32
        (Nat.pow_le_pow_right (by norm_num) hk)
      _ = 6 ^ V.floor := by rw [← mul_pow]; norm_num
      _ ≤ _ := Nat.pow_le_pow_left (by norm_num) _
  have hnat := hpower.trans hlower
  have hreal : (32 : ℝ) * ((3 ^ k : ℕ) : ℝ) ≤
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) := by exact_mod_cast hnat
  linarith

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
