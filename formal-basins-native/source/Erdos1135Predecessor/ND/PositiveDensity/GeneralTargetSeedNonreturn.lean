/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.StoppingTime
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideGeometricFullTerminalCount
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideHistoryPhysicalCollision
import Mathlib.Dynamics.PeriodicPts.Defs

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

theorem hit_time_unique_of_no_return {α : Type*} {f : α → α}
    {source target : α} {d e : ℕ}
    (hreturn : ∀ k : ℕ, 0 < k → (f^[k]) target ≠ target)
    (hd : (f^[d]) source = target) (he : (f^[e]) source = target) : d = e := by
  suffices h : ∀ d e : ℕ, (f^[d]) source = target →
      (f^[e]) source = target → d < e → False by
    exact le_antisymm (le_of_not_gt (h e d he hd)) (le_of_not_gt (h d e hd he))
  intro d e hd he hde
  apply hreturn (e - d) (by omega)
  have heq : e = (e - d) + d := by omega
  rw [heq, Function.iterate_add_apply, hd] at he
  exact he

theorem exists_bound_predecessor_no_return (f : ℕ → ℕ) (a : ℕ) :
    ∃ B : ℕ, ∀ r : ℕ, B < r → (∃ m : ℕ, (f^[m]) r = a) →
      ∀ k : ℕ, 0 < k → (f^[k]) r ≠ r := by
  classical
  by_cases hperiodic : ∃ p : ℕ, 0 < p ∧ (f^[p]) a = a
  · obtain ⟨p, hp, hpa⟩ := hperiodic
    let B := (Finset.range p).sup (fun j => (f^[j]) a)
    refine ⟨B, ?_⟩
    intro r hr ⟨m, hm⟩ k hk hkr
    have hkp : Function.IsPeriodicPt f k r := hkr
    have hmp : m ≤ m * k := by
      simpa using Nat.mul_le_mul_left m (show 1 ≤ k by omega)
    have hback : (f^[m * k - m]) a = r := by
      rw [← hm, ← Function.iterate_add_apply, Nat.sub_add_cancel hmp]
      exact hkp.const_mul m
    have hpp : Function.IsPeriodicPt f p a := hpa
    have hres : (f^[(m * k - m) % p]) a = r :=
      (hpp.iterate_mod_apply _).trans hback
    have hle : (f^[(m * k - m) % p]) a ≤ B :=
      Finset.le_sup (f := fun j => (f^[j]) a)
        (Finset.mem_range.mpr (Nat.mod_lt _ hp))
    rw [hres] at hle
    exact (Nat.not_lt_of_ge hle) hr
  · refine ⟨0, ?_⟩
    intro r _ ⟨m, hm⟩ k hk hkr
    apply hperiodic
    have hkp : Function.IsPeriodicPt f k r := hkr
    have ha := hkp.apply_iterate m
    rw [hm] at ha
    exact ⟨k, hk, ha⟩

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem fullTerminal_eq_of_nonreturningSeed_ancestor_source_eq
    {U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState}
    {cap : ℕ → ℕ} {n : ℕ} {shift : (U.forwardIterate cap n).state.Label → ℕ} {K : ℕ}
    (hseed : ∀ i k, 0 < k → (Tao.syracuse^[k]) (U.state.root i) ≠ U.state.root i)
    {z w : U.FullTerminalAt cap n shift K}
    (ha : fullTerminalAncestor z = fullTerminalAncestor w)
    (hs : ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z =
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource w) : z = w := by
  let p := U.fullTerminalPath cap n shift K z
  let q := U.fullTerminalPath cap n shift K w
  have hq : (Tao.syracuse^[q.depth])
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) =
      U.state.root (fullTerminalAncestor z) := by rw [hs, ha]; exact q.terminal_eq
  have hd := hit_time_unique_of_no_return (hseed _) p.terminal_eq hq
  have hw := NDGeom2RootSideSyracusePath.word_eq_of_source_depth_eq p q hs hd
  apply fullTerminal_eq_of_ancestor_word_eq ha
  apply List.reverse_injective
  exact (U.fullTerminalPath_word_eq_reverse cap n shift K z).symm.trans
    (hw.trans (U.fullTerminalPath_word_eq_reverse cap n shift K w))

theorem fullTerminal_reaches_target_of_seed_reaches
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K a : ℕ)
    (hseed : ∀ i, Erdos1135Predecessor.Reaches (U.state.root i) a)
    (z : U.FullTerminalAt cap n shift K) :
    Erdos1135Predecessor.Reaches (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) a := by
  let p := U.fullTerminalPath cap n shift K z
  have h := Tao.reaches_syracuse_iterate p.sourceOdd p.depth
  rw [p.terminal_eq] at h
  exact h.trans (hseed _)

theorem fullTerminal_weighted_source_charge_of_nonreturningSeed
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (hseed : ∀ i k, 0 < k → (Tao.syracuse^[k]) (U.state.root i) ≠ U.state.root i)
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
  have hinj : Function.Injective cell := fun z w h =>
    fullTerminal_eq_of_nonreturningSeed_ancestor_source_eq hseed
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

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState
end Erdos1135Predecessor.ND.PositiveDensity
