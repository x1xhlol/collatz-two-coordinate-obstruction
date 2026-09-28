/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootSideCommonFloorFullTerminalPhysical

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem iterate_succ_eq_tail
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) :
    U.iterate cap (n + 1) = (U.next (cap 0)).iterate (ndGeom2RootSideCapTail cap) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (U.iterate cap (n + 1)).next (cap (n + 1)) =
        ((U.next (cap 0)).iterate (ndGeom2RootSideCapTail cap) n).next (cap (n + 1))
      exact congrArg (fun V => V.next (cap (n + 1))) ih

def forwardIterate (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : ℕ → NDGeom2ShiftedWideSymmetricRootSideUniformFloorState
  | 0 => U
  | n + 1 => (U.next (cap 0)).forwardIterate (ndGeom2RootSideCapTail cap) n

theorem forwardIterate_eq_iterate
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) : U.forwardIterate cap n = U.iterate cap n := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      simp only [forwardIterate, ih]
      exact (U.iterate_succ_eq_tail cap n).symm

def forwardAncestor (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : (n : ℕ) → (U.forwardIterate cap n).state.Label → U.state.Label
  | 0, i => i
  | n + 1, z => ndGeom2PredictableRootSideUnitChildIncidenceLabel
      ((U.next (cap 0)).forwardAncestor (ndGeom2RootSideCapTail cap) n z)

def forwardFirstIncidence (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap (n + 1)).state.Label) :
    (U.next (cap 0)).state.Label :=
  (U.next (cap 0)).forwardAncestor (ndGeom2RootSideCapTail cap) n z

def forwardWord (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : (n : ℕ) → (U.forwardIterate cap n).state.Label → List ℕ+
  | 0, _ => []
  | n + 1, z =>
      ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord
        (U.forwardFirstIncidence cap n z) ++
      (U.next (cap 0)).forwardWord (ndGeom2RootSideCapTail cap) n z

private theorem packetRootLower
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) :
    ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
  (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)

theorem forwardLabel_tail_eq_of_append
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (z w : (U.forwardIterate cap n).state.Label) (tailZ tailW : List ℕ+)
    (ha : U.forwardAncestor cap n z = U.forwardAncestor cap n w)
    (hw : U.forwardWord cap n z ++ tailZ = U.forwardWord cap n w ++ tailW) :
    z = w ∧ tailZ = tailW := by
  induction n generalizing U cap with
  | zero => exact ⟨ha, by simpa [forwardWord] using hw⟩
  | succ n ih =>
      let iz := U.forwardFirstIncidence cap n z
      let iw := U.forwardFirstIncidence cap n w
      have hpz : ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord iz =
          (U.forwardWord cap (n + 1) z ++ tailZ).take
            (ndGeom2PredictableRootSideUnitChildIncidenceDepth iz) := by
        rw [← ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length iz]
        simp only [forwardWord, List.append_assoc, iz, List.take_left]
      have hpw : ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord iw =
          (U.forwardWord cap (n + 1) z ++ tailZ).take
            (ndGeom2PredictableRootSideUnitChildIncidenceDepth iw) := by
        rw [hw, ← ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length iw]
        simp only [forwardWord, List.append_assoc, iw, List.take_left]
      have hf : iz = iw :=
        ndGeom2PredictableRootSideUnitChildIncidence_eq_of_label_eq_of_commonPrefix
          U.state.root_odd (by have h := U.floor_twoHundred; omega)
          U.packetRootLower ha hpz hpw
      have ht : (U.next (cap 0)).forwardWord (ndGeom2RootSideCapTail cap) n z ++ tailZ =
          (U.next (cap 0)).forwardWord (ndGeom2RootSideCapTail cap) n w ++ tailW := by
        change (_ ++ _) ++ tailZ = (_ ++ _) ++ tailW at hw
        change (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord iz ++ _) ++ tailZ =
          (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord iw ++ _) ++ tailW at hw
        rw [hf] at hw
        exact List.append_cancel_left (by simpa only [List.append_assoc] using hw)
      exact ih (U := U.next (cap 0)) (cap := ndGeom2RootSideCapTail cap) z w hf ht

abbrev FullTerminalAt (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ) :=
  NDGeom2PredictableRootSideBoundedOvershootIncidence
    (U.forwardIterate cap n).state.Label (U.forwardIterate cap n).state.root
    (fun _ => (U.forwardIterate cap n).floor) shift K

def fullTerminalAncestor {U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState}
    {cap : ℕ → ℕ} {n : ℕ} {shift : (U.forwardIterate cap n).state.Label → ℕ} {K : ℕ}
    (z : U.FullTerminalAt cap n shift K) : U.state.Label :=
  U.forwardAncestor cap n (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)

def fullTerminalWord {U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState}
    {cap : ℕ → ℕ} {n : ℕ} {shift : (U.forwardIterate cap n).state.Label → ℕ} {K : ℕ}
    (z : U.FullTerminalAt cap n shift K) : List ℕ+ :=
  U.forwardWord cap n (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z) ++
    ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z

theorem fullTerminal_eq_of_ancestor_word_eq
    {U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState}
    {cap : ℕ → ℕ} {n : ℕ} {shift : (U.forwardIterate cap n).state.Label → ℕ} {K : ℕ}
    {z w : U.FullTerminalAt cap n shift K}
    (ha : fullTerminalAncestor z = fullTerminalAncestor w)
    (hw : fullTerminalWord z = fullTerminalWord w) : z = w := by
  have h := U.forwardLabel_tail_eq_of_append cap n
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel w)
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z)
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord w) ha hw
  apply ndGeom2PredictableRootSideBoundedOvershootIncidence_eq_of_label_eq_of_commonPrefix h.1
    (fullRootSide := ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z)
  · rw [← ndGeom2PredictableRootSideBoundedOvershootIncidence_word_length z, List.take_length]
  · rw [h.2, ← ndGeom2PredictableRootSideBoundedOvershootIncidence_word_length w,
      List.take_length]

def fullTerminalPath (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) : (n : ℕ) →
    (shift : (U.forwardIterate cap n).state.Label → ℕ) → (K : ℕ) →
    (z : U.FullTerminalAt cap n shift K) →
    NDGeom2RootSideSyracusePath
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)
      (U.state.root (fullTerminalAncestor z))
  | 0, _, _, z => by
      let p := NDGeom2RootSideSyracusePath.nil
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd
          U.state.root_odd (fun _ => by have h := U.floor_twoHundred; omega) U.packetRootLower z)
      exact p.appendRootSideIncidence U.state.root_odd
        (fun _ => by have h := U.floor_twoHundred; omega) U.packetRootLower z
  | n + 1, shift, K, z => by
      let first := U.forwardFirstIncidence cap n
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
      let p := (U.next (cap 0)).fullTerminalPath (ndGeom2RootSideCapTail cap) n shift K z
      exact p.appendRootSideIncidence U.state.root_odd
        (fun _ => by have h := U.floor_twoHundred; omega) U.packetRootLower
        (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical first)

theorem fullTerminalPath_word_eq_reverse
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K) :
    (U.fullTerminalPath cap n shift K z).word = (fullTerminalWord z).reverse := by
  induction n generalizing U cap with
  | zero => rfl
  | succ n ih =>
      change ((U.next (cap 0)).fullTerminalPath (ndGeom2RootSideCapTail cap) n shift K z).word ++
          ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord
            (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical
              (U.forwardFirstIncidence cap n
                (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))) = _
      rw [ih]
      simp only [fullTerminalWord, forwardWord,
        ndGeom2PredictableRootSideBoundedOvershootIncidenceChronologicalWord,
        ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_word,
        List.reverse_append, List.append_assoc]
      rfl

theorem successfulSeed_hit_time_unique
    {source target : ℕ} {d e m : ℕ} (ht : target ≠ 1)
    (hd : (Tao.syracuse^[d]) source = target)
    (he : (Tao.syracuse^[e]) source = target)
    (hm : (Tao.syracuse^[m]) target = 1) : d = e := by
  suffices h : ∀ d e : ℕ, (Tao.syracuse^[d]) source = target →
      (Tao.syracuse^[e]) source = target → d < e → False by
    exact le_antisymm (le_of_not_gt (h e d he hd)) (le_of_not_gt (h d e hd he))
  intro d e hd he hde
  let k := e - d
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hp : (Tao.syracuse^[k]) target = target := by
    have heq : e = k + d := by dsimp [k]; omega
    rw [heq, Function.iterate_add_apply, hd] at he
    exact he
  have hpk : ∀ q, (Tao.syracuse^[q * k]) target = target := by
    intro q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.succ_mul, Function.iterate_add_apply, hp, ih]
  have hf : Tao.syracuse 1 = 1 := by
    rw [Tao.syracuse_eq_ordCompl_two]
    simpa using Nat.ordCompl_self_pow (p := 2) (k := 2) Nat.prime_two
  have hmk : m ≤ m * k := by simpa using Nat.mul_le_mul_left m hk
  have hlate : (Tao.syracuse^[m * k]) target = 1 := by
    calc
      _ = (Tao.syracuse^[(m * k - m) + m]) target := by rw [Nat.sub_add_cancel hmk]
      _ = (Tao.syracuse^[m * k - m]) ((Tao.syracuse^[m]) target) := by
        rw [Function.iterate_add_apply]
      _ = 1 := by rw [hm, Function.iterate_fixed hf]
  exact ht ((hpk m).symm.trans hlate)

theorem fullTerminal_eq_of_successfulSeed_ancestor_source_eq
    {U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState}
    {cap : ℕ → ℕ} {n : ℕ} {shift : (U.forwardIterate cap n).state.Label → ℕ} {K : ℕ}
    (hseedNeOne : ∀ i, U.state.root i ≠ 1)
    (hseedHitsOne : ∀ i, ∃ m : ℕ, (Tao.syracuse^[m]) (U.state.root i) = 1)
    {z w : U.FullTerminalAt cap n shift K}
    (ha : fullTerminalAncestor z = fullTerminalAncestor w)
    (hs : ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z =
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource w) : z = w := by
  let p := U.fullTerminalPath cap n shift K z
  let q := U.fullTerminalPath cap n shift K w
  obtain ⟨m, hm⟩ := hseedHitsOne (fullTerminalAncestor z)
  have hq : (Tao.syracuse^[q.depth])
      (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) =
      U.state.root (fullTerminalAncestor z) := by rw [hs, ha]; exact q.terminal_eq
  have hd := successfulSeed_hit_time_unique (hseedNeOne _) p.terminal_eq hq hm
  have hw := NDGeom2RootSideSyracusePath.word_eq_of_source_depth_eq p q hs hd
  have hpw := U.fullTerminalPath_word_eq_reverse cap n shift K z
  have hqw := U.fullTerminalPath_word_eq_reverse cap n shift K w
  apply fullTerminal_eq_of_ancestor_word_eq ha
  apply List.reverse_injective
  exact hpw.symm.trans (hw.trans hqw)

theorem fullTerminal_source_mul_weight_le_frozenOwner
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (z : U.FullTerminalAt cap n shift K) :
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ) *
        ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
          (U.forwardIterate cap n).state.outerWeight z ≤
      (U.state.root (fullTerminalAncestor z) : ℝ) *
        U.state.outerWeight (fullTerminalAncestor z) := by
  induction n generalizing U cap with
  | zero =>
      have he := ndGeom2PredictableRootSideBoundedOvershootIncidence_source_mul_atom_le_root
        U.state.root_odd (fun _ => by have h := U.floor_twoHundred; omega) U.packetRootLower z
      have h := mul_le_mul_of_nonneg_left he
        (U.state.weight_nonneg (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z))
      change (_ : ℝ) * (_ * _) ≤ _ * _
      simpa only [fullTerminalAncestor, forwardAncestor, forwardIterate,
        mul_assoc, mul_left_comm, mul_comm] using h
  | succ n ih =>
      have ht := ih (U := U.next (cap 0)) (cap := ndGeom2RootSideCapTail cap) shift z
      let first := U.forwardFirstIncidence cap n
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z)
      have he := ndGeom2PredictableRootSideUnitChildIncidence_source_mul_weight_le_parent
        U.state.outerWeight (fun i _ => U.state.weight_nonneg i) U.state.root_odd
        (by have h := U.floor_twoHundred; omega) U.packetRootLower first
      exact ht.trans he

def fullTerminalSources (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ) : Finset ℕ := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  exact Finset.univ.image
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource
      (Label := (U.forwardIterate cap n).state.Label)
      (root := (U.forwardIterate cap n).state.root)
      (base := fun _ => (U.forwardIterate cap n).floor) (shift := shift) (K := K))

def fullTerminalMass (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ) : ℝ := by
  letI := (U.forwardIterate cap n).state.labelFintype
  exact ndGeom2PredictableRootSideBoundedOvershootIncidenceMass
    (U.forwardIterate cap n).state.outerWeight (U.forwardIterate cap n).state.root
    (fun _ => (U.forwardIterate cap n).floor) shift K

theorem fullTerminal_mass_mul_lower_le_frozenPotential_mul_card
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ)
    (shift : (U.forwardIterate cap n).state.Label → ℕ) (K : ℕ)
    (hseedNeOne : ∀ i, U.state.root i ≠ 1)
    (hseedHitsOne : ∀ i, ∃ m : ℕ, (Tao.syracuse^[m]) (U.state.root i) = 1)
    (X : ℝ)
    (hX : ∀ z : U.FullTerminalAt cap n shift K,
      X ≤ (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℝ)) :
    X * U.fullTerminalMass cap n shift K ≤
      U.parentSourcePotential * (U.fullTerminalSources cap n shift K).card := by
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
  calc
    X * U.fullTerminalMass cap n shift K = ∑ z, X * W z := by
      change X * (∑ z, W z) = _
      rw [Finset.mul_sum]
    _ ≤ ∑ z : U.FullTerminalAt cap n shift K, P (fullTerminalAncestor z) := by
      apply Finset.sum_le_sum
      intro z _
      have hw := ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg
        (U.forwardIterate cap n).state.outerWeight
        (U.forwardIterate cap n).state.weight_nonneg z
      exact (mul_le_mul_of_nonneg_right (hX z) hw).trans
        (U.fullTerminal_source_mul_weight_le_frozenOwner cap n shift K z)
    _ = ∑ c ∈ Finset.univ.image cell, P c.1 := by
      rw [Finset.sum_image]
      exact fun a _ b _ h => hinj h
    _ ≤ ∑ c ∈ Finset.univ.product sources, P c.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro c _ _
      exact mul_nonneg (Nat.cast_nonneg _) (U.state.weight_nonneg c.1)
    _ = U.parentSourcePotential * (U.fullTerminalSources cap n shift K).card := by
      calc
        _ = ∑ i : U.state.Label, ∑ _s ∈ sources, P i := Finset.sum_product _ _ _
        _ = _ := ?_
      simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      unfold parentSourcePotential ndGeom2PredictableRootSideParentSourcePotential
        NDGeom2ShiftedWideSymmetricRegenerativeState.rootSideUniformFloorAllLabels
      dsimp only [P, sources]
      ring

theorem fullTerminal_capOne_public_count
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) {C : ℝ} (hC : 250 ≤ C)
    (htarget : ∀ i, U.state.root i ∈ oddSyracuseLogTimeOneSet C)
    (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin
        (U.forwardIterate cap n).floor ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
        (U.forwardIterate cap n).floor ((U.forwardIterate cap n).state.root i)) :
    let shift := (U.forwardIterate cap n).fullTerminalShift X hX hi;
    let sources := U.fullTerminalSources cap n shift 1;
    (∀ source ∈ sources, source ∈ oddSyracuseLogTimeOneSet C ∧
      X ≤ (source : ℝ) ∧ (source : ℝ) < 32 * X) ∧
    X * U.fullTerminalMass cap n shift 1 ≤ U.parentSourcePotential * sources.card := by
  let V := U.forwardIterate cap n
  let shift := V.fullTerminalShift X hX hi
  have ht : ∀ i, V.state.root i ∈ oddSyracuseLogTimeOneSet C := by
    dsimp only [V]
    rw [U.forwardIterate_eq_iterate cap n]
    exact U.iterate_root_mem_same_target cap hC htarget n
  have hs (z : U.FullTerminalAt cap n shift 1) :=
    V.fullTerminal_source_mem_target_and_window X hX hi hC ht z
  have hn : ∀ i, U.state.root i ≠ 1 := by
    intro i
    have hl := U.packetRootLower i
    have h16 : 16 ≤ 16 ^ U.floor := by
      have hfloor := U.floor_twoHundred
      simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 16) (show 1 ≤ U.floor by omega)
    omega
  have hh : ∀ i, ∃ m : ℕ, (Tao.syracuse^[m]) (U.state.root i) = 1 := by
    intro i
    obtain ⟨_, _, m, _, hm⟩ := htarget i
    exact ⟨m, hm⟩
  constructor
  · intro source hsource
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hsource
    exact hs z
  · exact U.fullTerminal_mass_mul_lower_le_frozenPotential_mul_card cap n shift 1
      hn hh X (fun z => (hs z).2.1)

theorem frozenSourcePotential_nonneg
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) :
    0 ≤ U.parentSourcePotential := by
  unfold parentSourcePotential ndGeom2PredictableRootSideParentSourcePotential
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (U.state.weight_nonneg i)

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
