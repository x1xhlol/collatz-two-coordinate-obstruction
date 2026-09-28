/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricReferenceMarkedPhysicalIncidence
import Mathlib.Analysis.SpecificLimits.Normed

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

def ndRootUniformWordAtom (w : List ℕ+) : ℝ :=
  (3 : ℝ) ^ w.length / (2 : ℝ) ^ Tao.taoTupleWeight w

def ndRootUniformWordOffset (w : List ℕ+) : ℝ :=
  (Tao.taoOffsetList w.reverse : ℝ)

theorem rootUniformWordAtom_pos (w : List ℕ+) : 0 < ndRootUniformWordAtom w := by
  unfold ndRootUniformWordAtom
  positivity

theorem rootUniformWordAtom_append (v w : List ℕ+) :
    ndRootUniformWordAtom (v ++ w) = ndRootUniformWordAtom v * ndRootUniformWordAtom w := by
  simp only [ndRootUniformWordAtom, List.length_append, Tao.taoTupleWeight_append, pow_add]
  ring

theorem rootUniformWordOffset_nonneg (w : List ℕ+) : 0 ≤ ndRootUniformWordOffset w := by
  unfold ndRootUniformWordOffset
  exact_mod_cast Tao.taoOffsetList_nonneg w.reverse

theorem rootUniformWordOffset_append (v w : List ℕ+) :
    ndRootUniformWordOffset (v ++ w) =
      ndRootUniformWordOffset v + ndRootUniformWordAtom v * ndRootUniformWordOffset w := by
  unfold ndRootUniformWordOffset ndRootUniformWordAtom
  rw [List.reverse_append, Tao.taoOffsetList_append]
  simp only [List.length_reverse, Tao.taoTupleWeight_reverse,
    Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
  ring

theorem rootUniformWordOffset_le_threeHalves (w : List ℕ+) :
    ndRootUniformWordOffset w ≤ (3 / 2 : ℝ) ^ w.length - 1 := by
  induction w with
  | nil => norm_num [ndRootUniformWordOffset, Tao.taoOffsetList]
  | cons a w ih =>
      have hden : (2 : ℝ) ≤ 2 ^ (a : ℕ) := by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) a.property
      have hnum : 0 ≤ 1 + 3 * ndRootUniformWordOffset w := by
        have := rootUniformWordOffset_nonneg w
        positivity
      have hrec : ndRootUniformWordOffset (a :: w) =
          (1 + 3 * ndRootUniformWordOffset w) / (2 : ℝ) ^ (a : ℕ) := by
        unfold ndRootUniformWordOffset
        rw [Tao.taoOffsetList_reverse_cons]
        push_cast
        rfl
      rw [hrec]
      calc
        _ ≤ (1 + 3 * ndRootUniformWordOffset w) / 2 :=
          div_le_div_of_nonneg_left hnum (by norm_num) hden
        _ ≤ (3 / 2 : ℝ) ^ (a :: w).length - 1 := by
          simp only [List.length_cons, pow_succ]
          linarith

private theorem rootUniform_threeHalves_pow_le_twoPow {d b : ℕ}
    (hd : 5 * d ≤ 8 * b) : (3 / 2 : ℝ) ^ d ≤ 2 ^ b := by
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2) hd
  have hsmall : (3 / 2 : ℝ) ^ 8 ≤ 2 ^ 5 := by norm_num
  have hlarge := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (3 / 2) ^ 8) hsmall b
  have hpow : ((3 / 2 : ℝ) ^ d) ^ 5 ≤ ((2 : ℝ) ^ b) ^ 5 := by
    calc
      _ = (3 / 2 : ℝ) ^ (5 * d) := by rw [← pow_mul]; congr 1; omega
      _ ≤ (3 / 2 : ℝ) ^ (8 * b) := h
      _ ≤ (2 : ℝ) ^ (5 * b) := by simpa only [pow_mul] using hlarge
      _ = ((2 : ℝ) ^ b) ^ 5 := by rw [← pow_mul]; congr 1; omega
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 5 ≠ 0)).mp hpow

theorem rootUniformWordOffset_le_twoPow_of_length_le_horizon
    {w : List ℕ+} {b : ℕ} (h : w.length ≤ ndGeom2ShiftedWideSymmetricHorizon b) :
    ndRootUniformWordOffset w ≤ (2 : ℝ) ^ b := by
  have hd : 5 * w.length ≤ 8 * b := by
    simp only [ndGeom2ShiftedWideSymmetricHorizon, ndGeom2ShiftedWideSymmetricWidth] at h
    omega
  have hp := rootUniform_threeHalves_pow_le_twoPow hd
  exact (rootUniformWordOffset_le_threeHalves w).trans (by linarith)

theorem rootUniformWord_affine_of_path {N M : ℕ}
    (p : NDGeom2RootSideSyracusePath N M) :
    ndRootUniformWordAtom p.word.reverse * (N : ℝ) +
      ndRootUniformWordOffset p.word.reverse = (M : ℝ) := by
  have ha := Tao.syracuse_iterate_eq_taoAffList p.depth N p.sourceOdd
  rw [p.valuation_eq, p.terminal_eq, Tao.taoAffList_closed] at ha
  have hr := congrArg (fun x : ℚ => (x : ℝ)) ha.symm
  simpa only [ndRootUniformWordAtom, ndRootUniformWordOffset, List.reverse_reverse,
    List.length_reverse, Tao.taoTupleWeight_reverse, Rat.cast_add, Rat.cast_mul,
    Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] using hr

theorem unitIncidenceAtom_eq_rootUniformWordAtom
    {Label : Type*} {Labels : Finset Label} {root : Label → ℕ} {b a K : ℕ}
    (z : NDGeom2PredictableRootSideUnitChildIncidence Labels root b a K) :
    ndGeom2PredictableRootSideUnitChildIncidenceAtom z =
      ndRootUniformWordAtom (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z) := by
  unfold ndGeom2PredictableRootSideUnitChildIncidenceAtom ndRootUniformWordAtom
  rw [← ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length z,
    referencePrefix_atom_eq]
  simp only [zpow_neg, zpow_natCast, div_eq_mul_inv]

theorem rootUniform_sameResidue_weighted_card_le
    (S : Finset ℕ) {Q : ℕ} (hQ : 0 < Q) (y : ZMod Q) {W C : ℝ}
    (hW : 0 ≤ W) (hC : 0 ≤ C)
    (hres : ∀ N ∈ S, (N : ZMod Q) = y)
    (hdiam : ∀ N ∈ S, ∀ M ∈ S, W * (N : ℝ) ≤ W * (M : ℝ) + C) :
    (Q : ℝ) * W * S.card ≤ C + (Q : ℝ) * W := by
  classical
  by_cases hS : S.Nonempty
  · let lo := S.min' hS
    let hi := S.max' hS
    have hlo : lo ∈ S := S.min'_mem hS
    have hhi : hi ∈ S := S.max'_mem hS
    have hbounds : ∀ N ∈ S, lo ≤ N ∧ N ≤ hi := fun N hN =>
      ⟨S.min'_le N hN, S.le_max' N hN⟩
    have hmod : ∀ N ∈ S, N % Q = lo % Q := fun N hN =>
      (ZMod.natCast_eq_natCast_iff' N lo Q).mp ((hres N hN).trans (hres lo hlo).symm)
    have hinj : (S : Set ℕ).InjOn (fun N => N / Q) := by
      intro N hN M hM heq
      change N / Q = M / Q at heq
      have hN' := Nat.mod_add_div N Q
      have hM' := Nat.mod_add_div M Q
      rw [hmod N hN] at hN'
      rw [hmod M hM, ← heq] at hM'
      omega
    have hc : S.card ≤ hi / Q + 1 - lo / Q := by
      have hmap : Set.MapsTo (fun N => N / Q) (S : Set ℕ)
          (Finset.Icc (lo / Q) (hi / Q) : Set ℕ) := by
        intro N hN
        exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right (hbounds N hN).1,
          Nat.div_le_div_right (hbounds N hN).2⟩
      simpa only [Nat.card_Icc] using Finset.card_le_card_of_injOn _ hmap hinj
    have hquot : lo / Q ≤ hi / Q := Nat.div_le_div_right (hbounds lo hlo).2
    have hcR : (S.card : ℝ) ≤ (hi / Q : ℕ) + 1 - (lo / Q : ℕ) := by
      have hcadd : S.card + lo / Q ≤ hi / Q + 1 := by omega
      have hcaddR : (S.card : ℝ) + (lo / Q : ℕ) ≤ (hi / Q : ℕ) + 1 := by
        exact_mod_cast hcadd
      linarith
    have heqN : lo + Q * (hi / Q) = hi + Q * (lo / Q) := by
      have hl := Nat.mod_add_div lo Q
      have hh := Nat.mod_add_div hi Q
      rw [hmod hi hhi] at hh
      omega
    have heq : (lo : ℝ) + (Q : ℝ) * (hi / Q : ℕ) =
        (hi : ℝ) + (Q : ℝ) * (lo / Q : ℕ) := by exact_mod_cast heqN
    have hbound := mul_le_mul_of_nonneg_left hcR
      (mul_nonneg (Nat.cast_nonneg Q) hW)
    have hspread := hdiam hi hhi lo hlo
    have hWeq := congrArg (fun x : ℝ => W * x) heq
    nlinarith only [hbound, hspread, hWeq]
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp only [hempty, Finset.card_empty, Nat.cast_zero, mul_zero]
    positivity

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

private theorem rootUniform_packetLower
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) :
    ∀ i, 16 ^ U.floor ≤ U.state.root i := fun i =>
  (Nat.pow_le_pow_right (by norm_num) (U.floor_le_base i)).trans (U.state.rootLower i)

theorem forwardLabel_eq_of_ancestor_root_depth_eq
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) {z w : (U.forwardIterate cap n).state.Label}
    (ha : U.forwardAncestor cap n z = U.forwardAncestor cap n w)
    (hr : (U.forwardIterate cap n).state.root z = (U.forwardIterate cap n).state.root w)
    (hd : (U.forwardWord cap n z).length = (U.forwardWord cap n w).length) : z = w := by
  let p := U.forwardRootPath cap n z
  let q := U.forwardRootPath cap n w
  have hdepth : p.depth = q.depth := by
    rw [← p.word_length, ← q.word_length]
    simpa only [p, q, forwardRootPath_word_eq_reverse, List.length_reverse] using hd
  have hw := NDGeom2RootSideSyracusePath.word_eq_of_source_depth_eq p q hr hdepth
  have hword : U.forwardWord cap n z = U.forwardWord cap n w := by
    apply List.reverse_injective
    exact (U.forwardRootPath_word_eq_reverse cap n z).symm.trans
      (hw.trans (U.forwardRootPath_word_eq_reverse cap n w))
  exact (U.forwardLabel_tail_eq_of_append cap n z w [] [] ha (by simpa using hword)).1

theorem forwardWord_affine
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap n).state.Label) :
    ndRootUniformWordAtom (U.forwardWord cap n z) *
        ((U.forwardIterate cap n).state.root z : ℝ) +
      ndRootUniformWordOffset (U.forwardWord cap n z) =
        (U.state.root (U.forwardAncestor cap n z) : ℝ) := by
  have h := rootUniformWord_affine_of_path (U.forwardRootPath cap n z)
  simpa only [forwardRootPath_word_eq_reverse, List.reverse_reverse] using h

theorem forwardWeight_eq_ownerWeight_mul_wordAtom
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap n).state.Label) :
    (U.forwardIterate cap n).state.outerWeight z =
      U.state.outerWeight (U.forwardAncestor cap n z) *
        ndRootUniformWordAtom (U.forwardWord cap n z) := by
  induction n generalizing U cap with
  | zero => simp [forwardIterate, forwardAncestor, forwardWord, ndRootUniformWordAtom]
  | succ n ih =>
      rw [forwardWord, rootUniformWordAtom_append]
      have h := ih (U := U.next (cap 0)) (cap := ndGeom2RootSideCapTail cap) z
      change _ = (U.state.outerWeight (U.forwardAncestor cap (n + 1) z) *
        ndGeom2PredictableRootSideUnitChildIncidenceAtom
          (U.forwardFirstIncidence cap n z)) * _ at h
      rw [unitIncidenceAtom_eq_rootUniformWordAtom] at h
      exact h.trans (by ring)

theorem next_root_ge_sixteenPow_mul_parent
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (K : ℕ)
    (z : (U.next K).state.Label) :
    16 ^ (U.floor / 100) * U.state.root
        (ndGeom2PredictableRootSideUnitChildIncidenceLabel z) ≤ (U.next K).state.root z := by
  let b := U.floor
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  let M := U.state.root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z)
  let N := (U.next K).state.root z
  have hs := ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_shell
    U.state.root_odd (fun _ => by have := U.floor_twoHundred; omega)
    U.rootUniform_packetLower (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z)
  have hl : 4 * 2 ^ r * 3 ^ b * (16 ^ (b / 100) * M) ≤
      2 ^ r * 4 ^ b * M := by
    calc
      _ = 2 ^ r * M * (4 * 3 ^ b * 16 ^ (b / 100)) := by ring
      _ ≤ 2 ^ r * M * 4 ^ b := by
        gcongr
        exact four_mul_threePow_mul_sixteenPow_oneHundredth_le_fourPow U.floor_twoHundred
      _ = _ := by ring
  have hs' : 2 ^ r * 4 ^ b * M ≤ 4 * 2 ^ r * 3 ^ b * N := hs.1
  exact Nat.le_of_mul_le_mul_left (hl.trans hs') (by positivity)

theorem next_wordAtom_mul_sixteenPow_le_one
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState) (K : ℕ)
    (z : (U.next K).state.Label) :
    ndRootUniformWordAtom (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z) *
      (16 : ℝ) ^ (U.floor / 100) ≤ 1 := by
  let W := ndRootUniformWordAtom (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z)
  let M := U.state.root (ndGeom2PredictableRootSideUnitChildIncidenceLabel z)
  let N := (U.next K).state.root z
  have ha := U.forwardWord_affine (fun _ => K) 1 z
  have ha' : W * (N : ℝ) +
      ndRootUniformWordOffset (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z) =
      (M : ℝ) := by simpa [forwardWord, forwardAncestor, forwardFirstIncidence] using ha
  have hg : (16 : ℝ) ^ (U.floor / 100) * (M : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast U.next_root_ge_sixteenPow_mul_parent K z
  have hW : 0 ≤ W := (rootUniformWordAtom_pos _).le
  have hF := rootUniformWordOffset_nonneg
    (ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z)
  have hM : (0 : ℝ) < M := by exact_mod_cast (U.state.root_odd _).pos
  have hmul := mul_le_mul_of_nonneg_left hg hW
  apply (mul_le_mul_iff_left₀ hM).mp
  nlinarith only [hmul, ha', hF]

theorem forwardWordOffset_le_rootUniform
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap n).state.Label) :
    ndRootUniformWordOffset (U.forwardWord cap n z) ≤ (2 : ℝ) ^ (U.floor + 1) := by
  induction n generalizing U cap with
  | zero => simp [forwardWord, ndRootUniformWordOffset, Tao.taoOffsetList]
  | succ n ih =>
      let iz := U.forwardFirstIncidence cap n z
      let w := ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord iz
      let b := U.floor
      let d := b / 100
      have hd : 1 ≤ d := by have := U.floor_twoHundred; dsimp [d, b]; omega
      have hlen : w.length ≤ ndGeom2ShiftedWideSymmetricHorizon b := by
        rw [ndGeom2PredictableRootSideUnitChildIncidence_rootSideWord_length]
        exact (Finset.mem_Icc.mp iz.2.1.2).2
      have hF := rootUniformWordOffset_le_twoPow_of_length_le_horizon hlen
      have hW := U.next_wordAtom_mul_sixteenPow_le_one (cap 0) iz
      have htail := ih (U := U.next (cap 0)) (cap := ndGeom2RootSideCapTail cap) z
      have hp : (2 : ℝ) ^ ((U.next (cap 0)).floor + 1) ≤ (2 : ℝ) ^ b * 16 ^ d := by
        change (2 : ℝ) ^ (b + d + 1) ≤ _
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hm := mul_le_mul_of_nonneg_left (htail.trans hp)
        (rootUniformWordAtom_pos w).le
      have hbW := mul_le_mul_of_nonneg_left hW (by positivity : 0 ≤ (2 : ℝ) ^ b)
      rw [forwardWord, rootUniformWordOffset_append]
      change ndRootUniformWordOffset w + _ ≤ _
      rw [pow_succ]
      nlinarith only [hF, hm, hbW]

theorem forwardWord_weighted_source_band
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap n).state.Label) :
    (U.state.root (U.forwardAncestor cap n z) : ℝ) - (2 : ℝ) ^ (U.floor + 1) ≤
        ndRootUniformWordAtom (U.forwardWord cap n z) *
          ((U.forwardIterate cap n).state.root z : ℝ) ∧
      ndRootUniformWordAtom (U.forwardWord cap n z) *
          ((U.forwardIterate cap n).state.root z : ℝ) ≤
        (U.state.root (U.forwardAncestor cap n z) : ℝ) := by
  have ha := U.forwardWord_affine cap n z
  have hF := U.forwardWordOffset_le_rootUniform cap n z
  have hF0 := rootUniformWordOffset_nonneg (U.forwardWord cap n z)
  constructor <;> linarith only [ha, hF, hF0]

theorem forwardWordAtom_mul_sixteenPow_floor_le
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (z : (U.forwardIterate cap n).state.Label) :
    ndRootUniformWordAtom (U.forwardWord cap n z) *
      (16 : ℝ) ^ (U.forwardIterate cap n).floor ≤ (16 : ℝ) ^ U.floor := by
  induction n generalizing U cap with
  | zero => simp [forwardWord, forwardIterate, ndRootUniformWordAtom]
  | succ n ih =>
      let w := ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord
        (U.forwardFirstIncidence cap n z)
      have ht := ih (U := U.next (cap 0)) (cap := ndGeom2RootSideCapTail cap) z
      have hm := mul_le_mul_of_nonneg_left ht (rootUniformWordAtom_pos w).le
      have he := mul_le_mul_of_nonneg_left
        (U.next_wordAtom_mul_sixteenPow_le_one (cap 0) (U.forwardFirstIncidence cap n z))
        (by positivity : 0 ≤ (16 : ℝ) ^ U.floor)
      rw [forwardWord, rootUniformWordAtom_append]
      change _ ≤ (16 : ℝ) ^ U.floor
      have hp : (16 : ℝ) ^ (U.next (cap 0)).floor =
          (16 : ℝ) ^ U.floor * (16 : ℝ) ^ (U.floor / 100) := pow_add _ _ _
      rw [hp] at hm
      dsimp only [forwardIterate, w] at hm he ⊢
      nlinarith only [hm, he]

theorem threePow_mul_forwardWordAtom_le_rootUniform_edge
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n q : ℕ) (hq : q ≤ 2 * (U.forwardIterate cap n).floor)
    (z : (U.forwardIterate cap n).state.Label) :
    (3 : ℝ) ^ q * ndRootUniformWordAtom (U.forwardWord cap n z) ≤
      (16 : ℝ) ^ U.floor * (9 / 16 : ℝ) ^ (U.forwardIterate cap n).floor := by
  let b := (U.forwardIterate cap n).floor
  let W := ndRootUniformWordAtom (U.forwardWord cap n z)
  have hqR : (3 : ℝ) ^ q ≤ 9 ^ b := by
    calc
      _ ≤ (3 : ℝ) ^ (2 * b) := pow_le_pow_right₀ (by norm_num) hq
      _ = _ := by rw [pow_mul]; norm_num
  have ht := U.forwardWordAtom_mul_sixteenPow_floor_le cap n z
  calc
    _ ≤ (9 : ℝ) ^ b * W := mul_le_mul_of_nonneg_right hqR (rootUniformWordAtom_pos _).le
    _ ≤ (16 : ℝ) ^ U.floor * ((9 : ℝ) ^ b / 16 ^ b) := by
      have h := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ (9 : ℝ) ^ b)
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : 0 < (16 : ℝ) ^ b)).2
      simpa only [W, b, mul_assoc, mul_left_comm, mul_comm] using h
    _ = _ := by rw [div_pow]

def forwardRootGroup
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (i : U.state.Label) (D A : ℕ) :
    Finset (U.forwardIterate cap n).state.Label := by
  classical
  letI := (U.forwardIterate cap n).state.labelFintype
  exact Finset.univ.filter fun z => U.forwardAncestor cap n z = i ∧
    (U.forwardWord cap n z).length = D ∧ Tao.taoTupleWeight (U.forwardWord cap n z) = A

def forwardRootGroupHistogram
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (i : U.state.Label) (D A q : ℕ) (y : ZMod (3 ^ q)) : ℝ := by
  classical
  exact ∑ z ∈ (U.forwardRootGroup cap n i D A).filter
    (fun z => ((U.forwardIterate cap n).state.root z : ZMod (3 ^ q)) = y),
      (U.forwardIterate cap n).state.outerWeight z

theorem threePow_mul_forwardRootGroupHistogram_le_rootUniform
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (i : U.state.Label) (D A q : ℕ) (y : ZMod (3 ^ q)) :
    (3 : ℝ) ^ q * U.forwardRootGroupHistogram cap n i D A q y ≤
      U.state.outerWeight i * ((2 : ℝ) ^ (U.floor + 1) +
        (3 : ℝ) ^ q * ((3 : ℝ) ^ D / (2 : ℝ) ^ A)) := by
  classical
  let V := U.forwardIterate cap n
  let Z := (U.forwardRootGroup cap n i D A).filter
    (fun z => (V.state.root z : ZMod (3 ^ q)) = y)
  let S := Z.image V.state.root
  let W : ℝ := (3 : ℝ) ^ D / (2 : ℝ) ^ A
  have hmem : ∀ z ∈ Z, U.forwardAncestor cap n z = i ∧
      (U.forwardWord cap n z).length = D ∧ Tao.taoTupleWeight (U.forwardWord cap n z) = A := by
    intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
  have hword : ∀ z ∈ Z, ndRootUniformWordAtom (U.forwardWord cap n z) = W := by
    intro z hz
    simp only [ndRootUniformWordAtom, (hmem z hz).2.1, (hmem z hz).2.2, W]
  have hinj : (Z : Set V.state.Label).InjOn V.state.root := by
    intro z hz w hw hr
    exact U.forwardLabel_eq_of_ancestor_root_depth_eq cap n
      ((hmem z hz).1.trans (hmem w hw).1.symm) hr
      ((hmem z hz).2.1.trans (hmem w hw).2.1.symm)
  have hcard : S.card = Z.card := Finset.card_image_of_injOn hinj
  have hdiam : ∀ N ∈ S, ∀ M ∈ S, W * (N : ℝ) ≤ W * (M : ℝ) + (2 : ℝ) ^ (U.floor + 1) := by
    intro N hN M hM
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hN
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hM
    have hzB := U.forwardWord_weighted_source_band cap n z
    have hwB := U.forwardWord_weighted_source_band cap n w
    rw [(hmem z hz).1, hword z hz] at hzB
    rw [(hmem w hw).1, hword w hw] at hwB
    linarith only [hzB.2, hwB.1]
  have hres : ∀ N ∈ S, (N : ZMod (3 ^ q)) = y := by
    intro N hN
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hN
    exact (Finset.mem_filter.mp hz).2
  have hc := rootUniform_sameResidue_weighted_card_le S (by positivity : 0 < 3 ^ q) y
    (by positivity : 0 ≤ W) (by positivity : 0 ≤ (2 : ℝ) ^ (U.floor + 1)) hres hdiam
  rw [hcard] at hc
  have hsum : U.forwardRootGroupHistogram cap n i D A q y =
      U.state.outerWeight i * W * Z.card := by
    change (∑ z ∈ Z, V.state.outerWeight z) = _
    calc
      _ = ∑ _z ∈ Z, U.state.outerWeight i * W := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [U.forwardWeight_eq_ownerWeight_mul_wordAtom cap n z, (hmem z hz).1, hword z hz]
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hsum]
  have h := mul_le_mul_of_nonneg_left hc (U.state.weight_nonneg i)
  simpa only [Nat.cast_pow, Nat.cast_ofNat, W, mul_assoc, mul_left_comm] using h

theorem threePow_mul_forwardRootGroupHistogram_le_rootUniform_edge
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap : ℕ → ℕ) (n : ℕ) (i : U.state.Label) (D A q : ℕ)
    (hq : q ≤ 2 * (U.forwardIterate cap n).floor) (y : ZMod (3 ^ q)) :
    (3 : ℝ) ^ q * U.forwardRootGroupHistogram cap n i D A q y ≤
      U.state.outerWeight i * ((2 : ℝ) ^ (U.floor + 1) +
        (16 : ℝ) ^ U.floor * (9 / 16 : ℝ) ^ (U.forwardIterate cap n).floor) := by
  classical
  by_cases hne : (U.forwardRootGroup cap n i D A).Nonempty
  · obtain ⟨z, hz⟩ := hne
    have hd := (Finset.mem_filter.mp hz).2
    have he := U.threePow_mul_forwardWordAtom_le_rootUniform_edge cap n q hq z
    simp only [ndRootUniformWordAtom, hd.2.1, hd.2.2] at he
    exact (U.threePow_mul_forwardRootGroupHistogram_le_rootUniform cap n i D A q y).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) he) (U.state.weight_nonneg i))
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [forwardRootGroupHistogram, hempty, Finset.filter_empty, Finset.sum_empty, mul_zero]
    exact mul_nonneg (U.state.weight_nonneg i) (by positivity)

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
