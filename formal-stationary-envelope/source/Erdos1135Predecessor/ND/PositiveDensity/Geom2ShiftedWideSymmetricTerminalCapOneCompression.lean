/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricTerminalShiftImageRate

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

def ndTerminalSourceFan (j x : ℕ) : ℕ :=
  ((fun y : ℕ => 4 * y + 1)^[j]) x

theorem terminalSourceFan_cleared (j x : ℕ) :
    3 * ndTerminalSourceFan j x + 1 = 4 ^ j * (3 * x + 1) := by
  induction j with
  | zero => simp [ndTerminalSourceFan]
  | succ j ih =>
    change 3 * ((fun y : ℕ => 4 * y + 1)^[j + 1]) x + 1 = _
    rw [Function.iterate_succ_apply']
    change 3 * (4 * ndTerminalSourceFan j x + 1) + 1 = _
    rw [pow_succ]
    nlinarith [ih]

theorem exists_terminal_head_compressed_source
    {tail : List ℕ+} {v : ℕ+} {x r j : ℕ}
    (hr : Odd r) (hj : 2 * j < (v : ℕ))
    (haff : Tao.taoAffList (v :: tail) (x : ℚ) = (r : ℚ)) :
    ∃ x0 : ℕ, Odd x0 ∧ x = ndTerminalSourceFan j x0 ∧
      Tao.taoAffList (⟨(v : ℕ) - 2 * j, by omega⟩ :: tail)
        (x0 : ℚ) = (r : ℚ) := by
  obtain ⟨hx, hvalues, _⟩ := Tao.taoAffList_oddNat_decode (v :: tail) x r hr haff
  have hv : Tao.syracuseExponent x = (v : ℕ) := by
    have hhead := List.cons.inj hvalues
    exact congrArg (fun a : ℕ+ => (a : ℕ)) hhead.1
  have hfactor : 3 * x + 1 = 2 ^ (v : ℕ) * Tao.syracuse x := by
    rw [← hv, Tao.two_pow_syracuseExponent_mul_syracuse]
  let B := 2 ^ ((v : ℕ) - 2 * j) * Tao.syracuse x
  have hB : 4 ^ j * B = 3 * x + 1 := by
    rw [hfactor]
    dsimp [B]
    have hvsplit : (v : ℕ) = 2 * j + ((v : ℕ) - 2 * j) := by omega
    conv_rhs => rw [hvsplit, pow_add]
    rw [pow_mul]
    norm_num
    ring
  have hmod : B % 3 = 1 := by
    have hm := congrArg (fun z : ℕ => z % 3) hB
    simpa [Nat.mul_mod, Nat.add_mod, Nat.pow_mod] using hm
  have hB0 : 3 * (B / 3) + 1 = B := by omega
  let x0 := B / 3
  have hhead0 : Tao.taoSingleAff
      ⟨(v : ℕ) - 2 * j, by omega⟩ (x0 : ℚ) = (Tao.syracuse x : ℚ) := by
    unfold Tao.taoSingleAff
    apply (div_eq_iff (by positivity)).2
    have hnat : 3 * x0 + 1 = Tao.syracuse x * 2 ^ ((v : ℕ) - 2 * j) := by
      simpa [x0, B, Nat.mul_comm] using hB0
    exact_mod_cast hnat
  have hhead : Tao.taoSingleAff v (x : ℚ) = (Tao.syracuse x : ℚ) := by
    unfold Tao.taoSingleAff
    apply (div_eq_iff (by positivity)).2
    exact_mod_cast hfactor.trans (Nat.mul_comm _ _)
  have haff0 : Tao.taoAffList
      (⟨(v : ℕ) - 2 * j, by omega⟩ :: tail) (x0 : ℚ) = (r : ℚ) := by
    change Tao.taoAffList tail (Tao.taoSingleAff _ _) = _
    rw [hhead0, ← hhead]
    exact haff
  refine ⟨x0, (Tao.taoAffList_oddNat_decode _ x0 r hr haff0).choose, ?_, haff0⟩
  have hfan := terminalSourceFan_cleared j x0
  have hB0' : 3 * x0 + 1 = B := hB0
  rw [hB0'] at hfan
  omega

theorem exists_first_crossing_cap_one_compression
    {b a s K : ℕ} {word : List ℕ+} (hlen : word.length = s)
    (hevent : ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt
      b a s K word) :
    ∃ (pre : List ℕ+) (v0 : ℕ+) (j : ℕ),
      j ≤ K / 2 ∧ pre.length + 1 = s ∧
      word = pre ++ [ndPNatAddNat (2 * j) v0] ∧
      ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt
        b a s 1 (pre ++ [v0]) := by
  have hfirst := hevent.1
  have hsB := Finset.mem_Icc.mp hfirst.1
  have hs : 0 < s := by omega
  obtain ⟨pre, v, hw⟩ : ∃ pre : List ℕ+, ∃ v : ℕ+, word = pre ++ [v] := by
    rcases List.eq_nil_or_concat' word with h | h
    · simp [h] at hlen
      omega
    · exact h
  subst word
  have hpre : pre.length = s - 1 := by
    simp only [List.length_append, List.length_singleton] at hlen
    omega
  let O := Tao.taoTupleWeight (pre ++ [v]) + ndBalancedTotal (b - s) +
    ndGeom2ShiftedWideSymmetricShiftRadius b -
    (2 * b + ndBalancedTotal (s - b) + a)
  have hhit := hfirst.2.1.2
  change ndGeom2ShiftedWideSymmetricHit b a s (pre ++ [v]) at hhit
  unfold ndGeom2ShiftedWideSymmetricHit at hhit
  rw [show (pre ++ [v]).take s = pre ++ [v] by rw [← hlen, List.take_length]] at hhit
  have hsum : Tao.taoTupleWeight (pre ++ [v]) + ndBalancedTotal (b - s) +
      ndGeom2ShiftedWideSymmetricShiftRadius b =
      2 * b + ndBalancedTotal (s - b) + a + O := by dsimp [O]; omega
  have hv := ndGeom2ShiftedWideSymmetric_firstCrossing_overshoot_succ_le_terminal
    hlen hfirst
  have hterminal : Tao.geom2PNatListTerminalValue (pre ++ [v]) = (v : ℕ) := by
    simp [Tao.geom2PNatListTerminalValue]
  rw [hterminal] at hv
  have hK : O ≤ K := by
    have h := hevent.2
    unfold ndGeom2ShiftedWideSymmetricBoundedOvershoot at h
    omega
  let j := O / 2
  have hjv : 2 * j < (v : ℕ) := by dsimp [j]; omega
  let v0 : ℕ+ := ⟨(v : ℕ) - 2 * j, by omega⟩
  have hv0 : v = ndPNatAddNat (2 * j) v0 := by
    apply Subtype.ext
    change (v : ℕ) = 2 * j + (v0 : ℕ)
    dsimp [v0]
    omega
  have hw0 : Tao.taoTupleWeight (pre ++ [v]) =
      Tao.taoTupleWeight (pre ++ [v0]) + 2 * j := by
    simp only [Tao.taoTupleWeight_append, Tao.taoTupleWeight_cons,
      Tao.taoTupleWeight_nil, add_zero]
    dsimp [v0]
    omega
  have hlen0 : (pre ++ [v0]).length = s := by simpa using hlen
  have hhit0 : ndGeom2ShiftedWideSymmetricHit b a s (pre ++ [v0]) := by
    unfold ndGeom2ShiftedWideSymmetricHit
    rw [show (pre ++ [v0]).take s = pre ++ [v0] by rw [← hlen0, List.take_length]]
    dsimp [j] at hw0
    omega
  have hbefore (t : ℕ) (ht : t < s) :=
    ndGeom2ShiftedWideSymmetricHit_append_terminal_iff_of_lt
      (b := b) (a := a) v v0 hpre hs ht
  have hmiss0 : ¬ndGeom2ShiftedWideSymmetricHit b a
      (ndGeom2ShiftedWideSymmetricLower b) (pre ++ [v0]) := by
    intro h
    exact hfirst.2.1.1 ((hbefore _ (by omega)).2 h)
  refine ⟨pre, v0, j, by dsimp [j]; omega, by omega, by rw [← hv0], ?_⟩
  constructor
  · refine ⟨hfirst.1, ⟨hmiss0, hhit0⟩, ?_⟩
    intro t ht hts hthit
    exact hfirst.2.2 t ht hts ⟨hfirst.2.1.1, (hbefore t hts).2 hthit.2⟩
  · unfold ndGeom2ShiftedWideSymmetricBoundedOvershoot
    dsimp [j] at hw0
    omega

def ndTerminalEvenRaise (j : ℕ) (word : List ℕ+) : List ℕ+ :=
  (match word.reverse with
    | [] => []
    | v :: tail => ndPNatAddNat (2 * j) v :: tail).reverse

theorem terminalEvenRaise_append (j : ℕ) (pre : List ℕ+) (v : ℕ+) :
    ndTerminalEvenRaise j (pre ++ [v]) = pre ++ [ndPNatAddNat (2 * j) v] := by
  simp [ndTerminalEvenRaise]

theorem terminalEvenRaise_atom (j : ℕ) (pre : List ℕ+) (v : ℕ+) :
    (Tao.geom2PNatListPMF (pre ++ [v]).length
      (ndTerminalEvenRaise j (pre ++ [v]))).toReal =
      (1 / 4 : ℝ) ^ j * (Tao.geom2PNatListPMF (pre ++ [v]).length
        (pre ++ [v])).toReal := by
  rw [terminalEvenRaise_append]
  have hlen : (pre ++ [ndPNatAddNat (2 * j) v]).length = (pre ++ [v]).length := by simp
  rw [← hlen, Tao.geom2PNatListPMF_apply_length_toReal_eq_weight]
  rw [hlen, Tao.geom2PNatListPMF_apply_length_toReal_eq_weight]
  simp only [Tao.taoTupleWeight_append, Tao.taoTupleWeight_cons,
    Tao.taoTupleWeight_nil, add_zero, ndPNatAddNat_coe]
  rw [show Tao.taoTupleWeight pre + (2 * j + (v : ℕ)) =
      2 * j + (Tao.taoTupleWeight pre + (v : ℕ)) by omega, pow_add, pow_mul]
  norm_num

theorem exists_physical_terminal_cap_one_compression
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (hbase : ∀ i, 9 ≤ base i)
    (hroot : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift K) :
    ∃ (z0 : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift 1)
      (j : Fin (K / 2 + 1)),
      ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z =
        ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z0 ∧
      ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z =
        ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z0 ∧
      ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z =
        ndTerminalEvenRaise j.val
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z0) ∧
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z =
        ndTerminalSourceFan j.val
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z0) ∧
      ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom z =
        (1 / 4 : ℝ) ^ j.val *
          ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom z0 := by
  classical
  rcases z with ⟨i, ⟨s, hs⟩, word, hword⟩
  let z : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift K :=
    ⟨i, ⟨s, hs⟩, word, hword⟩
  obtain ⟨hlen, hevent, _⟩ :=
    mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mp hword
  obtain ⟨pre, v0, j, hj, hpre, hw, hevent0⟩ :=
    exists_first_crossing_cap_one_compression hlen hevent
  have haff := (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource_odd_and_affine
    hrootOdd hbase hroot z).2
  change Tao.taoAffList word.reverse
    (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z : ℚ) = (root i : ℚ) at haff
  rw [hw, List.reverse_append, List.reverse_singleton, List.singleton_append] at haff
  have hv : 2 * j < (ndPNatAddNat (2 * j) v0 : ℕ) := by
    change 2 * j < 2 * j + (v0 : ℕ)
    exact Nat.lt_add_of_pos_right v0.2
  obtain ⟨x0, hx0, hsource, haff0⟩ :=
    exists_terminal_head_compressed_source (hrootOdd i) hv haff
  have hv0 : (⟨(ndPNatAddNat (2 * j) v0 : ℕ) - 2 * j, by omega⟩ : ℕ+) = v0 := by
    apply Subtype.ext
    simp [ndPNatAddNat_coe]
    rfl
  rw [hv0] at haff0
  have haff0' : Tao.taoAffList (pre ++ [v0]).reverse (x0 : ℚ) = (root i : ℚ) := by
    simpa using haff0
  have hlen0 : (pre ++ [v0]).length = s := by simpa using hpre
  have hoffset : Tao.taoSection7OffsetZMod s (pre ++ [v0]) = (root i : ZMod (3 ^ s)) := by
    have h := Tao.taoAffineOffsetZMod_eq_of_taoAffList_eq
      (N := ⟨x0, hx0⟩) (show (pre ++ [v0]).reverse.length = s by simpa using hlen0) haff0'
    rw [Tao.taoAffineOffsetZMod_reverse_eq_taoSection7OffsetZMod hlen0] at h
    exact h.symm
  let z0 : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift 1 :=
    ⟨i, ⟨s, hs⟩, pre ++ [v0],
      mem_ndGeom2ShiftedWideSymmetricRootSideBoundedOvershootWordFinset_iff.mpr
        ⟨hlen0, hevent0, hoffset⟩⟩
  have hsource0 : ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z0 = x0 :=
    Tao.taoAffineSourceCandidate_eq_of_taoAffList_eq
      (show (pre ++ [v0]).reverse.length = s by simpa using hlen0) haff0'
  refine ⟨z0, ⟨j, by omega⟩, rfl, rfl, ?_, ?_, ?_⟩
  · change word = ndTerminalEvenRaise j (pre ++ [v0])
    rw [terminalEvenRaise_append]
    exact hw
  · change ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z = _
    rw [hsource0]
    exact hsource
  · change (3 : ℝ) ^ s * (Tao.geom2PNatListPMF s word).toReal =
      (1 / 4 : ℝ) ^ j * ((3 : ℝ) ^ s *
        (Tao.geom2PNatListPMF s (pre ++ [v0])).toReal)
    rw [hw, ← terminalEvenRaise_append]
    rw [← hlen0, terminalEvenRaise_atom]
    ring

def ndPhysicalTerminalCompression
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (hbase : ∀ i, 9 ≤ base i)
    (hroot : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift K) :
    NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift 1 ×
      Fin (K / 2 + 1) :=
  let h := exists_physical_terminal_cap_one_compression hrootOdd hbase hroot z
  ⟨h.choose, h.choose_spec.choose⟩

theorem physicalTerminalCompression_spec
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (hbase : ∀ i, 9 ≤ base i)
    (hroot : ∀ i, 16 ^ base i ≤ root i)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift K) :
    let p := ndPhysicalTerminalCompression hrootOdd hbase hroot z
    ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel z =
        ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel p.1 ∧
      ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth z =
        ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth p.1 ∧
      ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord z =
        ndTerminalEvenRaise p.2.val
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord p.1) ∧
      ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z =
        ndTerminalSourceFan p.2.val
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource p.1) ∧
      ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom z =
        (1 / 4 : ℝ) ^ p.2.val *
          ndGeom2PredictableRootSideBoundedOvershootIncidenceAtom p.1 :=
  (exists_physical_terminal_cap_one_compression hrootOdd hbase hroot z).choose_spec.choose_spec

theorem physicalTerminalCompression_injective
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (hbase : ∀ i, 9 ≤ base i)
    (hroot : ∀ i, 16 ^ base i ≤ root i) :
    Function.Injective (ndPhysicalTerminalCompression (shift := shift) (K := K)
      hrootOdd hbase hroot) := by
  intro z w heq
  have hz := physicalTerminalCompression_spec hrootOdd hbase hroot z
  have hw := physicalTerminalCompression_spec hrootOdd hbase hroot w
  dsimp only at hz hw
  rw [heq] at hz
  exact ndGeom2PredictableRootSideBoundedOvershootIncidence_ext
    (hz.1.trans hw.1.symm) (hz.2.1.trans hw.2.1.symm)
    (hz.2.2.1.trans hw.2.2.1.symm)

theorem physicalTerminalCompression_weighted_mark
    {Label : Type*} {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (hbase : ∀ i, 9 ≤ base i)
    (hroot : ∀ i, 16 ^ base i ≤ root i)
    (outerWeight : Label → ℝ) (g : ℕ → ℝ)
    (z : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift K) :
    let p := ndPhysicalTerminalCompression hrootOdd hbase hroot z
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight z *
        g (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) =
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight p.1 *
        ((1 / 4 : ℝ) ^ p.2.val * g (ndTerminalSourceFan p.2.val
          (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource p.1))) := by
  have h := physicalTerminalCompression_spec hrootOdd hbase hroot z
  dsimp only
  unfold ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
  rw [h.1, h.2.2.2.1, h.2.2.2.2]
  ring

theorem physical_terminal_mark_le_cap_one_fan
    {Label : Type*} [Fintype Label] {root base shift : Label → ℕ} {K : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (hbase : ∀ i, 9 ≤ base i)
    (hroot : ∀ i, 16 ^ base i ≤ root i)
    (outerWeight : Label → ℝ) (hw : ∀ i, 0 ≤ outerWeight i)
    (g : ℕ → ℝ) (hg : ∀ x, 0 ≤ g x) :
    (∑ z : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift K,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight z *
        g (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)) ≤
    ∑ z0 : NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift 1,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight z0 *
        ∑ j : Fin (K / 2 + 1), (1 / 4 : ℝ) ^ j.val *
          g (ndTerminalSourceFan j.val
            (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z0)) := by
  classical
  let f := ndPhysicalTerminalCompression (shift := shift) (K := K) hrootOdd hbase hroot
  let G : (NDGeom2PredictableRootSideBoundedOvershootIncidence Label root base shift 1 ×
      Fin (K / 2 + 1)) → ℝ := fun p =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight p.1 *
      ((1 / 4 : ℝ) ^ p.2.val * g (ndTerminalSourceFan p.2.val
        (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource p.1)))
  have hG : ∀ p, 0 ≤ G p := by
    intro p
    exact mul_nonneg (ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg
      outerWeight hw p.1) (mul_nonneg (by positivity) (hg _))
  calc
    _ = ∑ z, G (f z) := Finset.sum_congr rfl fun z _ =>
      physicalTerminalCompression_weighted_mark hrootOdd hbase hroot outerWeight g z
    _ = ∑ p ∈ Finset.univ.image f, G p :=
      (Finset.sum_image fun z _ w _ h =>
        physicalTerminalCompression_injective hrootOdd hbase hroot h).symm
    _ ≤ ∑ p, G p := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun p _ _ => hG p)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z0 _
      dsimp [G]
      rw [Finset.mul_sum]

def ndTerminalUnitPhysicalMap
    {Label : Type*} [DecidableEq Label] (root shift : Label → ℕ) (b K : ℕ)
    (z : Σ i : Label, NDGeom2PredictableRootSideUnitChildIncidence
      ({i} : Finset Label) root b (shift i) K) :
    NDGeom2PredictableRootSideBoundedOvershootIncidence Label root (fun _ => b) shift K := by
  rcases z with ⟨i, ⟨⟨j, hj⟩, s, u, w⟩⟩
  have hji : j = i := Finset.mem_singleton.mp hj
  subst j
  let z : NDGeom2PredictableRootSideUnitChildIncidence ({i} : Finset Label)
      root b (shift i) K := ⟨⟨i, hj⟩, s, u, w⟩
  exact ⟨i, s, (ndGeom2PredictableRootSideUnitChildIncidence.toPhysical z).2.2⟩

theorem terminalUnitPhysicalMap_spec
    {Label : Type*} [DecidableEq Label] (root shift : Label → ℕ) (b K : ℕ)
    (z : Σ i : Label, NDGeom2PredictableRootSideUnitChildIncidence
      ({i} : Finset Label) root b (shift i) K) :
    ndGeom2PredictableRootSideBoundedOvershootIncidenceLabel
        (ndTerminalUnitPhysicalMap root shift b K z) = z.1 ∧
    ndGeom2PredictableRootSideBoundedOvershootIncidenceDepth
        (ndTerminalUnitPhysicalMap root shift b K z) =
      ndGeom2PredictableRootSideUnitChildIncidenceDepth z.2 ∧
    ndGeom2PredictableRootSideBoundedOvershootIncidenceRootSideWord
        (ndTerminalUnitPhysicalMap root shift b K z) =
      ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z.2 ∧
    ndGeom2PredictableRootSideBoundedOvershootIncidenceSource
        (ndTerminalUnitPhysicalMap root shift b K z) =
      ndGeom2PredictableRootSideUnitChildIncidenceSource z.2 ∧
    ∀ outerWeight : Label → ℝ,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight
          (ndTerminalUnitPhysicalMap root shift b K z) =
        ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z.2 := by
  rcases z with ⟨i, ⟨⟨j, hj⟩, s, u, w⟩⟩
  have hji : j = i := Finset.mem_singleton.mp hj
  subst j
  exact ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem terminalUnitPhysicalMap_injective
    {Label : Type*} [DecidableEq Label] {root shift : Label → ℕ} {b K : ℕ}
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hroot : ∀ i, 16 ^ b ≤ root i) :
    Function.Injective (ndTerminalUnitPhysicalMap root shift b K) := by
  rintro ⟨i, z⟩ ⟨j, w⟩ heq
  have hz := terminalUnitPhysicalMap_spec root shift b K ⟨i, z⟩
  have hw := terminalUnitPhysicalMap_spec root shift b K ⟨j, w⟩
  dsimp only at hz hw
  have hij : i = j := by
    rw [← hz.1, ← hw.1, heq]
  subst j
  have hzw : z = w := by
    apply ndGeom2PredictableRootSideUnitChildIncidence_toPhysical_injective hrootOdd hb hroot
    apply ndGeom2PredictableRootSideBoundedOvershootIncidence_ext
    · exact (Finset.mem_singleton.mp z.1.2).trans (Finset.mem_singleton.mp w.1.2).symm
    · change ndGeom2PredictableRootSideUnitChildIncidenceDepth z =
        ndGeom2PredictableRootSideUnitChildIncidenceDepth w
      rw [← hz.2.1, ← hw.2.1, heq]
    · change ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord z =
        ndGeom2PredictableRootSideUnitChildIncidenceRootSideWord w
      rw [← hz.2.2.1, ← hw.2.2.1, heq]
  subst w
  rfl

theorem singleton_unit_terminal_mark_le_physical
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (root shift : Label → ℕ) (b K : ℕ)
    (hrootOdd : ∀ i, Odd (root i)) (hb : 9 ≤ b)
    (hroot : ∀ i, 16 ^ b ≤ root i)
    (outerWeight : Label → ℝ) (hw : ∀ i, 0 ≤ outerWeight i)
    (g : ℕ → ℝ) (hg : ∀ x, 0 ≤ g x) :
    (∑ i : Label, ∑ z : NDGeom2PredictableRootSideUnitChildIncidence
      ({i} : Finset Label) root b (shift i) K,
      ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z *
        g (ndGeom2PredictableRootSideUnitChildIncidenceSource z)) ≤
    ∑ z : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root (fun _ => b) shift K,
      ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight z *
        g (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) := by
  classical
  let f := ndTerminalUnitPhysicalMap root shift b K
  let G : NDGeom2PredictableRootSideBoundedOvershootIncidence
      Label root (fun _ => b) shift K → ℝ := fun z =>
    ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight outerWeight z *
      g (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z)
  have hG : ∀ z, 0 ≤ G z := fun z =>
    mul_nonneg (ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight_nonneg
      outerWeight hw z) (hg _)
  calc
    _ = ∑ z : Σ i : Label, NDGeom2PredictableRootSideUnitChildIncidence
        ({i} : Finset Label) root b (shift i) K,
        ndGeom2PredictableRootSideUnitChildIncidenceWeight outerWeight z.2 *
          g (ndGeom2PredictableRootSideUnitChildIncidenceSource z.2) :=
      (Fintype.sum_sigma _).symm
    _ = ∑ z, G (f z) := by
      apply Finset.sum_congr rfl
      intro z _
      have h := terminalUnitPhysicalMap_spec root shift b K z
      dsimp [G, f]
      rw [h.2.2.2.1, h.2.2.2.2]
    _ = ∑ z ∈ Finset.univ.image f, G z :=
      (Finset.sum_image fun z _ w _ h =>
        terminalUnitPhysicalMap_injective hrootOdd hb hroot h).symm
    _ ≤ ∑ z, G z := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun z _ _ => hG z)

namespace NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

theorem forwardCoreTerminalUnitMass_le_full_cap_one_fan
    (U : NDGeom2ShiftedWideSymmetricRootSideUniformFloorState)
    (cap width : ℕ → ℕ) (n K k : ℕ) (X : ℝ) (hX : 0 < X)
    (hi : ∀ i : (U.forwardIterate cap n).state.Label,
      ndGeom2ShiftedWideSymmetricPhysicalIntervalMin (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i) < X ∧
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax (U.forwardIterate cap n).floor
        ((U.forwardIterate cap n).state.root i)) :
    let V := U.forwardIterate cap n
    letI := V.state.labelFintype
    U.forwardCoreTerminalUnitMass cap width n K k X hX hi ≤
      ∑ z : V.FullTerminalIncidence X hX hi,
        ndGeom2PredictableRootSideBoundedOvershootIncidenceWeight
          (U.forwardCoreOuterWeight cap width n) z *
          ∑ j : Fin (K / 2 + 1), (1 / 4 : ℝ) ^ j.val *
            ndSyracuseUnitReferenceDensity k
              (ndTerminalSourceFan j.val
                (ndGeom2PredictableRootSideBoundedOvershootIncidenceSource z) : ZMod (3 ^ k)) := by
  classical
  let V := U.forwardIterate cap n
  letI := V.state.labelFintype
  let g := fun x : ℕ => ndSyracuseUnitReferenceDensity k (x : ZMod (3 ^ k))
  have hg : ∀ x, 0 ≤ g x := by intro x; exact ndSyracuseUnitReferenceDensity_nonneg _ _
  have hw : ∀ i, 0 ≤ U.forwardCoreOuterWeight cap width n i := by
    intro i
    unfold forwardCoreOuterWeight
    split_ifs
    · exact V.state.weight_nonneg i
    · exact le_rfl
  have hr : ∀ i, 16 ^ V.floor ≤ V.state.root i := fun i =>
    (Nat.pow_le_pow_right (by norm_num) (V.floor_le_base i)).trans (V.state.rootLower i)
  exact (singleton_unit_terminal_mark_le_physical V.state.root
    (V.fullTerminalShift X hX hi) V.floor K V.state.root_odd
    (by have := V.floor_twoHundred; omega) hr
    (U.forwardCoreOuterWeight cap width n) hw g hg).trans
    (physical_terminal_mark_le_cap_one_fan V.state.root_odd
      (fun _ => by have := V.floor_twoHundred; omega) hr
      (U.forwardCoreOuterWeight cap width n) hw g hg)

end NDGeom2ShiftedWideSymmetricRootSideUniformFloorState

end

end Erdos1135Predecessor.ND.PositiveDensity
