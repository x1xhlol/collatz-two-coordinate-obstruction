import Erdos1135.Tao.Renewal.CanonicalFirstPassageEndpoint
import Erdos1135.Tao.Renewal.Lemma77EndpointAssembly
import Mathlib.Tactic

/-!
# Canonical First-Passage Terminal Reindex

This module encodes every supported canonical endpoint prefix by its terminal
Hold point and predecessor endpoint coordinates.  The encoding is injective
because the code reconstructs the original prefix by `snoc`.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Lemma77

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

/-- Exact predecessor-prefix fiber for one terminal coordinate cell. -/
def Lemma77TerminalPrefixFiber
    (start : TaoSection7RenewalPoint) (r s q lp n : ℕ) :=
  {pref : List TaoSection7RenewalPoint //
    pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent start n
      (lemma77HorizontalShift732 (r : ℤ) q) (((s - lp : ℕ) : ℤ))}

/-- Countable terminal-coordinate target in the fixed order `q, lp, n, pref`. -/
def Lemma77TerminalCoordinate
    (start : TaoSection7RenewalPoint) (r s : ℕ) :=
  Σ q : ℕ,
    Σ lp : Fin (s + 1),
      Σ n : ℕ, Lemma77TerminalPrefixFiber start r s q lp.1 n

/-- Reconstruct a stopped prefix from its terminal coordinate code. -/
def lemma77TerminalCoordinateReconstruct
    {start : TaoSection7RenewalPoint} {r s : ℕ} (overshoot : ℤ)
    (code : Lemma77TerminalCoordinate start r s) :
    List TaoSection7RenewalPoint :=
  code.2.2.2.1 ++
    [lemma77TerminalHoldPoint code.1 overshoot code.2.1.1]

/-- Every supported endpoint prefix admits a reconstructing terminal code. -/
theorem lemma77CanonicalEndpointSupportFiber_exists_terminalCoordinate
    {start : TaoSection7RenewalPoint} {s r : ℕ} {ell : ℤ}
    (x : Lemma77CanonicalEndpointSupportFiber start s r ell) :
    ∃ code : Lemma77TerminalCoordinate start r s,
      lemma77TerminalCoordinateReconstruct
          (relativeVerticalOvershoot s ell) code = x.1.1 := by
  let pre := x.1.1
  have hmass : lemma77CanonicalFirstPassagePrefixPMF start s pre ≠ 0 := by
    simpa [pre] using x.2
  have hcert := lemma77CanonicalFirstPassagePrefixPMF_nonzero_certifies hmass
  have hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix
      start s pre.length pre := hcert.1
  have hendpoint :
      lemma77HoldPrefixIncrement start pre.length pre = r ∧
        lemma77HoldPrefixVerticalIncrement start pre.length pre = ell := by
    have h := x.1.2
    constructor
    · simpa [lemma77EndpointOfPrefix, pre] using congrArg Prod.fst h
    · simpa [lemma77EndpointOfPrefix, pre] using congrArg Prod.snd h
  rcases verticalFirstPassagePrefix_exists_snoc hfirst with
    ⟨n, pref, last, hK, hlen, hsnoc⟩
  have hhold : taoSection7HoldListPMF pre.length pre ≠ 0 := by
    rw [← lemma77CanonicalFirstPassagePrefixPMF_apply_of_firstPassage
      hfirst hcert.2]
    exact hmass
  have hholdReal : (taoSection7HoldListPMF pre.length pre).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hhold, PMF.apply_ne_top _ _⟩
  have hprev : 0 ≤ lemma77HoldPrefixVerticalIncrement start n pref := by
    have hall := taoSection7HoldListPMF_ne_zero_all_l_nonneg hholdReal
    exact lemma77HoldPrefixVerticalIncrement_nonneg_of_all_l_nonneg
      start n pref (by
        intro h hh
        exact hall h (by rw [hsnoc]; simp [hh]))
  rcases lemma77EndpointFiber_snoc_terminalCoordinates
      (start := start) (origin := start) (s := s) (r := r)
      (K := pre.length) (n := n) (ell := ell)
      (pre := pre) (pref := pref) (last := last)
      hfirst hendpoint rfl hK hsnoc hlen hprev with
    ⟨q, lp, hlp, hlast, hpref⟩
  let code : Lemma77TerminalCoordinate start r s :=
    ⟨q, ⟨⟨lp, by simpa using hlp⟩, ⟨n, ⟨pref, hpref⟩⟩⟩⟩
  refine ⟨code, ?_⟩
  change pref ++
      [lemma77TerminalHoldPoint q (relativeVerticalOvershoot s ell) lp] = pre
  rw [← hlast]
  exact hsnoc.symm

/-- Chosen terminal code for a supported endpoint prefix. -/
noncomputable def lemma77CanonicalEndpointTerminalEncode
    {start : TaoSection7RenewalPoint} {s r : ℕ} {ell : ℤ}
    (x : Lemma77CanonicalEndpointSupportFiber start s r ell) :
    Lemma77TerminalCoordinate start r s :=
  Classical.choose
    (lemma77CanonicalEndpointSupportFiber_exists_terminalCoordinate x)

/-- The chosen terminal code reconstructs its source prefix. -/
theorem lemma77CanonicalEndpointTerminalEncode_reconstruct
    {start : TaoSection7RenewalPoint} {s r : ℕ} {ell : ℤ}
    (x : Lemma77CanonicalEndpointSupportFiber start s r ell) :
    lemma77TerminalCoordinateReconstruct (relativeVerticalOvershoot s ell)
        (lemma77CanonicalEndpointTerminalEncode x) = x.1.1 :=
  Classical.choose_spec
    (lemma77CanonicalEndpointSupportFiber_exists_terminalCoordinate x)

/-- The terminal encoder is injective; no target surjectivity is needed. -/
theorem lemma77CanonicalEndpointTerminalEncode_injective
    {start : TaoSection7RenewalPoint} {s r : ℕ} {ell : ℤ} :
    Function.Injective
      (lemma77CanonicalEndpointTerminalEncode
        (start := start) (s := s) (r := r) (ell := ell)) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  rw [← lemma77CanonicalEndpointTerminalEncode_reconstruct x,
    ← lemma77CanonicalEndpointTerminalEncode_reconstruct y, hxy]

/-- Native `ENNReal` snoc factorization of the iid Hold-list mass. -/
theorem taoSection7HoldListPMF_snoc
    (pre : List TaoSection7RenewalPoint) (last : TaoSection7RenewalPoint) :
    taoSection7HoldListPMF (pre.length + 1) (pre ++ [last]) =
      taoSection7HoldListPMF pre.length pre * taoSection7HoldPMF last := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))).mp
  rw [ENNReal.toReal_mul]
  exact taoSection7HoldListPMF_snoc_toReal pre last

/-- Native snoc factorization with an externally named predecessor length. -/
theorem taoSection7HoldListPMF_snoc_of_length
    {n : ℕ} {pre : List TaoSection7RenewalPoint}
    (hlen : pre.length = n) (last : TaoSection7RenewalPoint) :
    taoSection7HoldListPMF (n + 1) (pre ++ [last]) =
      taoSection7HoldListPMF n pre * taoSection7HoldPMF last := by
  subst n
  exact taoSection7HoldListPMF_snoc pre last

/-- Native mass assigned to one terminal coordinate code. -/
def lemma77TerminalCoordinateMass
    {start : TaoSection7RenewalPoint} {r s : ℕ} (overshoot : ℤ)
    (code : Lemma77TerminalCoordinate start r s) : ENNReal :=
  taoSection7HoldPMF
      (lemma77TerminalHoldPoint code.1 overshoot code.2.1.1) *
    taoSection7HoldListPMF code.2.2.1 code.2.2.2.1

/-- Reconstructing a terminal code preserves its factored iid Hold mass. -/
theorem taoSection7HoldListPMF_reconstruct_eq_terminalCoordinateMass
    {start : TaoSection7RenewalPoint} {r s : ℕ} (overshoot : ℤ)
    (code : Lemma77TerminalCoordinate start r s) :
    taoSection7HoldListPMF
        (lemma77TerminalCoordinateReconstruct overshoot code).length
        (lemma77TerminalCoordinateReconstruct overshoot code) =
      lemma77TerminalCoordinateMass overshoot code := by
  let pref := code.2.2.2.1
  let last := lemma77TerminalHoldPoint code.1 overshoot code.2.1.1
  have hlen : pref.length = code.2.2.1 := code.2.2.2.2.2
  have hfull : (pref ++ [last]).length = code.2.2.1 + 1 := by
    simp [hlen]
  unfold lemma77TerminalCoordinateReconstruct lemma77TerminalCoordinateMass
  change taoSection7HoldListPMF (pref ++ [last]).length (pref ++ [last]) =
    taoSection7HoldPMF last * taoSection7HoldListPMF code.2.2.1 pref
  rw [hfull, taoSection7HoldListPMF_snoc_of_length hlen]
  exact mul_comm _ _

/-- The supported source atom equals the mass of its chosen terminal code. -/
theorem lemma77CanonicalEndpointTerminalEncode_mass_eq
    {start : TaoSection7RenewalPoint} {s r : ℕ} {ell : ℤ}
    (x : Lemma77CanonicalEndpointSupportFiber start s r ell) :
    lemma77CanonicalFirstPassagePrefixPMF start s x.1.1 =
      lemma77TerminalCoordinateMass (relativeVerticalOvershoot s ell)
        (lemma77CanonicalEndpointTerminalEncode x) := by
  have hcert :=
    lemma77CanonicalFirstPassagePrefixPMF_nonzero_certifies x.2
  have hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix
      start s x.1.1.length x.1.1 := hcert.1
  calc
    lemma77CanonicalFirstPassagePrefixPMF start s x.1.1 =
        taoSection7HoldListPMF x.1.1.length x.1.1 :=
      lemma77CanonicalFirstPassagePrefixPMF_apply_of_firstPassage
        hfirst hcert.2
    _ = taoSection7HoldListPMF
        (lemma77TerminalCoordinateReconstruct (relativeVerticalOvershoot s ell)
          (lemma77CanonicalEndpointTerminalEncode x)).length
        (lemma77TerminalCoordinateReconstruct (relativeVerticalOvershoot s ell)
          (lemma77CanonicalEndpointTerminalEncode x)) := by
      rw [lemma77CanonicalEndpointTerminalEncode_reconstruct]
    _ = lemma77TerminalCoordinateMass (relativeVerticalOvershoot s ell)
          (lemma77CanonicalEndpointTerminalEncode x) :=
      taoSection7HoldListPMF_reconstruct_eq_terminalCoordinateMass _ _

/-- Native atomization of one exact-length predecessor endpoint fiber. -/
theorem lemma77_ofReal_holdPrefixSignedEndpointMass_eq_tsum_length_fiber
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    ENNReal.ofReal (lemma77HoldPrefixSignedEndpointMass start n j ell) =
      ∑' pref : {pref : List TaoSection7RenewalPoint //
          pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent start n j ell},
        taoSection7HoldListPMF n pref.1 := by
  let E := lemma77HoldPrefixSignedEndpointLengthEvent start n j ell
  have hsummable : Summable fun pref : {pref // pref ∈ E} =>
      (taoSection7HoldListPMF n pref.1).toReal :=
    (taoSection7HoldListPMF_summable_toReal n).subtype E
  rw [lemma77HoldPrefixSignedEndpointMass_eq_tsum_length_fiber]
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun _ => ENNReal.toReal_nonneg) hsummable]
  apply tsum_congr
  intro pref
  exact ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)

/-- Native atomization of the height-potential sum over predecessor epochs. -/
theorem lemma77_ofReal_heightPotentialMass_eq_tsum_length_fibers
    (start : TaoSection7RenewalPoint) (j : ℤ) (s' : ℕ) :
    ENNReal.ofReal (lemma77HeightPotentialMass start j s') =
      ∑' n : ℕ,
        ∑' pref : {pref : List TaoSection7RenewalPoint //
            pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent
              start n j (s' : ℤ)},
          taoSection7HoldListPMF n pref.1 := by
  unfold lemma77HeightPotentialMass
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun n => lemma77HoldPrefixSignedEndpointMass_nonneg
      start n j (s' : ℤ))
    (lemma77HeightPotentialMass_summable start j (s' : ℤ))]
  apply tsum_congr
  intro n
  exact lemma77_ofReal_holdPrefixSignedEndpointMass_eq_tsum_length_fiber
    start n j (s' : ℤ)

/-- Height-potential rows vanish at negative horizontal displacement. -/
theorem lemma77HeightPotentialMass_eq_zero_of_j_neg_terminal
    (start : TaoSection7RenewalPoint) {j : ℤ} (s' : ℕ) (hj : j < 0) :
    lemma77HeightPotentialMass start j s' = 0 := by
  unfold lemma77HeightPotentialMass
  simp_rw [lemma77HoldPrefixSignedEndpointMass_eq_zero_of_j_neg hj]
  simp

/-- Terminal rows at `r ≤ q` vanish because their predecessor shift is negative. -/
theorem lemma77EndpointTerminalSplitRow_eq_zero_of_le
    (start : TaoSection7RenewalPoint) {r q : ℕ} (s : ℕ) (overshoot : ℤ)
    (hrq : r ≤ q) :
    (∑ lp ∈ Finset.range (s + 1),
      (taoSection7HoldPMF
        (lemma77TerminalHoldPoint q overshoot lp)).toReal *
        lemma77HeightPotentialMass start
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) = 0 := by
  have hshift : lemma77HorizontalShift732 (r : ℤ) q < 0 := by
    simp [lemma77HorizontalShift732, lemma77PositiveHorizontalIncrement]
    omega
  apply Finset.sum_eq_zero
  intro lp _hlp
  rw [lemma77HeightPotentialMass_eq_zero_of_j_neg_terminal
    start (s - lp) hshift]
  simp

/-- The real outer terminal row has finite support `q < r`. -/
theorem lemma77EndpointTerminalSplitRow_summable
    (start : TaoSection7RenewalPoint) (r s : ℕ) (overshoot : ℤ) :
    Summable fun q : ℕ =>
      ∑ lp ∈ Finset.range (s + 1),
        (taoSection7HoldPMF
          (lemma77TerminalHoldPoint q overshoot lp)).toReal *
          lemma77HeightPotentialMass start
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) := by
  apply summable_of_ne_finset_zero (s := Finset.range r)
  intro q hq
  have hrq : r ≤ q := by
    simpa [Finset.mem_range, not_lt] using hq
  exact lemma77EndpointTerminalSplitRow_eq_zero_of_le
    start s overshoot hrq

/-- Ordered native evaluation of the complete terminal-coordinate target. -/
theorem lemma77_tsum_terminalCoordinateMass_eq_ofReal_terminalSplitMass
    (start : TaoSection7RenewalPoint) (r s : ℕ) (overshoot : ℤ) :
    (∑' code : Lemma77TerminalCoordinate start r s,
        lemma77TerminalCoordinateMass overshoot code) =
      ENNReal.ofReal
        (lemma77EndpointTerminalSplitMass start r s overshoot) := by
  have hreal :
      ENNReal.ofReal
          (lemma77EndpointTerminalSplitMass start r s overshoot) =
        ∑' q : ℕ,
          ∑ lp ∈ Finset.range (s + 1),
            taoSection7HoldPMF
                (lemma77TerminalHoldPoint q overshoot lp) *
              ENNReal.ofReal
                (lemma77HeightPotentialMass start
                  (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) := by
    unfold lemma77EndpointTerminalSplitMass
    rw [ENNReal.ofReal_tsum_of_nonneg]
    · apply tsum_congr
      intro q
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro lp _hlp
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
      · intro lp _hlp
        exact mul_nonneg ENNReal.toReal_nonneg
          (lemma77HeightPotentialMass_nonneg start
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))
    · intro q
      apply Finset.sum_nonneg
      intro lp _hlp
      exact mul_nonneg ENNReal.toReal_nonneg
        (lemma77HeightPotentialMass_nonneg start
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))
    · exact lemma77EndpointTerminalSplitRow_summable start r s overshoot
  rw [hreal]
  unfold lemma77TerminalCoordinateMass Lemma77TerminalCoordinate
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro q
  rw [ENNReal.tsum_sigma', tsum_fintype, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro lp hlp
  have hlp_lt : lp < s + 1 := by simpa using hlp
  rw [dite_eq_left hlp_lt]
  rw [ENNReal.tsum_sigma']
  change (∑' n : ℕ,
      ∑' pref : Lemma77TerminalPrefixFiber start r s q lp n,
        taoSection7HoldPMF (lemma77TerminalHoldPoint q overshoot lp) *
          taoSection7HoldListPMF n pref.1) = _
  simp_rw [ENNReal.tsum_mul_left]
  congr 1
  simpa [Lemma77TerminalPrefixFiber] using
    (lemma77_ofReal_heightPotentialMass_eq_tsum_length_fibers
      start (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)).symm

/-- Canonical endpoint atoms are bounded by the exact terminal split. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_apply_le_ofReal_terminalSplitMass
    (start : TaoSection7RenewalPoint) (s r : ℕ) (ell : ℤ) :
    lemma77CanonicalFirstPassageEndpointPMF start s (r, ell) ≤
      ENNReal.ofReal
        (lemma77EndpointTerminalSplitMass start r s
          (relativeVerticalOvershoot s ell)) := by
  rw [lemma77CanonicalFirstPassageEndpointPMF_apply_eq_tsum_supportFiber]
  calc
    (∑' x : Lemma77CanonicalEndpointSupportFiber start s r ell,
        lemma77CanonicalFirstPassagePrefixPMF start s x.1.1) =
        ∑' x : Lemma77CanonicalEndpointSupportFiber start s r ell,
          lemma77TerminalCoordinateMass (relativeVerticalOvershoot s ell)
            (lemma77CanonicalEndpointTerminalEncode x) := by
      apply tsum_congr
      intro x
      exact lemma77CanonicalEndpointTerminalEncode_mass_eq x
    _ ≤ ∑' code : Lemma77TerminalCoordinate start r s,
          lemma77TerminalCoordinateMass (relativeVerticalOvershoot s ell) code :=
      ENNReal.tsum_comp_le_tsum_of_injective
        lemma77CanonicalEndpointTerminalEncode_injective _
    _ = ENNReal.ofReal
        (lemma77EndpointTerminalSplitMass start r s
          (relativeVerticalOvershoot s ell)) :=
      lemma77_tsum_terminalCoordinateMass_eq_ofReal_terminalSplitMass
        start r s (relativeVerticalOvershoot s ell)

/-- The explicit real terminal split is nonnegative. -/
theorem lemma77EndpointTerminalSplitMass_nonneg
    (start : TaoSection7RenewalPoint) (r s : ℕ) (overshoot : ℤ) :
    0 ≤ lemma77EndpointTerminalSplitMass start r s overshoot := by
  unfold lemma77EndpointTerminalSplitMass
  apply tsum_nonneg
  intro q
  apply Finset.sum_nonneg
  intro lp _hlp
  exact mul_nonneg ENNReal.toReal_nonneg
    (lemma77HeightPotentialMass_nonneg start
      (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))

/-- Real point-mass corollary of the native terminal reindex. -/
theorem lemma77CanonicalFirstPassageEndpointPMF_apply_toReal_le_terminalSplitMass
    (start : TaoSection7RenewalPoint) (s r : ℕ) (ell : ℤ) :
    (lemma77CanonicalFirstPassageEndpointPMF start s (r, ell)).toReal ≤
      lemma77EndpointTerminalSplitMass start r s
        (relativeVerticalOvershoot s ell) := by
  calc
    (lemma77CanonicalFirstPassageEndpointPMF start s (r, ell)).toReal ≤
        (ENNReal.ofReal
          (lemma77EndpointTerminalSplitMass start r s
            (relativeVerticalOvershoot s ell))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (lemma77CanonicalFirstPassageEndpointPMF_apply_le_ofReal_terminalSplitMass
          start s r ell)
    _ = lemma77EndpointTerminalSplitMass start r s
        (relativeVerticalOvershoot s ell) :=
      ENNReal.toReal_ofReal
        (lemma77EndpointTerminalSplitMass_nonneg start r s
          (relativeVerticalOvershoot s ell))

end TaoSection7Lemma77

end

end Tao
end Erdos1135
