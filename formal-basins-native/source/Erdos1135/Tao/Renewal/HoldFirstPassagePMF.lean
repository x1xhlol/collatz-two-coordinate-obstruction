import Erdos1135.Tao.Renewal.HoldIID
import Erdos1135.Tao.Renewal.VerticalFirstPassageBasic
import Mathlib.Tactic

/-!
# Canonical Hold First-Passage Prefix PMF

This low module owns the raw-source decoder, least positive vertical cut, and
the p-free stopped-prefix law at the exact horizon `gap + 1`.  It contains no
fresh-tail, endpoint, geometry, or finite-carrier machinery.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Decode the raw iid Hold source-prefix carrier to renewal increments. -/
def lemma79DecodeHoldSourcePrefixes
    (xs : List (ℕ × List ℕ)) : List TaoSection7RenewalPoint :=
  xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2

@[simp] theorem lemma79DecodeHoldSourcePrefixes_length
    (xs : List (ℕ × List ℕ)) :
    (lemma79DecodeHoldSourcePrefixes xs).length = xs.length := by
  simp [lemma79DecodeHoldSourcePrefixes]

/-- Every renewal increment decoded from the raw Hold source raises `l`. -/
theorem lemma79DecodeHoldSourcePrefixes_all_l_ge_one
    (xs : List (ℕ × List ℕ)) :
    taoSection7AllHoldIncrementsLGeOne
      (lemma79DecodeHoldSourcePrefixes xs) := by
  intro h hh
  rw [lemma79DecodeHoldSourcePrefixes] at hh
  rcases List.mem_map.mp hh with ⟨x, _hx, rfl⟩
  change (1 : ℤ) ≤ Int.ofNat (x.2.sum + 3)
  exact Int.ofNat_le.mpr (show 1 ≤ x.2.sum + 3 by omega)

/-- Every nonzero iid Hold-list atom consists entirely of increments whose
vertical coordinate is at least one. -/
theorem taoSection7HoldListPMF_ne_zero_all_l_ge_one
    {N : ℕ} {full : List TaoSection7RenewalPoint}
    (hfull : taoSection7HoldListPMF N full ≠ 0) :
    taoSection7AllHoldIncrementsLGeOne full := by
  have hmem : full ∈ (taoSection7HoldListPMF N).support := hfull
  rw [← taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq N] at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
    ⟨src, _hsrc, hdecode⟩
  have hdecode' : lemma79DecodeHoldSourcePrefixes src = full := by
    simpa [lemma79DecodeHoldSourcePrefixes] using hdecode
  rw [← hdecode']
  exact lemma79DecodeHoldSourcePrefixes_all_l_ge_one src

/-- Least positive vertical crossing time, totalized by zero if none exists. -/
noncomputable def lemma79VerticalFirstPassageCut
    (start : TaoSection7RenewalPoint) (gap : ℕ)
    (full : List TaoSection7RenewalPoint) : ℕ := by
  classical
  exact if h : ∃ K : ℕ,
      0 < K ∧ K ≤ full.length ∧
        start.l + (gap : ℤ) <
          (taoSection7RenewalPathPoint start full K).l then
    Nat.find h
  else
    0

/-- A certified first-passage prefix determines the cut of every extension. -/
theorem lemma79VerticalFirstPassageCut_append_eq
    {start : TaoSection7RenewalPoint} {gap K : ℕ}
    {pre : List TaoSection7RenewalPoint}
    (tail : List TaoSection7RenewalPoint)
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre) :
    lemma79VerticalFirstPassageCut start gap (pre ++ tail) = K := by
  let full := pre ++ tail
  let P : ℕ → Prop := fun k =>
    0 < k ∧ k ≤ full.length ∧
      start.l + (gap : ℤ) <
        (taoSection7RenewalPathPoint start full k).l
  have hpre_take : full.take K = pre := by
    simp [full, ← hfirst.length_eq]
  have hKle : K ≤ full.length := by
    simp [full, hfirst.length_eq]
  have hpath_K :
      taoSection7RenewalPathPoint start full K =
        taoSection7RenewalPathPoint start pre K := by
    calc
      taoSection7RenewalPathPoint start full K =
          taoSection7RenewalPathPoint start (full.take K) K :=
        (taoSection7RenewalPathPoint_take_eq_of_le
          start full K K le_rfl).symm
      _ = taoSection7RenewalPathPoint start pre K := by rw [hpre_take]
  have hKmem : P K :=
    ⟨hfirst.K_pos, hKle, by simpa [hpath_K] using hfirst.crosses⟩
  have hex : ∃ k, P k := ⟨K, hKmem⟩
  rw [lemma79VerticalFirstPassageCut, dif_pos hex]
  apply Nat.le_antisymm
  · exact Nat.find_min' hex hKmem
  · by_contra hnot
    have hfind_lt : Nat.find hex < K := Nat.lt_of_not_ge hnot
    have hspec : P (Nat.find hex) := Nat.find_spec hex
    have hpath_find :
        taoSection7RenewalPathPoint start pre (Nat.find hex) =
          taoSection7RenewalPathPoint start full (Nat.find hex) := by
      calc
        taoSection7RenewalPathPoint start pre (Nat.find hex) =
            taoSection7RenewalPathPoint start (full.take K) (Nat.find hex) := by
          rw [hpre_take]
        _ = taoSection7RenewalPathPoint start full (Nat.find hex) :=
          taoSection7RenewalPathPoint_take_eq_of_le
            start full (Nat.find hex) K (Nat.le_of_lt hfind_lt)
    have hbefore := hfirst.minimal (Nat.find hex) hfind_lt
    have hcross_find :
        start.l + (gap : ℤ) <
          (taoSection7RenewalPathPoint start pre (Nat.find hex)).l := by
      simpa [hpath_find] using hspec.2.2
    exact (not_lt_of_ge hbefore) hcross_find

/-- The totalized first-passage cut never exceeds the list length. -/
theorem lemma79VerticalFirstPassageCut_le_length
    (start : TaoSection7RenewalPoint) (gap : ℕ)
    (full : List TaoSection7RenewalPoint) :
    lemma79VerticalFirstPassageCut start gap full ≤ full.length := by
  classical
  by_cases h : ∃ K : ℕ,
      0 < K ∧ K ≤ full.length ∧
        start.l + (gap : ℤ) <
          (taoSection7RenewalPathPoint start full K).l
  · rw [lemma79VerticalFirstPassageCut, dif_pos h]
    exact (Nat.find_spec h).2.1
  · rw [lemma79VerticalFirstPassageCut, dif_neg h]
    exact Nat.zero_le full.length

/-- A positive named cut carries its exact first-passage certificate. -/
theorem lemma79VerticalFirstPassagePrefix_take_cut_of_pos
    (start : TaoSection7RenewalPoint) (gap : ℕ)
    (full : List TaoSection7RenewalPoint)
    (hpos : 0 < lemma79VerticalFirstPassageCut start gap full) :
    TaoSection7Lemma710.VerticalFirstPassagePrefix
      start gap (lemma79VerticalFirstPassageCut start gap full)
        (full.take (lemma79VerticalFirstPassageCut start gap full)) := by
  classical
  let K := lemma79VerticalFirstPassageCut start gap full
  let P : ℕ → Prop := fun k =>
    0 < k ∧ k ≤ full.length ∧
      start.l + (gap : ℤ) <
        (taoSection7RenewalPathPoint start full k).l
  have hex : ∃ k, P k := by
    by_contra hnone
    have hzero : K = 0 := by
      dsimp [K]
      rw [lemma79VerticalFirstPassageCut, dif_neg (by simpa [P] using hnone)]
    exact (Nat.ne_of_gt hpos) hzero
  have hKfind : K = Nat.find hex := by
    dsimp [K]
    rw [lemma79VerticalFirstPassageCut, dif_pos (by simpa [P] using hex)]
  have hspec : P K := by
    rw [hKfind]
    exact Nat.find_spec hex
  refine
    { K_pos := hspec.1
      length_eq := by
        change (full.take K).length = K
        simp [List.length_take, hspec.2.1]
      crosses := ?_
      minimal := ?_ }
  · have hpath :
        taoSection7RenewalPathPoint start (full.take K) K =
          taoSection7RenewalPathPoint start full K :=
      taoSection7RenewalPathPoint_take_eq_of_le start full K K le_rfl
    simpa [K, hpath] using hspec.2.2
  · intro k hk
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hpath :
          taoSection7RenewalPathPoint start (full.take K) k =
            taoSection7RenewalPathPoint start full k :=
        taoSection7RenewalPathPoint_take_eq_of_le
          start full k K (Nat.le_of_lt hk)
      by_contra hnot
      have hcross_full :
          start.l + (gap : ℤ) <
            (taoSection7RenewalPathPoint start full k).l := by
        have hcross_take :
            start.l + (gap : ℤ) <
              (taoSection7RenewalPathPoint start (full.take K) k).l :=
          lt_of_not_ge hnot
        simpa [hpath] using hcross_take
      have hkfind : k < Nat.find hex := by
        rw [← hKfind]
        exact hk
      exact (Nat.find_min (p := P) hex hkfind)
        ⟨Nat.pos_of_ne_zero hk0,
          (Nat.le_of_lt hk).trans hspec.2.1, hcross_full⟩

/-- Decoded horizon `gap+1` always contains a positive crossing by that horizon. -/
theorem lemma79VerticalFirstPassageCut_decode_pos_le_gap_add_one
    (start : TaoSection7RenewalPoint) (gap : ℕ)
    (src : List (ℕ × List ℕ))
    (hlen : gap + 1 ≤ src.length) :
    0 < lemma79VerticalFirstPassageCut start gap
        (lemma79DecodeHoldSourcePrefixes src) ∧
      lemma79VerticalFirstPassageCut start gap
        (lemma79DecodeHoldSourcePrefixes src) ≤ gap + 1 := by
  let full := lemma79DecodeHoldSourcePrefixes src
  let B := gap + 1
  have hBlen : B ≤ full.length := by simpa [B, full] using hlen
  have hgrowth :
      start.l + (B : ℤ) ≤
        (taoSection7RenewalPathPoint start full B).l :=
    taoSection7RenewalPathPoint_l_growth_ge_steps start full B hBlen
      (lemma79DecodeHoldSourcePrefixes_all_l_ge_one src)
  have hcross :
      start.l + (gap : ℤ) <
        (taoSection7RenewalPathPoint start full B).l := by
    have hgap_lt_B : (gap : ℤ) < (B : ℤ) := by simp [B]
    omega
  let P : ℕ → Prop := fun K =>
    0 < K ∧ K ≤ full.length ∧
      start.l + (gap : ℤ) <
        (taoSection7RenewalPathPoint start full K).l
  have hBmem : P B := ⟨by simp [B], hBlen, hcross⟩
  have hex : ∃ K, P K := ⟨B, hBmem⟩
  have hcut : lemma79VerticalFirstPassageCut start gap full = Nat.find hex := by
    rw [lemma79VerticalFirstPassageCut, dif_pos hex]
  rw [show lemma79DecodeHoldSourcePrefixes src = full from rfl, hcut]
  exact ⟨(Nat.find_spec hex).1, Nat.find_min' hex hBmem⟩

theorem lemma79VerticalFirstPassagePrefix_take_cut_decode_and_le
    (start : TaoSection7RenewalPoint) (gap : ℕ)
    (src : List (ℕ × List ℕ))
    (hlen : gap + 1 ≤ src.length) :
    let full := lemma79DecodeHoldSourcePrefixes src
    let K := lemma79VerticalFirstPassageCut start gap full
    TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K (full.take K) ∧
      K ≤ gap + 1 := by
  dsimp
  have hcut := lemma79VerticalFirstPassageCut_decode_pos_le_gap_add_one
    start gap src hlen
  exact ⟨lemma79VerticalFirstPassagePrefix_take_cut_of_pos
    start gap (lemma79DecodeHoldSourcePrefixes src) hcut.1, hcut.2⟩

/-- Source-facing exact-cut certificate without projecting the horizon bound. -/
theorem lemma79VerticalFirstPassagePrefix_take_cut_decode
    (start : TaoSection7RenewalPoint) (gap : ℕ)
    (src : List (ℕ × List ℕ))
    (hlen : gap + 1 ≤ src.length) :
    let full := lemma79DecodeHoldSourcePrefixes src
    let K := lemma79VerticalFirstPassageCut start gap full
    TaoSection7Lemma710.VerticalFirstPassagePrefix
      start gap K (full.take K) := by
  exact (lemma79VerticalFirstPassagePrefix_take_cut_decode_and_le
    start gap src hlen).1

/-- A certified `take K` prefix identifies the totalized cut. -/
theorem lemma79VerticalFirstPassageCut_eq_of_take_eq
    {start : TaoSection7RenewalPoint} {gap K : ℕ}
    {pre full : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (htake : full.take K = pre) :
    lemma79VerticalFirstPassageCut start gap full = K := by
  have hfull : full = pre ++ full.drop K := by
    calc
      full = full.take K ++ full.drop K := (List.take_append_drop K full).symm
      _ = pre ++ full.drop K := by rw [htake]
  rw [hfull]
  exact lemma79VerticalFirstPassageCut_append_eq (full.drop K) hfirst

/-- PMF map point masses agree when their source fibers agree. -/
theorem lemma79_map_apply_eq_of_fiber_iff
    {Src A B : Type*} (rho : PMF Src)
    (f : Src → A) (g : Src → B) (a : A) (b : B)
    (hfiber : ∀ src, a = f src ↔ b = g src) :
    (rho.map f) a = (rho.map g) b := by
  classical
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro src
  by_cases ha : a = f src
  · have hb : b = g src := (hfiber src).mp ha
    simp [ha, hb]
  · have hb : b ≠ g src := fun hb => ha ((hfiber src).mpr hb)
    simp [ha, hb]

/-- The p-free canonical stopped-prefix law at the exact horizon `gap+1`. -/
noncomputable def lemma77CanonicalFirstPassagePrefixPMF
    (start : TaoSection7RenewalPoint) (gap : ℕ) :
    PMF (List TaoSection7RenewalPoint) :=
  (taoSection7HoldSourcePrefixListPMF (gap + 1)).map fun src =>
    let full := lemma79DecodeHoldSourcePrefixes src
    full.take (lemma79VerticalFirstPassageCut start gap full)

theorem lemma77CanonicalFirstPassageTake_eq_iff_take_eq
    {start : TaoSection7RenewalPoint} {gap K : ℕ}
    {pre full : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre) :
    full.take (lemma79VerticalFirstPassageCut start gap full) = pre ↔
      full.take K = pre := by
  constructor
  · intro hpre
    have hcut_le := lemma79VerticalFirstPassageCut_le_length start gap full
    have hcut : lemma79VerticalFirstPassageCut start gap full = K := by
      calc
        lemma79VerticalFirstPassageCut start gap full =
            (full.take (lemma79VerticalFirstPassageCut start gap full)).length := by
          simp [List.length_take, hcut_le]
        _ = pre.length := congrArg List.length hpre
        _ = K := hfirst.length_eq
    simpa [hcut] using hpre
  · intro htake
    have hcut := lemma79VerticalFirstPassageCut_eq_of_take_eq hfirst htake
    simpa [hcut] using htake

/-- A certified prefix has its ordinary iid Hold-list point mass. -/
theorem lemma77CanonicalFirstPassagePrefixPMF_apply_of_firstPassage
    {start : TaoSection7RenewalPoint} {gap K : ℕ}
    {pre : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (hK : K ≤ gap + 1) :
    lemma77CanonicalFirstPassagePrefixPMF start gap pre =
      taoSection7HoldListPMF K pre := by
  unfold lemma77CanonicalFirstPassagePrefixPMF
  have hmap :
      ((taoSection7HoldSourcePrefixListPMF (gap + 1)).map
          (fun src =>
            let full := lemma79DecodeHoldSourcePrefixes src
            full.take (lemma79VerticalFirstPassageCut start gap full))) pre =
        ((taoSection7HoldSourcePrefixListPMF (gap + 1)).map
          (fun src => (lemma79DecodeHoldSourcePrefixes src).take K)) pre :=
    lemma79_map_apply_eq_of_fiber_iff
      (taoSection7HoldSourcePrefixListPMF (gap + 1)) _ _ pre pre (by
        intro src
        simpa only [eq_comm] using
          lemma77CanonicalFirstPassageTake_eq_iff_take_eq
            (full := lemma79DecodeHoldSourcePrefixes src) hfirst)
  rw [hmap]
  have htake := taoSection7HoldSourcePrefixListPMF_map_take_holdPoint_eq_of_le hK
  exact congrArg (fun rho : PMF (List TaoSection7RenewalPoint) => rho pre)
    (by simpa [lemma79DecodeHoldSourcePrefixes] using htake)

/-- Every nonzero canonical atom carries first passage and the horizon bound. -/
theorem lemma77CanonicalFirstPassagePrefixPMF_nonzero_certifies
    {start : TaoSection7RenewalPoint} {gap : ℕ}
    {pre : List TaoSection7RenewalPoint}
    (hne : lemma77CanonicalFirstPassagePrefixPMF start gap pre ≠ 0) :
    TaoSection7Lemma710.VerticalFirstPassagePrefix
        start gap pre.length pre ∧
      pre.length ≤ gap + 1 := by
  classical
  have hmem : pre ∈ (lemma77CanonicalFirstPassagePrefixPMF start gap).support := hne
  unfold lemma77CanonicalFirstPassagePrefixPMF at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with ⟨src, hsrc, hout⟩
  have hsrc_length : src.length = gap + 1 := by
    by_contra hneq
    exact hsrc (taoSection7HoldSourcePrefixListPMF_apply_eq_zero_of_length_ne
      (gap + 1) src hneq)
  let full := lemma79DecodeHoldSourcePrefixes src
  let K := lemma79VerticalFirstPassageCut start gap full
  have hcert := lemma79VerticalFirstPassagePrefix_take_cut_decode_and_le
    start gap src (by omega)
  change
    TaoSection7Lemma710.VerticalFirstPassagePrefix
        start gap K (full.take K) ∧ K ≤ gap + 1 at hcert
  have hpre : full.take K = pre := by
    change full.take K = pre at hout
    exact hout
  have hK : K = pre.length := by
    calc
      K = (full.take K).length := hcert.1.length_eq.symm
      _ = pre.length := congrArg List.length hpre
  have hfirst :
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        start gap pre.length pre := by
    rw [← hK, ← hpre]
    exact hcert.1
  exact ⟨hfirst, by simpa [← hK] using hcert.2⟩

/-- Invalid stopped prefixes have zero canonical mass. -/
theorem lemma77CanonicalFirstPassagePrefixPMF_apply_eq_zero_of_invalid
    {start : TaoSection7RenewalPoint} {gap : ℕ}
    {pre : List TaoSection7RenewalPoint}
    (hinvalid :
      ¬ (TaoSection7Lemma710.VerticalFirstPassagePrefix
          start gap pre.length pre ∧ pre.length ≤ gap + 1)) :
    lemma77CanonicalFirstPassagePrefixPMF start gap pre = 0 := by
  by_contra hne
  exact hinvalid (lemma77CanonicalFirstPassagePrefixPMF_nonzero_certifies hne)

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
