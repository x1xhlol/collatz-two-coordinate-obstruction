import Erdos1135.Tao.Renewal.Lemma79Restart

/-!
# Lemma 7.9 First-Exit Restart

This module separates Tao's vertical first-exit clock from the later stopping
times.  A first-exit certificate says that the old triangle has not yet been
left before `k1` and stays strictly below the path from `k1` onward.  That is
enough to turn a zero-inclusive trace of the restarted path into the complete
stopping tail after the old triangle, even when the restarted trace is empty
or begins at local time zero.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/--
Deterministic height contract at Tao's absolute first-exit clock.

The clock `k1` is not required to be a stopping time.  Before it, the path is
at or below the old triangle's top edge; from it onward, the path remains
strictly above that edge.
-/
structure Lemma79FirstExitCertificate
    (pointAt : ℕ -> TaoSection7Point)
    (old : TaoSection7Triangle) (p k1 : ℕ) : Prop where
  entry_lt_exit : p < k1
  before_exit_le :
    ∀ q : ℕ, p < q -> q < k1 -> (pointAt q).l ≤ old.cornerL
  at_after_exit_lt :
    ∀ q : ℕ, k1 ≤ q -> old.cornerL < (pointAt q).l

theorem Lemma79FirstExitCertificate.no_afterTriangleHit_before
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {p k1 q : ℕ}
    (h : Lemma79FirstExitCertificate pointAt old p k1)
    (hpq : p < q) (hqk : q < k1) :
    ¬ TaoSection7Case3AfterTriangleHit pointAt family old q := by
  intro hhit
  exact (not_lt_of_ge (h.before_exit_le q hpq hqk)) hhit.1

theorem Lemma79FirstExitCertificate.afterTriangleHit_iff_triangleHit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {p k1 q : ℕ}
    (h : Lemma79FirstExitCertificate pointAt old p k1)
    (hkq : k1 ≤ q) :
    TaoSection7Case3AfterTriangleHit pointAt family old q ↔
      TaoSection7Case3TriangleHit pointAt family q := by
  constructor
  · exact fun hhit => hhit.2
  · exact fun hhit => ⟨h.at_after_exit_lt q hkq, hhit⟩

/-- Shift a local stopping tail back to the global clock. -/
theorem lemma79StoppingTail_shift
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q : ℕ} {old : TaoSection7Triangle}
    {steps : List (ℕ × TaoSection7Triangle)}
    (k : ℕ)
    (htail : TaoSection7Case3StoppingTail
      (lemma79RestartPointAt pointAt k) family q old steps) :
    TaoSection7Case3StoppingTail pointAt family (k + q) old
      (lemma79ShiftSteps k steps) := by
  induction htail with
  | nil q old =>
      simpa [lemma79ShiftSteps] using
        TaoSection7Case3StoppingTail.nil
          (pointAt := pointAt) (family := family) (k + q) old
  | @cons q first old Gamma rest hstep htail ih =>
      exact TaoSection7Case3StoppingTail.cons
        { first_after_exit :=
            (lemma79FirstAfterTriangleHitFrom_restart_iff
              pointAt family old k q first).1 hstep.first_after_exit
          new_mem_family := hstep.new_mem_family
          new_mem := by
            simpa [lemma79RestartPointAt] using hstep.new_mem
          new_ne_old := hstep.new_ne_old }
        ih

/--
A zero-inclusive restarted prefix is a global stopping tail after a certified
first exit.  Its first local hit may occur at time zero.
-/
theorem lemma79InclusiveStoppingPrefix_shift_after_firstExit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {p k1 : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    (hexit : Lemma79FirstExitCertificate pointAt old p k1)
    (hprefix : Lemma79InclusiveStoppingPrefix
      (lemma79RestartPointAt pointAt k1) family steps) :
    TaoSection7Case3StoppingTail pointAt family p old
      (lemma79ShiftSteps k1 steps) := by
  cases hprefix with
  | nil =>
      simpa [lemma79ShiftSteps] using
        TaoSection7Case3StoppingTail.nil
          (pointAt := pointAt) (family := family) p old
  | @cons first Gamma rest hfirst hGamma hGamma_mem htail =>
      have htransition : TaoSection7Case3StoppingTransition
          pointAt family p old (k1 + first) Gamma := by
        refine
          { first_after_exit := ?_
            new_mem_family := hGamma
            new_mem := ?_
            new_ne_old := ?_ }
        · refine
            ⟨hexit.entry_lt_exit.trans_le (Nat.le_add_right k1 first), ?_, ?_⟩
          · refine ⟨hexit.at_after_exit_lt (k1 + first) (by omega), ?_⟩
            rcases hfirst.1 with ⟨Delta, hDelta, hDelta_mem⟩
            exact ⟨Delta, hDelta, by
              simpa [lemma79RestartPointAt] using hDelta_mem⟩
          · intro q hpq hqfirst hhit
            by_cases hqk : q < k1
            · exact hexit.no_afterTriangleHit_before hpq hqk hhit
            · have hkq : k1 ≤ q := Nat.le_of_not_gt hqk
              let u := q - k1
              have hku : k1 + u = q := Nat.add_sub_of_le hkq
              have hufirst : u < first := by omega
              apply hfirst.2 u hufirst
              rcases hhit.2 with ⟨Delta, hDelta, hDelta_mem⟩
              exact ⟨Delta, hDelta, by
                simpa [lemma79RestartPointAt, hku] using hDelta_mem⟩
        · simpa [lemma79RestartPointAt] using hGamma_mem
        · intro hEq
          subst Gamma
          exact taoSection7Case3_not_mem_of_cornerL_lt
            (hexit.at_after_exit_lt (k1 + first) (by omega))
            (by simpa [lemma79RestartPointAt] using hGamma_mem)
      exact TaoSection7Case3StoppingTail.cons htransition
        (lemma79StoppingTail_shift k1 htail)

/--
Shift a complete restarted trace into a complete global tail after the old
triangle.  This handles `k1 < C`, `k1 = C`, and `C < k1` uniformly.
-/
theorem lemma79BoundedInclusiveTrace_shift_after_firstExit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {C p k1 : ℕ}
    {steps : List (ℕ × TaoSection7Triangle)}
    (hexit : Lemma79FirstExitCertificate pointAt old p k1)
    (htrace : Lemma79BoundedInclusiveTrace
      (lemma79RestartPointAt pointAt k1) family (C - k1) steps) :
    Lemma79BoundedStoppingTail pointAt family p old C
      (lemma79ShiftSteps k1 steps) := by
  refine
    { trace_tail :=
        lemma79InclusiveStoppingPrefix_shift_after_firstExit
          hexit htrace.trace_prefix
      all_stop_lt := ?_
      terminal_empty := ?_
      terminal_last := ?_ }
  · intro step hstep
    rcases List.mem_map.mp hstep with ⟨localStep, hlocalStep, rfl⟩
    have hlt := htrace.all_stop_lt localStep hlocalStep
    omega
  · intro hnil q hpq hqC
    have hsteps : steps = [] := by
      cases steps with
      | nil => rfl
      | cons step rest => simp [lemma79ShiftSteps] at hnil
    by_cases hqk : q < k1
    · exact hexit.no_afterTriangleHit_before hpq hqk
    · have hkq : k1 ≤ q := Nat.le_of_not_gt hqk
      let u := q - k1
      have hku : k1 + u = q := Nat.add_sub_of_le hkq
      have huC : u < C - k1 := by omega
      intro hhit
      apply htrace.terminal_empty hsteps u huC
      rcases hhit.2 with ⟨Delta, hDelta, hDelta_mem⟩
      exact ⟨Delta, hDelta, by
        simpa [lemma79RestartPointAt, hku] using hDelta_mem⟩
  · intro last hlast q hlast_q hqC
    have hmap := lemma79StoppingLast?_shiftSteps k1 steps
    have hsome : Option.map
        (fun step : ℕ × TaoSection7Triangle =>
          (k1 + step.1, step.2))
        (TaoSection7Case3StoppingLast? steps) = some last := by
      rw [← hmap]
      exact hlast
    rcases Option.map_eq_some_iff.mp hsome with
      ⟨localLast, hlocalLast, hlocalEq⟩
    subst last
    have hkq : k1 ≤ q := by omega
    let u := q - k1
    have hku : k1 + u = q := Nat.add_sub_of_le hkq
    have hlast_u : localLast.1 < u := by omega
    have huC : u < C - k1 := by omega
    intro hhit
    apply htrace.terminal_last localLast hlocalLast u hlast_u huC
    simpa [TaoSection7Case3AfterTriangleHit,
      lemma79RestartPointAt, hku] using hhit

/--
The complete global tail after a nonempty trace is the shifted canonical trace
of the process restarted at the first-exit clock.
-/
theorem lemma79CutoffTrace_tail_eq_shift_firstExit
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {C p k1 : ℕ} {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hexit : Lemma79FirstExitCertificate pointAt old p k1)
    (htrace : Lemma79BoundedInclusiveTrace pointAt family C
      ((p, old) :: rest)) :
    rest = lemma79ShiftSteps k1
      (lemma79CutoffTrace
        (lemma79RestartPointAt pointAt k1) family (C - k1)) := by
  exact Lemma79BoundedStoppingTail.steps_eq_of_pairwiseDisjoint
    hpair htrace.toBoundedStoppingTail
      (lemma79BoundedInclusiveTrace_shift_after_firstExit hexit
        (lemma79CutoffTrace_spec
          (lemma79RestartPointAt pointAt k1) family (C - k1)))

/-- Hold-path specialization padded back to the canonical cutoff horizon. -/
theorem lemma79HoldPathCutoffTrace_tail_eq_shift_firstExit_padded
    {n C p k1 : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {old : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon C) family)
    (hlen : C ≤ full.length)
    (hexit : Lemma79FirstExitCertificate
      (lemma79HoldPathPointAt start full) old p k1)
    (htrace : Lemma79BoundedInclusiveTrace
      (lemma79HoldPathPointAt start full) family C
      ((p, old) :: rest)) :
    rest = lemma79ShiftSteps k1
      (lemma79CutoffTrace
        (lemma79RestartPointAt
          (lemma79HoldPathPointAt start full) k1) family C) := by
  calc
    rest = lemma79ShiftSteps k1
        (lemma79CutoffTrace
          (lemma79RestartPointAt
            (lemma79HoldPathPointAt start full) k1) family (C - k1)) :=
      lemma79CutoffTrace_tail_eq_shift_firstExit hpair hexit htrace
    _ = lemma79ShiftSteps k1
        (lemma79CutoffTrace
          (lemma79RestartPointAt
            (lemma79HoldPathPointAt start full) k1) family C) := by
      rw [lemma79HoldPathCutoffTrace_restart_padding hpair hcover hlen]

/-- Every nonnegative increment keeps a finite renewal path above its start. -/
theorem lemma79RenewalPathPoint_l_ge_start_of_all_nonneg
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    (q : ℕ)
    (hall : ∀ h, h ∈ full -> 0 ≤ h.l) :
    start.l ≤ (taoSection7RenewalPathPoint start full q).l := by
  have hnonneg :=
    TaoSection7Lemma77.lemma77HoldPrefixVerticalIncrement_nonneg_of_all_l_nonneg
      start q full hall
  simpa [TaoSection7Lemma77.lemma77HoldPrefixVerticalIncrement,
    TaoSection7Lemma77.prefixVerticalIncrement] using hnonneg

/-- A renewal path with nonnegative increments is monotone in its clock. -/
theorem lemma79RenewalPathPoint_l_mono_of_all_nonneg
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    (k u : ℕ)
    (hall : ∀ h, h ∈ full -> 0 ≤ h.l) :
    (taoSection7RenewalPathPoint start full k).l ≤
      (taoSection7RenewalPathPoint start full (k + u)).l := by
  have htail : ∀ h, h ∈ full.drop k -> 0 ≤ h.l := by
    intro h hh
    exact hall h (List.mem_of_mem_drop hh)
  have hmono := lemma79RenewalPathPoint_l_ge_start_of_all_nonneg
    (taoSection7RenewalPathPoint start full k) (full.drop k) u htail
  rw [taoSection7RenewalPathPoint_drop_add] at hmono
  exact hmono

/-- Natural vertical gap from an entry point to the old triangle's top edge. -/
def lemma79EntryVerticalGap
    (old : TaoSection7Triangle) (entry : TaoSection7Point) : ℕ :=
  (old.cornerL - entry.l).toNat

theorem lemma79EntryVerticalGap_coe_of_mem
    {old : TaoSection7Triangle} {entry : TaoSection7Point}
    (hmem : old.Mem entry) :
    old.cornerL - entry.l = (lemma79EntryVerticalGap old entry : ℤ) := by
  symm
  exact Int.toNat_of_nonneg (sub_nonneg.mpr hmem.2.1)

/--
A vertical first-passage prefix on the Hold suffix produces the global
first-exit height certificate at the absolute clock `p + K`.
-/
theorem lemma79FirstExitCertificate_of_holdPath_firstPassage
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    (old : TaoSection7Triangle) (p gap K : ℕ)
    (hgap :
      old.cornerL -
          (taoSection7RenewalPathPoint start full p).l = (gap : ℤ))
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix
      (taoSection7RenewalPathPoint start full p) gap K
        ((full.drop p).take K))
    (hall : ∀ h, h ∈ full.drop p -> 0 ≤ h.l) :
    Lemma79FirstExitCertificate
      (lemma79HoldPathPointAt start full) old p (p + K) := by
  let entry := taoSection7RenewalPathPoint start full p
  let suffix := full.drop p
  have hbase : entry.l + (gap : ℤ) = old.cornerL := by
    dsimp [entry]
    omega
  have htake : ∀ u : ℕ, u ≤ K ->
      taoSection7RenewalPathPoint entry (suffix.take K) u =
        taoSection7RenewalPathPoint entry suffix u := by
    intro u hu
    exact TaoSection7Lemma710.renewalPathPoint_take_eq_of_le
      entry suffix u K hu
  refine
    { entry_lt_exit := by
        have := hfirst.K_pos
        omega
      before_exit_le := ?_
      at_after_exit_lt := ?_ }
  · intro q hpq hqexit
    let u := q - p
    have hpu : p + u = q := Nat.add_sub_of_le (Nat.le_of_lt hpq)
    have huK : u < K := by omega
    have hminimal := hfirst.minimal u huK
    have hminimal' :
        (taoSection7RenewalPathPoint entry (suffix.take K) u).l ≤
          entry.l + (gap : ℤ) := by
      simpa [entry, suffix] using hminimal
    have hlocal :
        (taoSection7RenewalPathPoint entry suffix u).l ≤
          old.cornerL := by
      calc
        (taoSection7RenewalPathPoint entry suffix u).l =
            (taoSection7RenewalPathPoint
              entry (suffix.take K) u).l := by
                rw [htake u (Nat.le_of_lt huK)]
        _ ≤ entry.l + (gap : ℤ) := hminimal'
        _ = old.cornerL := hbase
    have hglobal := taoSection7RenewalPathPoint_drop_add start full p u
    simpa [lemma79HoldPathPointAt, entry, suffix, hpu, hglobal] using hlocal
  · intro q hqexit
    let u := q - (p + K)
    have hqeq : p + K + u = q := Nat.add_sub_of_le hqexit
    have hcross' :
        entry.l + (gap : ℤ) <
          (taoSection7RenewalPathPoint entry (suffix.take K) K).l := by
      simpa [entry, suffix] using hfirst.crosses
    have hcross :
        old.cornerL <
          (taoSection7RenewalPathPoint entry suffix K).l := by
      calc
        old.cornerL = entry.l + (gap : ℤ) := hbase.symm
        _ < (taoSection7RenewalPathPoint
              entry (suffix.take K) K).l := hcross'
        _ = (taoSection7RenewalPathPoint entry suffix K).l := by
          rw [htake K le_rfl]
    have hmono := lemma79RenewalPathPoint_l_mono_of_all_nonneg
      entry suffix K u hall
    have hlocal :
        old.cornerL <
          (taoSection7RenewalPathPoint entry suffix (K + u)).l :=
      hcross.trans_le hmono
    have hglobal := taoSection7RenewalPathPoint_drop_add
      start full p (K + u)
    have hpKu : p + (K + u) = q := by omega
    simpa [lemma79HoldPathPointAt, entry, suffix, hpKu, hglobal] using hlocal

/-- Absolute first-exit cut selected from the Hold suffix after entry time `p`. -/
noncomputable def lemma79HoldFirstExitCut
    (start : TaoSection7RenewalPoint)
    (full : List TaoSection7RenewalPoint)
    (p gap : ℕ) : ℕ :=
  lemma79VerticalFirstPassageCut
    (taoSection7RenewalPathPoint start full p) gap (full.drop p)

/--
A sufficiently long decoded raw Hold source produces the exact global
first-exit certificate.  The room premise is deliberately stated on the
common source clock.
-/
theorem lemma79FirstExitCertificate_of_decodedHoldSource
    (start : TaoSection7RenewalPoint)
    (old : TaoSection7Triangle)
    (p : ℕ) (src : List (ℕ × List ℕ))
    (hentry : old.Mem
      (lemma79HoldPathPointAt start
        (lemma79DecodeHoldSourcePrefixes src) p))
    (hroom :
      p + lemma79EntryVerticalGap old
          (lemma79HoldPathPointAt start
            (lemma79DecodeHoldSourcePrefixes src) p) + 1 ≤ src.length) :
    let full := lemma79DecodeHoldSourcePrefixes src
    let gap := lemma79EntryVerticalGap old
      (lemma79HoldPathPointAt start full p)
    let K := lemma79HoldFirstExitCut start full p gap
    Lemma79FirstExitCertificate
      (lemma79HoldPathPointAt start full) old p (p + K) := by
  dsimp only
  let full := lemma79DecodeHoldSourcePrefixes src
  let entry := taoSection7RenewalPathPoint start full p
  let gap := lemma79EntryVerticalGap old entry.toPoint
  let K := lemma79HoldFirstExitCut start full p gap
  have hp : p ≤ src.length := by omega
  have hroom' : p + gap + 1 ≤ src.length := by
    simpa [gap, entry, full, lemma79HoldPathPointAt] using hroom
  have hsuffix_len : (src.drop p).length = src.length - p := by simp
  have hgap_room : gap + 1 ≤ (src.drop p).length := by
    rw [hsuffix_len]
    omega
  have hfirstRaw := lemma79VerticalFirstPassagePrefix_take_cut_decode
    entry gap (src.drop p) hgap_room
  have hdecode_drop :
      lemma79DecodeHoldSourcePrefixes (src.drop p) = full.drop p := by
    simp [lemma79DecodeHoldSourcePrefixes, full, List.map_drop]
  have hK :
      lemma79VerticalFirstPassageCut entry gap (full.drop p) = K := by
    rfl
  have hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix
      entry gap K ((full.drop p).take K) := by
    simpa [hdecode_drop, hK] using hfirstRaw
  have hallFull := lemma79DecodeHoldSourcePrefixes_all_l_ge_one src
  have hall : ∀ h, h ∈ full.drop p -> 0 ≤ h.l := by
    intro h hh
    have hone : (1 : ℤ) ≤ h.l :=
      hallFull h (by exact List.mem_of_mem_drop hh)
    omega
  apply lemma79FirstExitCertificate_of_holdPath_firstPassage
    start full old p gap K
  · simpa [entry, full, gap, lemma79HoldPathPointAt] using
      lemma79EntryVerticalGap_coe_of_mem hentry
  · simpa [entry] using hfirst
  · exact hall

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
