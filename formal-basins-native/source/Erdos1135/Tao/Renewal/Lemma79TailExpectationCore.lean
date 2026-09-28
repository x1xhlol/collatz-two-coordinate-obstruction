import Erdos1135.Tao.Renewal.Lemma77FirstPassageEndpoint
import Erdos1135.Tao.Renewal.Lemma710PostStoppedKernel
import Erdos1135.Tao.Renewal.HoldFirstPassagePMF
import Erdos1135.Tao.Renewal.Prop78Case3Stopping

/-!
# Lemma 7.9 Repaired Tail Expectation Sockets

This module names the first expectation-side sockets for the repaired Lemma
7.9 tail statistic used by the Case 3 packet.  It deliberately does not prove
the full Lemma 7.9 expectation estimate.  The checked algebra here isolates
the first-entry exit-white contraction that Tao obtains by reusing the
`loko-4` first-passage argument.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Indicator-weighted finite-PMF random variable for one atom. -/
noncomputable def atomIndicator {Omega : Type*}
    (Atom : Set Omega) (X : Omega -> ℝ) : Omega -> ℝ := by
  classical
  exact fun omega => if omega ∈ Atom then X omega else 0

/--
One-step exponential weight from the exit-white event.

This is the scalar `exp(-1_W)` factor in Tao's Lemma 7.9 induction, with value
`exp(-1)` on the white exit event and `1` off it.
-/
noncomputable def exitWhiteWeight {Omega : Type*}
    (ExitWhite : Set Omega) : Omega -> ℝ := by
  classical
  exact fun omega => if omega ∈ ExitWhite then Real.exp (-1) else 1

/-- Atom-local future moment after the first-entry restart. -/
noncomputable def exitFutureMoment {Omega : Type*}
    (Atom ExitWhite : Set Omega) (futureMoment : Omega -> ℝ) : Omega -> ℝ :=
  atomIndicator Atom (fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega)

/--
Source-facing data for the repaired tail moment.

This is only the samplewise moment identity.  The source-law induction that
proves its expectation bound is split into restart, tower, and exit-white
sockets below.
-/
structure Lemma79TailMomentData
    {Omega : Type*} [Fintype Omega]
    (steps : Omega -> List (ℕ × TaoSection7Triangle))
    (R : ℕ)
    (tailCount : Omega -> ℕ)
    (epsilon : ℝ)
    (tailMoment : Omega -> ℝ) : Prop where
  repaired_tail :
    Lemma79RepairedTailOnRGeR steps R tailCount tailMoment epsilon

/--
First triangle hit in the Lemma 7.9 first-entry partition, allowing the
time-zero atom.

The reusable Case 3 stopping predicate `TaoSection7Case3FirstTriangleHitFrom`
is strict above its start index, so `start = 0` excludes the `t_1 = 0` slice.
Lemma 7.9 needs the actual first hit time in `ℕ`, including zero.
-/
def Lemma79FirstTriangleHitFromZero
    (pointAt : ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (first : ℕ) : Prop :=
  TaoSection7Case3TriangleHit pointAt family first ∧
    ∀ s : ℕ, s < first ->
      ¬ TaoSection7Case3TriangleHit pointAt family s

theorem Lemma79FirstTriangleHitFromZero.to_firstTriangleHitFrom
    {pointAt : ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {first : ℕ}
    (hfirst : Lemma79FirstTriangleHitFromZero pointAt family first)
    (hpos : 0 < first) :
    TaoSection7Case3FirstTriangleHitFrom pointAt family 0 first := by
  rcases hfirst with ⟨hhit, hminimal⟩
  exact ⟨hpos, hhit, fun s _hs0 hslt => hminimal s hslt⟩

/--
First-entry atom family for the Lemma 7.9 induction.

The atom metadata keeps the future exit-white socket from degenerating to a
bare `{t_1 = p}` partition: each atom carries its time, entry triangle, entry
point, and prefix-white history.
-/
structure Lemma79FirstEntryAtomFamily
    {Omega iota : Type*} [Fintype iota]
    (nonzero : Set Omega)
    (W : Omega -> ℕ -> Prop)
    (pointAt : Omega -> ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) : Type _ where
  atom : iota -> Set Omega
  firstEntryTime : iota -> ℕ
  entryTriangle : iota -> TaoSection7Triangle
  entryPoint : iota -> TaoSection7Point
  atom_subset_nonzero : ∀ i, atom i ⊆ nonzero
  cover_nonzero : ∀ omega, omega ∈ nonzero -> ∃ i, omega ∈ atom i
  atom_unique : ∀ omega i j, omega ∈ atom i -> omega ∈ atom j -> i = j
  first_entry :
    ∀ i omega, omega ∈ atom i ->
      Lemma79FirstTriangleHitFromZero
        (pointAt omega) family (firstEntryTime i)
  entry_eq :
    ∀ i omega, omega ∈ atom i ->
      pointAt omega (firstEntryTime i) = entryPoint i
  entry_triangle_mem : ∀ i, entryTriangle i ∈ family
  entry_mem_triangle : ∀ i, (entryTriangle i).Mem (entryPoint i)
  prefix_white :
    ∀ i omega, omega ∈ atom i ->
      ∀ p : ℕ, p < firstEntryTime i -> W omega p

/--
Source shape for one first-entry atom in Tao's Lemma 7.9 proof.

This is intentionally just the line-1690 atom data: first-entry time, first
triangle, entry point, and prefix-white history.  Packet parameters such as
`R`, `FSlack`, endpoint budgets, and many-white conclusions stay outside this
source atom.  It also deliberately has no near-top hypothesis; Lemma 7.9 reuses
only Tao's `loko-4` exit-white subargument, not the full near-top Case 2
estimate.
-/
structure Lemma79FirstEntryAtom
    (W : ℕ -> Prop)
    (family : Set TaoSection7Triangle)
    (pointAt : ℕ -> TaoSection7Point)
    (first : ℕ)
    (Delta : TaoSection7Triangle)
    (entry : TaoSection7Point) : Prop where
  first_hit :
    Lemma79FirstTriangleHitFromZero pointAt family first
  entry_triangle_mem : Delta ∈ family
  entry_mem_triangle : Delta.Mem entry
  entry_eq : pointAt first = entry
  prefix_white :
    ∀ p : ℕ, p < first -> W p

namespace Lemma79FirstEntryAtomFamily

theorem firstEntryAtom_of_mem
    {Omega iota : Type*} [Fintype iota]
    {nonzero : Set Omega}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    (A : Lemma79FirstEntryAtomFamily nonzero W pointAt family)
    {i : iota} {omega : Omega}
    (hmem : omega ∈ A.atom i) :
    Lemma79FirstEntryAtom (W omega) family (pointAt omega)
      (A.firstEntryTime i) (A.entryTriangle i) (A.entryPoint i) where
  first_hit := A.first_entry i omega hmem
  entry_triangle_mem := A.entry_triangle_mem i
  entry_mem_triangle := A.entry_mem_triangle i
  entry_eq := A.entry_eq i omega hmem
  prefix_white := A.prefix_white i omega hmem

end Lemma79FirstEntryAtomFamily

/--
Deterministic restart identity for one first-entry atom.

The atom is expected to include the branch conditions under which the first
entry has occurred.  This socket records only the samplewise split of the
repaired tail moment into the exit-white factor and the restarted future
moment.
-/
structure Lemma79TailRestartIdentity
    {Omega : Type*}
    (Atom ExitWhite : Set Omega)
    (tailMoment futureMoment : Omega -> ℝ) : Prop where
  split_on_atom :
    ∀ omega, omega ∈ Atom ->
      tailMoment omega =
        exitWhiteWeight ExitWhite omega * futureMoment omega

/--
Stopped-prefix tower input for one atom.

This is the source-law socket: after conditioning on the first-entry atom and
integrating the restarted future first, the future contribution is bounded by
`exp epsilon` times the exit-white one-step weight.
-/
structure Lemma79TailTowerInput
    {Omega : Type*} [Fintype Omega]
    (mu : PMF Omega)
    (Atom ExitWhite : Set Omega)
    (futureMoment : Omega -> ℝ)
    (epsilon : ℝ) : Prop where
  tower_le :
    pmfExpectation mu (exitFutureMoment Atom ExitWhite futureMoment) ≤
      Real.exp epsilon *
        pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite))

/--
Exit-white lower-bound socket for one first-entry atom.

The hard source-specific theorem should prove `exitWhite_prob_ge` by repeating
the first-passage-to-white argument used for Tao's `(7.51)`/`loko-4`.
The scalar field records the small-`epsilon` bridge needed to turn that lower
bound into the contraction factor.
-/
structure Lemma79ExitWhiteContraction
    {Omega : Type*} [Fintype Omega]
    (mu : PMF Omega)
    (Atom ExitWhite : Set Omega)
    (c0 epsilon : ℝ) : Prop where
  exitWhite_prob_ge :
    c0 * pmfProb mu Atom ≤ pmfProb mu (Atom ∩ ExitWhite)
  epsilon_small :
    1 - (1 - Real.exp (-1)) * c0 ≤ Real.exp (-epsilon)

/--
Probability partition data for lifting per-atom exit-white lower bounds to the
whole nonzero branch.

The actual source partition and disjoint-union equalities remain explicit
inputs; this record only keeps the algebraic consumer from hiding the hard
first-entry atom theorem.
-/
structure Lemma79ExitWhiteAtomPartition
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    (mu : PMF Omega)
    (nonzero ExitWhite : Set Omega)
    (atom : iota -> Set Omega)
    (c0 : ℝ) : Prop where
  prob_partition :
    pmfProb mu nonzero = ∑ i, pmfProb mu (atom i)
  exit_partition_le :
    (∑ i, pmfProb mu (atom i ∩ ExitWhite)) ≤
      pmfProb mu (nonzero ∩ ExitWhite)
  atom_exitWhite_ge :
    ∀ i, c0 * pmfProb mu (atom i) ≤
      pmfProb mu (atom i ∩ ExitWhite)

theorem Lemma79ExitWhiteAtomPartition.exitWhite_prob_ge
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {nonzero ExitWhite : Set Omega}
    {atom : iota -> Set Omega}
    {c0 : ℝ}
    (h : Lemma79ExitWhiteAtomPartition mu nonzero ExitWhite atom c0) :
    c0 * pmfProb mu nonzero ≤ pmfProb mu (nonzero ∩ ExitWhite) := by
  rw [h.prob_partition, Finset.mul_sum]
  exact le_trans
    (Finset.sum_le_sum fun i _hi => h.atom_exitWhite_ge i)
    h.exit_partition_le

theorem Lemma79ExitWhiteAtomPartition.to_contraction
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {nonzero ExitWhite : Set Omega}
    {atom : iota -> Set Omega}
    {c0 epsilon : ℝ}
    (h : Lemma79ExitWhiteAtomPartition mu nonzero ExitWhite atom c0)
    (hscalar :
      1 - (1 - Real.exp (-1)) * c0 ≤ Real.exp (-epsilon)) :
    Lemma79ExitWhiteContraction mu nonzero ExitWhite c0 epsilon where
  exitWhite_prob_ge := h.exitWhite_prob_ge
  epsilon_small := hscalar

/--
Source-level first-passage lower-bound socket for the repeated `loko-4`
argument inside Lemma 7.9.

This is intentionally not the final white-exit conclusion.  It records the
future theorem that a first-entry atom has a constant-probability good
geometric exit, with vertical first-passage data visible.
-/
structure Lemma79FirstEntryExitGoodSource
    {Omega : Type*} [Fintype Omega]
    (mu : PMF Omega)
    (Atom ExitGood : Set Omega)
    (entry : Omega -> TaoSection7Point)
    (Delta : TaoSection7Triangle)
    (start : Omega -> TaoSection7RenewalPoint)
    (verticalGap K : Omega -> ℕ)
    (pre : Omega -> List TaoSection7RenewalPoint)
    (c0 : ℝ) : Prop where
  entry_mem_triangle :
    ∀ omega, omega ∈ Atom -> Delta.Mem (entry omega)
  vertical_first_passage :
    ∀ omega, omega ∈ Atom ->
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        (start omega) (verticalGap omega) (K omega) (pre omega)
  good_exit_prob_ge :
    c0 * pmfProb mu Atom ≤ pmfProb mu (Atom ∩ ExitGood)

/--
Fixed-entry source layer for the Lemma 7.9 first-entry exit-good step.

Tao's reused `loko-4` argument is applied after conditioning on a single
first-entry atom: the entry triangle, entry point, restart origin, and vertical
gap are fixed on that atom.  This record keeps that source boundary visible
before erasing down to the lower algebraic socket
`Lemma79FirstEntryExitGoodSource`.
-/
structure Lemma79FixedFirstEntryExitGoodSource
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    (mu : PMF Omega)
    (nonzero Atom ExitGood : Set Omega)
    (W : Omega -> ℕ -> Prop)
    (pointAt : Omega -> ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family)
    (i : iota)
    (origin : TaoSection7RenewalPoint)
    (gap : ℕ)
    (K : Omega -> ℕ)
    (pre : Omega -> List TaoSection7RenewalPoint)
    (c0 : ℝ) : Prop where
  atom_eq : Atom = firstAtoms.atom i
  origin_entry : origin.toPoint = firstAtoms.entryPoint i
  gap_height :
    origin.l + (gap : ℤ) = (firstAtoms.entryTriangle i).cornerL
  source_on_atom :
    TaoSection7Lemma77.Lemma77EndpointSourceProvenanceOnGood
      mu (fun _ => origin) K pre gap Atom
  first_passage_on_atom :
    ∀ omega, omega ∈ Atom ->
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        origin gap (K omega) (pre omega)
  good_exit_prob_ge :
    c0 * pmfProb mu Atom ≤ pmfProb mu (Atom ∩ ExitGood)

/--
Fixed-entry suffix first-passage law for the reused `loko-4` lower bound.

After conditioning on one first-entry atom, the suffix process is represented
by a sample map into an abstract first-passage suffix space.  The law states
that suffix events factor as the parent atom mass times a fixed suffix
probability.
-/
structure Lemma79FixedEntrySuffixFirstPassageLaw
    {Omega Suffix : Type*} [Fintype Omega]
    (mu : PMF Omega)
    (Atom : Set Omega)
    (suffix : Omega -> Suffix)
    (holdFirstPassageProb : Set Suffix -> ℝ) : Prop where
  suffix_law :
    ∀ S : Set Suffix,
      pmfProb mu {omega | omega ∈ Atom ∧ suffix omega ∈ S} =
        pmfProb mu Atom * holdFirstPassageProb S

theorem lemma79_loko4_fixedEntry_goodExit_prob_ge
    {Omega Suffix : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {Atom ExitGood : Set Omega}
    {suffix : Omega -> Suffix}
    {holdFirstPassageProb : Set Suffix -> ℝ}
    {loko4GoodExit : Set Suffix}
    {c0 : ℝ}
    (hlaw :
      Lemma79FixedEntrySuffixFirstPassageLaw
        mu Atom suffix holdFirstPassageProb)
    (hloko4 : c0 ≤ holdFirstPassageProb loko4GoodExit)
    (hsubset :
      {omega | omega ∈ Atom ∧ suffix omega ∈ loko4GoodExit} ⊆
        Atom ∩ ExitGood) :
    c0 * pmfProb mu Atom ≤ pmfProb mu (Atom ∩ ExitGood) := by
  have hmass_nonneg : 0 ≤ pmfProb mu Atom := pmfProb_nonneg mu Atom
  have hmul :
      c0 * pmfProb mu Atom ≤
        holdFirstPassageProb loko4GoodExit * pmfProb mu Atom :=
    mul_le_mul_of_nonneg_right hloko4 hmass_nonneg
  calc
    c0 * pmfProb mu Atom ≤
        holdFirstPassageProb loko4GoodExit * pmfProb mu Atom :=
          hmul
    _ = pmfProb mu Atom * holdFirstPassageProb loko4GoodExit := by
          ring
    _ = pmfProb mu {omega |
          omega ∈ Atom ∧ suffix omega ∈ loko4GoodExit} := by
          exact (hlaw.suffix_law loko4GoodExit).symm
    _ ≤ pmfProb mu (Atom ∩ ExitGood) :=
          pmfProb_mono mu hsubset

theorem lemma79_loko4_fixedEntry_exitWhite_prob_ge
    {Omega Suffix : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {Atom ExitWhite : Set Omega}
    {suffix : Omega -> Suffix}
    {holdFirstPassageProb : Set Suffix -> ℝ}
    {loko4GoodExit : Set Suffix}
    {c0 : ℝ}
    (hlaw :
      Lemma79FixedEntrySuffixFirstPassageLaw
        mu Atom suffix holdFirstPassageProb)
    (hloko4 : c0 ≤ holdFirstPassageProb loko4GoodExit)
    (hsubset :
      {omega | omega ∈ Atom ∧ suffix omega ∈ loko4GoodExit} ⊆
        Atom ∩ ExitWhite) :
    c0 * pmfProb mu Atom ≤ pmfProb mu (Atom ∩ ExitWhite) :=
  lemma79_loko4_fixedEntry_goodExit_prob_ge
    (mu := mu) (Atom := Atom) (ExitGood := ExitWhite) (suffix := suffix)
    (holdFirstPassageProb := holdFirstPassageProb)
    (loko4GoodExit := loko4GoodExit) (c0 := c0) hlaw hloko4 hsubset

theorem lemma79_fixedFirstEntryExitGoodSource_of_loko4SuffixLaw
    {Omega iota Suffix : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {nonzero Atom ExitGood : Set Omega}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family}
    {i : iota}
    {origin : TaoSection7RenewalPoint}
    {gap : ℕ}
    {K : Omega -> ℕ}
    {pre : Omega -> List TaoSection7RenewalPoint}
    {suffix : Omega -> Suffix}
    {holdFirstPassageProb : Set Suffix -> ℝ}
    {loko4GoodExit : Set Suffix}
    {c0 : ℝ}
    (atom_eq : Atom = firstAtoms.atom i)
    (origin_entry : origin.toPoint = firstAtoms.entryPoint i)
    (gap_height :
      origin.l + (gap : ℤ) = (firstAtoms.entryTriangle i).cornerL)
    (source_on_atom :
      TaoSection7Lemma77.Lemma77EndpointSourceProvenanceOnGood
        mu (fun _ => origin) K pre gap Atom)
    (hlaw :
      Lemma79FixedEntrySuffixFirstPassageLaw
        mu Atom suffix holdFirstPassageProb)
    (hloko4 : c0 ≤ holdFirstPassageProb loko4GoodExit)
    (hsubset :
      {omega | omega ∈ Atom ∧ suffix omega ∈ loko4GoodExit} ⊆
        Atom ∩ ExitGood) :
    Lemma79FixedFirstEntryExitGoodSource
      mu nonzero Atom ExitGood W pointAt family firstAtoms i origin gap K pre
      c0 where
  atom_eq := atom_eq
  origin_entry := origin_entry
  gap_height := gap_height
  source_on_atom := source_on_atom
  first_passage_on_atom := by
    intro omega hmem
    exact source_on_atom.first_passage_good omega hmem
  good_exit_prob_ge :=
    lemma79_loko4_fixedEntry_goodExit_prob_ge
      (mu := mu) (Atom := Atom) (ExitGood := ExitGood) (suffix := suffix)
      (holdFirstPassageProb := holdFirstPassageProb)
      (loko4GoodExit := loko4GoodExit) (c0 := c0) hlaw hloko4 hsubset

theorem Lemma79FixedFirstEntryExitGoodSource.to_exitGoodSource
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {nonzero Atom ExitGood : Set Omega}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family}
    {i : iota}
    {origin : TaoSection7RenewalPoint}
    {gap : ℕ}
    {K : Omega -> ℕ}
    {pre : Omega -> List TaoSection7RenewalPoint}
    {c0 : ℝ}
    (hfixed :
      Lemma79FixedFirstEntryExitGoodSource
        mu nonzero Atom ExitGood W pointAt family firstAtoms i origin gap K
        pre c0) :
    Lemma79FirstEntryExitGoodSource
      mu Atom ExitGood (fun _ => firstAtoms.entryPoint i)
      (firstAtoms.entryTriangle i) (fun _ => origin) (fun _ => gap) K pre c0
    where
  entry_mem_triangle := by
    intro _omega _hmem
    exact firstAtoms.entry_mem_triangle i
  vertical_first_passage := by
    intro omega hmem
    exact hfixed.first_passage_on_atom omega hmem
  good_exit_prob_ge := hfixed.good_exit_prob_ge

/--
Deterministic geometry bridge from the good first-passage exit event to the
white exit event.

The future proof should use the Lemma 7.4/`ClaimStar` geometry vocabulary here,
not the near-top Proposition 7.8 boundary route.
-/
structure Lemma79ExitGoodToExitWhite
    {Omega : Type*}
    (Atom ExitGood ExitWhite : Set Omega) : Prop where
  subset : Atom ∩ ExitGood ⊆ Atom ∩ ExitWhite

theorem lemma79_firstEntryAtom_exitWhite_ge_of_exitGood
    {Omega : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {Atom ExitGood ExitWhite : Set Omega}
    {entry : Omega -> TaoSection7Point}
    {Delta : TaoSection7Triangle}
    {start : Omega -> TaoSection7RenewalPoint}
    {verticalGap K : Omega -> ℕ}
    {pre : Omega -> List TaoSection7RenewalPoint}
    {c0 : ℝ}
    (hgood :
      Lemma79FirstEntryExitGoodSource
        mu Atom ExitGood entry Delta start verticalGap K pre c0)
    (hwhite : Lemma79ExitGoodToExitWhite Atom ExitGood ExitWhite) :
    c0 * pmfProb mu Atom ≤ pmfProb mu (Atom ∩ ExitWhite) :=
  le_trans hgood.good_exit_prob_ge (pmfProb_mono mu hwhite.subset)

theorem lemma79_firstEntryAtom_exitWhite_ge_of_fixedEntryExitGood
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {nonzero Atom ExitGood ExitWhite : Set Omega}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family}
    {i : iota}
    {origin : TaoSection7RenewalPoint}
    {gap : ℕ}
    {K : Omega -> ℕ}
    {pre : Omega -> List TaoSection7RenewalPoint}
    {c0 : ℝ}
    (hfixed :
      Lemma79FixedFirstEntryExitGoodSource
        mu nonzero Atom ExitGood W pointAt family firstAtoms i origin gap K
        pre c0)
    (hwhite : Lemma79ExitGoodToExitWhite Atom ExitGood ExitWhite) :
    c0 * pmfProb mu Atom ≤ pmfProb mu (Atom ∩ ExitWhite) :=
  lemma79_firstEntryAtom_exitWhite_ge_of_exitGood
    hfixed.to_exitGoodSource hwhite

theorem lemma79_exitWhiteContraction_of_exitGood
    {Omega : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {Atom ExitGood ExitWhite : Set Omega}
    {entry : Omega -> TaoSection7Point}
    {Delta : TaoSection7Triangle}
    {start : Omega -> TaoSection7RenewalPoint}
    {verticalGap K : Omega -> ℕ}
    {pre : Omega -> List TaoSection7RenewalPoint}
    {c0 epsilon : ℝ}
    (hgood :
      Lemma79FirstEntryExitGoodSource
        mu Atom ExitGood entry Delta start verticalGap K pre c0)
    (hwhite : Lemma79ExitGoodToExitWhite Atom ExitGood ExitWhite)
    (hscalar :
      1 - (1 - Real.exp (-1)) * c0 ≤ Real.exp (-epsilon)) :
    Lemma79ExitWhiteContraction mu Atom ExitWhite c0 epsilon where
  exitWhite_prob_ge :=
    lemma79_firstEntryAtom_exitWhite_ge_of_exitGood hgood hwhite
  epsilon_small := hscalar

theorem lemma79_exitWhiteContraction_of_fixedEntryExitGood
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {nonzero Atom ExitGood ExitWhite : Set Omega}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family}
    {i : iota}
    {origin : TaoSection7RenewalPoint}
    {gap : ℕ}
    {K : Omega -> ℕ}
    {pre : Omega -> List TaoSection7RenewalPoint}
    {c0 epsilon : ℝ}
    (hfixed :
      Lemma79FixedFirstEntryExitGoodSource
        mu nonzero Atom ExitGood W pointAt family firstAtoms i origin gap K
        pre c0)
    (hwhite : Lemma79ExitGoodToExitWhite Atom ExitGood ExitWhite)
    (hscalar :
      1 - (1 - Real.exp (-1)) * c0 ≤ Real.exp (-epsilon)) :
    Lemma79ExitWhiteContraction mu Atom ExitWhite c0 epsilon :=
  lemma79_exitWhiteContraction_of_exitGood
    hfixed.to_exitGoodSource hwhite hscalar

theorem lemma79_exitWhiteContraction_of_fixedEntryLoko4SuffixLaw
    {Omega iota Suffix : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {nonzero Atom ExitGood ExitWhite : Set Omega}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family}
    {i : iota}
    {origin : TaoSection7RenewalPoint}
    {gap : ℕ}
    {K : Omega -> ℕ}
    {pre : Omega -> List TaoSection7RenewalPoint}
    {suffix : Omega -> Suffix}
    {holdFirstPassageProb : Set Suffix -> ℝ}
    {loko4GoodExit : Set Suffix}
    {c0 epsilon : ℝ}
    (atom_eq : Atom = firstAtoms.atom i)
    (origin_entry : origin.toPoint = firstAtoms.entryPoint i)
    (gap_height :
      origin.l + (gap : ℤ) = (firstAtoms.entryTriangle i).cornerL)
    (source_on_atom :
      TaoSection7Lemma77.Lemma77EndpointSourceProvenanceOnGood
        mu (fun _ => origin) K pre gap Atom)
    (hlaw :
      Lemma79FixedEntrySuffixFirstPassageLaw
        mu Atom suffix holdFirstPassageProb)
    (hloko4 : c0 ≤ holdFirstPassageProb loko4GoodExit)
    (hgood :
      {omega | omega ∈ Atom ∧ suffix omega ∈ loko4GoodExit} ⊆
        Atom ∩ ExitGood)
    (hwhite : Lemma79ExitGoodToExitWhite Atom ExitGood ExitWhite)
    (hscalar :
      1 - (1 - Real.exp (-1)) * c0 ≤ Real.exp (-epsilon)) :
    Lemma79ExitWhiteContraction mu Atom ExitWhite c0 epsilon :=
  lemma79_exitWhiteContraction_of_fixedEntryExitGood
    (hfixed :=
      lemma79_fixedFirstEntryExitGoodSource_of_loko4SuffixLaw
        (mu := mu) (nonzero := nonzero) (Atom := Atom)
        (ExitGood := ExitGood) (W := W) (pointAt := pointAt)
        (family := family) (firstAtoms := firstAtoms) (i := i)
        (origin := origin) (gap := gap) (K := K) (pre := pre)
        (suffix := suffix) (holdFirstPassageProb := holdFirstPassageProb)
        (loko4GoodExit := loko4GoodExit) (c0 := c0)
        atom_eq origin_entry gap_height source_on_atom hlaw hloko4 hgood)
    hwhite hscalar

theorem atom_exitWhiteWeight_expectation_eq
    {Omega : Type*} [Fintype Omega]
    (mu : PMF Omega)
    (Atom ExitWhite : Set Omega) :
    pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite)) =
      pmfProb mu Atom -
        (1 - Real.exp (-1)) * pmfProb mu (Atom ∩ ExitWhite) := by
  classical
  simp only [pmfExpectation, atomIndicator, exitWhiteWeight]
  calc
    (∑ omega, (mu omega).toReal *
        (if omega ∈ Atom then
          (if omega ∈ ExitWhite then Real.exp (-1) else 1)
        else 0))
        =
      ∑ omega,
        ((if omega ∈ Atom then (mu omega).toReal else 0) -
          (1 - Real.exp (-1)) *
            (if omega ∈ Atom ∩ ExitWhite then (mu omega).toReal else 0)) := by
        refine Finset.sum_congr rfl ?_
        intro omega _homega
        by_cases hAtom : omega ∈ Atom
        · by_cases hExit : omega ∈ ExitWhite
          · simp [hAtom, hExit, Set.mem_inter_iff]
            ring
          · have hnotInter : omega ∉ Atom ∩ ExitWhite := by
              intro hmem
              exact hExit hmem.2
            simp [hAtom, hExit, hnotInter]
        · have hnotInter : omega ∉ Atom ∩ ExitWhite := by
            intro hmem
            exact hAtom hmem.1
          simp [hAtom, hnotInter]
    _ = pmfProb mu Atom -
        (1 - Real.exp (-1)) * pmfProb mu (Atom ∩ ExitWhite) := by
        rw [pmfProb, pmfProb, Finset.sum_sub_distrib, Finset.mul_sum]
        simp

theorem exitWhiteWeight_expectation_le
    {Omega : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {Atom ExitWhite : Set Omega}
    {c0 epsilon : ℝ}
    (h : Lemma79ExitWhiteContraction mu Atom ExitWhite c0 epsilon) :
    pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite)) ≤
      Real.exp (-epsilon) * pmfProb mu Atom := by
  have hweight_nonneg : 0 ≤ 1 - Real.exp (-1) := by
    have hexp_le_one : Real.exp (-1 : ℝ) ≤ 1 := by
      have hlt : Real.exp (-1 : ℝ) < Real.exp (0 : ℝ) :=
        Real.exp_lt_exp.mpr (by norm_num)
      calc
        Real.exp (-1 : ℝ) ≤ Real.exp (0 : ℝ) := hlt.le
        _ = 1 := by simp
    linarith
  have hmul :
      (1 - Real.exp (-1)) * (c0 * pmfProb mu Atom) ≤
        (1 - Real.exp (-1)) * pmfProb mu (Atom ∩ ExitWhite) :=
    mul_le_mul_of_nonneg_left h.exitWhite_prob_ge hweight_nonneg
  have hbase :
      pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite)) ≤
        (1 - (1 - Real.exp (-1)) * c0) * pmfProb mu Atom := by
    rw [atom_exitWhiteWeight_expectation_eq]
    nlinarith
  exact le_trans hbase
    (mul_le_mul_of_nonneg_right h.epsilon_small (pmfProb_nonneg mu Atom))

theorem exitWhiteWeight_expectation_le_of_atomPartition
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {nonzero ExitWhite : Set Omega}
    {atom : iota -> Set Omega}
    {c0 epsilon : ℝ}
    (hpart :
      Lemma79ExitWhiteAtomPartition mu nonzero ExitWhite atom c0)
    (hscalar :
      1 - (1 - Real.exp (-1)) * c0 ≤ Real.exp (-epsilon)) :
    pmfExpectation mu (atomIndicator nonzero (exitWhiteWeight ExitWhite)) ≤
      Real.exp (-epsilon) * pmfProb mu nonzero :=
  exitWhiteWeight_expectation_le (hpart.to_contraction hscalar)

theorem exitFutureMoment_expectation_le_atomProb
    {Omega : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {Atom ExitWhite : Set Omega}
    {futureMoment : Omega -> ℝ}
    {c0 epsilon : ℝ}
    (htower : Lemma79TailTowerInput mu Atom ExitWhite futureMoment epsilon)
    (hexit : Lemma79ExitWhiteContraction mu Atom ExitWhite c0 epsilon) :
    pmfExpectation mu (exitFutureMoment Atom ExitWhite futureMoment) ≤
      pmfProb mu Atom := by
  have hwhite :
      pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite)) ≤
        Real.exp (-epsilon) * pmfProb mu Atom :=
    exitWhiteWeight_expectation_le hexit
  have hmul :
      Real.exp epsilon *
          pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite)) ≤
        Real.exp epsilon * (Real.exp (-epsilon) * pmfProb mu Atom) :=
    mul_le_mul_of_nonneg_left hwhite (Real.exp_pos epsilon).le
  have hcancel :
      Real.exp epsilon * (Real.exp (-epsilon) * pmfProb mu Atom) =
        pmfProb mu Atom := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  exact le_trans htower.tower_le (by simpa [hcancel] using hmul)

theorem tailMoment_atom_expectation_le_atomProb
    {Omega : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {Atom ExitWhite : Set Omega}
    {tailMoment futureMoment : Omega -> ℝ}
    {c0 epsilon : ℝ}
    (hrestart :
      Lemma79TailRestartIdentity Atom ExitWhite tailMoment futureMoment)
    (htower : Lemma79TailTowerInput mu Atom ExitWhite futureMoment epsilon)
    (hexit : Lemma79ExitWhiteContraction mu Atom ExitWhite c0 epsilon) :
    pmfExpectation mu (atomIndicator Atom tailMoment) ≤ pmfProb mu Atom := by
  classical
  have hrewrite :
      pmfExpectation mu (atomIndicator Atom tailMoment) =
        pmfExpectation mu (exitFutureMoment Atom ExitWhite futureMoment) := by
    unfold pmfExpectation
    refine Finset.sum_congr rfl ?_
    intro omega _homega
    by_cases hAtom : omega ∈ Atom
    · simp [atomIndicator, exitFutureMoment, hAtom,
        hrestart.split_on_atom omega hAtom]
    · simp [atomIndicator, exitFutureMoment, hAtom]
  rw [hrewrite]
  exact exitFutureMoment_expectation_le_atomProb htower hexit

theorem tailMoment_expectation_le_exp_of_zero_nonzero_atom_partition
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {zero nonzero : Set Omega}
    {atom : iota -> Set Omega}
    {tailMoment : Omega -> ℝ}
    {epsilon : ℝ}
    (hzero :
      pmfExpectation mu (atomIndicator zero tailMoment) ≤ pmfProb mu zero)
    (hnz_expect_partition :
      pmfExpectation mu (atomIndicator nonzero tailMoment) =
        ∑ i, pmfExpectation mu (atomIndicator (atom i) tailMoment))
    (hnz_prob_partition :
      pmfProb mu nonzero = ∑ i, pmfProb mu (atom i))
    (hatom :
      ∀ i, pmfExpectation mu (atomIndicator (atom i) tailMoment) ≤
        Real.exp epsilon * pmfProb mu (atom i))
    (hfull_split :
      pmfExpectation mu tailMoment =
        pmfExpectation mu (atomIndicator zero tailMoment) +
          pmfExpectation mu (atomIndicator nonzero tailMoment))
    (hprob_split : pmfProb mu zero + pmfProb mu nonzero = 1)
    (heps_nonneg : 0 ≤ epsilon) :
    pmfExpectation mu tailMoment ≤ Real.exp epsilon := by
  have hexp_ge_one : 1 ≤ Real.exp epsilon := by
    simpa using Real.exp_le_exp.mpr heps_nonneg
  have hzero_weak : pmfProb mu zero ≤ Real.exp epsilon * pmfProb mu zero := by
    have hz_nonneg : 0 ≤ pmfProb mu zero := pmfProb_nonneg mu zero
    nlinarith
  calc
    pmfExpectation mu tailMoment =
        pmfExpectation mu (atomIndicator zero tailMoment) +
          pmfExpectation mu (atomIndicator nonzero tailMoment) := hfull_split
    _ ≤ pmfProb mu zero +
          pmfExpectation mu (atomIndicator nonzero tailMoment) := by
        exact add_le_add hzero le_rfl
    _ = pmfProb mu zero +
          ∑ i, pmfExpectation mu (atomIndicator (atom i) tailMoment) := by
        rw [hnz_expect_partition]
    _ ≤ pmfProb mu zero +
          ∑ i, Real.exp epsilon * pmfProb mu (atom i) := by
        have hsum :
            (∑ i, pmfExpectation mu (atomIndicator (atom i) tailMoment)) ≤
              ∑ i, Real.exp epsilon * pmfProb mu (atom i) :=
          Finset.sum_le_sum fun i _hi => hatom i
        exact add_le_add le_rfl hsum
    _ = pmfProb mu zero + Real.exp epsilon * pmfProb mu nonzero := by
        rw [← Finset.mul_sum, ← hnz_prob_partition]
    _ ≤ Real.exp epsilon * pmfProb mu zero +
          Real.exp epsilon * pmfProb mu nonzero := by
        exact add_le_add hzero_weak le_rfl
    _ = Real.exp epsilon * (pmfProb mu zero + pmfProb mu nonzero) := by
        ring
    _ = Real.exp epsilon := by
        rw [hprob_split, mul_one]

/--
Source-facing link between the algebraic atom family and the inclusive
first-entry atom family used by Lemma 7.9.

This record exists to keep the full-`Z` induction-step socket from accepting an
anonymous atom partition while the source proof needs the actual `{t_1 = p}`
partition, including the `t_1 = 0` slice.
-/
structure Lemma79FullZSourceAtomPartition
    {Omega iota : Type*} [Fintype iota]
    {nonzero : Set Omega}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    (firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family)
    (atom : iota -> Set Omega) : Prop where
  atom_eq : ∀ i, firstAtoms.atom i = atom i

/--
Finite carrier for the first-entry atoms in the full Lemma 7.9 `Z_R`
induction.

Tao's informal atom key is `(t_1, Δ_1, entry point)`, but the checked
finite-PMF algebra needs a finite index type.  This record packages a finite
carrier `iota`, a key map from samples to that carrier, the inclusive
first-entry atom family, and the partition equalities needed by the full-`Z`
induction-step consumer.
-/
structure Lemma79FirstEntryAtomFiniteCarrier
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    (mu : PMF Omega)
    (zero nonzero : Set Omega)
    (atom : iota -> Set Omega)
    (fullMoment : Omega -> ℝ)
    (W : Omega -> ℕ -> Prop)
    (pointAt : Omega -> ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle) : Type _ where
  key : Omega -> iota
  firstAtoms :
    Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family
  source_atom_partition :
    Lemma79FullZSourceAtomPartition (iota := iota) firstAtoms atom
  key_mem : ∀ omega, omega ∈ nonzero -> omega ∈ atom (key omega)
  atom_key : ∀ i omega, omega ∈ atom i -> key omega = i
  atom_subset_nonzero : ∀ i, atom i ⊆ nonzero
  nonzero_expect_partition :
    pmfExpectation mu (atomIndicator nonzero fullMoment) =
      ∑ i, pmfExpectation mu (atomIndicator (atom i) fullMoment)
  nonzero_prob_partition :
    pmfProb mu nonzero = ∑ i, pmfProb mu (atom i)
  full_split :
    pmfExpectation mu fullMoment =
      pmfExpectation mu (atomIndicator zero fullMoment) +
        pmfExpectation mu (atomIndicator nonzero fullMoment)
  prob_split : pmfProb mu zero + pmfProb mu nonzero = 1

namespace Lemma79FirstEntryAtomFiniteCarrier

theorem atom_mem_iff_of_key
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {zero nonzero : Set Omega}
    {atom : iota -> Set Omega}
    {fullMoment : Omega -> ℝ}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    (hcarrier :
      Lemma79FirstEntryAtomFiniteCarrier
        mu zero nonzero atom fullMoment W pointAt family)
    (i : iota) (omega : Omega) :
    omega ∈ atom i ↔ omega ∈ nonzero ∧ hcarrier.key omega = i := by
  constructor
  · intro hmem
    exact ⟨hcarrier.atom_subset_nonzero i hmem,
      hcarrier.atom_key i omega hmem⟩
  · intro hmem
    rcases hmem with ⟨hnonzero, hkey⟩
    have hkey_mem := hcarrier.key_mem omega hnonzero
    simpa [hkey] using hkey_mem

theorem nonzero_prob_partition_of_key
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {zero nonzero : Set Omega}
    {atom : iota -> Set Omega}
    {fullMoment : Omega -> ℝ}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    (hcarrier :
      Lemma79FirstEntryAtomFiniteCarrier
        mu zero nonzero atom fullMoment W pointAt family) :
    pmfProb mu nonzero = ∑ i, pmfProb mu (atom i) := by
  classical
  calc
    pmfProb mu nonzero =
        ∑ omega, if omega ∈ nonzero then (mu omega).toReal else 0 := by
          rw [pmfProb]
    _ = ∑ omega, ∑ i, if omega ∈ atom i then (mu omega).toReal else 0 := by
        refine Finset.sum_congr rfl ?_
        intro omega _homega
        by_cases hnonzero : omega ∈ nonzero
        · have hkey_mem := hcarrier.key_mem omega hnonzero
          rw [Finset.sum_eq_single (hcarrier.key omega)]
          · simp [hnonzero, hkey_mem]
          · intro i _hi hne
            have hnot : omega ∉ atom i := by
              intro hmem
              exact hne (hcarrier.atom_key i omega hmem).symm
            simp [hnot]
          · intro hnot_mem
            exact (hnot_mem (Finset.mem_univ _)).elim
        · have hnot : ∀ i, omega ∉ atom i := by
            intro i hmem
            exact hnonzero (hcarrier.atom_subset_nonzero i hmem)
          simp [hnonzero, hnot]
    _ = ∑ i, ∑ omega, if omega ∈ atom i then (mu omega).toReal else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ i, pmfProb mu (atom i) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [pmfProb]

theorem nonzero_expect_partition_of_key
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {zero nonzero : Set Omega}
    {atom : iota -> Set Omega}
    {fullMoment : Omega -> ℝ}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    (hcarrier :
      Lemma79FirstEntryAtomFiniteCarrier
        mu zero nonzero atom fullMoment W pointAt family) :
    pmfExpectation mu (atomIndicator nonzero fullMoment) =
      ∑ i, pmfExpectation mu (atomIndicator (atom i) fullMoment) := by
  classical
  calc
    pmfExpectation mu (atomIndicator nonzero fullMoment) =
        ∑ omega, (mu omega).toReal *
          (if omega ∈ nonzero then fullMoment omega else 0) := by
          simp [pmfExpectation, atomIndicator]
    _ = ∑ omega, ∑ i,
          (mu omega).toReal *
            (if omega ∈ atom i then fullMoment omega else 0) := by
        refine Finset.sum_congr rfl ?_
        intro omega _homega
        by_cases hnonzero : omega ∈ nonzero
        · have hkey_mem := hcarrier.key_mem omega hnonzero
          rw [Finset.sum_eq_single (hcarrier.key omega)]
          · simp [hnonzero, hkey_mem]
          · intro i _hi hne
            have hnot : omega ∉ atom i := by
              intro hmem
              exact hne (hcarrier.atom_key i omega hmem).symm
            simp [hnot]
          · intro hnot_mem
            exact (hnot_mem (Finset.mem_univ _)).elim
        · have hnot : ∀ i, omega ∉ atom i := by
            intro i hmem
            exact hnonzero (hcarrier.atom_subset_nonzero i hmem)
          simp [hnonzero, hnot]
    _ = ∑ i, ∑ omega,
          (mu omega).toReal *
            (if omega ∈ atom i then fullMoment omega else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ i, pmfExpectation mu (atomIndicator (atom i) fullMoment) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp [pmfExpectation, atomIndicator]

end Lemma79FirstEntryAtomFiniteCarrier

theorem fullExpectation_split_of_zero_nonzero_partition
    {Omega : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {zero nonzero : Set Omega}
    {X : Omega -> ℝ}
    (hcover : ∀ omega, omega ∈ zero ∨ omega ∈ nonzero)
    (hdisjoint : ∀ omega, omega ∈ zero -> omega ∈ nonzero -> False) :
    pmfExpectation mu X =
      pmfExpectation mu (atomIndicator zero X) +
        pmfExpectation mu (atomIndicator nonzero X) := by
  classical
  unfold pmfExpectation atomIndicator
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro omega _homega
  rcases hcover omega with hzero | hnonzero
  · have hnot_nonzero : omega ∉ nonzero := by
      intro hmem
      exact hdisjoint omega hzero hmem
    simp [hzero, hnot_nonzero]
  · have hnot_zero : omega ∉ zero := by
      intro hmem
      exact hdisjoint omega hmem hnonzero
    simp [hnonzero, hnot_zero]

theorem prob_split_of_zero_nonzero_partition
    {Omega : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {zero nonzero : Set Omega}
    (hcover : ∀ omega, omega ∈ zero ∨ omega ∈ nonzero)
    (hdisjoint : ∀ omega, omega ∈ zero -> omega ∈ nonzero -> False) :
    pmfProb mu zero + pmfProb mu nonzero = 1 := by
  classical
  rw [← pmfProb_univ mu]
  unfold pmfProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro omega _homega
  rcases hcover omega with hzero | hnonzero
  · have hnot_nonzero : omega ∉ nonzero := by
      intro hmem
      exact hdisjoint omega hzero hmem
    simp [hzero, hnot_nonzero]
  · have hnot_zero : omega ∉ zero := by
      intro hmem
      exact hdisjoint omega hmem hnonzero
    simp [hnonzero, hnot_zero]

theorem pmfExpectation_atomIndicator_const_mul
    {Omega : Type*} [Fintype Omega]
    (mu : PMF Omega)
    (Atom : Set Omega)
    (c : ℝ)
    (X : Omega -> ℝ) :
    pmfExpectation mu (atomIndicator Atom (fun omega => c * X omega)) =
      c * pmfExpectation mu (atomIndicator Atom X) := by
  classical
  unfold pmfExpectation atomIndicator
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro omega _homega
  by_cases hmem : omega ∈ Atom
  · simp [hmem]
    ring
  · simp [hmem]

theorem pmfExpectation_const_mul
    {Omega : Type*} [Fintype Omega]
    (mu : PMF Omega)
    (c : ℝ)
    (X : Omega -> ℝ) :
    pmfExpectation mu (fun omega => c * X omega) =
      c * pmfExpectation mu X := by
  classical
  unfold pmfExpectation
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro omega _homega
  ring

theorem pmfExpectation_atomIndicator_const
    {Omega : Type*} [Fintype Omega]
    (mu : PMF Omega)
    (Atom : Set Omega)
    (c : ℝ) :
    pmfExpectation mu (atomIndicator Atom (fun _ => c)) =
      c * pmfProb mu Atom := by
  classical
  unfold pmfExpectation atomIndicator pmfProb
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro omega _homega
  by_cases hmem : omega ∈ Atom
  · simp [hmem]
    ring
  · simp [hmem]

theorem pmfExpectation_atomIndicator_tail_eq_sum_fibers
    {Omega Tail : Type*} [Fintype Omega] [Fintype Tail]
    (mu : PMF Omega)
    (AtomA : Set Omega)
    (tailOf : Omega -> Tail)
    (F : Tail -> ℝ) :
    pmfExpectation mu (atomIndicator AtomA (fun omega => F (tailOf omega))) =
      ∑ tail,
        F tail * pmfProb mu {omega | omega ∈ AtomA ∧ tailOf omega = tail} := by
  classical
  have hfiberwise :=
    (Finset.sum_fiberwise (Finset.univ : Finset Omega) tailOf
      (fun omega =>
        (mu omega).toReal *
          atomIndicator AtomA (fun omega => F (tailOf omega)) omega))
  calc
    pmfExpectation mu (atomIndicator AtomA (fun omega => F (tailOf omega)))
        =
      ∑ omega,
        (mu omega).toReal *
          atomIndicator AtomA (fun omega => F (tailOf omega)) omega := by
          rfl
    _ =
      ∑ tail, ∑ omega ∈ (Finset.univ : Finset Omega) with tailOf omega = tail,
        (mu omega).toReal *
          atomIndicator AtomA (fun omega => F (tailOf omega)) omega := by
          exact hfiberwise.symm
    _ =
      ∑ tail,
        F tail * pmfProb mu {omega | omega ∈ AtomA ∧ tailOf omega = tail} := by
          refine Finset.sum_congr rfl ?_
          intro tail _htail_mem
          rw [Finset.sum_filter]
          unfold pmfProb atomIndicator
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro omega _homega
          by_cases htail : tailOf omega = tail
          · by_cases hmem : omega ∈ AtomA
            · simp [htail, hmem]
              ring
            · simp [htail, hmem]
          · by_cases hmem : omega ∈ AtomA
            · simp [htail, hmem]
            · simp [htail, hmem]

theorem pmfExpectation_atomIndicator_le_const_mul_of_mem_imp
    {Omega : Type*} [Fintype Omega]
    (mu : PMF Omega)
    (Atom : Set Omega)
    (X Y : Omega -> ℝ)
    (c : ℝ)
    (hXY : ∀ omega, omega ∈ Atom -> X omega ≤ c * Y omega) :
    pmfExpectation mu (atomIndicator Atom X) ≤
      c * pmfExpectation mu (atomIndicator Atom Y) := by
  calc
    pmfExpectation mu (atomIndicator Atom X) ≤
        pmfExpectation mu (atomIndicator Atom (fun omega => c * Y omega)) := by
          exact pmfExpectation_mono mu fun omega => by
            by_cases hmem : omega ∈ Atom
            · simpa [atomIndicator, hmem] using hXY omega hmem
            · simp [atomIndicator, hmem]
    _ = c * pmfExpectation mu (atomIndicator Atom Y) :=
        pmfExpectation_atomIndicator_const_mul mu Atom c Y

theorem pmfExpectation_atomIndicator_partition_of_key
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    (mu : PMF Omega)
    {Parent : Set Omega}
    {atom : iota -> Set Omega}
    {key : Omega -> iota}
    {X : Omega -> ℝ}
    (hkey_mem : ∀ omega, omega ∈ Parent -> omega ∈ atom (key omega))
    (hatom_key : ∀ i omega, omega ∈ atom i -> omega ∈ Parent ∧ key omega = i) :
    pmfExpectation mu (atomIndicator Parent X) =
      ∑ i, pmfExpectation mu (atomIndicator (atom i) X) := by
  classical
  calc
    pmfExpectation mu (atomIndicator Parent X) =
        ∑ omega, (mu omega).toReal *
          (if omega ∈ Parent then X omega else 0) := by
          simp [pmfExpectation, atomIndicator]
    _ = ∑ omega, ∑ i,
          (mu omega).toReal *
            (if omega ∈ atom i then X omega else 0) := by
        refine Finset.sum_congr rfl ?_
        intro omega _homega
        by_cases hParent : omega ∈ Parent
        · have hkey_mem := hkey_mem omega hParent
          rw [Finset.sum_eq_single (key omega)]
          · simp [hParent, hkey_mem]
          · intro i _hi hne
            have hnot : omega ∉ atom i := by
              intro hmem
              exact hne ((hatom_key i omega hmem).2).symm
            simp [hnot]
          · intro hnot_mem
            exact (hnot_mem (Finset.mem_univ _)).elim
        · have hnot : ∀ i, omega ∉ atom i := by
            intro i hmem
            exact hParent (hatom_key i omega hmem).1
          simp [hParent, hnot]
    _ = ∑ i, ∑ omega,
          (mu omega).toReal *
            (if omega ∈ atom i then X omega else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ i, pmfExpectation mu (atomIndicator (atom i) X) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        simp [pmfExpectation, atomIndicator]

theorem pmfProb_partition_of_key
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    (mu : PMF Omega)
    {Parent : Set Omega}
    {atom : iota -> Set Omega}
    {key : Omega -> iota}
    (hkey_mem : ∀ omega, omega ∈ Parent -> omega ∈ atom (key omega))
    (hatom_key : ∀ i omega, omega ∈ atom i -> omega ∈ Parent ∧ key omega = i) :
    pmfProb mu Parent = ∑ i, pmfProb mu (atom i) := by
  classical
  have hpart :
      pmfExpectation mu (atomIndicator Parent (fun _ => (1 : ℝ))) =
        ∑ i, pmfExpectation mu (atomIndicator (atom i) (fun _ => (1 : ℝ))) :=
    pmfExpectation_atomIndicator_partition_of_key
      (mu := mu) (Parent := Parent) (atom := atom) (key := key)
      (X := fun _ => (1 : ℝ)) hkey_mem hatom_key
  calc
    pmfProb mu Parent =
        pmfExpectation mu (atomIndicator Parent (fun _ => (1 : ℝ))) := by
          rw [pmfExpectation_atomIndicator_const]
          ring
    _ = ∑ i, pmfExpectation mu (atomIndicator (atom i) (fun _ => (1 : ℝ))) :=
          hpart
    _ = ∑ i, pmfProb mu (atom i) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [pmfExpectation_atomIndicator_const]
          ring

/--
Stopped-prefix restart/tower source socket for one first-entry atom.

This record exposes the order of Tao's Lemma 7.9 induction on one atom:
partition by the stopped prefix through `k_1`, integrate the future
`Z(_, R - 1)` term, then compare the remaining prefix factor to the exit-white
weight.  The checked theorem below only assembles those inputs into
`Lemma79FullZAtomRestartTowerInput`.
-/
structure Lemma79StoppedRestartTowerSource
    {Omega kappa : Type*} [Fintype Omega] [Fintype kappa]
    (mu : PMF Omega)
    (R Rprev : ℕ)
    (Atom ExitWhite : Set Omega)
    (prefixAtom : kappa -> Set Omega)
    (start : kappa -> TaoSection7RenewalPoint)
    (verticalGap K : kappa -> ℕ)
    (pre : kappa -> List TaoSection7RenewalPoint)
    (endpoint : kappa -> TaoSection7RenewalPoint)
    (fullMoment futureMoment : Omega -> ℝ)
    (prefixFuture prefixFactor : kappa -> Omega -> ℝ)
    (epsilon : ℝ) : Prop where
  two_le_R : 2 ≤ R
  Rprev_eq : Rprev = R - 1
  restart :
    Lemma79TailRestartIdentity Atom ExitWhite fullMoment futureMoment
  prefix_first_passage :
    ∀ a omega, omega ∈ prefixAtom a ->
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        (start a) (verticalGap a) (K a) (pre a)
  prefix_endpoint_eq :
    ∀ a omega, omega ∈ prefixAtom a ->
      endpoint a = taoSection7RenewalPathPoint (start a) (pre a) (K a)
  prefix_expect_partition :
    pmfExpectation mu (exitFutureMoment Atom ExitWhite futureMoment) =
      ∑ a, pmfExpectation mu (atomIndicator (prefixAtom a) (prefixFuture a))
  future_induction_after_prefix :
    ∀ a,
      pmfExpectation mu (atomIndicator (prefixAtom a) (prefixFuture a)) ≤
        Real.exp epsilon *
          pmfExpectation mu (atomIndicator (prefixAtom a) (prefixFactor a))
  prefix_factor_le_exit_weight :
    ∀ a,
      pmfExpectation mu (atomIndicator (prefixAtom a) (prefixFactor a)) ≤
        Real.exp epsilon *
          pmfExpectation mu (atomIndicator (prefixAtom a)
            (exitWhiteWeight ExitWhite))
  prefix_exit_weight_partition :
    (∑ a, pmfExpectation mu (atomIndicator (prefixAtom a)
      (exitWhiteWeight ExitWhite))) =
      pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite))

/--
Fixed-origin source layer for the stopped-prefix restart/tower socket.

This uses the post-entry convention for one first-entry atom: after
conditioning on the fixed entry atom, the restart origin and target height gap
are fixed while the realized stopped prefix varies through `prefixAtom`.
-/
structure Lemma79FixedOriginStoppedRestartTowerSource
    {Omega iota kappa : Type*} [Fintype Omega] [Fintype iota]
    [Fintype kappa]
    (mu : PMF Omega)
    (R Rprev : ℕ)
    (nonzero Atom ExitWhite : Set Omega)
    (W : Omega -> ℕ -> Prop)
    (pointAt : Omega -> ℕ -> TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family)
    (i : iota)
    (prefixAtom : kappa -> Set Omega)
    (origin : TaoSection7RenewalPoint)
    (gap : ℕ)
    (K : kappa -> ℕ)
    (pre : kappa -> List TaoSection7RenewalPoint)
    (endpoint : kappa -> TaoSection7RenewalPoint)
    (fullMoment futureMoment : Omega -> ℝ)
    (prefixFuture prefixFactor : kappa -> Omega -> ℝ)
    (epsilon : ℝ) : Prop where
  two_le_R : 2 ≤ R
  Rprev_eq : Rprev = R - 1
  atom_eq : Atom = firstAtoms.atom i
  origin_entry : origin.toPoint = firstAtoms.entryPoint i
  target_height :
    origin.l + (gap : ℤ) = (firstAtoms.entryTriangle i).cornerL
  restart :
    Lemma79TailRestartIdentity Atom ExitWhite fullMoment futureMoment
  prefix_first_passage :
    ∀ a omega, omega ∈ prefixAtom a ->
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        origin gap (K a) (pre a)
  prefix_endpoint_eq :
    ∀ a omega, omega ∈ prefixAtom a ->
      endpoint a = taoSection7RenewalPathPoint origin (pre a) (K a)
  prefix_expect_partition :
    pmfExpectation mu (exitFutureMoment Atom ExitWhite futureMoment) =
      ∑ a, pmfExpectation mu (atomIndicator (prefixAtom a) (prefixFuture a))
  future_induction_after_prefix :
    ∀ a,
      pmfExpectation mu (atomIndicator (prefixAtom a) (prefixFuture a)) ≤
        Real.exp epsilon *
          pmfExpectation mu (atomIndicator (prefixAtom a) (prefixFactor a))
  prefix_factor_le_exit_weight :
    ∀ a,
      pmfExpectation mu (atomIndicator (prefixAtom a) (prefixFactor a)) ≤
        Real.exp epsilon *
          pmfExpectation mu (atomIndicator (prefixAtom a)
            (exitWhiteWeight ExitWhite))
  prefix_exit_weight_partition :
    (∑ a, pmfExpectation mu (atomIndicator (prefixAtom a)
      (exitWhiteWeight ExitWhite))) =
      pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite))

theorem Lemma79FixedOriginStoppedRestartTowerSource.to_stoppedRestartTowerSource
    {Omega iota kappa : Type*} [Fintype Omega] [Fintype iota]
    [Fintype kappa]
    {mu : PMF Omega}
    {R Rprev : ℕ}
    {nonzero Atom ExitWhite : Set Omega}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family}
    {i : iota}
    {prefixAtom : kappa -> Set Omega}
    {origin : TaoSection7RenewalPoint}
    {gap : ℕ}
    {K : kappa -> ℕ}
    {pre : kappa -> List TaoSection7RenewalPoint}
    {endpoint : kappa -> TaoSection7RenewalPoint}
    {fullMoment futureMoment : Omega -> ℝ}
    {prefixFuture prefixFactor : kappa -> Omega -> ℝ}
    {epsilon : ℝ}
    (hsrc :
      Lemma79FixedOriginStoppedRestartTowerSource
        mu R Rprev nonzero Atom ExitWhite W pointAt family firstAtoms i
        prefixAtom origin gap K pre endpoint fullMoment futureMoment
        prefixFuture prefixFactor epsilon) :
    Lemma79StoppedRestartTowerSource
      mu R Rprev Atom ExitWhite prefixAtom (fun _ => origin) (fun _ => gap)
      K pre endpoint fullMoment futureMoment prefixFuture prefixFactor epsilon
    where
  two_le_R := hsrc.two_le_R
  Rprev_eq := hsrc.Rprev_eq
  restart := hsrc.restart
  prefix_first_passage := by
    intro a omega hmem
    exact hsrc.prefix_first_passage a omega hmem
  prefix_endpoint_eq := by
    intro a omega hmem
    exact hsrc.prefix_endpoint_eq a omega hmem
  prefix_expect_partition := hsrc.prefix_expect_partition
  future_induction_after_prefix := hsrc.future_induction_after_prefix
  prefix_factor_le_exit_weight := hsrc.prefix_factor_le_exit_weight
  prefix_exit_weight_partition := hsrc.prefix_exit_weight_partition

/--
Fixed-prefix fresh-tail expectation law.

For a fixed stopped-prefix atom, future tail expectations are represented by a
tail PMF independent of the prefix, with the parent atom mass factored out.
This is the expectation-level socket behind the `prefix_tower` premise.
-/
structure Lemma79FixedPrefixFreshTailExpectationLaw
    {Omega Tail : Type*} [Fintype Omega] [Fintype Tail]
    (mu : PMF Omega)
    (AtomA : Set Omega)
    (tailOf : Omega -> Tail)
    (nuTail : PMF Tail) : Prop where
  expectation_law :
    ∀ F : Tail -> ℝ,
      pmfExpectation mu (atomIndicator AtomA (fun omega => F (tailOf omega))) =
        pmfProb mu AtomA * pmfExpectation nuTail F

/--
Finite tail-fiber mass law for a fixed stopped-prefix atom.

This is the source-facing mass socket beneath
`Lemma79FixedPrefixFreshTailExpectationLaw`: each finite tail key has mass
equal to the atom mass times the fresh-tail PMF weight, without conditioning by
division.

At this layer `Tail` is only an abstract finite observable for the
`prefix_tower` expectation socket.  A reusable post-stopped continuation
carrier must expose its endpoint, remaining horizon, continuation data, and
later event projections in a separate source-facing interface.
-/
structure Lemma79FixedPrefixTailFiberLaw
    {Omega Tail : Type*} [Fintype Omega] [Fintype Tail]
    (mu : PMF Omega)
    (AtomA : Set Omega)
    (tailOf : Omega -> Tail)
    (nuTail : PMF Tail) : Prop where
  tail_fiber_law :
    ∀ tail : Tail,
      pmfProb mu {omega | omega ∈ AtomA ∧ tailOf omega = tail} =
        pmfProb mu AtomA * (nuTail tail).toReal

/--
Finite source prefix/tail product law.

This is still a source-facing socket: it records the marginal mass of each
finite prefix key and the joint mass of each prefix/tail key.  It does not
construct those keys or prove the stopped strong-Markov law.
-/
structure Lemma79SourcePrefixTailProductLaw
    {OmegaSrc Prefix Tail : Type*} [Fintype OmegaSrc] [Fintype Prefix]
    [Fintype Tail]
    (nu : PMF OmegaSrc)
    (prefixOf : OmegaSrc -> Prefix)
    (tailKey : OmegaSrc -> Tail)
    (prefixMass : Prefix -> ℝ)
    (nuTail : PMF Tail) : Prop where
  prefix_fiber_law :
    ∀ pfx,
      pmfProb nu {sigma | prefixOf sigma = pfx} = prefixMass pfx
  joint_fiber_law :
    ∀ pfx tail,
      pmfProb nu {sigma | prefixOf sigma = pfx ∧ tailKey sigma = tail} =
        prefixMass pfx * (nuTail tail).toReal

theorem lemma79_sourcePrefixTailProductLaw_of_pairProductMass
    {Pre Tail : Type*} [Fintype Pre] [Fintype Tail]
    {nu : PMF (Pre × Tail)}
    {prefixMass : Pre -> ℝ}
    {nuTail : PMF Tail}
    (hpair :
      ∀ pre tail,
        (nu (pre, tail)).toReal =
          prefixMass pre * (nuTail tail).toReal) :
    Lemma79SourcePrefixTailProductLaw
      nu Prod.fst Prod.snd prefixMass nuTail := by
  classical
  refine ⟨?_, ?_⟩
  · intro pre
    calc
      pmfProb nu {sigma | sigma.1 = pre} =
          ∑ x : Pre × Tail, if x.1 = pre then (nu x).toReal else 0 := by
          unfold pmfProb
          refine Finset.sum_congr rfl ?_
          intro x _hx
          simp
      _ =
          ∑ pre' : Pre, ∑ tail : Tail,
            if pre' = pre then (nu (pre', tail)).toReal else 0 := by
          rw [Fintype.sum_prod_type]
      _ = ∑ tail : Tail, (nu (pre, tail)).toReal := by
          rw [Finset.sum_eq_single pre]
          · simp
          · intro pre' _hpre' hne
            simp [hne]
          · intro hnot
            exact (hnot (Finset.mem_univ pre)).elim
      _ = ∑ tail : Tail, prefixMass pre * (nuTail tail).toReal := by
          refine Finset.sum_congr rfl ?_
          intro tail _htail
          rw [hpair pre tail]
      _ = prefixMass pre * ∑ tail : Tail, (nuTail tail).toReal := by
          rw [Finset.mul_sum]
      _ = prefixMass pre := by
          rw [pmf_sum_toReal nuTail]
          ring
  · intro pre tail
    calc
      pmfProb nu {sigma | sigma.1 = pre ∧ sigma.2 = tail} =
          ∑ x : Pre × Tail,
            if x.1 = pre ∧ x.2 = tail then (nu x).toReal else 0 := by
          unfold pmfProb
          refine Finset.sum_congr rfl ?_
          intro x _hx
          simp
      _ = (nu (pre, tail)).toReal := by
          rw [Finset.sum_eq_single (pre, tail)]
          · simp
          · intro x _hx hne
            have hnot : ¬ (x.1 = pre ∧ x.2 = tail) := by
              intro h
              exact hne (Prod.ext h.1 h.2)
            simp [hnot]
          · intro hnot
            exact (hnot (Finset.mem_univ (pre, tail))).elim
      _ = prefixMass pre * (nuTail tail).toReal := by
          rw [hpair pre tail]

theorem lemma79_sourcePrefixTailProductLaw_of_finiteProductCarrier
    {Pre Tail : Type*} [Fintype Pre] [Fintype Tail]
    {nu : PMF (Pre × Tail)}
    {nuPre : PMF Pre} {nuTail : PMF Tail}
    (hprod :
      ∀ pre tail,
        (nu (pre, tail)).toReal =
          (nuPre pre).toReal * (nuTail tail).toReal) :
    Lemma79SourcePrefixTailProductLaw
      nu Prod.fst Prod.snd (fun pre => (nuPre pre).toReal) nuTail := by
  classical
  refine ⟨?_, ?_⟩
  · intro pre
    calc
      pmfProb nu {sigma | sigma.1 = pre} =
          ∑ x : Pre × Tail, if x.1 = pre then (nu x).toReal else 0 := by
          unfold pmfProb
          refine Finset.sum_congr rfl ?_
          intro x _hx
          simp
      _ =
          ∑ pre' : Pre, ∑ tail : Tail,
            if pre' = pre then (nu (pre', tail)).toReal else 0 := by
          rw [Fintype.sum_prod_type]
      _ = ∑ tail : Tail, (nu (pre, tail)).toReal := by
          rw [Finset.sum_eq_single pre]
          · simp
          · intro pre' _hpre' hne
            simp [hne]
          · intro hnot
            exact (hnot (Finset.mem_univ pre)).elim
      _ = ∑ tail : Tail, (nuPre pre).toReal * (nuTail tail).toReal := by
          refine Finset.sum_congr rfl ?_
          intro tail _htail
          rw [hprod pre tail]
      _ = (nuPre pre).toReal * ∑ tail : Tail, (nuTail tail).toReal := by
          rw [Finset.mul_sum]
      _ = (nuPre pre).toReal := by
          rw [pmf_sum_toReal nuTail]
          ring
  · intro pre tail
    calc
      pmfProb nu {sigma | sigma.1 = pre ∧ sigma.2 = tail} =
          ∑ x : Pre × Tail,
            if x.1 = pre ∧ x.2 = tail then (nu x).toReal else 0 := by
          unfold pmfProb
          refine Finset.sum_congr rfl ?_
          intro x _hx
          simp
      _ = (nu (pre, tail)).toReal := by
          rw [Finset.sum_eq_single (pre, tail)]
          · simp
          · intro x _hx hne
            have hnot : ¬ (x.1 = pre ∧ x.2 = tail) := by
              intro h
              exact hne (Prod.ext h.1 h.2)
            simp [hnot]
          · intro hnot
            exact (hnot (Finset.mem_univ (pre, tail))).elim
      _ = (nuPre pre).toReal * (nuTail tail).toReal := by
          rw [hprod pre tail]

theorem lemma79_sourcePrefixTailProductLaw_of_holdAppendProductCarrier
    {Pre Tail : Type*} [Fintype Pre] [Fintype Tail]
    {K p : ℕ}
    {preList : Pre -> List TaoSection7RenewalPoint}
    {tailList : Tail -> List TaoSection7RenewalPoint}
    {nu : PMF (Pre × Tail)}
    {nuPre : PMF Pre} {nuTail : PMF Tail}
    (hpre_len : ∀ pre, (preList pre).length = K)
    (htail_len : ∀ tail, (tailList tail).length = p)
    (hnu :
      ∀ pre tail,
        (nu (pre, tail)).toReal =
          (taoSection7HoldListPMF (K + p)
            (preList pre ++ tailList tail)).toReal)
    (hnuPre :
      ∀ pre,
        (nuPre pre).toReal =
          (taoSection7HoldListPMF K (preList pre)).toReal)
    (hnuTail :
      ∀ tail,
        (nuTail tail).toReal =
          (taoSection7HoldListPMF p (tailList tail)).toReal) :
    Lemma79SourcePrefixTailProductLaw
      nu Prod.fst Prod.snd (fun pre => (nuPre pre).toReal) nuTail := by
  refine lemma79_sourcePrefixTailProductLaw_of_finiteProductCarrier ?_
  intro pre tail
  rw [hnu pre tail, hnuPre pre, hnuTail tail]
  exact taoSection7HoldListPMF_append_toReal_of_lengths
    (hpre_len pre) (htail_len tail)

theorem lemma79_sourcePrefixTailProductLaw_of_variableHoldAppendProductCarrier
    {Pre Tail : Type*} [Fintype Pre] [Fintype Tail]
    {K : Pre -> ℕ} {p : ℕ}
    {preList : Pre -> List TaoSection7RenewalPoint}
    {tailList : Tail -> List TaoSection7RenewalPoint}
    {nu : PMF (Pre × Tail)}
    {nuPre : PMF Pre} {nuTail : PMF Tail}
    (hpre_len : ∀ pre, (preList pre).length = K pre)
    (htail_len : ∀ tail, (tailList tail).length = p)
    (hnu :
      ∀ pre tail,
        (nu (pre, tail)).toReal =
          (taoSection7HoldListPMF (K pre + p)
            (preList pre ++ tailList tail)).toReal)
    (hnuPre :
      ∀ pre,
        (nuPre pre).toReal =
          (taoSection7HoldListPMF (K pre) (preList pre)).toReal)
    (hnuTail :
      ∀ tail,
        (nuTail tail).toReal =
          (taoSection7HoldListPMF p (tailList tail)).toReal) :
    Lemma79SourcePrefixTailProductLaw
      nu Prod.fst Prod.snd (fun pre => (nuPre pre).toReal) nuTail := by
  refine lemma79_sourcePrefixTailProductLaw_of_finiteProductCarrier ?_
  intro pre tail
  rw [hnu pre tail, hnuPre pre, hnuTail tail]
  exact taoSection7HoldListPMF_append_toReal_of_lengths
    (hpre_len pre) (htail_len tail)

/--
Pointwise pair mass for a literal `Pre × Tail` carrier with product-law fields.

This lets later sampled-law producers reuse the already-required
`source_product` field instead of separately assuming a pointwise formula for
the same source PMF.
-/
theorem lemma79_pairMass_of_sourcePrefixTailProductLaw
    {Pre Tail : Type*} [Fintype Pre] [Fintype Tail]
    {nu : PMF (Pre × Tail)}
    {prefixMass : Pre -> ℝ}
    {nuTail : PMF Tail}
    (hprod :
      Lemma79SourcePrefixTailProductLaw
        nu Prod.fst Prod.snd prefixMass nuTail) :
    ∀ pre tail,
      (nu (pre, tail)).toReal =
        prefixMass pre * (nuTail tail).toReal := by
  classical
  intro pre tail
  have hsingleton :
      pmfProb nu {sigma | sigma.1 = pre ∧ sigma.2 = tail} =
        (nu (pre, tail)).toReal := by
    unfold pmfProb
    rw [Finset.sum_eq_single (pre, tail)]
    · simp
    · rintro ⟨pre', tail'⟩ _hmem hne
      by_cases hpair : pre' = pre ∧ tail' = tail
      · have hp : (pre', tail') = (pre, tail) := by
          ext <;> simp [hpair.1, hpair.2]
        exact False.elim (hne hp)
      · simp [hpair]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  rw [← hsingleton, hprod.joint_fiber_law pre tail]

theorem lemma79_sourceTailKeyLaw_of_prefixTailProductLaw
    {OmegaSrc Prefix Tail : Type*} [Fintype OmegaSrc] [Fintype Prefix]
    [Fintype Tail]
    {nu : PMF OmegaSrc}
    {prefixOf : OmegaSrc -> Prefix}
    {tailKey : OmegaSrc -> Tail}
    {prefixMass : Prefix -> ℝ}
    {nuTail : PMF Tail}
    {prefixOK : Prefix -> Prop} [DecidablePred prefixOK]
    (hprod :
      Lemma79SourcePrefixTailProductLaw
        nu prefixOf tailKey prefixMass nuTail) :
    ∀ tail,
      pmfProb nu {sigma | prefixOK (prefixOf sigma) ∧ tailKey sigma = tail} =
        pmfProb nu {sigma | prefixOK (prefixOf sigma)} *
          (nuTail tail).toReal := by
  intro tail
  have hprefix_partition :
      pmfProb nu {sigma | prefixOK (prefixOf sigma)} =
        ∑ pfx, if prefixOK pfx then prefixMass pfx else 0 := by
    calc
      pmfProb nu {sigma | prefixOK (prefixOf sigma)} =
          ∑ pfx,
            pmfProb nu {sigma | prefixOK pfx ∧ prefixOf sigma = pfx} := by
            exact pmfProb_partition_of_key
              (mu := nu)
              (Parent := {sigma | prefixOK (prefixOf sigma)})
              (atom := fun pfx =>
                {sigma | prefixOK pfx ∧ prefixOf sigma = pfx})
              (key := prefixOf)
              (by
                intro sigma hsigma
                exact ⟨hsigma, rfl⟩)
              (by
                intro pfx sigma hsigma
                exact ⟨by simpa [hsigma.2] using hsigma.1, hsigma.2⟩)
      _ = ∑ pfx, if prefixOK pfx then prefixMass pfx else 0 := by
            refine Finset.sum_congr rfl ?_
            intro pfx _hpfx
            by_cases hp : prefixOK pfx
            · simp [hp, hprod.prefix_fiber_law pfx]
            · simp [hp, pmfProb_empty]
  have hjoint_partition :
      pmfProb nu {sigma | prefixOK (prefixOf sigma) ∧ tailKey sigma = tail} =
        ∑ pfx,
          if prefixOK pfx then prefixMass pfx * (nuTail tail).toReal else 0 := by
    calc
      pmfProb nu {sigma | prefixOK (prefixOf sigma) ∧ tailKey sigma = tail} =
          ∑ pfx,
            pmfProb nu
              {sigma | prefixOK pfx ∧ prefixOf sigma = pfx ∧
                tailKey sigma = tail} := by
            exact pmfProb_partition_of_key
              (mu := nu)
              (Parent :=
                {sigma | prefixOK (prefixOf sigma) ∧ tailKey sigma = tail})
              (atom := fun pfx =>
                {sigma | prefixOK pfx ∧ prefixOf sigma = pfx ∧
                  tailKey sigma = tail})
              (key := prefixOf)
              (by
                intro sigma hsigma
                exact ⟨by simpa using hsigma.1, rfl, hsigma.2⟩)
              (by
                intro pfx sigma hsigma
                exact ⟨⟨by simpa [hsigma.2.1] using hsigma.1,
                  hsigma.2.2⟩, hsigma.2.1⟩)
      _ =
        ∑ pfx,
          if prefixOK pfx then prefixMass pfx * (nuTail tail).toReal else 0 := by
            refine Finset.sum_congr rfl ?_
            intro pfx _hpfx
            by_cases hp : prefixOK pfx
            · simp [hp, hprod.joint_fiber_law pfx tail]
            · simp [hp, pmfProb_empty]
  rw [hjoint_partition, hprefix_partition]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro pfx _hpfx
  by_cases hp : prefixOK pfx
  · simp [hp]
  · simp [hp]

theorem lemma79_sourceTailKeyLaw_of_prefixTailProductLaw_and_atomPullback
    {OmegaSrc Omega Prefix Tail : Type*} [Fintype OmegaSrc] [Fintype Prefix]
    [Fintype Tail]
    {nu : PMF OmegaSrc}
    {sampleOf : OmegaSrc -> Omega}
    {AtomA : Set Omega}
    {prefixOf : OmegaSrc -> Prefix}
    {tailKey : OmegaSrc -> Tail}
    {prefixMass : Prefix -> ℝ}
    {nuTail : PMF Tail}
    {prefixOK : Prefix -> Prop} [DecidablePred prefixOK]
    (hprod :
      Lemma79SourcePrefixTailProductLaw
        nu prefixOf tailKey prefixMass nuTail)
    (hatom :
      ∀ sigma, sampleOf sigma ∈ AtomA ↔ prefixOK (prefixOf sigma)) :
    ∀ tail,
      pmfProb nu {sigma | sampleOf sigma ∈ AtomA ∧ tailKey sigma = tail} =
        pmfProb nu {sigma | sampleOf sigma ∈ AtomA} *
          (nuTail tail).toReal := by
  intro tail
  have htail_law :=
    lemma79_sourceTailKeyLaw_of_prefixTailProductLaw
      (nu := nu) (prefixOf := prefixOf) (tailKey := tailKey)
      (prefixMass := prefixMass) (nuTail := nuTail)
      (prefixOK := prefixOK) hprod tail
  have htail_event :
      {sigma | sampleOf sigma ∈ AtomA ∧ tailKey sigma = tail} =
        {sigma | prefixOK (prefixOf sigma) ∧ tailKey sigma = tail} := by
    ext sigma
    constructor
    · intro hsigma
      exact ⟨(hatom sigma).mp hsigma.1, hsigma.2⟩
    · intro hsigma
      exact ⟨(hatom sigma).mpr hsigma.1, hsigma.2⟩
  have hatom_event :
      {sigma | sampleOf sigma ∈ AtomA} =
        {sigma | prefixOK (prefixOf sigma)} := by
    ext sigma
    exact hatom sigma
  rw [htail_event, hatom_event]
  exact htail_law

theorem lemma79_sourceTailKeyLaw_of_finiteProductCarrier
    {Pre Tail Omega : Type*} [Fintype Pre] [Fintype Tail]
    {nu : PMF (Pre × Tail)}
    {nuPre : PMF Pre} {nuTail : PMF Tail}
    {sampleOf : Pre × Tail -> Omega}
    {AtomA : Set Omega}
    {PreAtom : Set Pre}
    {tailKey : Pre × Tail -> Tail}
    (hprod :
      ∀ pre tail,
        (nu (pre, tail)).toReal =
          (nuPre pre).toReal * (nuTail tail).toReal)
    (hatom :
      ∀ pre tail, sampleOf (pre, tail) ∈ AtomA ↔ pre ∈ PreAtom)
    (htail :
      ∀ pre tail, tailKey (pre, tail) = tail) :
    ∀ tail,
      pmfProb nu {sigma | sampleOf sigma ∈ AtomA ∧ tailKey sigma = tail} =
        pmfProb nu {sigma | sampleOf sigma ∈ AtomA} *
          (nuTail tail).toReal := by
  classical
  intro tail
  have hden :
      pmfProb nu {sigma | sampleOf sigma ∈ AtomA} =
        ∑ pre, if pre ∈ PreAtom then (nuPre pre).toReal else 0 := by
    calc
      pmfProb nu {sigma | sampleOf sigma ∈ AtomA} =
          ∑ x : Pre × Tail,
            if sampleOf x ∈ AtomA then (nu x).toReal else 0 := by
            unfold pmfProb
            refine Finset.sum_congr rfl ?_
            intro x _hx
            simp
      _ = ∑ pre, ∑ tail' : Tail,
            if sampleOf (pre, tail') ∈ AtomA then
              (nu (pre, tail')).toReal else 0 := by
            rw [Fintype.sum_prod_type]
      _ = ∑ pre, ∑ tail' : Tail,
            if pre ∈ PreAtom then
              (nuPre pre).toReal * (nuTail tail').toReal else 0 := by
            refine Finset.sum_congr rfl ?_
            intro pre _hpre
            refine Finset.sum_congr rfl ?_
            intro tail' _htail'
            by_cases hp : pre ∈ PreAtom
            · have hat : sampleOf (pre, tail') ∈ AtomA :=
                (hatom pre tail').mpr hp
              rw [if_pos hat, if_pos hp, hprod pre tail']
            · have hnot : sampleOf (pre, tail') ∉ AtomA := by
                intro hmem
                exact hp ((hatom pre tail').mp hmem)
              rw [if_neg hnot, if_neg hp]
      _ = ∑ pre, if pre ∈ PreAtom then (nuPre pre).toReal else 0 := by
            refine Finset.sum_congr rfl ?_
            intro pre _hpre
            by_cases hp : pre ∈ PreAtom
            · calc
                (∑ tail' : Tail,
                    if pre ∈ PreAtom then
                      (nuPre pre).toReal * (nuTail tail').toReal else 0)
                    = ∑ tail' : Tail,
                        (nuPre pre).toReal * (nuTail tail').toReal := by
                        simp [hp]
                _ = (nuPre pre).toReal *
                      ∑ tail' : Tail, (nuTail tail').toReal := by
                        rw [Finset.mul_sum]
                _ = (nuPre pre).toReal := by
                        rw [pmf_sum_toReal nuTail]
                        ring
                _ = (if pre ∈ PreAtom then (nuPre pre).toReal else 0) := by
                        simp [hp]
            · simp [hp]
  have hnum :
      pmfProb nu {sigma | sampleOf sigma ∈ AtomA ∧ tailKey sigma = tail} =
        ∑ pre, if pre ∈ PreAtom then
          (nuPre pre).toReal * (nuTail tail).toReal else 0 := by
    calc
      pmfProb nu {sigma | sampleOf sigma ∈ AtomA ∧ tailKey sigma = tail} =
          ∑ x : Pre × Tail,
            if sampleOf x ∈ AtomA ∧ tailKey x = tail then
              (nu x).toReal else 0 := by
            unfold pmfProb
            refine Finset.sum_congr rfl ?_
            intro x _hx
            simp
      _ = ∑ pre, ∑ tail' : Tail,
            if sampleOf (pre, tail') ∈ AtomA ∧
                tailKey (pre, tail') = tail then
              (nu (pre, tail')).toReal else 0 := by
            rw [Fintype.sum_prod_type]
      _ = ∑ pre, ∑ tail' : Tail,
            if pre ∈ PreAtom ∧ tail' = tail then
              (nuPre pre).toReal * (nuTail tail').toReal else 0 := by
            refine Finset.sum_congr rfl ?_
            intro pre _hpre
            refine Finset.sum_congr rfl ?_
            intro tail' _htail'
            by_cases hp : pre ∈ PreAtom
            · by_cases ht : tail' = tail
              · subst tail'
                have hat : sampleOf (pre, tail) ∈ AtomA :=
                  (hatom pre tail).mpr hp
                have hleft :
                    sampleOf (pre, tail) ∈ AtomA ∧
                      tailKey (pre, tail) = tail :=
                  ⟨hat, htail pre tail⟩
                have hright : pre ∈ PreAtom ∧ tail = tail := ⟨hp, rfl⟩
                rw [if_pos hleft, if_pos hright, hprod pre tail]
              · have hleft :
                    ¬ (sampleOf (pre, tail') ∈ AtomA ∧
                      tailKey (pre, tail') = tail) := by
                  intro h
                  have htail_eq : tail' = tail := by
                    rw [← htail pre tail']
                    exact h.2
                  exact ht htail_eq
                have hright : ¬ (pre ∈ PreAtom ∧ tail' = tail) := by
                  intro h
                  exact ht h.2
                rw [if_neg hleft, if_neg hright]
            · have hleft :
                  ¬ (sampleOf (pre, tail') ∈ AtomA ∧
                    tailKey (pre, tail') = tail) := by
                intro h
                exact hp ((hatom pre tail').mp h.1)
              have hright : ¬ (pre ∈ PreAtom ∧ tail' = tail) := by
                intro h
                exact hp h.1
              rw [if_neg hleft, if_neg hright]
      _ = ∑ pre, if pre ∈ PreAtom then
            (nuPre pre).toReal * (nuTail tail).toReal else 0 := by
            refine Finset.sum_congr rfl ?_
            intro pre _hpre
            by_cases hp : pre ∈ PreAtom
            · rw [Finset.sum_eq_single tail]
              · simp [hp]
              · intro tail' _htail' hne
                simp [hp, hne]
              · intro hnot
                exact (hnot (Finset.mem_univ tail)).elim
            · simp [hp]
  rw [hnum, hden]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro pre _hpre
  by_cases hp : pre ∈ PreAtom
  · simp [hp]
  · simp [hp]

/--
Named finite-product producer for the `hsource` premise consumed by
`lemma79_fixedPrefixTailFiberLaw_of_sourceTailKey`.

This is an alias of `lemma79_sourceTailKeyLaw_of_finiteProductCarrier`; the
name is kept as a route socket for probes and downstream adapters.
-/
theorem lemma79_sourceTailKey_hsource_of_finiteProductCarrier
    {Pre Tail Omega : Type*} [Fintype Pre] [Fintype Tail]
    {nu : PMF (Pre × Tail)}
    {nuPre : PMF Pre} {nuTail : PMF Tail}
    {sampleOf : Pre × Tail -> Omega}
    {AtomA : Set Omega}
    {PreAtom : Set Pre}
    {tailKey : Pre × Tail -> Tail}
    (hprod :
      ∀ pre tail,
        (nu (pre, tail)).toReal =
          (nuPre pre).toReal * (nuTail tail).toReal)
    (hatom :
      ∀ pre tail, sampleOf (pre, tail) ∈ AtomA ↔ pre ∈ PreAtom)
    (htail :
      ∀ pre tail, tailKey (pre, tail) = tail) :
    ∀ tail,
      pmfProb nu {sigma | sampleOf sigma ∈ AtomA ∧ tailKey sigma = tail} =
        pmfProb nu {sigma | sampleOf sigma ∈ AtomA} *
          (nuTail tail).toReal := by
  exact lemma79_sourceTailKeyLaw_of_finiteProductCarrier
    (nu := nu) (nuPre := nuPre) (nuTail := nuTail)
    (sampleOf := sampleOf) (AtomA := AtomA) (PreAtom := PreAtom)
    (tailKey := tailKey) hprod hatom htail

/--
Transport a finite source tail-key factorization through a sampled PMF.

This bridge separates the carrier transport `mu = nu.map sampleOf` from the
actual source-side tail-key law `hsource`.  The theorem does not prove
stopped independence; it only turns a source factorization into the finite
tail-fiber law consumed by the prefix-tower observable layer.
-/
theorem lemma79_fixedPrefixTailFiberLaw_of_sourceTailKey
    {OmegaSrc Omega Tail : Type*} [Fintype OmegaSrc] [Fintype Omega]
    [Fintype Tail]
    {nu : PMF OmegaSrc}
    {mu : PMF Omega}
    {sampleOf : OmegaSrc -> Omega}
    {AtomA : Set Omega}
    {tailOf : Omega -> Tail}
    {tailKey : OmegaSrc -> Tail}
    {nuTail : PMF Tail}
    (hmu : mu = nu.map sampleOf)
    (htail_compat :
      ∀ sigma, sampleOf sigma ∈ AtomA ->
        tailOf (sampleOf sigma) = tailKey sigma)
    (hsource :
      ∀ tail,
        pmfProb nu {sigma | sampleOf sigma ∈ AtomA ∧ tailKey sigma = tail} =
          pmfProb nu {sigma | sampleOf sigma ∈ AtomA} *
            (nuTail tail).toReal) :
    Lemma79FixedPrefixTailFiberLaw mu AtomA tailOf nuTail := by
  refine ⟨?_⟩
  intro tail
  have hatom_pull :
      pmfProb mu AtomA = pmfProb nu {sigma | sampleOf sigma ∈ AtomA} := by
    rw [hmu]
    exact pmfProb_map_preimage nu sampleOf AtomA
  have hpreimage :
      sampleOf ⁻¹' {omega | omega ∈ AtomA ∧ tailOf omega = tail} =
        {sigma | sampleOf sigma ∈ AtomA ∧ tailKey sigma = tail} := by
    ext sigma
    constructor
    · intro hsigma
      exact ⟨hsigma.1, by simpa [htail_compat sigma hsigma.1] using hsigma.2⟩
    · intro hsigma
      exact ⟨hsigma.1, by rw [htail_compat sigma hsigma.1, hsigma.2]⟩
  have hfiber_pull :
      pmfProb mu {omega | omega ∈ AtomA ∧ tailOf omega = tail} =
        pmfProb nu {sigma | sampleOf sigma ∈ AtomA ∧ tailKey sigma = tail} := by
    rw [hmu]
    rw [pmfProb_map_preimage nu sampleOf
      {omega | omega ∈ AtomA ∧ tailOf omega = tail}]
    rw [hpreimage]
  rw [hfiber_pull, hsource tail, hatom_pull]

/--
Convert global stopped-split fiber masses into the sampled-law field.

This is only finite PMF algebra.  The premise must be proved for the same
global source PMF `nu` that will feed the product law; a PMF normalized on a
selected atom would prove a different conditional statement and must be
reweighted before it can feed `Lemma79FixedPrefixObservableProductSource`.
-/
theorem lemma79_sampleLaw_of_stoppedSplitFiberProb
    {Omega Pre Tail : Type*} [Fintype Omega] [Fintype Pre] [Fintype Tail]
    {mu : PMF Omega}
    {nu : PMF (Pre × Tail)}
    {sampleOf : Pre × Tail -> Omega}
    (hfiber :
      ∀ omega,
        (mu omega).toReal =
          pmfProb nu {sigma | sampleOf sigma = omega}) :
    mu = nu.map sampleOf :=
  pmf_eq_map_of_fiber_prob_toReal (p := nu) (q := mu) (f := sampleOf) hfiber

/--
Common-source stopped split coherence for the sampled-law field.

This removes the global fiber-sum premise when both the observable law `mu`
and the split law `nu` are pushforwards of one source PMF `rho`, and the source
sample agrees pointwise with evaluating the split sample.
-/
theorem lemma79_sampleLaw_of_commonSourceSplit
    {Src Omega Pre Tail : Type*}
    {rho : PMF Src}
    {mu : PMF Omega}
    {nu : PMF (Pre × Tail)}
    {splitOf : Src -> Pre × Tail}
    {sampleSrc : Src -> Omega}
    {sampleOf : Pre × Tail -> Omega}
    (hmu : mu = rho.map sampleSrc)
    (hnu : nu = rho.map splitOf)
    (hcompat : ∀ src, sampleSrc src = sampleOf (splitOf src)) :
    mu = nu.map sampleOf := by
  rw [hmu, hnu]
  rw [PMF.map_comp]
  apply congrArg (fun f => rho.map f)
  funext src
  exact hcompat src

/--
Common stopped-split source law for the Lemma 7.9 sampled carrier.

The `split_law` field is the synchronization guard for source credit: the
finite `nu : PMF (Pre × Tail)` used by the sampled-law and product-law sockets
must be the pushforward of the same stopped source `rho` by the same split
map.
-/
structure Lemma79StoppedSplitSourceLaw
    {Src Omega Pre Tail : Type*}
    (rho : PMF Src)
    (mu : PMF Omega)
    (nu : PMF (Pre × Tail))
    (splitOf : Src -> Pre × Tail)
    (sampleSrc : Src -> Omega)
    (sampleOf : Pre × Tail -> Omega) : Prop where
  source_law : mu = rho.map sampleSrc
  split_law : nu = rho.map splitOf
  sample_compat : ∀ src, sampleSrc src = sampleOf (splitOf src)

theorem Lemma79StoppedSplitSourceLaw.sample_law
    {Src Omega Pre Tail : Type*}
    {rho : PMF Src}
    {mu : PMF Omega}
    {nu : PMF (Pre × Tail)}
    {splitOf : Src -> Pre × Tail}
    {sampleSrc : Src -> Omega}
    {sampleOf : Pre × Tail -> Omega}
    (hsrc :
      Lemma79StoppedSplitSourceLaw
        rho mu nu splitOf sampleSrc sampleOf) :
    mu = nu.map sampleOf :=
  lemma79_sampleLaw_of_commonSourceSplit
    hsrc.source_law hsrc.split_law hsrc.sample_compat

/-- The variable first-passage prefix/tail split of a decoded Hold list. -/
noncomputable def lemma79VerticalFirstPassageSplit
    (start : TaoSection7RenewalPoint) (gap : ℕ)
    (full : List TaoSection7RenewalPoint) :
    List TaoSection7RenewalPoint × List TaoSection7RenewalPoint :=
  let K := lemma79VerticalFirstPassageCut start gap full
  (full.take K, full.drop K)

/-- The first `p` increments after the variable first-passage prefix. -/
noncomputable def lemma79VerticalFirstPassageFixedTailSplit
    (p : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ)
    (full : List TaoSection7RenewalPoint) :
    List TaoSection7RenewalPoint × List TaoSection7RenewalPoint :=
  let K := lemma79VerticalFirstPassageCut start gap full
  (full.take K, (full.drop K).take p)

/--
The concrete split law obtained from the raw iid Hold source-prefix PMF.
-/
noncomputable def lemma79RawHoldFirstPassageSplitPMF
    (N : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ) :
    PMF (List TaoSection7RenewalPoint × List TaoSection7RenewalPoint) :=
  (taoSection7HoldSourcePrefixListPMF N).map fun src =>
    lemma79VerticalFirstPassageSplit start gap
      (lemma79DecodeHoldSourcePrefixes src)

/--
The concrete fixed-`p` split law obtained from the raw iid Hold source PMF.
-/
noncomputable def lemma79RawHoldFirstPassageFixedTailSplitPMF
    (N p : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ) :
    PMF (List TaoSection7RenewalPoint × List TaoSection7RenewalPoint) :=
  (taoSection7HoldSourcePrefixListPMF N).map fun src =>
    lemma79VerticalFirstPassageFixedTailSplit p start gap
      (lemma79DecodeHoldSourcePrefixes src)

/--
Every nonzero atom of the common length-`gap+1+p` raw source PMF carries the
exact-cut first-passage certificate and common cut bound.
-/
theorem lemma79VerticalFirstPassagePrefix_take_cut_of_rawSource_nonzero
    (start : TaoSection7RenewalPoint) (gap p : ℕ)
    (src : List (ℕ × List ℕ))
    (hsrc :
      taoSection7HoldSourcePrefixListPMF (gap + 1 + p) src ≠ 0) :
    let full := lemma79DecodeHoldSourcePrefixes src
    let K := lemma79VerticalFirstPassageCut start gap full
    TaoSection7Lemma710.VerticalFirstPassagePrefix
        start gap K (full.take K) ∧ K ≤ gap + 1 := by
  have hlength : src.length = gap + 1 + p := by
    by_contra hne
    exact hsrc
      (taoSection7HoldSourcePrefixListPMF_apply_eq_zero_of_length_ne
        (gap + 1 + p) src hne)
  have hlen : gap + 1 ≤ src.length := by omega
  exact
    lemma79VerticalFirstPassagePrefix_take_cut_decode_and_le
      start gap src hlen

/--
At a certified first-passage prefix, the variable fixed-`p` split fiber is
exactly the ordinary `(K+p)` prefix fiber.
-/
theorem lemma79VerticalFirstPassageFixedTailSplit_eq_iff_take_add_eq
    {start : TaoSection7RenewalPoint} {gap K p : ℕ}
    {pre tail full : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre) :
    lemma79VerticalFirstPassageFixedTailSplit p start gap full = (pre, tail) ↔
      full.take (K + p) = pre ++ tail := by
  let cut := lemma79VerticalFirstPassageCut start gap full
  constructor
  · intro hsplit
    have hpre : full.take cut = pre := by
      exact congrArg Prod.fst hsplit
    have htail_take : (full.drop cut).take p = tail := by
      exact congrArg Prod.snd hsplit
    have hcut_le : cut ≤ full.length :=
      lemma79VerticalFirstPassageCut_le_length start gap full
    have hcut : cut = K := by
      calc
        cut = (full.take cut).length := by
          simp [List.length_take, hcut_le]
        _ = pre.length := congrArg List.length hpre
        _ = K := hfirst.length_eq
    calc
      full.take (K + p) = full.take K ++ (full.drop K).take p :=
        List.take_add
      _ = pre ++ tail := by simpa [hcut] using congrArg₂ (· ++ ·) hpre htail_take
  · intro hprefix
    have hpre : full.take K = pre := by
      have htake := congrArg (fun xs => xs.take K) hprefix
      change (full.take (K + p)).take K = (pre ++ tail).take K at htake
      rw [List.take_take, Nat.min_eq_left (Nat.le_add_right K p)] at htake
      simpa [hfirst.length_eq] using htake
    have htail_take : (full.drop K).take p = tail := by
      have hdrop := congrArg (fun xs => xs.drop K) hprefix
      change (full.take (K + p)).drop K = (pre ++ tail).drop K at hdrop
      rw [List.drop_take, Nat.add_sub_cancel_left] at hdrop
      simpa [hfirst.length_eq] using hdrop
    have hcut : lemma79VerticalFirstPassageCut start gap full = K :=
      lemma79VerticalFirstPassageCut_eq_of_take_eq hfirst hpre
    apply Prod.ext
    · simpa [lemma79VerticalFirstPassageFixedTailSplit, hcut] using hpre
    · simpa [lemma79VerticalFirstPassageFixedTailSplit, hcut] using htail_take

/--
Variable take/drop is injective for every cut function: appending the two
output lists reconstructs the input list.
-/
theorem lemma79_variableTakeDrop_injective
    {α : Type*} (cut : List α -> ℕ) :
    Function.Injective (fun full : List α =>
      (full.take (cut full), full.drop (cut full))) := by
  intro xs ys hxy
  have happ := congrArg
    (fun z : List α × List α => z.1 ++ z.2) hxy
  exact (List.take_append_drop (cut xs) xs).symm.trans
    (happ.trans (List.take_append_drop (cut ys) ys))

/-- Exact point mass of an arbitrary PMF under a variable take/drop split. -/
theorem lemma79_variableTakeDrop_map_apply
    {α : Type*} (rho : PMF (List α)) (cut : List α -> ℕ)
    (pre tail : List α) (hcut : cut (pre ++ tail) = pre.length) :
    (rho.map fun full => (full.take (cut full), full.drop (cut full)))
        (pre, tail) = rho (pre ++ tail) := by
  classical
  rw [PMF.map_apply]
  rw [tsum_eq_single (pre ++ tail)]
  · simp [hcut]
  · intro full hne
    have htarget :
        ((pre ++ tail).take (cut (pre ++ tail)),
          (pre ++ tail).drop (cut (pre ++ tail))) = (pre, tail) := by
      simp [hcut]
    have hpair_ne :
        (pre, tail) ≠ (full.take (cut full), full.drop (cut full)) := by
      intro hpair
      have hsame : pre ++ tail = full :=
        lemma79_variableTakeDrop_injective cut (htarget.trans hpair)
      exact hne hsame.symm
    simp [hpair_ne]

/--
Exact variable first-passage split mass for the decoded iid Hold-list PMF.
-/
theorem lemma79_decodedHoldFirstPassageSplit_apply_toReal
    {start : TaoSection7RenewalPoint} {gap K N : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre) :
    (((taoSection7HoldListPMF N).map
        (lemma79VerticalFirstPassageSplit start gap)) (pre, tail)).toReal =
      (taoSection7HoldListPMF N (pre ++ tail)).toReal := by
  apply congrArg ENNReal.toReal
  exact
    lemma79_variableTakeDrop_map_apply
      (taoSection7HoldListPMF N)
      (lemma79VerticalFirstPassageCut start gap) pre tail
      ((lemma79VerticalFirstPassageCut_append_eq
        (K := K) tail hfirst).trans hfirst.length_eq.symm)

/--
Exact variable first-passage split mass from the actual raw iid Hold
source-prefix PMF.

This is a concrete full-residual source point-mass kernel for Lemma 7.9: the
raw source is decoded, cut at its least vertical first-passage time, and split
into prefix and the entire remaining suffix by one pushforward map.
-/
theorem lemma79_rawHoldFirstPassageSplit_apply_toReal
    {start : TaoSection7RenewalPoint} {gap K N : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre) :
    (lemma79RawHoldFirstPassageSplitPMF N start gap (pre, tail)).toReal =
      (taoSection7HoldListPMF N (pre ++ tail)).toReal := by
  unfold lemma79RawHoldFirstPassageSplitPMF
  change
    (((taoSection7HoldSourcePrefixListPMF N).map
        (lemma79VerticalFirstPassageSplit start gap ∘
          lemma79DecodeHoldSourcePrefixes)) (pre, tail)).toReal = _
  rw [← PMF.map_comp]
  change
    ((((taoSection7HoldSourcePrefixListPMF N).map
        (fun xs => xs.map fun x =>
          taoSection7HoldPointOfPrefix x.1 x.2)).map
        (lemma79VerticalFirstPassageSplit start gap)) (pre, tail)).toReal = _
  rw [taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq]
  exact lemma79_decodedHoldFirstPassageSplit_apply_toReal hfirst

/--
Fixed-`K` slice form of the concrete raw full-residual split mass.

The premise `N = K + p` is atom-specific.  It is not a global fixed-`p` law
when the first-passage time varies under one fixed source horizon.
-/
theorem lemma79_rawHoldFirstPassageSplit_apply_toReal_of_lengths
    {start : TaoSection7RenewalPoint} {gap K p N : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (htail : tail.length = p) (hN : N = K + p) :
    (lemma79RawHoldFirstPassageSplitPMF N start gap (pre, tail)).toReal =
      (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal := by
  have _hfull : (pre ++ tail).length = N := by
    simp [hfirst.length_eq, htail, hN]
  rw [lemma79_rawHoldFirstPassageSplit_apply_toReal hfirst, hN]

/--
Exact fixed-`p` first-passage split mass for the decoded iid Hold-list PMF.

Unlike the full-residual theorem above, this uses one common source horizon
`N` and only assumes that the certified stopped prefix plus `p` future
increments fit inside that horizon.
-/
theorem lemma79_decodedHoldFirstPassageFixedTailSplit_apply_toReal
    {start : TaoSection7RenewalPoint} {gap K p N : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (horizon : K + p ≤ N) :
    (((taoSection7HoldListPMF N).map
        (lemma79VerticalFirstPassageFixedTailSplit p start gap))
      (pre, tail)).toReal =
      (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal := by
  have hmap :
      ((taoSection7HoldListPMF N).map
          (lemma79VerticalFirstPassageFixedTailSplit p start gap))
          (pre, tail) =
        ((taoSection7HoldListPMF N).map
          (fun full : List TaoSection7RenewalPoint => full.take (K + p)))
          (pre ++ tail) := by
    exact
      lemma79_map_apply_eq_of_fiber_iff
        (taoSection7HoldListPMF N)
        (lemma79VerticalFirstPassageFixedTailSplit p start gap)
        (fun full : List TaoSection7RenewalPoint => full.take (K + p))
        (pre, tail) (pre ++ tail) (by
          intro full
          simpa only [eq_comm] using
            lemma79VerticalFirstPassageFixedTailSplit_eq_iff_take_add_eq
              (full := full) (p := p) (tail := tail) hfirst)
  rw [hmap]
  exact
    taoSection7HoldListPMF_map_take_apply_toReal_eq_of_le
      horizon (pre ++ tail)

/--
Exact fixed-`p` first-passage split mass from the actual raw iid Hold source.
-/
theorem lemma79_rawHoldFirstPassageFixedTailSplit_apply_toReal
    {start : TaoSection7RenewalPoint} {gap K p N : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (horizon : K + p ≤ N) :
    (lemma79RawHoldFirstPassageFixedTailSplitPMF N p start gap
      (pre, tail)).toReal =
      (taoSection7HoldListPMF (K + p) (pre ++ tail)).toReal := by
  unfold lemma79RawHoldFirstPassageFixedTailSplitPMF
  change
    (((taoSection7HoldSourcePrefixListPMF N).map
        (lemma79VerticalFirstPassageFixedTailSplit p start gap ∘
          lemma79DecodeHoldSourcePrefixes)) (pre, tail)).toReal = _
  rw [← PMF.map_comp]
  change
    ((((taoSection7HoldSourcePrefixListPMF N).map
        (fun xs => xs.map fun x =>
          taoSection7HoldPointOfPrefix x.1 x.2)).map
        (lemma79VerticalFirstPassageFixedTailSplit p start gap))
      (pre, tail)).toReal = _
  rw [taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq]
  exact
    lemma79_decodedHoldFirstPassageFixedTailSplit_apply_toReal
      hfirst horizon

/-- Pointwise prefix/tail product form of the raw fixed-`p` split law. -/
theorem lemma79_rawHoldFirstPassageFixedTailSplit_product_toReal
    {start : TaoSection7RenewalPoint} {gap K p N : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (htail : tail.length = p) (horizon : K + p ≤ N) :
    (lemma79RawHoldFirstPassageFixedTailSplitPMF N p start gap
      (pre, tail)).toReal =
      (taoSection7HoldListPMF K pre).toReal *
        (taoSection7HoldListPMF p tail).toReal := by
  rw [lemma79_rawHoldFirstPassageFixedTailSplit_apply_toReal
    hfirst horizon]
  exact taoSection7HoldListPMF_append_toReal_of_lengths
    hfirst.length_eq htail

/--
Common length-`B+p` source form of the raw fixed-`p` pointwise product law.

This is the horizon shape needed by a future bounded first-passage producer:
the stopping time may vary with the source, but every certified value lies
below the same deterministic bound `B`.
-/
theorem lemma79_rawHoldFirstPassageFixedTailSplit_product_toReal_of_le_bound
    {start : TaoSection7RenewalPoint} {gap K B p : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (htail : tail.length = p) (hKB : K ≤ B) :
    (lemma79RawHoldFirstPassageFixedTailSplitPMF (B + p) p start gap
      (pre, tail)).toReal =
      (taoSection7HoldListPMF K pre).toReal *
        (taoSection7HoldListPMF p tail).toReal :=
  lemma79_rawHoldFirstPassageFixedTailSplit_product_toReal
    hfirst htail (Nat.add_le_add_right hKB p)

/-- The stopped-prefix marginal of the raw fixed-`p` first-passage split. -/
noncomputable def lemma79RawHoldFirstPassagePrefixPMF
    (p : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ) :
    PMF (List TaoSection7RenewalPoint) :=
  (lemma79RawHoldFirstPassageFixedTailSplitPMF
    (gap + 1 + p) p start gap).map Prod.fst

/-- Native `ENNReal` form of the certified stopped-prefix/tail product. -/
theorem lemma79_rawHoldFirstPassageFixedTailSplit_product_of_le_bound
    {start : TaoSection7RenewalPoint} {gap K B p : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (htail : tail.length = p) (hKB : K ≤ B) :
    lemma79RawHoldFirstPassageFixedTailSplitPMF (B + p) p start gap
        (pre, tail) =
      taoSection7HoldListPMF K pre * taoSection7HoldListPMF p tail := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))).mp
  rw [ENNReal.toReal_mul]
  exact
    lemma79_rawHoldFirstPassageFixedTailSplit_product_toReal_of_le_bound
      hfirst htail hKB

/--
At a certified first-passage prefix, the stopped prefix fiber is the ordinary
fixed-length prefix fiber.
-/
theorem lemma79VerticalFirstPassageFixedTailSplit_fst_eq_iff_take_eq
    {start : TaoSection7RenewalPoint} {gap K p : ℕ}
    {pre full : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre) :
    (lemma79VerticalFirstPassageFixedTailSplit p start gap full).1 = pre ↔
      full.take K = pre := by
  let cut := lemma79VerticalFirstPassageCut start gap full
  constructor
  · intro hpre
    change full.take cut = pre at hpre
    have hcut_le : cut ≤ full.length :=
      lemma79VerticalFirstPassageCut_le_length start gap full
    have hcut : cut = K := by
      calc
        cut = (full.take cut).length := by
          simp [List.length_take, hcut_le]
        _ = pre.length := congrArg List.length hpre
        _ = K := hfirst.length_eq
    simpa [hcut] using hpre
  · intro htake
    have hcut : lemma79VerticalFirstPassageCut start gap full = K :=
      lemma79VerticalFirstPassageCut_eq_of_take_eq hfirst htake
    simpa [lemma79VerticalFirstPassageFixedTailSplit, hcut] using htake

/-- The stopped-prefix marginal has the expected mass on a certified prefix. -/
theorem lemma79_rawHoldFirstPassagePrefixPMF_apply_of_firstPassage
    {start : TaoSection7RenewalPoint} {gap K p : ℕ}
    {pre : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start gap K pre)
    (hK : K ≤ gap + 1) :
    lemma79RawHoldFirstPassagePrefixPMF p start gap pre =
      taoSection7HoldListPMF K pre := by
  have hKN : K ≤ gap + 1 + p := hK.trans (Nat.le_add_right (gap + 1) p)
  unfold lemma79RawHoldFirstPassagePrefixPMF
  unfold lemma79RawHoldFirstPassageFixedTailSplitPMF
  rw [PMF.map_comp]
  have hmap :
      ((taoSection7HoldSourcePrefixListPMF (gap + 1 + p)).map
          (Prod.fst ∘ fun src =>
            lemma79VerticalFirstPassageFixedTailSplit p start gap
              (lemma79DecodeHoldSourcePrefixes src))) pre =
        ((taoSection7HoldSourcePrefixListPMF (gap + 1 + p)).map
          (fun src => (lemma79DecodeHoldSourcePrefixes src).take K)) pre := by
    exact
      lemma79_map_apply_eq_of_fiber_iff
        (taoSection7HoldSourcePrefixListPMF (gap + 1 + p))
        (Prod.fst ∘ fun src =>
          lemma79VerticalFirstPassageFixedTailSplit p start gap
            (lemma79DecodeHoldSourcePrefixes src))
        (fun src => (lemma79DecodeHoldSourcePrefixes src).take K)
        pre pre (by
          intro src
          simpa only [Function.comp_apply, eq_comm] using
            lemma79VerticalFirstPassageFixedTailSplit_fst_eq_iff_take_eq
              (p := p) (full := lemma79DecodeHoldSourcePrefixes src) hfirst)
  rw [hmap]
  have htake :=
    taoSection7HoldSourcePrefixListPMF_map_take_holdPoint_eq_of_le hKN
  exact congrArg (fun rho : PMF (List TaoSection7RenewalPoint) => rho pre)
    (by simpa [lemma79DecodeHoldSourcePrefixes] using htake)

/--
Every nonzero atom of the raw stopped split carries the complete
first-passage, prefix-bound, and fresh-tail-length certificate.
-/
theorem lemma79_rawHoldFirstPassageFixedTailSplit_nonzero_certifies
    {start : TaoSection7RenewalPoint} {gap p : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hpair :
      lemma79RawHoldFirstPassageFixedTailSplitPMF (gap + 1 + p) p start gap
        (pre, tail) ≠ 0) :
    TaoSection7Lemma710.VerticalFirstPassagePrefix
        start gap pre.length pre ∧
      pre.length ≤ gap + 1 ∧ tail.length = p := by
  classical
  have hmem :
      (pre, tail) ∈
        (lemma79RawHoldFirstPassageFixedTailSplitPMF
          (gap + 1 + p) p start gap).support := hpair
  unfold lemma79RawHoldFirstPassageFixedTailSplitPMF at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
    ⟨src, hsrc, hsplit⟩
  let full := lemma79DecodeHoldSourcePrefixes src
  let K := lemma79VerticalFirstPassageCut start gap full
  have hcert :=
    lemma79VerticalFirstPassagePrefix_take_cut_of_rawSource_nonzero
      start gap p src (by simpa using hsrc)
  change
    TaoSection7Lemma710.VerticalFirstPassagePrefix
        start gap K (full.take K) ∧ K ≤ gap + 1 at hcert
  have hpre : full.take K = pre := by
    exact congrArg Prod.fst hsplit
  have htail : (full.drop K).take p = tail := by
    exact congrArg Prod.snd hsplit
  have hK : K = pre.length := by
    calc
      K = (full.take K).length := hcert.1.length_eq.symm
      _ = pre.length := congrArg List.length hpre
  have hfirst :
      TaoSection7Lemma710.VerticalFirstPassagePrefix
        start gap pre.length pre := by
    rw [← hK, ← hpre]
    exact hcert.1
  have hB : pre.length ≤ gap + 1 := by
    rw [← hK]
    exact hcert.2
  have hsrc_length : src.length = gap + 1 + p := by
    by_contra hne
    exact hsrc
      (taoSection7HoldSourcePrefixListPMF_apply_eq_zero_of_length_ne
        (gap + 1 + p) src hne)
  have hfull_length : full.length = gap + 1 + p := by
    simpa [full] using hsrc_length
  have htail_length : tail.length = p := by
    rw [← htail]
    simp only [List.length_take, List.length_drop]
    rw [Nat.min_eq_left]
    omega
  exact ⟨hfirst, hB, htail_length⟩

/-- Invalid output keys have zero mass in the raw stopped split. -/
theorem lemma79_rawHoldFirstPassageFixedTailSplit_apply_eq_zero_of_invalid
    {start : TaoSection7RenewalPoint} {gap p : ℕ}
    {pre tail : List TaoSection7RenewalPoint}
    (hinvalid :
      ¬ (TaoSection7Lemma710.VerticalFirstPassagePrefix
          start gap pre.length pre ∧
        pre.length ≤ gap + 1 ∧ tail.length = p)) :
    lemma79RawHoldFirstPassageFixedTailSplitPMF (gap + 1 + p) p start gap
        (pre, tail) = 0 := by
  by_contra hne
  exact hinvalid
    (lemma79_rawHoldFirstPassageFixedTailSplit_nonzero_certifies hne)

/-- Invalid stopped prefixes have zero mass in the stopped-prefix marginal. -/
theorem lemma79_rawHoldFirstPassagePrefixPMF_apply_eq_zero_of_invalid
    {start : TaoSection7RenewalPoint} {gap p : ℕ}
    {pre : List TaoSection7RenewalPoint}
    (hinvalid :
      ¬ (TaoSection7Lemma710.VerticalFirstPassagePrefix
          start gap pre.length pre ∧ pre.length ≤ gap + 1)) :
    lemma79RawHoldFirstPassagePrefixPMF p start gap pre = 0 := by
  classical
  by_contra hne
  have hmem :
      pre ∈ (lemma79RawHoldFirstPassagePrefixPMF p start gap).support := hne
  unfold lemma79RawHoldFirstPassagePrefixPMF at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with
    ⟨pair, hpair, hfst⟩
  rcases pair with ⟨pre', tail⟩
  change pre' = pre at hfst
  subst pre'
  have hcert :=
    lemma79_rawHoldFirstPassageFixedTailSplit_nonzero_certifies
      (show
        lemma79RawHoldFirstPassageFixedTailSplitPMF (gap + 1 + p) p start gap
          (pre, tail) ≠ 0 from hpair)
  exact hinvalid ⟨hcert.1, hcert.2.1⟩

/-- The stopped-prefix marginal is independent of the requested fresh-tail length. -/
theorem lemma79_rawHoldFirstPassagePrefixPMF_eq_canonical
    (p : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ) :
    lemma79RawHoldFirstPassagePrefixPMF p start gap =
      lemma77CanonicalFirstPassagePrefixPMF start gap := by
  classical
  apply PMF.ext
  intro pre
  by_cases hpre :
      TaoSection7Lemma710.VerticalFirstPassagePrefix
          start gap pre.length pre ∧
        pre.length ≤ gap + 1
  · rw [lemma79_rawHoldFirstPassagePrefixPMF_apply_of_firstPassage
          hpre.1 hpre.2,
        lemma77CanonicalFirstPassagePrefixPMF_apply_of_firstPassage
          hpre.1 hpre.2]
  · rw [lemma79_rawHoldFirstPassagePrefixPMF_apply_eq_zero_of_invalid hpre,
        lemma77CanonicalFirstPassagePrefixPMF_apply_eq_zero_of_invalid hpre]

/-- Point mass of the independent prefix/fresh-tail bind. -/
theorem lemma79_prefixFreshTail_bind_apply
    {Pre Tail : Type*} (pi : PMF Pre) (tau : PMF Tail)
    (pre : Pre) (tail : Tail) :
    (pi.bind fun pre' => tau.map fun tail' => (pre', tail')) (pre, tail) =
      pi pre * tau tail := by
  classical
  rw [PMF.bind_apply]
  rw [tsum_eq_single pre]
  · rw [PMF.map_apply]
    rw [tsum_eq_single tail]
    · simp
    · intro tail' hne
      have hpair : (pre, tail) ≠ (pre, tail') := by
        intro h
        exact hne (Prod.ext_iff.mp h).2.symm
      simp [hpair]
  · intro pre' hne
    have hmap_zero :
        (tau.map fun tail' => (pre', tail')) (pre, tail) = 0 := by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro tail'
      have hpair : (pre, tail) ≠ (pre', tail') := by
        intro h
        exact hne (Prod.ext_iff.mp h).1.symm
      simp [hpair]
    rw [hmap_zero, mul_zero]

/--
The raw stopped-prefix/fresh-tail law.  The stopped prefix is countable, but
conditional on it the next `p` decoded Hold increments have the common iid
length-`p` law.
-/
theorem lemma79_rawHoldFirstPassageFixedTailSplitPMF_eq_bind
    (p : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ) :
    lemma79RawHoldFirstPassageFixedTailSplitPMF
        (gap + 1 + p) p start gap =
      (lemma79RawHoldFirstPassagePrefixPMF p start gap).bind fun pre =>
        (taoSection7HoldListPMF p).map fun tail => (pre, tail) := by
  classical
  apply PMF.ext
  rintro ⟨pre, tail⟩
  rw [lemma79_prefixFreshTail_bind_apply]
  by_cases hpre :
      TaoSection7Lemma710.VerticalFirstPassagePrefix
          start gap pre.length pre ∧ pre.length ≤ gap + 1
  · by_cases htail : tail.length = p
    · rw [lemma79_rawHoldFirstPassageFixedTailSplit_product_of_le_bound
          hpre.1 htail hpre.2]
      rw [lemma79_rawHoldFirstPassagePrefixPMF_apply_of_firstPassage
          hpre.1 hpre.2]
    · rw [taoSection7HoldListPMF_apply_eq_zero_of_length_ne p tail htail,
          mul_zero]
      exact
        lemma79_rawHoldFirstPassageFixedTailSplit_apply_eq_zero_of_invalid
          (fun hcert => htail hcert.2.2)
  · rw [lemma79_rawHoldFirstPassagePrefixPMF_apply_eq_zero_of_invalid hpre,
        zero_mul]
    exact
      lemma79_rawHoldFirstPassageFixedTailSplit_apply_eq_zero_of_invalid
        (fun hcert => hpre ⟨hcert.1, hcert.2.1⟩)

/-- Native nonnegative expectation for a countable PMF. -/
noncomputable def lemma79PMFENNExpectation
    {Omega : Type*} (mu : PMF Omega) (F : Omega -> ENNReal) : ENNReal :=
  ∑' omega, mu omega * F omega

/-- Native nonnegative expectation transport through an arbitrary PMF map. -/
theorem lemma79PMFENNExpectation_map
    {Omega Xi : Type*} (mu : PMF Omega) (f : Omega -> Xi)
    (G : Xi -> ENNReal) :
    lemma79PMFENNExpectation (mu.map f) G =
      lemma79PMFENNExpectation mu (G ∘ f) := by
  classical
  unfold lemma79PMFENNExpectation
  calc
    (∑' xi, (mu.map f) xi * G xi) =
        ∑' xi, (∑' omega, if xi = f omega then mu omega else 0) * G xi := by
      apply tsum_congr
      intro xi
      rw [PMF.map_apply]
    _ = ∑' xi, ∑' omega,
        (if xi = f omega then mu omega else 0) * G xi := by
      apply tsum_congr
      intro xi
      rw [ENNReal.tsum_mul_right]
    _ = ∑' omega, ∑' xi,
        (if xi = f omega then mu omega else 0) * G xi := by
      rw [ENNReal.tsum_comm]
    _ = ∑' omega, mu omega * G (f omega) := by
      apply tsum_congr
      intro omega
      rw [tsum_eq_single (f omega)]
      · simp
      · intro xi hne
        simp [hne]
    _ = ∑' omega, mu omega * (G ∘ f) omega := by
      rfl

/--
Expand a prefix-weighted expectation under an independent prefix/tail bind.
No finiteness or real-valued summability premise is needed.
-/
theorem lemma79_pmfENNExpectation_bind_pair_prefix_mul
    {Pre Tail : Type*} (pi : PMF Pre) (tau : PMF Tail)
    (prefixWeight : Pre -> ENNReal) (future : Pre -> Tail -> ENNReal) :
    lemma79PMFENNExpectation
        (pi.bind fun pre => tau.map fun tail => (pre, tail))
        (fun pair => prefixWeight pair.1 * future pair.1 pair.2) =
      ∑' pre, pi pre *
        (prefixWeight pre *
          ∑' tail, tau tail * future pre tail) := by
  classical
  unfold lemma79PMFENNExpectation
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro pre
  calc
    (∑' tail,
      (pi.bind fun pre => tau.map fun tail => (pre, tail)) (pre, tail) *
        (prefixWeight pre * future pre tail)) =
        ∑' tail, (pi pre * tau tail) *
          (prefixWeight pre * future pre tail) := by
            apply tsum_congr
            intro tail
            rw [lemma79_prefixFreshTail_bind_apply]
    _ = ∑' tail, pi pre *
        (prefixWeight pre * (tau tail * future pre tail)) := by
          apply tsum_congr
          intro tail
          ac_rfl
    _ = pi pre *
        ∑' tail, prefixWeight pre * (tau tail * future pre tail) := by
          rw [ENNReal.tsum_mul_left]
    _ = pi pre *
        (prefixWeight pre * ∑' tail, tau tail * future pre tail) := by
          rw [ENNReal.tsum_mul_left]

/--
Countable weighted-bind tower inequality.  A uniform bound on every exact
prefix's fresh-tail expectation may be integrated over the countable prefix
marginal without compressing the prefix to a finite key.
-/
theorem lemma79_pmfENNExpectation_bind_pair_prefix_mul_le
    {Pre Tail : Type*} (pi : PMF Pre) (tau : PMF Tail)
    (prefixWeight : Pre -> ENNReal) (future : Pre -> Tail -> ENNReal)
    (C : ENNReal)
    (hfuture :
      ∀ pre, lemma79PMFENNExpectation tau (future pre) ≤ C) :
    lemma79PMFENNExpectation
        (pi.bind fun pre => tau.map fun tail => (pre, tail))
        (fun pair => prefixWeight pair.1 * future pair.1 pair.2) ≤
      lemma79PMFENNExpectation pi (fun pre => prefixWeight pre * C) := by
  rw [lemma79_pmfENNExpectation_bind_pair_prefix_mul]
  unfold lemma79PMFENNExpectation
  apply ENNReal.tsum_le_tsum
  intro pre
  exact mul_le_mul_right
    (mul_le_mul_right (hfuture pre) (prefixWeight pre)) (pi pre)

/-- Pull a constant out of a native nonnegative PMF expectation. -/
theorem lemma79PMFENNExpectation_mul_const
    {Omega : Type*} (mu : PMF Omega) (F : Omega -> ENNReal) (C : ENNReal) :
    lemma79PMFENNExpectation mu (fun omega => F omega * C) =
      lemma79PMFENNExpectation mu F * C := by
  unfold lemma79PMFENNExpectation
  calc
    (∑' omega, mu omega * (F omega * C)) =
        ∑' omega, (mu omega * F omega) * C := by
          apply tsum_congr
          intro omega
          ac_rfl
    _ = (∑' omega, mu omega * F omega) * C :=
      ENNReal.tsum_mul_right

/-- An indicator-one native expectation is exactly PMF outer-measure mass. -/
theorem lemma79PMFENNExpectation_indicator_one_eq_toOuterMeasure
    {Omega : Type*} (mu : PMF Omega) (Event : Set Omega) :
    lemma79PMFENNExpectation mu (Event.indicator fun _ => 1) =
      mu.toOuterMeasure Event := by
  classical
  unfold lemma79PMFENNExpectation
  rw [PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro omega
  by_cases hmem : omega ∈ Event <;>
    simp [Set.indicator, hmem]

/--
Division-free parent-prefix/fresh-future expectation factorization.

The prefix event may contain many exact length-`K` lists.  Its total native
mass multiplies the common future expectation, including uniformly at `K=0`.
-/
theorem lemma79_holdList_prefixEvent_freshFutureExpectation
    (K N : ℕ) (PrefixEvent : Set (List TaoSection7RenewalPoint))
    (future : List TaoSection7RenewalPoint -> ENNReal) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF (K + N))
        (fun full =>
          PrefixEvent.indicator (fun _ => future (full.drop K))
            (full.take K)) =
      lemma79PMFENNExpectation
          (taoSection7HoldListPMF K)
          (PrefixEvent.indicator fun _ => 1) *
        lemma79PMFENNExpectation (taoSection7HoldListPMF N) future := by
  classical
  let weight : List TaoSection7RenewalPoint -> ENNReal :=
    PrefixEvent.indicator fun _ => 1
  let split : List TaoSection7RenewalPoint ->
      List TaoSection7RenewalPoint × List TaoSection7RenewalPoint := fun full =>
    (full.take K, full.drop K)
  calc
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF (K + N))
        (fun full =>
          PrefixEvent.indicator (fun _ => future (full.drop K))
            (full.take K)) =
        lemma79PMFENNExpectation
          (taoSection7HoldListPMF (K + N))
          ((fun pair => weight pair.1 * future pair.2) ∘ split) := by
      apply congrArg
        (lemma79PMFENNExpectation (taoSection7HoldListPMF (K + N)))
      funext full
      by_cases hmem : full.take K ∈ PrefixEvent <;>
        simp [weight, split, Function.comp_apply, Set.indicator, hmem]
    _ = lemma79PMFENNExpectation
        ((taoSection7HoldListPMF (K + N)).map split)
        (fun pair => weight pair.1 * future pair.2) :=
      (lemma79PMFENNExpectation_map
        (taoSection7HoldListPMF (K + N)) split
        (fun pair => weight pair.1 * future pair.2)).symm
    _ = lemma79PMFENNExpectation
        ((taoSection7HoldListPMF K).bind fun pre =>
          (taoSection7HoldListPMF N).map fun tail => (pre, tail))
        (fun pair => weight pair.1 * future pair.2) := by
      rw [taoSection7HoldListPMF_map_take_drop_eq K N]
    _ = ∑' pre, taoSection7HoldListPMF K pre *
        (weight pre *
          ∑' tail, taoSection7HoldListPMF N tail * future tail) := by
      exact lemma79_pmfENNExpectation_bind_pair_prefix_mul
        (taoSection7HoldListPMF K) (taoSection7HoldListPMF N)
        weight (fun _ tail => future tail)
    _ = lemma79PMFENNExpectation
        (taoSection7HoldListPMF K)
        (fun pre => weight pre *
          lemma79PMFENNExpectation (taoSection7HoldListPMF N) future) := by
      rfl
    _ = lemma79PMFENNExpectation (taoSection7HoldListPMF K) weight *
        lemma79PMFENNExpectation (taoSection7HoldListPMF N) future :=
      lemma79PMFENNExpectation_mul_const
        (taoSection7HoldListPMF K) weight
        (lemma79PMFENNExpectation (taoSection7HoldListPMF N) future)
    _ = lemma79PMFENNExpectation
        (taoSection7HoldListPMF K)
        (PrefixEvent.indicator fun _ => 1) *
      lemma79PMFENNExpectation (taoSection7HoldListPMF N) future := by
      rfl

/-- Prefix-event factorization stated directly with unnormalized event mass. -/
theorem lemma79_holdList_prefixEvent_freshFutureExpectation_eq_outerMeasure
    (K N : ℕ) (PrefixEvent : Set (List TaoSection7RenewalPoint))
    (future : List TaoSection7RenewalPoint -> ENNReal) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF (K + N))
        (fun full =>
          PrefixEvent.indicator (fun _ => future (full.drop K))
            (full.take K)) =
      (taoSection7HoldListPMF K).toOuterMeasure PrefixEvent *
        lemma79PMFENNExpectation (taoSection7HoldListPMF N) future := by
  rw [lemma79_holdList_prefixEvent_freshFutureExpectation]
  rw [lemma79PMFENNExpectation_indicator_one_eq_toOuterMeasure]

/-- Countable weighted-bind tower in the scalar-times-prefix form. -/
theorem lemma79_pmfENNExpectation_bind_pair_prefix_mul_le_const_mul
    {Pre Tail : Type*} (pi : PMF Pre) (tau : PMF Tail)
    (prefixWeight : Pre -> ENNReal) (future : Pre -> Tail -> ENNReal)
    (C : ENNReal)
    (hfuture :
      ∀ pre, lemma79PMFENNExpectation tau (future pre) ≤ C) :
    lemma79PMFENNExpectation
        (pi.bind fun pre => tau.map fun tail => (pre, tail))
        (fun pair => prefixWeight pair.1 * future pair.1 pair.2) ≤
      C * lemma79PMFENNExpectation pi prefixWeight := by
  calc
    lemma79PMFENNExpectation
        (pi.bind fun pre => tau.map fun tail => (pre, tail))
        (fun pair => prefixWeight pair.1 * future pair.1 pair.2) ≤
        lemma79PMFENNExpectation pi (fun pre => prefixWeight pre * C) :=
      lemma79_pmfENNExpectation_bind_pair_prefix_mul_le
        pi tau prefixWeight future C hfuture
    _ = lemma79PMFENNExpectation pi prefixWeight * C :=
      lemma79PMFENNExpectation_mul_const pi prefixWeight C
    _ = C * lemma79PMFENNExpectation pi prefixWeight := mul_comm _ _

/--
Source-facing O4 tower for the raw stopped-prefix/fresh-Hold-tail law.
The future kernel may depend on the exact stopped endpoint, and its bound is
assumed uniformly over every endpoint rather than over a finite quotient.
-/
theorem lemma79_rawHoldFirstPassageFixedTailSplit_weightedExpectation_le
    (J : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ)
    (prefixWeight : List TaoSection7RenewalPoint -> ENNReal)
    (future : TaoSection7RenewalPoint ->
      List TaoSection7RenewalPoint -> ENNReal)
    (C : ENNReal)
    (hfuture :
      ∀ endpoint,
        lemma79PMFENNExpectation
          (taoSection7HoldListPMF J) (future endpoint) ≤ C) :
    lemma79PMFENNExpectation
        (lemma79RawHoldFirstPassageFixedTailSplitPMF
          (gap + 1 + J) J start gap)
        (fun pair =>
          prefixWeight pair.1 *
            future
              (taoSection7RenewalPathPoint start pair.1 pair.1.length)
              pair.2) ≤
      C * lemma79PMFENNExpectation
        (lemma79RawHoldFirstPassagePrefixPMF J start gap)
        prefixWeight := by
  rw [lemma79_rawHoldFirstPassageFixedTailSplitPMF_eq_bind]
  exact
    lemma79_pmfENNExpectation_bind_pair_prefix_mul_le_const_mul
      (lemma79RawHoldFirstPassagePrefixPMF J start gap)
      (taoSection7HoldListPMF J) prefixWeight
      (fun pre tail =>
        future (taoSection7RenewalPathPoint start pre pre.length) tail)
      C (fun pre =>
        hfuture (taoSection7RenewalPathPoint start pre pre.length))

/-- Fiber atom of a parent event under an arbitrary key function. -/
def lemma79KeyAtom
    {Omega Key : Type*} (Parent : Set Omega) (key : Omega -> Key) (k : Key) :
    Set Omega :=
  {omega | omega ∈ Parent ∧ key omega = k}

/--
Partition a countable PMF event mass by the fibers of an arbitrary key.
Neither the sample type nor the key type needs a finiteness or countability
instance: only the countable support of the PMF contributes nonzero mass.
-/
theorem lemma79_pmfToOuterMeasure_partition_of_key
    {Omega Key : Type*} (mu : PMF Omega)
    (Parent : Set Omega) (key : Omega -> Key) :
    mu.toOuterMeasure Parent =
      ∑' k, mu.toOuterMeasure (lemma79KeyAtom Parent key k) := by
  classical
  rw [PMF.toOuterMeasure_apply]
  calc
    (∑' omega, Parent.indicator mu omega) =
        ∑' omega, ∑' k,
          (lemma79KeyAtom Parent key k).indicator mu omega := by
      apply tsum_congr
      intro omega
      by_cases hParent : omega ∈ Parent
      · rw [tsum_eq_single (key omega)]
        · simp [lemma79KeyAtom, hParent]
        · intro k hne
          have hkey_ne : key omega ≠ k := fun h => hne h.symm
          simp [lemma79KeyAtom, hParent, hkey_ne]
      · simp [lemma79KeyAtom, hParent]
    _ = ∑' k, ∑' omega,
        (lemma79KeyAtom Parent key k).indicator mu omega := by
      rw [ENNReal.tsum_comm]
    _ = ∑' k, mu.toOuterMeasure (lemma79KeyAtom Parent key k) := by
      apply tsum_congr
      intro k
      rw [PMF.toOuterMeasure_apply]

/-- Restricting the parent event restricts every key fiber. -/
theorem lemma79KeyAtom_inter
    {Omega Key : Type*} (Parent Exit : Set Omega)
    (key : Omega -> Key) (k : Key) :
    lemma79KeyAtom (Parent ∩ Exit) key k =
      lemma79KeyAtom Parent key k ∩ Exit := by
  ext omega
  simp [lemma79KeyAtom, and_comm, and_left_comm, and_assoc]

/--
Countable O5 aggregation algebra.  Unnormalized exit contractions on every
key fiber sum to the corresponding contraction on the whole parent event.
-/
theorem lemma79_pmfToOuterMeasure_exitContraction_of_key
    {Omega Key : Type*} (mu : PMF Omega)
    (Parent Exit : Set Omega) (key : Omega -> Key) (c0 : ENNReal)
    (hlocal :
      ∀ k,
        c0 * mu.toOuterMeasure (lemma79KeyAtom Parent key k) ≤
          mu.toOuterMeasure (lemma79KeyAtom Parent key k ∩ Exit)) :
    c0 * mu.toOuterMeasure Parent ≤
      mu.toOuterMeasure (Parent ∩ Exit) := by
  calc
    c0 * mu.toOuterMeasure Parent =
        c0 * ∑' k, mu.toOuterMeasure (lemma79KeyAtom Parent key k) := by
      rw [lemma79_pmfToOuterMeasure_partition_of_key]
    _ = ∑' k,
        c0 * mu.toOuterMeasure (lemma79KeyAtom Parent key k) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' k,
        mu.toOuterMeasure (lemma79KeyAtom Parent key k ∩ Exit) :=
      ENNReal.tsum_le_tsum hlocal
    _ = ∑' k,
        mu.toOuterMeasure (lemma79KeyAtom (Parent ∩ Exit) key k) := by
      apply tsum_congr
      intro k
      rw [lemma79KeyAtom_inter]
    _ = mu.toOuterMeasure (Parent ∩ Exit) :=
      (lemma79_pmfToOuterMeasure_partition_of_key
        mu (Parent ∩ Exit) key).symm

theorem lemma79_stoppedSplitSourceLaw_of_sourceFiberLaw
    {Src Omega Pre Tail : Type*} [Fintype Src]
    {rho : PMF Src}
    {mu : PMF Omega}
    {nu : PMF (Pre × Tail)}
    {splitOf : Src -> Pre × Tail}
    {sampleSrc : Src -> Omega}
    {sampleOf : Pre × Tail -> Omega}
    (hmu_source :
      ∀ omega,
        (mu omega).toReal =
          pmfProb rho {src | sampleSrc src = omega})
    (hnu : nu = rho.map splitOf)
    (hcompat : ∀ src, sampleSrc src = sampleOf (splitOf src)) :
    Lemma79StoppedSplitSourceLaw
      rho mu nu splitOf sampleSrc sampleOf
    where
  source_law :=
    pmf_eq_map_of_fiber_prob_toReal
      (p := rho) (q := mu) (f := sampleSrc) hmu_source
  split_law := hnu
  sample_compat := hcompat

theorem lemma79_pairMass_of_stoppedSplitSourceLaw
    {Src Omega Pre Tail : Type*} [Fintype Src]
    {rho : PMF Src}
    {mu : PMF Omega}
    {nu : PMF (Pre × Tail)}
    {splitOf : Src -> Pre × Tail}
    {sampleSrc : Src -> Omega}
    {sampleOf : Pre × Tail -> Omega}
    (hsrc :
      Lemma79StoppedSplitSourceLaw
        rho mu nu splitOf sampleSrc sampleOf) :
    ∀ sigma : Pre × Tail,
      (nu sigma).toReal =
        pmfProb rho {src | splitOf src = sigma} := by
  intro sigma
  rw [hsrc.split_law]
  exact (pmfProb_singleton_eq_map_apply_toReal rho splitOf sigma).symm

/--
Derive the expanded stopped-split Hold fiber formula from exact source
split-cylinder masses.

This is the finite partition step behind the sampled-law field: the source
fiber of `omega` is partitioned by the stopped split key `splitOf`, and each
split cylinder has the advertised Hold-list mass.
-/
theorem lemma79_stoppedSplitHoldFiberMass_of_sourceSplitCylinderMass
    {Src Omega Pre Tail : Type*} [Fintype Src] [Fintype Pre] [Fintype Tail]
    [DecidableEq Omega]
    {rho : PMF Src}
    {mu : PMF Omega}
    {K : Pre -> ℕ} {p : ℕ}
    {preList : Pre -> List TaoSection7RenewalPoint}
    {tailList : Tail -> List TaoSection7RenewalPoint}
    {splitOf : Src -> Pre × Tail}
    {sampleSrc : Src -> Omega}
    {sampleOf : Pre × Tail -> Omega}
    (hmu_source :
      ∀ omega,
        (mu omega).toReal =
          pmfProb rho {src | sampleSrc src = omega})
    (hcompat : ∀ src, sampleSrc src = sampleOf (splitOf src))
    (hsplit_mass :
      ∀ sigma : Pre × Tail,
        pmfProb rho {src | splitOf src = sigma} =
          (taoSection7HoldListPMF (K sigma.1 + p)
            (preList sigma.1 ++ tailList sigma.2)).toReal) :
    ∀ omega,
      (mu omega).toReal =
        ∑ sigma : Pre × Tail,
          if sampleOf sigma = omega then
            (taoSection7HoldListPMF (K sigma.1 + p)
              (preList sigma.1 ++ tailList sigma.2)).toReal
          else 0 := by
  classical
  intro omega
  let Parent : Set Src := {src | sampleSrc src = omega}
  let atom : Pre × Tail -> Set Src :=
    fun sigma => {src | sampleSrc src = omega ∧ splitOf src = sigma}
  have hpartition :
      pmfProb rho Parent = ∑ sigma, pmfProb rho (atom sigma) := by
    exact
      pmfProb_partition_of_key
        (mu := rho) (Parent := Parent) (atom := atom)
        (key := splitOf)
        (hkey_mem := by
          intro src hsrc
          exact ⟨hsrc, rfl⟩)
        (hatom_key := by
          intro sigma src hsrc
          exact ⟨hsrc.1, hsrc.2⟩)
  calc
    (mu omega).toReal = pmfProb rho Parent := hmu_source omega
    _ = ∑ sigma, pmfProb rho (atom sigma) := hpartition
    _ =
        ∑ sigma : Pre × Tail,
          if sampleOf sigma = omega then
            (taoSection7HoldListPMF (K sigma.1 + p)
              (preList sigma.1 ++ tailList sigma.2)).toReal
          else 0 := by
          refine Finset.sum_congr rfl ?_
          intro sigma _hsigma
          by_cases hsigma_omega : sampleOf sigma = omega
          · have hatom_eq :
                atom sigma = {src | splitOf src = sigma} := by
              ext src
              constructor
              · intro hsrc
                exact hsrc.2
              · intro hsrc
                exact ⟨by rw [hcompat src, hsrc, hsigma_omega], hsrc⟩
            simp [atom, hsigma_omega, hatom_eq, hsplit_mass sigma]
          · have hatom_empty : atom sigma = ∅ := by
              ext src
              constructor
              · intro hsrc
                have hsample : sampleOf sigma = omega := by
                  have hc := hcompat src
                  rw [hsrc.2] at hc
                  exact hc.symm.trans hsrc.1
                exact False.elim (hsigma_omega hsample)
              · intro hsrc
                cases hsrc
            simp [atom, hsigma_omega, hatom_empty, pmfProb_empty]

/--
Convert an expanded finite Hold-list stopped-split fiber mass into
`sample_law`.

This is still algebra below the real stopped/Hold source theorem: `hmu_fiber`
is the unproved global mass formula for the sampled process, and `hnu`
identifies the same global source PMF `nu` with the finite stopped prefix plus
raw tail carrier.
-/
theorem lemma79_sampleLaw_of_stoppedSplitHoldFiberMass
    {Omega Pre Tail : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype Pre] [Fintype Tail]
    {mu : PMF Omega}
    {nu : PMF (Pre × Tail)}
    {K : Pre -> ℕ} {p : ℕ}
    {preList : Pre -> List TaoSection7RenewalPoint}
    {tailList : Tail -> List TaoSection7RenewalPoint}
    {sampleOf : Pre × Tail -> Omega}
    (hmu_fiber :
      ∀ omega,
        (mu omega).toReal =
          ∑ sigma : Pre × Tail,
            if sampleOf sigma = omega then
              (taoSection7HoldListPMF (K sigma.1 + p)
                (preList sigma.1 ++ tailList sigma.2)).toReal
            else 0)
    (hnu :
      ∀ pre tail,
        (nu (pre, tail)).toReal =
          (taoSection7HoldListPMF (K pre + p)
            (preList pre ++ tailList tail)).toReal) :
    mu = nu.map sampleOf := by
  classical
  refine lemma79_sampleLaw_of_stoppedSplitFiberProb ?_
  intro omega
  calc
    (mu omega).toReal =
        ∑ sigma : Pre × Tail,
          if sampleOf sigma = omega then
            (taoSection7HoldListPMF (K sigma.1 + p)
              (preList sigma.1 ++ tailList sigma.2)).toReal
          else 0 := hmu_fiber omega
    _ = pmfProb nu {sigma | sampleOf sigma = omega} := by
          unfold pmfProb
          refine Finset.sum_congr rfl ?_
          rintro ⟨pre, tail⟩ _hsigma
          by_cases hs : sampleOf (pre, tail) = omega
          · simp [hs, hnu pre tail]
          · simp [hs]

/--
Expanded Hold-list sampled law using the existing source product-law field.

Compared with `lemma79_sampleLaw_of_stoppedSplitHoldFiberMass`, this removes
the separate pointwise `hnu` premise: pair masses are recovered from the
already-required `Lemma79SourcePrefixTailProductLaw` field and then identified
with finite Hold append masses.
-/
theorem lemma79_sampleLaw_of_stoppedSplitHoldFiberMass_of_sourceProduct
    {Omega Pre Tail : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype Pre] [Fintype Tail]
    {mu : PMF Omega}
    {nu : PMF (Pre × Tail)}
    {K : Pre -> ℕ} {p : ℕ}
    {preList : Pre -> List TaoSection7RenewalPoint}
    {tailList : Tail -> List TaoSection7RenewalPoint}
    {sampleOf : Pre × Tail -> Omega}
    {prefixMass : Pre -> ℝ}
    {nuTail : PMF Tail}
    (hmu_fiber :
      ∀ omega,
        (mu omega).toReal =
          ∑ sigma : Pre × Tail,
            if sampleOf sigma = omega then
              (taoSection7HoldListPMF (K sigma.1 + p)
                (preList sigma.1 ++ tailList sigma.2)).toReal
            else 0)
    (hsource_product :
      Lemma79SourcePrefixTailProductLaw
        nu Prod.fst Prod.snd prefixMass nuTail)
    (hpre_len : ∀ pre, (preList pre).length = K pre)
    (htail_len : ∀ tail, (tailList tail).length = p)
    (hprefixMass :
      ∀ pre,
        prefixMass pre =
          (taoSection7HoldListPMF (K pre) (preList pre)).toReal)
    (hnuTail :
      ∀ tail,
        (nuTail tail).toReal =
          (taoSection7HoldListPMF p (tailList tail)).toReal) :
    mu = nu.map sampleOf := by
  refine
    lemma79_sampleLaw_of_stoppedSplitHoldFiberMass
      (mu := mu) (nu := nu) (K := K) (p := p)
      (preList := preList) (tailList := tailList)
      (sampleOf := sampleOf) hmu_fiber ?_
  intro pre tail
  rw [lemma79_pairMass_of_sourcePrefixTailProductLaw
    (nu := nu) (prefixMass := prefixMass) (nuTail := nuTail)
    hsource_product pre tail]
  rw [hprefixMass pre, hnuTail tail]
  exact
    (taoSection7HoldListPMF_append_toReal_of_lengths
      (hpre_len pre) (htail_len tail)).symm

/--
Sampled law from a common source carrier, exact split-cylinder masses, and the
source product-law field.

This is the source-facing version of the sampled-law socket: it removes the
expanded `hmu_fiber` premise by deriving it from the ambient source law
`mu = rho.map sampleSrc`, split compatibility, and exact stopped split-cylinder
masses.
-/
theorem lemma79_sampleLaw_of_sourceSplitCylinderMass_and_sourceProduct
    {Src Omega Pre Tail : Type*} [Fintype Src] [Fintype Omega]
    [DecidableEq Omega] [Fintype Pre] [Fintype Tail]
    {rho : PMF Src}
    {mu : PMF Omega}
    {nu : PMF (Pre × Tail)}
    {K : Pre -> ℕ} {p : ℕ}
    {preList : Pre -> List TaoSection7RenewalPoint}
    {tailList : Tail -> List TaoSection7RenewalPoint}
    {splitOf : Src -> Pre × Tail}
    {sampleSrc : Src -> Omega}
    {sampleOf : Pre × Tail -> Omega}
    {prefixMass : Pre -> ℝ}
    {nuTail : PMF Tail}
    (hmu_source :
      ∀ omega,
        (mu omega).toReal =
          pmfProb rho {src | sampleSrc src = omega})
    (hcompat : ∀ src, sampleSrc src = sampleOf (splitOf src))
    (hsplit_mass :
      ∀ sigma : Pre × Tail,
        pmfProb rho {src | splitOf src = sigma} =
          (taoSection7HoldListPMF (K sigma.1 + p)
            (preList sigma.1 ++ tailList sigma.2)).toReal)
    (hsource_product :
      Lemma79SourcePrefixTailProductLaw
        nu Prod.fst Prod.snd prefixMass nuTail)
    (hpre_len : ∀ pre, (preList pre).length = K pre)
    (htail_len : ∀ tail, (tailList tail).length = p)
    (hprefixMass :
      ∀ pre,
        prefixMass pre =
          (taoSection7HoldListPMF (K pre) (preList pre)).toReal)
    (hnuTail :
      ∀ tail,
        (nuTail tail).toReal =
          (taoSection7HoldListPMF p (tailList tail)).toReal) :
    mu = nu.map sampleOf := by
  refine
    lemma79_sampleLaw_of_stoppedSplitHoldFiberMass_of_sourceProduct
      (mu := mu) (nu := nu) (K := K) (p := p)
      (preList := preList) (tailList := tailList)
      (sampleOf := sampleOf) ?_
      (hsource_product := hsource_product)
      (hpre_len := hpre_len) (htail_len := htail_len)
      (hprefixMass := hprefixMass) (hnuTail := hnuTail)
  exact
    lemma79_stoppedSplitHoldFiberMass_of_sourceSplitCylinderMass
      (rho := rho) (mu := mu) (K := K) (p := p)
      (preList := preList) (tailList := tailList)
      (splitOf := splitOf) (sampleSrc := sampleSrc)
      (sampleOf := sampleOf) hmu_source hcompat hsplit_mass

theorem lemma79_sourcePrefixTailProductLaw_of_stoppedSplitSourceLaw
    {Src Omega Pre Tail : Type*} [Fintype Src] [Fintype Pre] [Fintype Tail]
    {rho : PMF Src}
    {mu : PMF Omega}
    {nu : PMF (Pre × Tail)}
    {K : Pre -> ℕ} {p : ℕ}
    {preList : Pre -> List TaoSection7RenewalPoint}
    {tailList : Tail -> List TaoSection7RenewalPoint}
    {splitOf : Src -> Pre × Tail}
    {sampleSrc : Src -> Omega}
    {sampleOf : Pre × Tail -> Omega}
    {prefixMass : Pre -> ℝ}
    {nuTail : PMF Tail}
    (hsrc :
      Lemma79StoppedSplitSourceLaw
        rho mu nu splitOf sampleSrc sampleOf)
    (hsplit_mass :
      ∀ sigma : Pre × Tail,
        pmfProb rho {src | splitOf src = sigma} =
          (taoSection7HoldListPMF (K sigma.1 + p)
            (preList sigma.1 ++ tailList sigma.2)).toReal)
    (hpre_len : ∀ pre, (preList pre).length = K pre)
    (htail_len : ∀ tail, (tailList tail).length = p)
    (hprefixMass :
      ∀ pre,
        prefixMass pre =
          (taoSection7HoldListPMF (K pre) (preList pre)).toReal)
    (hnuTail :
      ∀ tail,
        (nuTail tail).toReal =
          (taoSection7HoldListPMF p (tailList tail)).toReal) :
    Lemma79SourcePrefixTailProductLaw
      nu Prod.fst Prod.snd prefixMass nuTail := by
  refine lemma79_sourcePrefixTailProductLaw_of_pairProductMass ?_
  intro pre tail
  calc
    (nu (pre, tail)).toReal =
        pmfProb rho {src | splitOf src = (pre, tail)} :=
          lemma79_pairMass_of_stoppedSplitSourceLaw
            (rho := rho) (mu := mu) (nu := nu)
            (splitOf := splitOf) (sampleSrc := sampleSrc)
            (sampleOf := sampleOf) hsrc (pre, tail)
    _ =
        (taoSection7HoldListPMF (K pre + p)
          (preList pre ++ tailList tail)).toReal := by
          exact hsplit_mass (pre, tail)
    _ = prefixMass pre * (nuTail tail).toReal := by
          rw [hprefixMass pre, hnuTail tail]
          exact taoSection7HoldListPMF_append_toReal_of_lengths
            (hpre_len pre) (htail_len tail)

/--
Per-fixed-prefix observable product source for the Lemma 7.9 tail-fiber law.

This packages exactly the source-side data needed to feed
`lemma79_fixedPrefixTailFiberLaw_of_sourceTailKey`: a finite source carrier, a
sampled PMF law, an atom/prefix-key pullback, a tail-key compatibility law, and
a finite prefix/tail product law.  It is still an observable prefix-tower
socket; it does not construct the realized stopped/Hold product carrier.
-/
structure Lemma79FixedPrefixObservableProductSource
    {Omega OmegaSrc Prefix Tail : Type*} [Fintype Omega] [Fintype OmegaSrc]
    [Fintype Prefix] [Fintype Tail]
    (mu : PMF Omega)
    (AtomA : Set Omega)
    (tailOf : Omega -> Tail)
    (nuTail : PMF Tail) : Type _ where
  nu : PMF OmegaSrc
  sampleOf : OmegaSrc -> Omega
  prefixOf : OmegaSrc -> Prefix
  tailKey : OmegaSrc -> Tail
  prefixMass : Prefix -> ℝ
  prefixOK : Prefix -> Prop
  source_product :
    Lemma79SourcePrefixTailProductLaw
      nu prefixOf tailKey prefixMass nuTail
  sample_law : mu = nu.map sampleOf
  atom_pullback :
    ∀ sigma, sampleOf sigma ∈ AtomA ↔ prefixOK (prefixOf sigma)
  tail_compat :
    ∀ sigma, sampleOf sigma ∈ AtomA ->
      tailOf (sampleOf sigma) = tailKey sigma

def lemma79_fixedPrefixObservableProductSource_of_stoppedSplitSourceLaw
    {Src Omega Pre Tail : Type*} [Fintype Src] [Fintype Omega]
    [Fintype Pre] [Fintype Tail]
    {rho : PMF Src}
    {mu : PMF Omega}
    {nu : PMF (Pre × Tail)}
    {AtomA : Set Omega}
    {tailOf : Omega -> Tail}
    {nuTail : PMF Tail}
    {K : Pre -> ℕ} {p : ℕ}
    {preList : Pre -> List TaoSection7RenewalPoint}
    {tailList : Tail -> List TaoSection7RenewalPoint}
    {splitOf : Src -> Pre × Tail}
    {sampleSrc : Src -> Omega}
    {sampleOf : Pre × Tail -> Omega}
    {prefixMass : Pre -> ℝ}
    {prefixOK : Pre -> Prop}
    (hsrc :
      Lemma79StoppedSplitSourceLaw
        rho mu nu splitOf sampleSrc sampleOf)
    (hsplit_mass :
      ∀ sigma : Pre × Tail,
        pmfProb rho {src | splitOf src = sigma} =
          (taoSection7HoldListPMF (K sigma.1 + p)
            (preList sigma.1 ++ tailList sigma.2)).toReal)
    (hpre_len : ∀ pre, (preList pre).length = K pre)
    (htail_len : ∀ tail, (tailList tail).length = p)
    (hprefixMass :
      ∀ pre,
        prefixMass pre =
          (taoSection7HoldListPMF (K pre) (preList pre)).toReal)
    (hnuTail :
      ∀ tail,
        (nuTail tail).toReal =
          (taoSection7HoldListPMF p (tailList tail)).toReal)
    (hatom :
      ∀ sigma : Pre × Tail,
        sampleOf sigma ∈ AtomA ↔ prefixOK sigma.1)
    (htail :
      ∀ sigma : Pre × Tail,
        sampleOf sigma ∈ AtomA ->
          tailOf (sampleOf sigma) = sigma.2) :
    Lemma79FixedPrefixObservableProductSource
      (OmegaSrc := Pre × Tail) (Prefix := Pre)
      mu AtomA tailOf nuTail
    where
  nu := nu
  sampleOf := sampleOf
  prefixOf := Prod.fst
  tailKey := Prod.snd
  prefixMass := prefixMass
  prefixOK := prefixOK
  source_product :=
    lemma79_sourcePrefixTailProductLaw_of_stoppedSplitSourceLaw
      (rho := rho) (mu := mu) (nu := nu) (K := K) (p := p)
      (preList := preList) (tailList := tailList)
      (splitOf := splitOf) (sampleSrc := sampleSrc)
      (sampleOf := sampleOf) (prefixMass := prefixMass)
      (nuTail := nuTail) hsrc hsplit_mass
      hpre_len htail_len hprefixMass hnuTail
  sample_law := hsrc.sample_law
  atom_pullback := by
    intro sigma
    exact hatom sigma
  tail_compat := by
    intro sigma hmem
    exact htail sigma hmem

theorem lemma79_fixedPrefixTailFiberLaw_of_observableProductSource
    {Omega OmegaSrc Prefix Tail : Type*} [Fintype Omega] [Fintype OmegaSrc]
    [Fintype Prefix] [Fintype Tail]
    {mu : PMF Omega}
    {AtomA : Set Omega}
    {tailOf : Omega -> Tail}
    {nuTail : PMF Tail}
    (hsrc :
      Lemma79FixedPrefixObservableProductSource
        (OmegaSrc := OmegaSrc) (Prefix := Prefix)
        mu AtomA tailOf nuTail) :
    Lemma79FixedPrefixTailFiberLaw mu AtomA tailOf nuTail := by
  classical
  exact
    lemma79_fixedPrefixTailFiberLaw_of_sourceTailKey
      (nu := hsrc.nu) (sampleOf := hsrc.sampleOf)
      (tailKey := hsrc.tailKey)
      hsrc.sample_law hsrc.tail_compat
      (lemma79_sourceTailKeyLaw_of_prefixTailProductLaw_and_atomPullback
        (nu := hsrc.nu) (sampleOf := hsrc.sampleOf) (AtomA := AtomA)
        (prefixOf := hsrc.prefixOf) (tailKey := hsrc.tailKey)
        (prefixMass := hsrc.prefixMass) (nuTail := nuTail)
        (prefixOK := hsrc.prefixOK)
        hsrc.source_product hsrc.atom_pullback)

theorem lemma79_fixedPrefixFreshTailExpectationLaw_of_tailFiberLaw
    {Omega Tail : Type*} [Fintype Omega] [Fintype Tail]
    {mu : PMF Omega}
    {AtomA : Set Omega}
    {tailOf : Omega -> Tail}
    {nuTail : PMF Tail}
    (hfiber : Lemma79FixedPrefixTailFiberLaw mu AtomA tailOf nuTail) :
    Lemma79FixedPrefixFreshTailExpectationLaw mu AtomA tailOf nuTail := by
  refine ⟨?_⟩
  intro F
  calc
    pmfExpectation mu (atomIndicator AtomA (fun omega => F (tailOf omega)))
        =
      ∑ tail,
        F tail * pmfProb mu {omega | omega ∈ AtomA ∧ tailOf omega = tail} :=
        pmfExpectation_atomIndicator_tail_eq_sum_fibers mu AtomA tailOf F
    _ = ∑ tail, F tail * (pmfProb mu AtomA * (nuTail tail).toReal) := by
          refine Finset.sum_congr rfl ?_
          intro tail _htail_mem
          rw [hfiber.tail_fiber_law tail]
    _ = pmfProb mu AtomA * pmfExpectation nuTail F := by
          unfold pmfExpectation
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro tail _htail_mem
          ring

theorem lemma79_fixedPrefixFreshTailExpectationLaw_family_of_tailFiberLaw
    {Omega kappa Tail : Type*} [Fintype Omega] [Fintype kappa]
    [Fintype Tail]
    {mu : PMF Omega}
    {prefixAtom : kappa -> Set Omega}
    {tailOf : kappa -> Omega -> Tail}
    {nuTail : kappa -> PMF Tail}
    (hfiber :
      ∀ a,
        Lemma79FixedPrefixTailFiberLaw
          mu (prefixAtom a) (tailOf a) (nuTail a)) :
    ∀ a,
      Lemma79FixedPrefixFreshTailExpectationLaw
        mu (prefixAtom a) (tailOf a) (nuTail a) := by
  intro a
  exact lemma79_fixedPrefixFreshTailExpectationLaw_of_tailFiberLaw (hfiber a)

theorem lemma79_prefix_tower_of_fixedPrefixFreshTailExpectationLaw
    {Omega Tail : Type*} [Fintype Omega] [Fintype Tail]
    {mu : PMF Omega}
    {AtomA ExitWhite : Set Omega}
    {tailOf : Omega -> Tail}
    {nuTail : PMF Tail}
    {futureMoment prefixFuture : Omega -> ℝ}
    {prefixWeight : ℝ}
    {tailFuture : Tail -> ℝ}
    (hfresh :
      Lemma79FixedPrefixFreshTailExpectationLaw mu AtomA tailOf nuTail)
    (hfuture :
      ∀ omega, omega ∈ AtomA ->
        exitWhiteWeight ExitWhite omega * futureMoment omega =
          prefixWeight * tailFuture (tailOf omega))
    (hprefixFuture :
      ∀ omega, omega ∈ AtomA ->
        prefixFuture omega =
          prefixWeight * pmfExpectation nuTail tailFuture) :
    pmfExpectation mu (atomIndicator AtomA
      (fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega)) =
      pmfExpectation mu (atomIndicator AtomA prefixFuture) := by
  classical
  have hleft :
      pmfExpectation mu (atomIndicator AtomA
        (fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega)) =
        pmfExpectation mu (atomIndicator AtomA
          (fun omega => prefixWeight * tailFuture (tailOf omega))) := by
    unfold pmfExpectation atomIndicator
    refine Finset.sum_congr rfl ?_
    intro omega _homega
    by_cases hmem : omega ∈ AtomA
    · simp [hmem, hfuture omega hmem]
    · simp [hmem]
  have htail_const :
      pmfExpectation nuTail (fun tail => prefixWeight * tailFuture tail) =
        prefixWeight * pmfExpectation nuTail tailFuture :=
    pmfExpectation_const_mul nuTail prefixWeight tailFuture
  have hleft_value :
      pmfExpectation mu (atomIndicator AtomA
        (fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega)) =
        pmfProb mu AtomA *
          (prefixWeight * pmfExpectation nuTail tailFuture) := by
    calc
      pmfExpectation mu (atomIndicator AtomA
          (fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega))
          =
        pmfExpectation mu (atomIndicator AtomA
          (fun omega => prefixWeight * tailFuture (tailOf omega))) :=
            hleft
      _ = pmfProb mu AtomA *
            pmfExpectation nuTail (fun tail => prefixWeight * tailFuture tail) :=
            hfresh.expectation_law
              (fun tail => prefixWeight * tailFuture tail)
      _ = pmfProb mu AtomA *
            (prefixWeight * pmfExpectation nuTail tailFuture) := by
            rw [htail_const]
  have hright :
      pmfExpectation mu (atomIndicator AtomA prefixFuture) =
        pmfExpectation mu (atomIndicator AtomA
          (fun _ => prefixWeight * pmfExpectation nuTail tailFuture)) := by
    unfold pmfExpectation atomIndicator
    refine Finset.sum_congr rfl ?_
    intro omega _homega
    by_cases hmem : omega ∈ AtomA
    · rw [if_pos hmem, if_pos hmem, hprefixFuture omega hmem]
      rfl
    · simp [hmem]
  have hright_value :
      pmfExpectation mu (atomIndicator AtomA prefixFuture) =
        prefixWeight * pmfExpectation nuTail tailFuture *
          pmfProb mu AtomA := by
    calc
      pmfExpectation mu (atomIndicator AtomA prefixFuture)
          =
        pmfExpectation mu (atomIndicator AtomA
          (fun _ => prefixWeight * pmfExpectation nuTail tailFuture)) :=
            hright
      _ = (prefixWeight * pmfExpectation nuTail tailFuture) *
            pmfProb mu AtomA :=
            pmfExpectation_atomIndicator_const
              mu AtomA (prefixWeight * pmfExpectation nuTail tailFuture)
  rw [hleft_value, hright_value]
  ring

theorem lemma79_prefixTower_family_of_fixedPrefixFreshTailExpectationLaw
    {Omega kappa Tail : Type*} [Fintype Omega] [Fintype kappa]
    [Fintype Tail]
    {mu : PMF Omega}
    {prefixAtom : kappa -> Set Omega}
    {ExitWhite : Set Omega}
    {tailOf : kappa -> Omega -> Tail}
    {nuTail : kappa -> PMF Tail}
    {futureMoment : Omega -> ℝ}
    {prefixFuture : kappa -> Omega -> ℝ}
    {prefixWeight : kappa -> ℝ}
    {tailFuture : kappa -> Tail -> ℝ}
    (hfresh :
      ∀ a,
        Lemma79FixedPrefixFreshTailExpectationLaw
          mu (prefixAtom a) (tailOf a) (nuTail a))
    (hfuture :
      ∀ a omega, omega ∈ prefixAtom a ->
        exitWhiteWeight ExitWhite omega * futureMoment omega =
          prefixWeight a * tailFuture a (tailOf a omega))
    (hprefixFuture :
      ∀ a omega, omega ∈ prefixAtom a ->
        prefixFuture a omega =
          prefixWeight a * pmfExpectation (nuTail a) (tailFuture a)) :
    ∀ a,
      pmfExpectation mu (atomIndicator (prefixAtom a)
        (fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega)) =
        pmfExpectation mu (atomIndicator (prefixAtom a) (prefixFuture a)) := by
  intro a
  exact lemma79_prefix_tower_of_fixedPrefixFreshTailExpectationLaw
    (mu := mu) (AtomA := prefixAtom a) (ExitWhite := ExitWhite)
    (tailOf := tailOf a) (nuTail := nuTail a)
    (futureMoment := futureMoment) (prefixFuture := prefixFuture a)
    (prefixWeight := prefixWeight a) (tailFuture := tailFuture a)
    (hfresh a) (hfuture a) (hprefixFuture a)

/--
Finite observable tail carrier for the `prefix_tower` sub-obligation.

This record intentionally has narrow scope: `Tail` is a finite observable
only for the fixed-prefix tower integrand.  It packages the finite tail-fiber
mass law and the two pointwise identifications needed to derive the
`prefix_tower` equality.  It is not a reusable post-stopped continuation law
for later stopped-tail event consumers.
-/
structure Lemma79PrefixTowerObservableTailFiberCarrier
    {Omega kappa Tail : Type*} [Fintype Omega] [Fintype kappa]
    [Fintype Tail]
    (mu : PMF Omega)
    (prefixAtom : kappa -> Set Omega)
    (ExitWhite : Set Omega)
    (tailOf : kappa -> Omega -> Tail)
    (nuTail : kappa -> PMF Tail)
    (futureMoment : Omega -> ℝ)
    (prefixFuture : kappa -> Omega -> ℝ)
    (prefixWeight : kappa -> ℝ)
    (tailFuture : kappa -> Tail -> ℝ) : Prop where
  tail_fiber :
    ∀ a,
      Lemma79FixedPrefixTailFiberLaw
        mu (prefixAtom a) (tailOf a) (nuTail a)
  future_on_prefix :
    ∀ a omega, omega ∈ prefixAtom a ->
      exitWhiteWeight ExitWhite omega * futureMoment omega =
        prefixWeight a * tailFuture a (tailOf a omega)
  prefix_future_on_prefix :
    ∀ a omega, omega ∈ prefixAtom a ->
      prefixFuture a omega =
        prefixWeight a * pmfExpectation (nuTail a) (tailFuture a)

theorem Lemma79PrefixTowerObservableTailFiberCarrier.prefix_tower
    {Omega kappa Tail : Type*} [Fintype Omega] [Fintype kappa]
    [Fintype Tail]
    {mu : PMF Omega}
    {prefixAtom : kappa -> Set Omega}
    {ExitWhite : Set Omega}
    {tailOf : kappa -> Omega -> Tail}
    {nuTail : kappa -> PMF Tail}
    {futureMoment : Omega -> ℝ}
    {prefixFuture : kappa -> Omega -> ℝ}
    {prefixWeight : kappa -> ℝ}
    {tailFuture : kappa -> Tail -> ℝ}
    (hobs :
      Lemma79PrefixTowerObservableTailFiberCarrier
        mu prefixAtom ExitWhite tailOf nuTail futureMoment prefixFuture
        prefixWeight tailFuture) :
    ∀ a,
      pmfExpectation mu (atomIndicator (prefixAtom a)
        (fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega)) =
        pmfExpectation mu (atomIndicator (prefixAtom a) (prefixFuture a)) :=
  lemma79_prefixTower_family_of_fixedPrefixFreshTailExpectationLaw
    (mu := mu) (prefixAtom := prefixAtom) (ExitWhite := ExitWhite)
    (tailOf := tailOf) (nuTail := nuTail) (futureMoment := futureMoment)
    (prefixFuture := prefixFuture) (prefixWeight := prefixWeight)
    (tailFuture := tailFuture)
    (lemma79_fixedPrefixFreshTailExpectationLaw_family_of_tailFiberLaw
      hobs.tail_fiber)
    hobs.future_on_prefix hobs.prefix_future_on_prefix

theorem lemma79_future_factor_le_of_tailIH
    {Omega kappa Tail : Type*} [Fintype Omega] [Fintype kappa]
    [Fintype Tail]
    {mu : PMF Omega}
    {prefixAtom : kappa -> Set Omega}
    {ExitWhite : Set Omega}
    {tailOf : kappa -> Omega -> Tail}
    {nuTail : kappa -> PMF Tail}
    {futureMoment : Omega -> ℝ}
    {prefixFuture prefixFactor : kappa -> Omega -> ℝ}
    {prefixWeight : kappa -> ℝ}
    {tailFuture : kappa -> Tail -> ℝ}
    {epsilon : ℝ}
    (hobs :
      Lemma79PrefixTowerObservableTailFiberCarrier
        mu prefixAtom ExitWhite tailOf nuTail futureMoment prefixFuture
        prefixWeight tailFuture)
    (tail_ih :
      ∀ a, pmfExpectation (nuTail a) (tailFuture a) ≤ Real.exp epsilon)
    (prefixFactor_eq :
      ∀ a omega, omega ∈ prefixAtom a ->
        prefixFactor a omega = prefixWeight a)
    (prefixWeight_nonneg : ∀ a, 0 ≤ prefixWeight a) :
    ∀ a omega, omega ∈ prefixAtom a ->
      prefixFuture a omega ≤ Real.exp epsilon * prefixFactor a omega := by
  intro a omega hmem
  rw [hobs.prefix_future_on_prefix a omega hmem,
    prefixFactor_eq a omega hmem]
  calc
    prefixWeight a * pmfExpectation (nuTail a) (tailFuture a) ≤
        prefixWeight a * Real.exp epsilon :=
      mul_le_mul_of_nonneg_left (tail_ih a) (prefixWeight_nonneg a)
    _ = Real.exp epsilon * prefixWeight a := by ring

theorem lemma79_prefix_drop_of_prefixWhiteCount
    {Omega kappa : Type*} [Fintype Omega] [Fintype kappa]
    {prefixAtom : kappa -> Set Omega}
    {ExitWhite : Set Omega}
    [DecidablePred (fun omega => omega ∈ ExitWhite)]
    {prefixFactor : kappa -> Omega -> ℝ}
    {prefixWeight : kappa -> ℝ}
    {prefixWhiteCount : kappa -> ℕ}
    {epsilon : ℝ}
    (prefixFactor_eq :
      ∀ a omega, omega ∈ prefixAtom a ->
        prefixFactor a omega = prefixWeight a)
    (prefixWeight_eq :
      ∀ a, prefixWeight a =
        Real.exp (-(prefixWhiteCount a : ℝ) + epsilon))
    (exit_indicator_le_prefixWhiteCount :
      ∀ a omega, omega ∈ prefixAtom a ->
        ((if omega ∈ ExitWhite then 1 else 0 : ℕ) ≤ prefixWhiteCount a)) :
    ∀ a omega, omega ∈ prefixAtom a ->
      prefixFactor a omega ≤
        Real.exp epsilon * exitWhiteWeight ExitWhite omega := by
  intro a omega hmem
  rw [prefixFactor_eq a omega hmem, prefixWeight_eq a]
  by_cases hwhite : omega ∈ ExitWhite
  · have hcount_nat : (1 : ℕ) ≤ prefixWhiteCount a := by
      simpa [hwhite] using exit_indicator_le_prefixWhiteCount a omega hmem
    have hcount : (1 : ℝ) ≤ (prefixWhiteCount a : ℝ) := by
      exact_mod_cast hcount_nat
    rw [exitWhiteWeight, if_pos hwhite, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · have hcount : (0 : ℝ) ≤ (prefixWhiteCount a : ℝ) := by
      exact_mod_cast Nat.zero_le (prefixWhiteCount a)
    rw [exitWhiteWeight, if_neg hwhite, mul_one]
    exact Real.exp_le_exp.mpr (by nlinarith)

theorem lemma79_fixedOriginStoppedRestartTowerSource_of_fixedPrefixCarrier
    {Omega iota kappa : Type*} [Fintype Omega] [Fintype iota]
    [Fintype kappa]
    {mu : PMF Omega}
    {R Rprev : ℕ}
    {nonzero Atom ExitWhite : Set Omega}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family}
    {i : iota}
    {prefixAtom : kappa -> Set Omega}
    {prefixKey : Omega -> kappa}
    {origin : TaoSection7RenewalPoint}
    {gap : ℕ}
    {K : kappa -> ℕ}
    {pre : kappa -> List TaoSection7RenewalPoint}
    {endpoint : kappa -> TaoSection7RenewalPoint}
    {fullMoment futureMoment : Omega -> ℝ}
    {prefixFuture prefixFactor : kappa -> Omega -> ℝ}
    {epsilon : ℝ}
    (two_le_R : 2 ≤ R)
    (Rprev_eq : Rprev = R - 1)
    (atom_eq : Atom = firstAtoms.atom i)
    (origin_entry : origin.toPoint = firstAtoms.entryPoint i)
    (target_height :
      origin.l + (gap : ℤ) = (firstAtoms.entryTriangle i).cornerL)
    (restart :
      Lemma79TailRestartIdentity Atom ExitWhite fullMoment futureMoment)
    (prefix_mem_iff :
      ∀ a omega, omega ∈ prefixAtom a ↔
        omega ∈ Atom ∧ prefixKey omega = a)
    (prefix_first :
      ∀ a omega, omega ∈ prefixAtom a ->
        TaoSection7Lemma710.VerticalFirstPassagePrefix
          origin gap (K a) (pre a))
    (endpoint_eq :
      ∀ a omega, omega ∈ prefixAtom a ->
        endpoint a = taoSection7RenewalPathPoint origin (pre a) (K a))
    (prefix_tower :
      ∀ a,
        pmfExpectation mu (atomIndicator (prefixAtom a)
          (fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega)) =
          pmfExpectation mu (atomIndicator (prefixAtom a) (prefixFuture a)))
    (future_factor_le :
      ∀ a omega, omega ∈ prefixAtom a ->
        prefixFuture a omega ≤ Real.exp epsilon * prefixFactor a omega)
    (prefix_drop :
      ∀ a omega, omega ∈ prefixAtom a ->
        prefixFactor a omega ≤ Real.exp epsilon * exitWhiteWeight ExitWhite omega) :
    Lemma79FixedOriginStoppedRestartTowerSource
      mu R Rprev nonzero Atom ExitWhite W pointAt family firstAtoms i
      prefixAtom origin gap K pre endpoint fullMoment futureMoment
      prefixFuture prefixFactor epsilon where
  two_le_R := two_le_R
  Rprev_eq := Rprev_eq
  atom_eq := atom_eq
  origin_entry := origin_entry
  target_height := target_height
  restart := restart
  prefix_first_passage := prefix_first
  prefix_endpoint_eq := endpoint_eq
  prefix_expect_partition := by
    have hpart :
        pmfExpectation mu (atomIndicator Atom
          (fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega)) =
          ∑ a, pmfExpectation mu (atomIndicator (prefixAtom a)
            (fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega)) :=
      pmfExpectation_atomIndicator_partition_of_key
        (mu := mu)
        (Parent := Atom)
        (atom := prefixAtom)
        (key := prefixKey)
        (X := fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega)
        (fun omega hAtom =>
          (prefix_mem_iff (prefixKey omega) omega).2 ⟨hAtom, rfl⟩)
        (fun a omega hmem => (prefix_mem_iff a omega).1 hmem)
    calc
      pmfExpectation mu (exitFutureMoment Atom ExitWhite futureMoment)
          =
        pmfExpectation mu (atomIndicator Atom
          (fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega)) :=
            rfl
      _ = ∑ a, pmfExpectation mu (atomIndicator (prefixAtom a)
            (fun omega => exitWhiteWeight ExitWhite omega * futureMoment omega)) :=
            hpart
      _ = ∑ a, pmfExpectation mu (atomIndicator (prefixAtom a)
            (prefixFuture a)) := by
            exact Finset.sum_congr rfl fun a _ha => prefix_tower a
  future_induction_after_prefix := by
    intro a
    exact pmfExpectation_atomIndicator_le_const_mul_of_mem_imp
      mu (prefixAtom a) (prefixFuture a) (prefixFactor a) (Real.exp epsilon)
      (future_factor_le a)
  prefix_factor_le_exit_weight := by
    intro a
    exact pmfExpectation_atomIndicator_le_const_mul_of_mem_imp
      mu (prefixAtom a) (prefixFactor a) (exitWhiteWeight ExitWhite)
      (Real.exp epsilon) (prefix_drop a)
  prefix_exit_weight_partition := by
    have hpart :
        pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite)) =
          ∑ a, pmfExpectation mu (atomIndicator (prefixAtom a)
            (exitWhiteWeight ExitWhite)) :=
      pmfExpectation_atomIndicator_partition_of_key
        (mu := mu)
        (Parent := Atom)
        (atom := prefixAtom)
        (key := prefixKey)
        (X := exitWhiteWeight ExitWhite)
        (fun omega hAtom =>
          (prefix_mem_iff (prefixKey omega) omega).2 ⟨hAtom, rfl⟩)
        (fun a omega hmem => (prefix_mem_iff a omega).1 hmem)
    exact hpart.symm

theorem lemma79_fixedOriginStoppedRestartTowerSource_of_prefixTowerObservableTailFiberCarrier
    {Omega iota kappa Tail : Type*} [Fintype Omega] [Fintype iota]
    [Fintype kappa] [Fintype Tail]
    {mu : PMF Omega}
    {R Rprev : ℕ}
    {nonzero Atom ExitWhite : Set Omega}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family}
    {i : iota}
    {prefixAtom : kappa -> Set Omega}
    {prefixKey : Omega -> kappa}
    {origin : TaoSection7RenewalPoint}
    {gap : ℕ}
    {K : kappa -> ℕ}
    {pre : kappa -> List TaoSection7RenewalPoint}
    {endpoint : kappa -> TaoSection7RenewalPoint}
    {fullMoment futureMoment : Omega -> ℝ}
    {prefixFuture prefixFactor : kappa -> Omega -> ℝ}
    {tailOf : kappa -> Omega -> Tail}
    {nuTail : kappa -> PMF Tail}
    {prefixWeight : kappa -> ℝ}
    {tailFuture : kappa -> Tail -> ℝ}
    {epsilon : ℝ}
    (two_le_R : 2 ≤ R)
    (Rprev_eq : Rprev = R - 1)
    (atom_eq : Atom = firstAtoms.atom i)
    (origin_entry : origin.toPoint = firstAtoms.entryPoint i)
    (target_height :
      origin.l + (gap : ℤ) = (firstAtoms.entryTriangle i).cornerL)
    (restart :
      Lemma79TailRestartIdentity Atom ExitWhite fullMoment futureMoment)
    (prefix_mem_iff :
      ∀ a omega, omega ∈ prefixAtom a ↔
        omega ∈ Atom ∧ prefixKey omega = a)
    (prefix_first :
      ∀ a omega, omega ∈ prefixAtom a ->
        TaoSection7Lemma710.VerticalFirstPassagePrefix
          origin gap (K a) (pre a))
    (endpoint_eq :
      ∀ a omega, omega ∈ prefixAtom a ->
        endpoint a = taoSection7RenewalPathPoint origin (pre a) (K a))
    (hobservable :
      Lemma79PrefixTowerObservableTailFiberCarrier
        mu prefixAtom ExitWhite tailOf nuTail futureMoment prefixFuture
        prefixWeight tailFuture)
    (future_factor_le :
      ∀ a omega, omega ∈ prefixAtom a ->
        prefixFuture a omega ≤ Real.exp epsilon * prefixFactor a omega)
    (prefix_drop :
      ∀ a omega, omega ∈ prefixAtom a ->
        prefixFactor a omega ≤ Real.exp epsilon * exitWhiteWeight ExitWhite omega) :
    Lemma79FixedOriginStoppedRestartTowerSource
      mu R Rprev nonzero Atom ExitWhite W pointAt family firstAtoms i
      prefixAtom origin gap K pre endpoint fullMoment futureMoment
      prefixFuture prefixFactor epsilon :=
  lemma79_fixedOriginStoppedRestartTowerSource_of_fixedPrefixCarrier
    (mu := mu) (R := R) (Rprev := Rprev) (nonzero := nonzero)
    (Atom := Atom) (ExitWhite := ExitWhite) (W := W) (pointAt := pointAt)
    (family := family) (firstAtoms := firstAtoms) (i := i)
    (prefixAtom := prefixAtom) (prefixKey := prefixKey)
    (origin := origin) (gap := gap) (K := K) (pre := pre)
    (endpoint := endpoint) (fullMoment := fullMoment)
    (futureMoment := futureMoment) (prefixFuture := prefixFuture)
    (prefixFactor := prefixFactor) (epsilon := epsilon)
    two_le_R Rprev_eq atom_eq origin_entry target_height restart
    prefix_mem_iff prefix_first endpoint_eq hobservable.prefix_tower
    future_factor_le prefix_drop

/--
Atom-level stopped restart/tower input for Tao's full Lemma 7.9 `Z_R` step.

The `tower_le` field is where the future stopped strong-Markov proof and the
uniform `Z(_, R - 1) ≤ exp epsilon` induction hypothesis are consumed.  The
factor `Real.exp (2 * epsilon)` keeps Tao's two positive epsilon contributions
visible before the exit-white contraction is applied.
-/
structure Lemma79FullZAtomRestartTowerInput
    {Omega : Type*} [Fintype Omega]
    (mu : PMF Omega)
    (R Rprev : ℕ)
    (Atom ExitWhite : Set Omega)
    (fullMoment futureMoment : Omega -> ℝ)
    (epsilon : ℝ) : Prop where
  two_le_R : 2 ≤ R
  Rprev_eq : Rprev = R - 1
  restart :
    Lemma79TailRestartIdentity Atom ExitWhite fullMoment futureMoment
  tower_le :
    pmfExpectation mu (exitFutureMoment Atom ExitWhite futureMoment) ≤
      Real.exp (2 * epsilon) *
        pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite))

theorem Lemma79FullZAtomRestartTowerInput.atom_expectation_le_exp_prob
    {Omega : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {R Rprev : ℕ}
    {Atom ExitWhite : Set Omega}
    {fullMoment futureMoment : Omega -> ℝ}
    {c0 epsilon : ℝ}
    (h :
      Lemma79FullZAtomRestartTowerInput
        mu R Rprev Atom ExitWhite fullMoment futureMoment epsilon)
    (hexit : Lemma79ExitWhiteContraction mu Atom ExitWhite c0 epsilon) :
    pmfExpectation mu (atomIndicator Atom fullMoment) ≤
      Real.exp epsilon * pmfProb mu Atom := by
  classical
  have hrewrite :
      pmfExpectation mu (atomIndicator Atom fullMoment) =
        pmfExpectation mu (exitFutureMoment Atom ExitWhite futureMoment) := by
    unfold pmfExpectation
    refine Finset.sum_congr rfl ?_
    intro omega _homega
    by_cases hAtom : omega ∈ Atom
    · simp [atomIndicator, exitFutureMoment, hAtom,
        h.restart.split_on_atom omega hAtom]
    · simp [atomIndicator, exitFutureMoment, hAtom]
  have hwhite :
      pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite)) ≤
        Real.exp (-epsilon) * pmfProb mu Atom :=
    exitWhiteWeight_expectation_le hexit
  have hmul :
      Real.exp (2 * epsilon) *
          pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite)) ≤
        Real.exp (2 * epsilon) *
          (Real.exp (-epsilon) * pmfProb mu Atom) :=
    mul_le_mul_of_nonneg_left hwhite (Real.exp_pos (2 * epsilon)).le
  have hcancel :
      Real.exp (2 * epsilon) *
          (Real.exp (-epsilon) * pmfProb mu Atom) =
        Real.exp epsilon * pmfProb mu Atom := by
    rw [← mul_assoc, ← Real.exp_add]
    have harg : 2 * epsilon + -epsilon = epsilon := by ring
    rw [harg]
  rw [hrewrite]
  exact le_trans h.tower_le (by simpa [hcancel] using hmul)

theorem lemma79_fullZAtomRestartTowerInput_of_stoppedRestartTowerSource
    {Omega kappa : Type*} [Fintype Omega] [Fintype kappa]
    {mu : PMF Omega}
    {R Rprev : ℕ}
    {Atom ExitWhite : Set Omega}
    {prefixAtom : kappa -> Set Omega}
    {start : kappa -> TaoSection7RenewalPoint}
    {verticalGap K : kappa -> ℕ}
    {pre : kappa -> List TaoSection7RenewalPoint}
    {endpoint : kappa -> TaoSection7RenewalPoint}
    {fullMoment futureMoment : Omega -> ℝ}
    {prefixFuture prefixFactor : kappa -> Omega -> ℝ}
    {epsilon : ℝ}
    (hsrc :
      Lemma79StoppedRestartTowerSource
        mu R Rprev Atom ExitWhite prefixAtom start verticalGap K pre endpoint
        fullMoment futureMoment prefixFuture prefixFactor epsilon) :
    Lemma79FullZAtomRestartTowerInput
      mu R Rprev Atom ExitWhite fullMoment futureMoment epsilon where
  two_le_R := hsrc.two_le_R
  Rprev_eq := hsrc.Rprev_eq
  restart := hsrc.restart
  tower_le := by
    have hper :
        ∀ a,
          pmfExpectation mu (atomIndicator (prefixAtom a) (prefixFuture a)) ≤
            Real.exp (2 * epsilon) *
              pmfExpectation mu (atomIndicator (prefixAtom a)
                (exitWhiteWeight ExitWhite)) := by
      intro a
      have hfactor :
          Real.exp epsilon *
              pmfExpectation mu (atomIndicator (prefixAtom a)
                (prefixFactor a)) ≤
            Real.exp epsilon *
              (Real.exp epsilon *
                pmfExpectation mu (atomIndicator (prefixAtom a)
                  (exitWhiteWeight ExitWhite))) :=
        mul_le_mul_of_nonneg_left
          (hsrc.prefix_factor_le_exit_weight a) (Real.exp_pos epsilon).le
      have hmul :
          Real.exp epsilon *
              (Real.exp epsilon *
                pmfExpectation mu (atomIndicator (prefixAtom a)
                  (exitWhiteWeight ExitWhite))) =
            Real.exp (2 * epsilon) *
              pmfExpectation mu (atomIndicator (prefixAtom a)
                (exitWhiteWeight ExitWhite)) := by
        rw [← mul_assoc, ← Real.exp_add]
        have harg : epsilon + epsilon = 2 * epsilon := by ring
        rw [harg]
      exact le_trans (hsrc.future_induction_after_prefix a)
        (by simpa [hmul] using hfactor)
    calc
      pmfExpectation mu (exitFutureMoment Atom ExitWhite futureMoment)
          = ∑ a,
              pmfExpectation mu
                (atomIndicator (prefixAtom a) (prefixFuture a)) :=
            hsrc.prefix_expect_partition
      _ ≤ ∑ a,
              Real.exp (2 * epsilon) *
                pmfExpectation mu (atomIndicator (prefixAtom a)
                  (exitWhiteWeight ExitWhite)) := by
            exact Finset.sum_le_sum fun a _ha => hper a
      _ = Real.exp (2 * epsilon) *
            (∑ a, pmfExpectation mu (atomIndicator (prefixAtom a)
              (exitWhiteWeight ExitWhite))) := by
            rw [Finset.mul_sum]
      _ = Real.exp (2 * epsilon) *
            pmfExpectation mu (atomIndicator Atom (exitWhiteWeight ExitWhite)) := by
            rw [hsrc.prefix_exit_weight_partition]

theorem lemma79_fullZAtomRestartTowerInput_of_fixedOriginStoppedRestartTowerSource
    {Omega iota kappa : Type*} [Fintype Omega] [Fintype iota]
    [Fintype kappa]
    {mu : PMF Omega}
    {R Rprev : ℕ}
    {nonzero Atom ExitWhite : Set Omega}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family}
    {i : iota}
    {prefixAtom : kappa -> Set Omega}
    {origin : TaoSection7RenewalPoint}
    {gap : ℕ}
    {K : kappa -> ℕ}
    {pre : kappa -> List TaoSection7RenewalPoint}
    {endpoint : kappa -> TaoSection7RenewalPoint}
    {fullMoment futureMoment : Omega -> ℝ}
    {prefixFuture prefixFactor : kappa -> Omega -> ℝ}
    {epsilon : ℝ}
    (hsrc :
      Lemma79FixedOriginStoppedRestartTowerSource
        mu R Rprev nonzero Atom ExitWhite W pointAt family firstAtoms i
        prefixAtom origin gap K pre endpoint fullMoment futureMoment
        prefixFuture prefixFactor epsilon) :
    Lemma79FullZAtomRestartTowerInput
      mu R Rprev Atom ExitWhite fullMoment futureMoment epsilon :=
  lemma79_fullZAtomRestartTowerInput_of_stoppedRestartTowerSource
    hsrc.to_stoppedRestartTowerSource

/--
Algebraic inputs for Tao's Lemma 7.9 full-`Z` induction step.

This source-facing socket exposes the `r = 0` branch, the inclusive first-entry
atom partition of `r ≠ 0`, the `R - 1` atom restart/tower data, the per-atom
exit-white lower bound, and the final finite-PMF partition equations.  It does
not prove any of those source laws.
-/
structure Lemma79FullZInductionStepInput
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    (mu : PMF Omega)
    (R Rprev : ℕ)
    (zero nonzero ExitWhite : Set Omega)
    (atom : iota -> Set Omega)
    (fullMoment : Omega -> ℝ)
    (futureMoment : iota -> Omega -> ℝ)
    (c0 epsilon : ℝ) : Prop where
  two_le_R : 2 ≤ R
  Rprev_eq : Rprev = R - 1
  zero_branch_le :
    pmfExpectation mu (atomIndicator zero fullMoment) ≤ pmfProb mu zero
  nonzero_expect_partition :
    pmfExpectation mu (atomIndicator nonzero fullMoment) =
      ∑ i, pmfExpectation mu (atomIndicator (atom i) fullMoment)
  nonzero_prob_partition :
    pmfProb mu nonzero = ∑ i, pmfProb mu (atom i)
  atom_restart_tower :
    ∀ i,
      Lemma79FullZAtomRestartTowerInput
        mu R Rprev (atom i) ExitWhite fullMoment (futureMoment i) epsilon
  atom_exit :
    ∀ i, Lemma79ExitWhiteContraction mu (atom i) ExitWhite c0 epsilon
  full_split :
    pmfExpectation mu fullMoment =
      pmfExpectation mu (atomIndicator zero fullMoment) +
        pmfExpectation mu (atomIndicator nonzero fullMoment)
  prob_split : pmfProb mu zero + pmfProb mu nonzero = 1
  epsilon_nonneg : 0 ≤ epsilon

theorem lemma79_fullZInductionStepInput_of_firstEntryFiniteCarrier
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {R Rprev : ℕ}
    {zero nonzero ExitWhite : Set Omega}
    {atom : iota -> Set Omega}
    {fullMoment : Omega -> ℝ}
    {futureMoment : iota -> Omega -> ℝ}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {c0 epsilon : ℝ}
    (hcarrier :
      Lemma79FirstEntryAtomFiniteCarrier
        mu zero nonzero atom fullMoment W pointAt family)
    (htwo : 2 ≤ R)
    (hRprev : Rprev = R - 1)
    (hzero :
      pmfExpectation mu (atomIndicator zero fullMoment) ≤ pmfProb mu zero)
    (hrestart_tower :
      ∀ i,
        Lemma79FullZAtomRestartTowerInput
          mu R Rprev (atom i) ExitWhite fullMoment
            (futureMoment i) epsilon)
    (hexit :
      ∀ i, Lemma79ExitWhiteContraction mu (atom i) ExitWhite c0 epsilon)
    (heps_nonneg : 0 ≤ epsilon) :
    Lemma79FullZInductionStepInput
      mu R Rprev zero nonzero ExitWhite atom fullMoment futureMoment
        c0 epsilon where
  two_le_R := htwo
  Rprev_eq := hRprev
  zero_branch_le := hzero
  nonzero_expect_partition := hcarrier.nonzero_expect_partition
  nonzero_prob_partition := hcarrier.nonzero_prob_partition
  atom_restart_tower := hrestart_tower
  atom_exit := hexit
  full_split := hcarrier.full_split
  prob_split := hcarrier.prob_split
  epsilon_nonneg := heps_nonneg

theorem Lemma79FullZInductionStepInput.full_expectation_le_exp
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {R Rprev : ℕ}
    {zero nonzero ExitWhite : Set Omega}
    {atom : iota -> Set Omega}
    {fullMoment : Omega -> ℝ}
    {futureMoment : iota -> Omega -> ℝ}
    {c0 epsilon : ℝ}
    (h :
      Lemma79FullZInductionStepInput
        mu R Rprev zero nonzero ExitWhite atom fullMoment futureMoment
          c0 epsilon) :
    pmfExpectation mu fullMoment ≤ Real.exp epsilon :=
  tailMoment_expectation_le_exp_of_zero_nonzero_atom_partition
    h.zero_branch_le
    h.nonzero_expect_partition
    h.nonzero_prob_partition
    (fun i =>
      (h.atom_restart_tower i).atom_expectation_le_exp_prob (h.atom_exit i))
    h.full_split
    h.prob_split
    h.epsilon_nonneg

theorem repairedTailExpectation_le_of_fullTailMoment
    {Omega : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {repairedMoment fullMoment : Omega -> ℝ}
    {epsilon : ℝ}
    (hdom : ∀ omega, repairedMoment omega ≤ fullMoment omega)
    (hfull : pmfExpectation mu fullMoment ≤ Real.exp epsilon) :
    pmfExpectation mu repairedMoment ≤ Real.exp epsilon :=
  le_trans (pmfExpectation_mono mu hdom) hfull

/-- Tao's full printed Lemma 7.9 moment at `t_min(r,R)`, abstracted by count. -/
noncomputable def fullTailMoment
    {Omega : Type*}
    (steps : Omega -> List (ℕ × TaoSection7Triangle))
    (R : ℕ)
    (fullCount : Omega -> ℕ)
    (epsilon : ℝ) : Omega -> ℝ :=
  fun omega =>
    Real.exp (-(fullCount omega : ℝ) +
      epsilon * (min (r (steps omega)) R : ℝ))

theorem lemma79_fullTailExpectation_step_of_firstEntryPartition
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {steps : Omega -> List (ℕ × TaoSection7Triangle)}
    {R Rprev : ℕ}
    {fullCount : Omega -> ℕ}
    {zero nonzero ExitWhite : Set Omega}
    {atom : iota -> Set Omega}
    {futureMoment : iota -> Omega -> ℝ}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {firstAtoms :
      Lemma79FirstEntryAtomFamily (iota := iota) nonzero W pointAt family}
    {c0 epsilon : ℝ}
    (hsource :
      Lemma79FullZSourceAtomPartition (iota := iota) firstAtoms atom)
    (hstep :
      Lemma79FullZInductionStepInput
        mu R Rprev zero nonzero ExitWhite atom
          (fullTailMoment steps R fullCount epsilon) futureMoment
          c0 epsilon) :
    pmfExpectation mu (fullTailMoment steps R fullCount epsilon) ≤
      Real.exp epsilon := by
  have _hsource := hsource.atom_eq
  exact hstep.full_expectation_le_exp

theorem lemma79_fullTailExpectation_step_of_firstEntryFiniteCarrier
    {Omega iota : Type*} [Fintype Omega] [Fintype iota]
    {mu : PMF Omega}
    {steps : Omega -> List (ℕ × TaoSection7Triangle)}
    {R Rprev : ℕ}
    {fullCount : Omega -> ℕ}
    {zero nonzero ExitWhite : Set Omega}
    {atom : iota -> Set Omega}
    {futureMoment : iota -> Omega -> ℝ}
    {W : Omega -> ℕ -> Prop}
    {pointAt : Omega -> ℕ -> TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {c0 epsilon : ℝ}
    (hcarrier :
      Lemma79FirstEntryAtomFiniteCarrier
        mu zero nonzero atom
          (fullTailMoment steps R fullCount epsilon) W pointAt family)
    (htwo : 2 ≤ R)
    (hRprev : Rprev = R - 1)
    (hzero :
      pmfExpectation mu
          (atomIndicator zero (fullTailMoment steps R fullCount epsilon)) ≤
        pmfProb mu zero)
    (hrestart_tower :
      ∀ i,
        Lemma79FullZAtomRestartTowerInput
          mu R Rprev (atom i) ExitWhite
            (fullTailMoment steps R fullCount epsilon)
            (futureMoment i) epsilon)
    (hexit :
      ∀ i, Lemma79ExitWhiteContraction mu (atom i) ExitWhite c0 epsilon)
    (heps_nonneg : 0 ≤ epsilon) :
    pmfExpectation mu (fullTailMoment steps R fullCount epsilon) ≤
      Real.exp epsilon := by
  exact
    (lemma79_fullZInductionStepInput_of_firstEntryFiniteCarrier
      hcarrier htwo hRprev hzero hrestart_tower hexit heps_nonneg).full_expectation_le_exp

theorem repairedTailMoment_le_fullLemma79Moment
    {Omega : Type*}
    {steps : Omega -> List (ℕ × TaoSection7Triangle)}
    {R : ℕ}
    {tailCount fullCount : Omega -> ℕ}
    {epsilon : ℝ}
    (hcount_on_branch :
      ∀ omega, R ≤ r (steps omega) -> tailCount omega = fullCount omega) :
    ∀ omega,
      Lemma79SourceFSlackMomentPacket.repairedTailMoment
          steps R tailCount epsilon omega ≤
        fullTailMoment steps R fullCount epsilon omega := by
  intro omega
  by_cases hr : R ≤ r (steps omega)
  · simp [Lemma79SourceFSlackMomentPacket.repairedTailMoment, hr,
      hcount_on_branch omega hr, fullTailMoment]
  · simpa [Lemma79SourceFSlackMomentPacket.repairedTailMoment, hr,
      fullTailMoment] using
      (Real.exp_pos
        (-(fullCount omega : ℝ) +
          epsilon * (min (r (steps omega)) R : ℝ))).le

theorem repairedTailMoment_le_fullTailMoment
    {Omega : Type*}
    {steps : Omega -> List (ℕ × TaoSection7Triangle)}
    {R : ℕ}
    {tailCount fullCount : Omega -> ℕ}
    {epsilon : ℝ}
    (hcount_on_branch :
      ∀ omega, R ≤ r (steps omega) -> tailCount omega = fullCount omega) :
    ∀ omega,
      Lemma79SourceFSlackMomentPacket.repairedTailMoment
          steps R tailCount epsilon omega ≤
        fullTailMoment steps R fullCount epsilon omega :=
  repairedTailMoment_le_fullLemma79Moment hcount_on_branch

theorem repairedTailExpectation_le_of_fullLemma79Moment
    {Omega : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {steps : Omega -> List (ℕ × TaoSection7Triangle)}
    {R : ℕ}
    {tailCount fullCount : Omega -> ℕ}
    {epsilon : ℝ}
    (hcount_on_branch :
      ∀ omega, R ≤ r (steps omega) -> tailCount omega = fullCount omega)
    (hfull :
      pmfExpectation mu (fullTailMoment steps R fullCount epsilon) ≤
        Real.exp epsilon) :
    pmfExpectation mu
        (Lemma79SourceFSlackMomentPacket.repairedTailMoment
          steps R tailCount epsilon) ≤
      Real.exp epsilon :=
  repairedTailExpectation_le_of_fullTailMoment
    (mu := mu)
    (hdom := repairedTailMoment_le_fullLemma79Moment hcount_on_branch)
    hfull

theorem repairedTailExpectation_le_of_fullTailExpectation
    {Omega : Type*} [Fintype Omega]
    {mu : PMF Omega}
    {steps : Omega -> List (ℕ × TaoSection7Triangle)}
    {R : ℕ}
    {tailCount fullCount : Omega -> ℕ}
    {epsilon : ℝ}
    (hcount_on_branch :
      ∀ omega, R ≤ r (steps omega) -> tailCount omega = fullCount omega)
    (hfull :
      pmfExpectation mu (fullTailMoment steps R fullCount epsilon) ≤
        Real.exp epsilon) :
    pmfExpectation mu
        (Lemma79SourceFSlackMomentPacket.repairedTailMoment
          steps R tailCount epsilon) ≤
      Real.exp epsilon :=
  repairedTailExpectation_le_of_fullLemma79Moment hcount_on_branch hfull

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
