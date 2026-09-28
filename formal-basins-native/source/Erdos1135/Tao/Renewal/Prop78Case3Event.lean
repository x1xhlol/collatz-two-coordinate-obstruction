import Erdos1135.Tao.Fourier.Section7SourceDomain
import Erdos1135.Tao.Probability.Finite
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Proposition 7.8 Case 3 Event Support

This module records support-only event and finite-counting adapters for Tao's
Proposition 7.8 Case 3 route.  It packages the low `P`-window counting core
and the outside-large-triangle-event `E*` consequence used later in Case 3.

It does not prove Lemma 7.9, Lemma 7.10, the probability bound for `E*`,
the endpoint budget, the many-whites estimate, Case 3, boundary estimate
`(7.41)`, Proposition 7.8, or Tao's theorem.
-/

namespace Erdos1135
namespace Tao

open Finset
open scoped BigOperators

/-- Source low-window white count: offsets `0 <= p < P`. -/
noncomputable def taoSection7Case3WindowWhiteCount
    (W : ℕ → Prop) [DecidablePred W] (P : ℕ) : ℕ :=
  (Finset.range P).sum fun p => if W p then 1 else 0

/-- Positive-offset white count from Tao's Case 3 restart: offsets `1 <= p <= t`. -/
noncomputable def taoSection7Case3PositiveWhiteCount
    (W : ℕ → Prop) [DecidablePred W] (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).sum fun p => if W p then 1 else 0

theorem taoSection7Case3_positiveOffsets_subset_window
    {P t : ℕ} (ht : t < P) :
    Finset.Icc 1 t ⊆ Finset.range P := by
  intro p hp
  exact Finset.mem_range.2 (lt_of_le_of_lt (Finset.mem_Icc.1 hp).2 ht)

theorem taoSection7Case3_positiveWhiteCount_le_window
    (W : ℕ → Prop) [DecidablePred W] {P t : ℕ} (ht : t < P) :
    taoSection7Case3PositiveWhiteCount W t ≤
      taoSection7Case3WindowWhiteCount W P := by
  unfold taoSection7Case3PositiveWhiteCount taoSection7Case3WindowWhiteCount
  exact Finset.sum_le_sum_of_subset
    (taoSection7Case3_positiveOffsets_subset_window ht)

theorem taoSection7Case3_many_positive_offsets_not_low_window
    (W : ℕ → Prop) [DecidablePred W] {P t threshold : ℕ}
    (ht : t < P)
    (hmany : threshold < taoSection7Case3PositiveWhiteCount W t) :
    ¬ taoSection7Case3WindowWhiteCount W P ≤ threshold := by
  intro hlow
  have hpositive_le_window :
      taoSection7Case3PositiveWhiteCount W t ≤
        taoSection7Case3WindowWhiteCount W P :=
    taoSection7Case3_positiveWhiteCount_le_window W ht
  exact not_lt_of_ge hlow (lt_of_lt_of_le hmany hpositive_le_window)

/--
Under the low `P`-window white-count event, every block of `threshold + 1`
usable offsets contains a non-white offset.
-/
theorem taoSection7Case3_low_window_forces_nonwhite_in_block
    (W : ℕ → Prop) [DecidablePred W] {P start threshold : ℕ}
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hblock : start + threshold < P) :
    ∃ q : ℕ, q ∈ Finset.Icc start (start + threshold) ∧ ¬ W q := by
  by_contra hnone
  have hall : ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) → W q := by
    intro q hq
    by_contra hW
    exact hnone ⟨q, hq, hW⟩
  let f : ℕ → ℕ := fun q => if W q then 1 else 0
  have hsub : Finset.Icc start (start + threshold) ⊆ Finset.range P := by
    intro q hq
    exact Finset.mem_range.2 (lt_of_le_of_lt (Finset.mem_Icc.1 hq).2 hblock)
  have hsum_card :
      (Finset.Icc start (start + threshold)).sum f =
        (Finset.Icc start (start + threshold)).card := by
    calc
      (Finset.Icc start (start + threshold)).sum f =
          (Finset.Icc start (start + threshold)).sum
            (fun _q : ℕ => (1 : ℕ)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            simp [f, hall q hq]
      _ = (Finset.Icc start (start + threshold)).card := by
        simp
  have hcard :
      (Finset.Icc start (start + threshold)).card = threshold + 1 := by
    rw [Nat.card_Icc]
    omega
  have hle_window :
      (Finset.Icc start (start + threshold)).sum f ≤
        taoSection7Case3WindowWhiteCount W P := by
    unfold taoSection7Case3WindowWhiteCount
    exact Finset.sum_le_sum_of_subset hsub
  have hbad : threshold + 1 ≤ threshold := by
    calc
      threshold + 1 =
          (Finset.Icc start (start + threshold)).sum f := by
            rw [hsum_card, hcard]
      _ ≤ taoSection7Case3WindowWhiteCount W P := hle_window
      _ ≤ threshold := hlow
  omega

/--
Positive-offset seed form for the first Case 3 stopping time.  It avoids using
offset `0` as the initial black/triangle hit while reusing the low-window
counting core.
-/
theorem taoSection7Case3_low_window_forces_positive_nonwhite_seed
    (W : ℕ → Prop) [DecidablePred W] {P T : ℕ}
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ T)
    (hroom : T + 1 < P) :
    ∃ p : ℕ, p ∈ Finset.Icc 1 (T + 1) ∧ ¬ W p := by
  simpa [Nat.add_comm] using
    (taoSection7Case3_low_window_forces_nonwhite_in_block
      (W := W) (P := P) (start := 1) (threshold := T) hlow
      (by simpa [Nat.add_comm] using hroom))

/--
Source-shaped large-triangle event `E_{p,s'}`: the selected offset point lies
in a triangle from the family whose size is at least `s'`.
-/
def taoSection7Case3LargeTriangleEvent
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (p : ℕ) (s' : ℝ) : Prop :=
  ∃ Δ : TaoSection7Triangle, Δ ∈ family ∧ Δ.Mem (pointAt p) ∧ s' ≤ Δ.size

/-- `E*` is a union of large-triangle events over an allowed offset range. -/
def taoSection7Case3LargeTriangleUnion
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (allowed : Set ℕ) (bound : ℕ → ℝ) : Prop :=
  ∃ p : ℕ, p ∈ allowed ∧
    taoSection7Case3LargeTriangleEvent pointAt family p (bound p)

/-- Source Case 3 large-triangle bound `4^A(1+p)^3`, kept as a real expression. -/
noncomputable def taoSection7Case3LargeTriangleBound
    (A p : ℕ) : ℝ :=
  (4 : ℝ) ^ A * (1 + (p : ℝ)) ^ 3

/--
Parameterized Case 3 large-triangle threshold.

The printed Tao threshold uses base `4`; downstream probability-budget repairs
may require a larger base or an explicit slack parameter before proving the
final `(7.56)`-style bound.
-/
noncomputable def taoSection7Case3LargeTriangleBoundWithBase
    (base : ℝ) (A p : ℕ) : ℝ :=
  base ^ A * (1 + (p : ℝ)) ^ 3

@[simp] theorem taoSection7Case3LargeTriangleBoundWithBase_four
    (A p : ℕ) :
    taoSection7Case3LargeTriangleBoundWithBase 4 A p =
      taoSection7Case3LargeTriangleBound A p := by
  rfl

theorem taoSection7Case3_largeTriangleBound_event_le_Kcut
    {Aevent Kcut p : ℕ} (hAK : Aevent ≤ Kcut) :
    taoSection7Case3LargeTriangleBound Aevent p ≤
      taoSection7Case3LargeTriangleBound Kcut p := by
  dsimp [taoSection7Case3LargeTriangleBound]
  gcongr
  norm_num

/-- Source-facing range and scale guards for a used-offset large-triangle event. -/
def TaoSection7Case3EStarUsedOffsetAdmissible
    (m p : ℕ) (s' : ℝ) : Prop :=
  (p : ℝ) ≤ Real.rpow (m : ℝ) ((1 : ℝ) / 10) ∧
    1 ≤ s' ∧
      s' ≤ Real.rpow (m : ℝ) ((2 : ℝ) / 5)

/--
Finite PMF algebra for the strengthened `E*_used` event.

This is only a union-bound consumer.  It does not prove that `EStarUsed` is
Tao's source event or that the per-offset events satisfy Lemma 7.10.
-/
theorem taoSection7Case3_prob_EStarUsed_le_sum_perBudget
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (allowed : Finset ℕ) (event : ℕ → Set Ω)
    (EStarUsed : Set Ω) (perBudget : ℕ → ℝ)
    (hcover :
      EStarUsed ⊆ {ω | ∃ p, p ∈ allowed ∧ ω ∈ event p})
    (hper :
      ∀ p, p ∈ allowed → pmfProb μ (event p) ≤ perBudget p) :
    pmfProb μ EStarUsed ≤ allowed.sum perBudget := by
  calc
    pmfProb μ EStarUsed
        ≤ allowed.sum fun p => pmfProb μ (event p) :=
          pmfProb_le_finset_sum_of_subset_exists
            μ allowed event EStarUsed (by
              intro ω hω
              exact hcover hω)
    _ ≤ allowed.sum perBudget := by
          exact Finset.sum_le_sum fun p hp => hper p hp

/--
Large-triangle specialization of the finite `E*_used` union bound.

The finite `allowed` set and per-offset budgets remain explicit inputs.
-/
theorem taoSection7Case3_prob_EStarUsed_le_sum_largeTriangle
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {allowed : Finset ℕ} {bound : ℕ → ℝ}
    {EStarUsed : Set Ω} {perBudget : ℕ → ℝ}
    (hcover :
      EStarUsed ⊆
        {ω | ∃ p, p ∈ allowed ∧
          taoSection7Case3LargeTriangleEvent (pointAt ω) family p (bound p)})
    (hper :
      ∀ p, p ∈ allowed →
        pmfProb μ
          {ω | taoSection7Case3LargeTriangleEvent (pointAt ω) family p (bound p)}
          ≤ perBudget p) :
    pmfProb μ EStarUsed ≤ allowed.sum perBudget :=
  taoSection7Case3_prob_EStarUsed_le_sum_perBudget
    (μ := μ) (allowed := allowed)
    (event := fun p =>
      {ω | taoSection7Case3LargeTriangleEvent (pointAt ω) family p (bound p)})
    (EStarUsed := EStarUsed) (perBudget := perBudget)
    hcover hper

/--
Source-support package for the future strengthened `E*_used` producer.

The probability theorem below consumes this record, but the record itself is
still only a contract: it names the finite offset cover, deterministic
inspected-offset coverage, source threshold relation, Lemma 7.10 range/scale
guards, per-offset probability estimates, and final finite-sum budget.
-/
structure TaoSection7Case3EStarUsedOffsetSupport
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    (pointAt : Ω → ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (EStarUsed : Set Ω)
    (Aweight Kcut m : ℕ)
    (inspected : Set ℕ) where
  allowed : Finset ℕ
  bound : ℕ → ℝ
  perBudget : ℕ → ℝ
  cover :
    EStarUsed ⊆
      {ω | ∃ p, p ∈ allowed ∧
        taoSection7Case3LargeTriangleEvent (pointAt ω) family p (bound p)}
  inspected_mem_allowed :
    ∀ p, p ∈ inspected → p ∈ allowed
  source_threshold :
    ∀ p, p ∈ allowed →
      bound p = taoSection7Case3LargeTriangleBound Kcut p ∨
        ∃ base : ℝ,
          4 ≤ base ∧
            bound p =
              taoSection7Case3LargeTriangleBoundWithBase base Kcut p
  admissible :
    ∀ p, p ∈ allowed →
      TaoSection7Case3EStarUsedOffsetAdmissible m p (bound p)
  per_offset_prob :
    ∀ p, p ∈ allowed →
      pmfProb μ
        {ω | taoSection7Case3LargeTriangleEvent (pointAt ω) family p (bound p)}
        ≤ perBudget p
  sum_budget :
    allowed.sum perBudget ≤ (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut)

/--
Finite-used-offset producer consumer for the strengthened `E*_used` budget.

This closes only the algebra once a source-support package is supplied.
-/
theorem taoSection7Case3_prob_EStarUsed_le_of_finite_used_offsets
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω} {Aweight Kcut m : ℕ}
    {inspected : Set ℕ}
    (support :
      TaoSection7Case3EStarUsedOffsetSupport
        μ pointAt family EStarUsed Aweight Kcut m inspected) :
    pmfProb μ EStarUsed ≤ (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) :=
  (taoSection7Case3_prob_EStarUsed_le_sum_largeTriangle
    (μ := μ) (pointAt := pointAt) (family := family)
    (allowed := support.allowed) (bound := support.bound)
    (EStarUsed := EStarUsed) (perBudget := support.perBudget)
    support.cover support.per_offset_prob).trans
    support.sum_budget

/--
Two-sided event-direction contract for the strengthened `E*_used` event.

The right inclusion is the probability-cover direction.  The left inclusion is
the deterministic direction needed to use `ω ∉ EStarUsed` as a no-large-event
fact for the offsets that the source recurrence may inspect.
-/
structure TaoSection7Case3EStarUsedLargeTriangleSandwich
    {Ω : Type*} [Fintype Ω]
    (pointAt : Ω → ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (EStarUsed : Set Ω)
    (used : Set ℕ) (allowed : Finset ℕ) (bound : ℕ → ℝ) where
  used_mem_allowed : ∀ p, p ∈ used → p ∈ allowed
  large_used_subset :
    {ω | ∃ p, p ∈ used ∧
      taoSection7Case3LargeTriangleEvent (pointAt ω) family p (bound p)}
      ⊆ EStarUsed
  cover_for_probability :
    EStarUsed ⊆
      {ω | ∃ p, p ∈ allowed ∧
        taoSection7Case3LargeTriangleEvent (pointAt ω) family p (bound p)}

theorem TaoSection7Case3EStarUsedLargeTriangleSandwich.not_large_union_of_not_mem
    {Ω : Type*} [Fintype Ω]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {used : Set ℕ} {allowed : Finset ℕ} {bound : ℕ → ℝ}
    (h :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAt family EStarUsed used allowed bound)
    {ω : Ω} (hω : ω ∉ EStarUsed) :
    ¬ taoSection7Case3LargeTriangleUnion (pointAt ω) family used bound := by
  intro hUnion
  exact hω (h.large_used_subset hUnion)

theorem TaoSection7Case3EStarUsedLargeTriangleSandwich.not_large_union_of_not_mem_subset
    {Ω : Type*} [Fintype Ω]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {used localAllowed : Set ℕ} {allowed : Finset ℕ} {bound : ℕ → ℝ}
    (h :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAt family EStarUsed used allowed bound)
    (hlocal : localAllowed ⊆ used)
    {ω : Ω} (hω : ω ∉ EStarUsed) :
    ¬ taoSection7Case3LargeTriangleUnion (pointAt ω) family localAllowed bound := by
  intro hUnion
  exact h.not_large_union_of_not_mem hω
    (by
      rcases hUnion with ⟨p, hp, hpLarge⟩
      exact ⟨p, hlocal hp, hpLarge⟩)

theorem TaoSection7Case3EStarUsedLargeTriangleSandwich.not_large_event_of_not_mem
    {Ω : Type*} [Fintype Ω]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {used : Set ℕ} {allowed : Finset ℕ} {bound : ℕ → ℝ}
    (h :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAt family EStarUsed used allowed bound)
    {ω : Ω} (hω : ω ∉ EStarUsed)
    {p : ℕ} (hp : p ∈ used) :
    ¬ taoSection7Case3LargeTriangleEvent (pointAt ω) family p (bound p) := by
  intro hpLarge
  exact hω (h.large_used_subset ⟨p, hp, hpLarge⟩)

theorem TaoSection7Case3EStarUsedLargeTriangleSandwich.triangle_size_lt_of_not_mem
    {Ω : Type*} [Fintype Ω]
    {pointAt : Ω → ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {used : Set ℕ} {allowed : Finset ℕ} {bound : ℕ → ℝ}
    (h :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAt family EStarUsed used allowed bound)
    {ω : Ω} (hω : ω ∉ EStarUsed)
    {p : ℕ} (hp : p ∈ used)
    {Δ : TaoSection7Triangle}
    (hΔ : Δ ∈ family)
    (hmem : Δ.Mem (pointAt ω p)) :
    Δ.size < bound p := by
  by_contra hnot
  have hlarge : bound p ≤ Δ.size := le_of_not_gt hnot
  exact hω (h.large_used_subset ⟨p, hp, Δ, hΔ, hmem, hlarge⟩)

theorem taoSection7Case3_not_large_event_of_not_union
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {allowed : Set ℕ} {bound : ℕ → ℝ}
    (hnotUnion :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed bound)
    {p : ℕ} (hp : p ∈ allowed) :
    ¬ taoSection7Case3LargeTriangleEvent pointAt family p (bound p) := by
  intro hpEvent
  exact hnotUnion ⟨p, hp, hpEvent⟩

theorem taoSection7Case3_triangle_size_lt_of_not_large_event
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {p : ℕ} {s' : ℝ} {Δ : TaoSection7Triangle}
    (hnotEvent :
      ¬ taoSection7Case3LargeTriangleEvent pointAt family p s')
    (hΔ : Δ ∈ family)
    (hmem : Δ.Mem (pointAt p)) :
    Δ.size < s' := by
  by_contra hnot
  have hlarge : s' ≤ Δ.size := le_of_not_gt hnot
  exact hnotEvent ⟨Δ, hΔ, hmem, hlarge⟩

theorem taoSection7Case3_triangle_size_lt_of_not_large_union
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {allowed : Set ℕ} {bound : ℕ → ℝ} {p : ℕ}
    (hnotUnion :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed bound)
    (hp : p ∈ allowed)
    {Δ : TaoSection7Triangle}
    (hΔ : Δ ∈ family)
    (hmem : Δ.Mem (pointAt p)) :
    Δ.size < bound p := by
  exact
    taoSection7Case3_triangle_size_lt_of_not_large_event
      (pointAt := pointAt) (family := family) (p := p) (s' := bound p)
      (taoSection7Case3_not_large_event_of_not_union
        (pointAt := pointAt) (family := family) hnotUnion hp)
      hΔ hmem

theorem taoSection7Case3_triangle_size_lt_of_not_large_union_source_bound
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {allowed : Set ℕ} {A p : ℕ}
    (hnotUnion :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed
          (taoSection7Case3LargeTriangleBound A))
    (hp : p ∈ allowed)
    {Δ : TaoSection7Triangle}
    (hΔ : Δ ∈ family)
    (hmem : Δ.Mem (pointAt p)) :
    Δ.size < taoSection7Case3LargeTriangleBound A p := by
  exact
    taoSection7Case3_triangle_size_lt_of_not_large_union
      (pointAt := pointAt) (family := family) (allowed := allowed)
      (bound := taoSection7Case3LargeTriangleBound A) hnotUnion hp hΔ hmem

/--
Monotone bridge for routes whose probability event uses an exponent `Aevent`
that is no larger than the deterministic recurrence exponent `Kcut`.
-/
theorem taoSection7Case3_triangle_size_lt_Kcut_of_not_large_union_event
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {allowed : Set ℕ} {Aevent Kcut p : ℕ}
    (hAK : Aevent ≤ Kcut)
    (hnotUnion :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed
          (taoSection7Case3LargeTriangleBound Aevent))
    (hp : p ∈ allowed)
    {Δ : TaoSection7Triangle}
    (hΔ : Δ ∈ family)
    (hmem : Δ.Mem (pointAt p)) :
    Δ.size < taoSection7Case3LargeTriangleBound Kcut p :=
  lt_of_lt_of_le
    (taoSection7Case3_triangle_size_lt_of_not_large_union_source_bound
      (A := Aevent) (p := p) (hnotUnion := hnotUnion) hp hΔ hmem)
    (taoSection7Case3_largeTriangleBound_event_le_Kcut
      (Aevent := Aevent) (Kcut := Kcut) (p := p) hAK)

theorem taoSection7SourceBlackPoint_of_not_sourceWhitePoint
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7Point}
    (hnotWhite : ¬ taoSection7SourceWhitePoint n xi epsilon p) :
    taoSection7SourceBlackPoint n xi epsilon p := by
  unfold taoSection7SourceWhitePoint at hnotWhite
  unfold taoSection7SourceBlackPoint
  by_contra hnotBlack
  exact hnotWhite
    ((taoSection7White_iff_not_black epsilon
      (taoSection7ThetaResidue n xi p.j p.l)).2 hnotBlack)

theorem taoSection7SourceBlackInDomain_of_not_sourceWhitePoint
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7Point}
    (hdomain : taoSection7SourcePointInDomain J p)
    (hnotWhite : ¬ taoSection7SourceWhitePoint n xi epsilon p) :
    taoSection7SourceBlackInDomain n xi epsilon J p :=
  ⟨hdomain, taoSection7SourceBlackPoint_of_not_sourceWhitePoint hnotWhite⟩

/--
Low-window plus source domain/cover data produces a triangle witness at a
non-white offset.
-/
theorem taoSection7Case3_low_window_produces_source_triangle_offset
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {P start threshold : ℕ}
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hblock : start + threshold < P)
    (hWwhite :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        (W q ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt q)))
    (hdomain :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7SourcePointInDomain J (pointAt q))
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ q : ℕ, q ∈ Finset.Icc start (start + threshold) ∧ ¬ W q ∧
      ∃ Δ : TaoSection7Triangle, Δ ∈ family ∧ Δ.Mem (pointAt q) := by
  rcases taoSection7Case3_low_window_forces_nonwhite_in_block
      W hlow hblock with ⟨q, hq, hnotW⟩
  refine ⟨q, hq, hnotW, ?_⟩
  exact (hcover (pointAt q)).1
    (taoSection7SourceBlackInDomain_of_not_sourceWhitePoint
      (hdomain q hq)
      (by
        intro hwhite
        exact hnotW ((hWwhite q hq).2 hwhite)))

/--
Composite Case 3 support adapter: if the `P`-window is low, the inspected
block fits inside the source/`E*` offset range, and the large-triangle union
`E*` does not occur, then some non-white offset lies in a black triangle whose
size is strictly below the source threshold `4^A(1+p)^3`.
-/
theorem taoSection7Case3_low_window_produces_small_source_triangle_offset
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {allowed : Set ℕ} {P start threshold : ℕ}
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hblock : start + threshold < P)
    (hallowed :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) → q ∈ allowed)
    (hnotUnion :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed
          (taoSection7Case3LargeTriangleBound A))
    (hWwhite :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        (W q ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt q)))
    (hdomain :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7SourcePointInDomain J (pointAt q))
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
  ∃ q : ℕ, q ∈ Finset.Icc start (start + threshold) ∧ ¬ W q ∧
      ∃ Δ : TaoSection7Triangle, Δ ∈ family ∧ Δ.Mem (pointAt q) ∧
        Δ.size < taoSection7Case3LargeTriangleBound A q := by
  rcases taoSection7Case3_low_window_produces_source_triangle_offset
      W pointAt hlow hblock hWwhite hdomain hcover with
    ⟨q, hq, hnotW, Δ, hΔ, hmem⟩
  exact
    ⟨q, hq, hnotW, Δ, hΔ, hmem,
      taoSection7Case3_triangle_size_lt_of_not_large_union_source_bound
        (pointAt := pointAt) (family := family) (allowed := allowed)
        (A := A) hnotUnion (hallowed q hq) hΔ hmem⟩

/--
Generic-bound version of the low-window support adapter.  This carries the
same large-triangle threshold through the no-large-union hypothesis and the
produced small-triangle witness, so repaired base-`Kcut` routes do not fall
back to the printed base-4 threshold.
-/
theorem taoSection7Case3_low_window_produces_small_triangle_offset_of_bound
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {allowed : Set ℕ} {bound : ℕ → ℝ}
    {P start threshold : ℕ}
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hblock : start + threshold < P)
    (hallowed :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) → q ∈ allowed)
    (hnotUnion :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed bound)
    (hWwhite :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        (W q ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt q)))
    (hdomain :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7SourcePointInDomain J (pointAt q))
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ q : ℕ, q ∈ Finset.Icc start (start + threshold) ∧ ¬ W q ∧
      ∃ Δ : TaoSection7Triangle, Δ ∈ family ∧ Δ.Mem (pointAt q) ∧
        Δ.size < bound q := by
  rcases taoSection7Case3_low_window_produces_source_triangle_offset
      W pointAt hlow hblock hWwhite hdomain hcover with
    ⟨q, hq, hnotW, Δ, hΔ, hmem⟩
  exact
    ⟨q, hq, hnotW, Δ, hΔ, hmem,
      taoSection7Case3_triangle_size_lt_of_not_large_union
        (pointAt := pointAt) (family := family) (allowed := allowed)
        (bound := bound) hnotUnion (hallowed q hq) hΔ hmem⟩

/--
Abstract remaining-window room for a Case 3 local advance.  The later source
producer should prove this from the source-calibrated finite exit budget before
one asks for the next offset.
-/
def taoSection7Case3AdvanceHeadroom
    (B : ℕ → ℕ) (P p : ℕ) : Prop :=
  B p < P

/--
Remaining-room premise at the black pivot selected inside the local window.
The concrete source proof should instantiate `ExitBound` with the
source-calibrated finite exit budget used for the later point.
-/
def taoSection7Case3ExitRoom
    (ExitBound : ℕ → ℕ) (P q : ℕ) : Prop :=
  ExitBound q < P

/-- Abstract height-exit endpoint after the selected black pivot. -/
def taoSection7Case3HeightExitBound
    (gapBound : ℕ → ℕ) (q : ℕ) : ℕ :=
  q + gapBound q

/-- Natural version of Tao's Case 3 gap `10 * 4^A(1+q)^3`. -/
def taoSection7Case3ExitGapBound (A q : ℕ) : ℕ :=
  10 * 4 ^ A * (q + 1) ^ 3

/--
Parameterized natural Case 3 exit gap.

This is the natural-number companion to
`taoSection7Case3LargeTriangleBoundWithBase`; the printed route is recovered at
base `4`.
-/
def taoSection7Case3ExitGapBoundWithBase (base A q : ℕ) : ℕ :=
  10 * base ^ A * (q + 1) ^ 3

@[simp] theorem taoSection7Case3ExitGapBoundWithBase_four
    (A q : ℕ) :
    taoSection7Case3ExitGapBoundWithBase 4 A q =
      taoSection7Case3ExitGapBound A q := by
  rfl

theorem taoSection7Case3ExitGapBound_mono (A : ℕ) :
    Monotone (taoSection7Case3ExitGapBound A) := by
  intro q r hqr
  dsimp [taoSection7Case3ExitGapBound]
  gcongr

theorem taoSection7Case3ExitGapBoundWithBase_mono (base A : ℕ) :
    Monotone (taoSection7Case3ExitGapBoundWithBase base A) := by
  intro q r hqr
  dsimp [taoSection7Case3ExitGapBoundWithBase]
  gcongr

/--
Abstract vertical-step sufficiency predicate for exiting the old triangle.
The path/index bridge that proves such steps from source data is separate.
-/
def taoSection7Case3SufficientVerticalSteps
    (A pivot n : ℕ) : Prop :=
  taoSection7Case3LargeTriangleBound A pivot ≤ (n : ℝ) * Real.log 2

theorem taoSection7Case3_one_le_ten_mul_log_two :
    (1 : ℝ) ≤ 10 * Real.log 2 := by
  have hlog : (1 / 10 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 10 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  nlinarith

theorem taoSection7Case3_exitGapBound_real_eq
    (A q : ℕ) :
    (taoSection7Case3ExitGapBound A q : ℝ) =
      10 * taoSection7Case3LargeTriangleBound A q := by
  simp [taoSection7Case3ExitGapBound,
    taoSection7Case3LargeTriangleBound]
  ring

theorem taoSection7Case3_largeTriangleBound_le_exitGapBound_log_two
    (A q : ℕ) :
    taoSection7Case3LargeTriangleBound A q ≤
      (taoSection7Case3ExitGapBound A q : ℝ) * Real.log 2 := by
  have hnonneg : 0 ≤ taoSection7Case3LargeTriangleBound A q := by
    simp [taoSection7Case3LargeTriangleBound]
    positivity
  have hscale :
      taoSection7Case3LargeTriangleBound A q ≤
        taoSection7Case3LargeTriangleBound A q * (10 * Real.log 2) := by
    calc
      taoSection7Case3LargeTriangleBound A q =
          taoSection7Case3LargeTriangleBound A q * 1 := by ring
      _ ≤ taoSection7Case3LargeTriangleBound A q * (10 * Real.log 2) :=
          mul_le_mul_of_nonneg_left
            taoSection7Case3_one_le_ten_mul_log_two hnonneg
  calc
    taoSection7Case3LargeTriangleBound A q
        ≤ taoSection7Case3LargeTriangleBound A q * (10 * Real.log 2) := hscale
    _ = (taoSection7Case3ExitGapBound A q : ℝ) * Real.log 2 := by
      rw [taoSection7Case3_exitGapBound_real_eq]
      ring

theorem taoSection7Case3_sufficientVerticalSteps_exitGapBound
    (A q : ℕ) :
    taoSection7Case3SufficientVerticalSteps A q
      (taoSection7Case3ExitGapBound A q) :=
  taoSection7Case3_largeTriangleBound_le_exitGapBound_log_two A q

theorem taoSection7Case3_exitGapBoundWithBase_real_eq
    (base A q : ℕ) :
    (taoSection7Case3ExitGapBoundWithBase base A q : ℝ) =
      10 * taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q := by
  simp [taoSection7Case3ExitGapBoundWithBase,
    taoSection7Case3LargeTriangleBoundWithBase]
  ring

theorem taoSection7Case3_largeTriangleBoundWithBase_le_exitGapBoundWithBase_log_two
    (base A q : ℕ) :
    taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q ≤
      (taoSection7Case3ExitGapBoundWithBase base A q : ℝ) * Real.log 2 := by
  have hnonneg :
      0 ≤ taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q := by
    simp [taoSection7Case3LargeTriangleBoundWithBase]
    positivity
  have hscale :
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q ≤
        taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q *
          (10 * Real.log 2) := by
    calc
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q =
          taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q * 1 := by
            ring
      _ ≤
          taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q *
            (10 * Real.log 2) :=
          mul_le_mul_of_nonneg_left
            taoSection7Case3_one_le_ten_mul_log_two hnonneg
  calc
    taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q
        ≤
          taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q *
            (10 * Real.log 2) := hscale
    _ = (taoSection7Case3ExitGapBoundWithBase base A q : ℝ) *
          Real.log 2 := by
      rw [taoSection7Case3_exitGapBoundWithBase_real_eq]
      ring

/--
Generic scale compatibility between a large-triangle threshold and the natural
gap bound used by the deterministic Case 3 recurrence.
-/
structure TaoSection7Case3RecurrenceScale
    (bound : ℕ → ℝ) (gapBound : ℕ → ℕ) : Prop where
  gap_mono : Monotone gapBound
  sufficient : ∀ q, bound q ≤ (gapBound q : ℝ) * Real.log 2

theorem taoSection7Case3RecurrenceScale_baseKcut
    (base Kcut : ℕ) :
    TaoSection7Case3RecurrenceScale
      (taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut)
      (taoSection7Case3ExitGapBoundWithBase base Kcut) where
  gap_mono := taoSection7Case3ExitGapBoundWithBase_mono base Kcut
  sufficient :=
    taoSection7Case3_largeTriangleBoundWithBase_le_exitGapBoundWithBase_log_two
      base Kcut

theorem taoSection7Case3_sufficientVerticalSteps_of_exitGapBound_le
    {A q n : ℕ}
    (hn : taoSection7Case3ExitGapBound A q ≤ n) :
    taoSection7Case3SufficientVerticalSteps A q n := by
  have hbase :
      taoSection7Case3LargeTriangleBound A q ≤
        (taoSection7Case3ExitGapBound A q : ℝ) * Real.log 2 :=
    taoSection7Case3_largeTriangleBound_le_exitGapBound_log_two A q
  have hlog2_nonneg : 0 ≤ Real.log 2 :=
    le_of_lt (Real.log_pos (by norm_num))
  have hn_real :
      (taoSection7Case3ExitGapBound A q : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  exact hbase.trans (mul_le_mul_of_nonneg_right hn_real hlog2_nonneg)

theorem taoSection7Case3_sufficientVerticalSteps_of_concreteHeightExit
    {A q candidate : ℕ}
    (hcandidate :
      taoSection7Case3HeightExitBound
        (taoSection7Case3ExitGapBound A) q < candidate) :
    taoSection7Case3SufficientVerticalSteps A q (candidate - q) := by
  apply taoSection7Case3_sufficientVerticalSteps_of_exitGapBound_le
  dsimp [taoSection7Case3HeightExitBound] at hcandidate
  omega

/--
First offset in the later search block.  The source inequality
`q + gap < p'` is represented by `q + gap + 1 <= p'`.
-/
def taoSection7Case3LaterSearchStart
    (gapBound : ℕ → ℕ) (q : ℕ) : ℕ :=
  taoSection7Case3HeightExitBound gapBound q + 1

/--
Endpoint of the `threshold + 1` later-search block.  This is the safe
instantiation target for `taoSection7Case3ExitRoom` when the future source
step must still find a later non-white offset after the strict exit gap.
-/
def taoSection7Case3LaterSearchBound
    (gapBound : ℕ → ℕ) (threshold q : ℕ) : ℕ :=
  taoSection7Case3LaterSearchStart gapBound q + threshold

/--
Exact Kcut stop-to-stop endpoint for the Case 3 deterministic recurrence.
This is the source recurrence `q + 10 * 4^Kcut * (q+1)^3 + 1 + T`, distinct
from the conservative right-endpoint window envelope used before the pivot is
known.
-/
def taoSection7Case3NextBound (Kcut T q : ℕ) : ℕ :=
  taoSection7Case3LaterSearchBound
    (taoSection7Case3ExitGapBound Kcut) T q

/--
Base-parameterized stop-to-stop endpoint for the Case 3 deterministic
recurrence.  This is the base-aware companion to
`taoSection7Case3NextBound`, using the same repaired gap as
`taoSection7Case3LargeTriangleBoundWithBase`.
-/
def taoSection7Case3BaseKcutNextBound (base Kcut T q : ℕ) : ℕ :=
  taoSection7Case3LaterSearchBound
    (taoSection7Case3ExitGapBoundWithBase base Kcut) T q

@[simp] theorem taoSection7Case3BaseKcutNextBound_four
    (Kcut T q : ℕ) :
    taoSection7Case3BaseKcutNextBound 4 Kcut T q =
      taoSection7Case3NextBound Kcut T q := by
  rfl

theorem taoSection7Case3NextBound_eq
    (Kcut T q : ℕ) :
    taoSection7Case3NextBound Kcut T q =
      q + taoSection7Case3ExitGapBound Kcut q + 1 + T := by
  rfl

theorem taoSection7Case3BaseKcutNextBound_eq
    (base Kcut T q : ℕ) :
    taoSection7Case3BaseKcutNextBound base Kcut T q =
      q + taoSection7Case3ExitGapBoundWithBase base Kcut q + 1 + T := by
  rfl

theorem taoSection7Case3NextBound_mono (Kcut T : ℕ) :
    Monotone (taoSection7Case3NextBound Kcut T) := by
  intro q r hqr
  have hgap :
      taoSection7Case3ExitGapBound Kcut q ≤
        taoSection7Case3ExitGapBound Kcut r :=
    taoSection7Case3ExitGapBound_mono Kcut hqr
  dsimp [taoSection7Case3NextBound,
    taoSection7Case3LaterSearchBound,
    taoSection7Case3LaterSearchStart,
    taoSection7Case3HeightExitBound]
  omega

theorem taoSection7Case3BaseKcutNextBound_mono (base Kcut T : ℕ) :
    Monotone (taoSection7Case3BaseKcutNextBound base Kcut T) := by
  intro q r hqr
  have hgap :
      taoSection7Case3ExitGapBoundWithBase base Kcut q ≤
        taoSection7Case3ExitGapBoundWithBase base Kcut r :=
    taoSection7Case3ExitGapBoundWithBase_mono base Kcut hqr
  dsimp [taoSection7Case3BaseKcutNextBound,
    taoSection7Case3LaterSearchBound,
    taoSection7Case3LaterSearchStart,
    taoSection7Case3HeightExitBound]
  omega

theorem taoSection7Case3_le_nextBound (Kcut T q : ℕ) :
    q ≤ taoSection7Case3NextBound Kcut T q := by
  dsimp [taoSection7Case3NextBound,
    taoSection7Case3LaterSearchBound,
    taoSection7Case3LaterSearchStart,
    taoSection7Case3HeightExitBound]
  omega

theorem taoSection7Case3_le_baseKcutNextBound (base Kcut T q : ℕ) :
    q ≤ taoSection7Case3BaseKcutNextBound base Kcut T q := by
  dsimp [taoSection7Case3BaseKcutNextBound,
    taoSection7Case3LaterSearchBound,
    taoSection7Case3LaterSearchStart,
    taoSection7Case3HeightExitBound]
  omega

theorem taoSection7Case3_lt_nextBound (Kcut T q : ℕ) :
    q < taoSection7Case3NextBound Kcut T q := by
  dsimp [taoSection7Case3NextBound,
    taoSection7Case3LaterSearchBound,
    taoSection7Case3LaterSearchStart,
    taoSection7Case3HeightExitBound]
  omega

theorem taoSection7Case3_lt_baseKcutNextBound (base Kcut T q : ℕ) :
    q < taoSection7Case3BaseKcutNextBound base Kcut T q := by
  dsimp [taoSection7Case3BaseKcutNextBound,
    taoSection7Case3LaterSearchBound,
    taoSection7Case3LaterSearchStart,
    taoSection7Case3HeightExitBound]
  omega

def taoSection7Case3IterateRoom
    (Next : ℕ → ℕ) (R start P : ℕ) : Prop :=
  (Next^[R]) start < P

theorem taoSection7Case3_le_iterate_of_le_self
    (Next : ℕ → ℕ) (hnext : ∀ q : ℕ, q ≤ Next q)
    (R start : ℕ) :
    start ≤ (Next^[R]) start := by
  induction R with
  | zero =>
      simp
  | succ R ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (hnext _)

theorem taoSection7Case3_iterate_le_iterate_of_le
    (Next : ℕ → ℕ) (hnext : ∀ q : ℕ, q ≤ Next q)
    {i R start : ℕ} (hi : i ≤ R) :
    (Next^[i]) start ≤ (Next^[R]) start := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi
  subst R
  rw [Nat.add_comm i k, Function.iterate_add_apply]
  exact
    taoSection7Case3_le_iterate_of_le_self
      Next hnext k ((Next^[i]) start)

theorem taoSection7Case3_nextBound_iterate_le_iterate_of_le
    {Kcut T i R start : ℕ} (hi : i ≤ R) :
    ((taoSection7Case3NextBound Kcut T)^[i]) start ≤
      ((taoSection7Case3NextBound Kcut T)^[R]) start :=
  taoSection7Case3_iterate_le_iterate_of_le
    (taoSection7Case3NextBound Kcut T)
    (taoSection7Case3_le_nextBound Kcut T) hi

theorem taoSection7Case3_baseKcutNextBound_iterate_le_iterate_of_le
    {base Kcut T i R start : ℕ} (hi : i ≤ R) :
    ((taoSection7Case3BaseKcutNextBound base Kcut T)^[i]) start ≤
      ((taoSection7Case3BaseKcutNextBound base Kcut T)^[R]) start :=
  taoSection7Case3_iterate_le_iterate_of_le
    (taoSection7Case3BaseKcutNextBound base Kcut T)
    (taoSection7Case3_le_baseKcutNextBound base Kcut T) hi

def taoSection7Case3NextBoundIterateRoom
    (Kcut T R start P : ℕ) : Prop :=
  taoSection7Case3IterateRoom
    (taoSection7Case3NextBound Kcut T) R start P

def taoSection7Case3BaseKcutNextBoundIterateRoom
    (base Kcut T R start P : ℕ) : Prop :=
  taoSection7Case3IterateRoom
    (taoSection7Case3BaseKcutNextBound base Kcut T) R start P

theorem taoSection7Case3_nextBound_iterate_lt_of_iterateRoom
    {Kcut T R start P i : ℕ}
    (hroom :
      taoSection7Case3NextBoundIterateRoom Kcut T R start P)
    (hi : i ≤ R) :
    ((taoSection7Case3NextBound Kcut T)^[i]) start < P :=
  lt_of_le_of_lt
    (taoSection7Case3_nextBound_iterate_le_iterate_of_le
      (Kcut := Kcut) (T := T) (start := start) hi)
    hroom

theorem taoSection7Case3_baseKcutNextBound_iterate_lt_of_iterateRoom
    {base Kcut T R start P i : ℕ}
    (hroom :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut T R start P)
    (hi : i ≤ R) :
    ((taoSection7Case3BaseKcutNextBound base Kcut T)^[i]) start < P :=
  lt_of_le_of_lt
    (taoSection7Case3_baseKcutNextBound_iterate_le_iterate_of_le
      (base := base) (Kcut := Kcut) (T := T) (start := start) hi)
    hroom

theorem taoSection7Case3_nextBound_exitRoom_of_iterateRoom
    {Kcut T R start P i : ℕ}
    (hroom :
      taoSection7Case3NextBoundIterateRoom Kcut T R start P)
    (hi : i.succ ≤ R) :
    taoSection7Case3ExitRoom
      (taoSection7Case3NextBound Kcut T) P
      (((taoSection7Case3NextBound Kcut T)^[i]) start) := by
  simpa [taoSection7Case3ExitRoom, Function.iterate_succ_apply']
    using
      taoSection7Case3_nextBound_iterate_lt_of_iterateRoom
        (Kcut := Kcut) (T := T) (R := R) (start := start)
        (P := P) (i := i.succ) hroom hi

theorem taoSection7Case3_baseKcutNextBound_exitRoom_of_iterateRoom
    {base Kcut T R start P i : ℕ}
    (hroom :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut T R start P)
    (hi : i.succ ≤ R) :
    taoSection7Case3ExitRoom
      (taoSection7Case3BaseKcutNextBound base Kcut T) P
      (((taoSection7Case3BaseKcutNextBound base Kcut T)^[i]) start) := by
  simpa [taoSection7Case3ExitRoom, Function.iterate_succ_apply']
    using
      taoSection7Case3_baseKcutNextBound_iterate_lt_of_iterateRoom
        (base := base) (Kcut := Kcut) (T := T) (R := R)
        (start := start) (P := P) (i := i.succ) hroom hi

/--
When `allowed = {p | p < P}`, strict room for `NextBound` supplies the
block-allowed proof needed by the outside-`E*` one-step lemmas.  This is only
local exclusion provenance; it is not a probability estimate for `E*_used`.
-/
theorem taoSection7Case3_nextBound_laterSearch_mem_lt_window
    {Kcut T P q p : ℕ}
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3NextBound Kcut T) P q)
    (hp :
      p ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound Kcut) q)
        (taoSection7Case3LaterSearchStart
          (taoSection7Case3ExitGapBound Kcut) q + T)) :
    p < P := by
  have hp_le :
      p ≤
        taoSection7Case3LaterSearchStart
            (taoSection7Case3ExitGapBound Kcut) q + T :=
    (Finset.mem_Icc.mp hp).2
  exact lt_of_le_of_lt hp_le (by
    simpa [taoSection7Case3ExitRoom, taoSection7Case3NextBound,
      taoSection7Case3LaterSearchBound] using hroom)

/-- Low-white event for the restarted Case 3 `P`-window. -/
def taoSection7Case3LowWhite
    (W : ℕ → Prop) [DecidablePred W] (P T : ℕ) : Prop :=
  taoSection7Case3WindowWhiteCount W P ≤ T

/--
Sample-space version of the restarted low-white event.  This is the event
whose probability is later bounded in the inner `(7.56)` ledger.
-/
noncomputable def taoSection7Case3LowWhiteEvent
    {Ω : Type*} (W : Ω → ℕ → Prop) [∀ ω, DecidablePred (W ω)]
    (P T : ℕ) : Set Ω :=
  {ω | taoSection7Case3LowWhite (W ω) P T}

/--
Outside the low-white event, the window has strictly more than `T` white
offsets.  This is the Nat-polarity helper used by the later exponential-tail
bridge for `(7.54)`.
-/
theorem taoSection7Case3WindowWhiteCount_succ_le_of_not_lowWhiteEvent
    {Ω : Type*} {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {P T : ℕ} {ω : Ω}
    (hnotLow : ω ∉ taoSection7Case3LowWhiteEvent W P T) :
    T + 1 ≤ taoSection7Case3WindowWhiteCount (W ω) P := by
  have hnot :
      ¬ taoSection7Case3WindowWhiteCount (W ω) P ≤ T := by
    simpa [taoSection7Case3LowWhiteEvent, taoSection7Case3LowWhite]
      using hnotLow
  omega

/--
Local provenance that the whole inspected block is included in the same
allowed set used by the `E*_used`/`E*_allowed` probability estimate.
This is intentionally stronger than merely knowing a selected stop is `< P`.
-/
structure TaoSection7Case3AllowedBlockTrace
    (allowed : Set ℕ) (start T : ℕ) : Prop where
  block_allowed :
    ∀ p : ℕ, p ∈ Finset.Icc start (start + T) → p ∈ allowed

/--
Generic later-search trace for any calibrated exit gap.  If the whole
later-search block fits in the `P` window, then each offset in that block is
allowed for the range `{p | p < P}`.
-/
theorem TaoSection7Case3AllowedBlockTrace.range_of_laterSearch_exitRoom
    {gapBound : ℕ → ℕ} {T P q : ℕ}
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound T) P q) :
    TaoSection7Case3AllowedBlockTrace
      {p : ℕ | p < P}
      (taoSection7Case3LaterSearchStart gapBound q)
      T := by
  refine ⟨?_⟩
  intro p hp
  have hp_le :
      p ≤ taoSection7Case3LaterSearchStart gapBound q + T :=
    (Finset.mem_Icc.mp hp).2
  exact lt_of_le_of_lt hp_le (by
    simpa [taoSection7Case3ExitRoom, taoSection7Case3LaterSearchBound]
      using hroom)

/--
The full local envelope from `q + 1` through the later-search right endpoint
contains the minimized first hit whenever that first hit is bounded by the
later-search candidate.

This is intentionally different from the later-search block itself: the
minimized first hit may occur before the strict-exit search interval.
-/
theorem TaoSection7Case3AllowedBlockTrace.first_mem_of_le_laterSearch_candidate
    {allowed : Set ℕ} {gapBound : ℕ → ℕ}
    {threshold q candidate first : ℕ}
    (hblock :
      TaoSection7Case3AllowedBlockTrace allowed (q + 1)
        (taoSection7Case3LaterSearchBound gapBound threshold q - (q + 1)))
    (hcandidate :
      candidate ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchBound gapBound threshold q))
    (hqfirst : q < first)
    (hfirst_le_candidate : first ≤ candidate) :
    first ∈ allowed := by
  refine hblock.block_allowed first (Finset.mem_Icc.mpr ?_)
  constructor
  · omega
  · have hcandidate_le :
        candidate ≤ taoSection7Case3LaterSearchBound gapBound threshold q :=
      (Finset.mem_Icc.mp hcandidate).2
    have hright :
        q + 1 +
            (taoSection7Case3LaterSearchBound gapBound threshold q -
              (q + 1)) =
          taoSection7Case3LaterSearchBound gapBound threshold q := by
      have hq_le_right :
          q + 1 ≤ taoSection7Case3LaterSearchBound gapBound threshold q := by
        dsimp [taoSection7Case3LaterSearchBound,
          taoSection7Case3LaterSearchStart,
          taoSection7Case3HeightExitBound]
        omega
      omega
    omega

/--
A fixed finite range that reaches the later-search right endpoint supplies the
full local envelope from `q + 1` through that endpoint.
-/
theorem TaoSection7Case3AllowedBlockTrace.fullEnvelope_of_right_le_range
    {gapBound : ℕ → ℕ} {threshold q Pmax : ℕ}
    (hright :
      taoSection7Case3LaterSearchBound gapBound threshold q ≤ Pmax) :
    TaoSection7Case3AllowedBlockTrace
      {p : ℕ | p ∈ Finset.range (Pmax + 1)}
      (q + 1)
      (taoSection7Case3LaterSearchBound gapBound threshold q - (q + 1)) := by
  refine ⟨?_⟩
  intro p hp
  have hp_le :
      p ≤ q + 1 +
        (taoSection7Case3LaterSearchBound gapBound threshold q - (q + 1)) :=
    (Finset.mem_Icc.mp hp).2
  have hq_le_right :
      q + 1 ≤ taoSection7Case3LaterSearchBound gapBound threshold q := by
    dsimp [taoSection7Case3LaterSearchBound,
      taoSection7Case3LaterSearchStart,
      taoSection7Case3HeightExitBound]
    omega
  have hp_le_right :
      p ≤ taoSection7Case3LaterSearchBound gapBound threshold q := by
    omega
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hp_le_right.trans hright))

/-- Local full envelope that can contain a minimized first hit before the
strict later-search interval. -/
def taoSection7Case3LocalSelectedEnvelope
    (gapBound : ℕ → ℕ) (threshold q : ℕ) : Set ℕ :=
  {p | p ∈ Finset.Icc (q + 1)
    (taoSection7Case3LaterSearchBound gapBound threshold q)}

/--
The local selected envelope supplies the full block trace over its own
interval.  This is the noncircular local block input for the one-state
local-envelope sandwich bridge.
-/
theorem TaoSection7Case3AllowedBlockTrace.localSelectedEnvelope
    {gapBound : ℕ → ℕ} {threshold q : ℕ} :
    TaoSection7Case3AllowedBlockTrace
      (taoSection7Case3LocalSelectedEnvelope gapBound threshold q)
      (q + 1)
      (taoSection7Case3LaterSearchBound gapBound threshold q - (q + 1)) := by
  refine ⟨?_⟩
  intro p hp
  have hp_left : q + 1 ≤ p := (Finset.mem_Icc.mp hp).1
  have hp_le :
      p ≤ q + 1 +
        (taoSection7Case3LaterSearchBound gapBound threshold q - (q + 1)) :=
    (Finset.mem_Icc.mp hp).2
  have hq_le_right :
      q + 1 ≤ taoSection7Case3LaterSearchBound gapBound threshold q := by
    dsimp [taoSection7Case3LaterSearchBound,
      taoSection7Case3LaterSearchStart,
      taoSection7Case3HeightExitBound]
    omega
  have hp_right :
      p ≤ taoSection7Case3LaterSearchBound gapBound threshold q := by
    omega
  exact
    (by
      simpa [taoSection7Case3LocalSelectedEnvelope] using
        (Finset.mem_Icc.mpr ⟨hp_left, hp_right⟩))

/--
Membership in the base-Kcut local selected envelope gives the corresponding
one-step base-Kcut stop bound.
-/
theorem taoSection7Case3_le_baseKcutNextBound_of_mem_localSelectedEnvelope
    {base Kcut threshold q p : ℕ}
    (hp : p ∈ taoSection7Case3LocalSelectedEnvelope
      (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold q) :
    p ≤ taoSection7Case3BaseKcutNextBound base Kcut threshold q := by
  have hp_right :
      p ≤ taoSection7Case3LaterSearchBound
        (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold q :=
    (Finset.mem_Icc.mp
      (by
        simpa [taoSection7Case3LocalSelectedEnvelope] using hp)).2
  simpa [taoSection7Case3BaseKcutNextBound] using hp_right

/--
The local selected envelope at an intermediate active stop is contained in the
pre-trace deterministic carrier obtained by iterating the base-Kcut stop bound.
-/
theorem taoSection7Case3_localSelectedEnvelope_subset_baseKcutIterateRange
    {base Kcut threshold R start q i p : ℕ}
    (htrace_le :
      q ≤ ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i]) start)
    (hi : i + 1 ≤ R)
    (hp : p ∈ taoSection7Case3LocalSelectedEnvelope
      (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold q) :
    p ∈ Finset.range
      (((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[R]) start + 1) := by
  let B := taoSection7Case3BaseKcutNextBound base Kcut threshold
  have hp_le_Bq : p ≤ B q := by
    have hp' :
        p ≤ taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold q :=
      (Finset.mem_Icc.mp
        (by
          simpa [taoSection7Case3LocalSelectedEnvelope] using hp)).2
    simpa [B, taoSection7Case3BaseKcutNextBound] using hp'
  have hBq_le :
      B q ≤ B ((B^[i]) start) := by
    exact
      taoSection7Case3BaseKcutNextBound_mono base Kcut threshold
        (by simpa [B] using htrace_le)
  have hBi_le :
      B ((B^[i]) start) ≤ (B^[R]) start := by
    have hiter :
        (B^[i + 1]) start ≤ (B^[R]) start := by
      simpa [B] using
        taoSection7Case3_baseKcutNextBound_iterate_le_iterate_of_le
          (base := base) (Kcut := Kcut) (T := threshold)
          (i := i + 1) (R := R) (start := start) hi
    simpa [Function.iterate_succ_apply'] using hiter
  have hp_le : p ≤ (B^[R]) start := hp_le_Bq.trans (hBq_le.trans hBi_le)
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa [B] using hp_le))

/--
If the base-Kcut iterate room extends two more deterministic steps beyond the
current traced state, then every point in the local selected envelope has
successor exit room.  This is the narrow room socket needed after a selected
pivot is known, unlike the stronger universal `hroom_next` callback.
-/
theorem taoSection7Case3_exitRoom_of_baseKcutIterateRoom_of_mem_localSelectedEnvelope
    {base Kcut threshold R start P q i p : ℕ}
    (hroom :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut threshold R start P)
    (htrace_le :
      q ≤ ((taoSection7Case3BaseKcutNextBound base Kcut threshold)^[i]) start)
    (hi : i + 2 ≤ R)
    (hp : p ∈ taoSection7Case3LocalSelectedEnvelope
      (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold q) :
    taoSection7Case3ExitRoom
      (taoSection7Case3LaterSearchBound
        (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold)
      P p := by
  let B := taoSection7Case3BaseKcutNextBound base Kcut threshold
  have hp_le_Bq : p ≤ B q := by
    have hp' :
        p ≤ taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBoundWithBase base Kcut) threshold q :=
      (Finset.mem_Icc.mp
        (by
          simpa [taoSection7Case3LocalSelectedEnvelope] using hp)).2
    simpa [B, taoSection7Case3BaseKcutNextBound] using hp'
  have hBq_le :
      B q ≤ B ((B^[i]) start) :=
    taoSection7Case3BaseKcutNextBound_mono base Kcut threshold
      (by simpa [B] using htrace_le)
  have hp_le_iter_succ : p ≤ (B^[i + 1]) start := by
    have hp_le : p ≤ B ((B^[i]) start) := hp_le_Bq.trans hBq_le
    simpa [B, Function.iterate_succ_apply'] using hp_le
  have hBp_le_iter_succ_succ : B p ≤ (B^[i + 2]) start := by
    have hmono :
        B p ≤ B ((B^[i + 1]) start) :=
      taoSection7Case3BaseKcutNextBound_mono base Kcut threshold
        (by simpa [B] using hp_le_iter_succ)
    simpa [B, Function.iterate_succ_apply', Nat.add_assoc] using hmono
  have hiter_le :
      (B^[i + 2]) start ≤ (B^[R]) start := by
    simpa [B] using
      taoSection7Case3_baseKcutNextBound_iterate_le_iterate_of_le
        (base := base) (Kcut := Kcut) (T := threshold)
        (i := i + 2) (R := R) (start := start) hi
  have hlt : B p < P :=
    lt_of_le_of_lt (hBp_le_iter_succ_succ.trans hiter_le)
      (by
        simpa [taoSection7Case3BaseKcutNextBoundIterateRoom,
          taoSection7Case3IterateRoom, B] using hroom)
  simpa [taoSection7Case3ExitRoom, taoSection7Case3BaseKcutNextBound, B] using hlt

/--
For the used-offset event `allowed = {p | p < P}`, strict room for the exact
Kcut `NextBound` supplies the local block-allowed trace consumed by outside
`E*` one-step lemmas.
-/
theorem TaoSection7Case3AllowedBlockTrace.range_of_nextBound_exitRoom
    {Kcut T P q : ℕ}
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3NextBound Kcut T) P q) :
    TaoSection7Case3AllowedBlockTrace
      {p : ℕ | p < P}
      (taoSection7Case3LaterSearchStart
        (taoSection7Case3ExitGapBound Kcut) q)
      T := by
  simpa [taoSection7Case3NextBound] using
    TaoSection7Case3AllowedBlockTrace.range_of_laterSearch_exitRoom
      (gapBound := taoSection7Case3ExitGapBound Kcut)
      (T := T) (P := P) (q := q) hroom

/--
Base-aware trace instantiation for repaired Case 3 scalar budgets.  This is
the deterministic counterpart of using
`taoSection7Case3LargeTriangleBoundWithBase` / `taoSection7Case3ExitGapBoundWithBase`
rather than the printed base-4 threshold.
-/
theorem TaoSection7Case3AllowedBlockTrace.range_of_baseKcutNextBound_exitRoom
    {base Kcut T P q : ℕ}
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3BaseKcutNextBound base Kcut T) P q) :
    TaoSection7Case3AllowedBlockTrace
      {p : ℕ | p < P}
      (taoSection7Case3LaterSearchStart
        (taoSection7Case3ExitGapBoundWithBase base Kcut) q)
      T := by
  simpa [taoSection7Case3BaseKcutNextBound] using
    TaoSection7Case3AllowedBlockTrace.range_of_laterSearch_exitRoom
      (gapBound := taoSection7Case3ExitGapBoundWithBase base Kcut)
      (T := T) (P := P) (q := q) hroom

/--
Generic inner `(7.56)` set contract: if every low-white sample outside both
the allowed large-triangle event and the slack Markov event is contradictory,
then the low-white event is contained in their union.
-/
theorem taoSection7Case3_lowWhite_subset_EStarUsed_union_FSlack
    {Ω : Type*} {LowWhite EStarUsed FSlack : Set Ω}
    (hcontr :
      ∀ ω : Ω, ω ∈ LowWhite → ω ∉ EStarUsed → ω ∉ FSlack → False) :
    LowWhite ⊆ EStarUsed ∪ FSlack := by
  intro ω hlow
  by_cases hE : ω ∈ EStarUsed
  · exact Or.inl hE
  · by_cases hF : ω ∈ FSlack
    · exact Or.inr hF
    · exact False.elim (hcontr ω hlow hE hF)

/--
Probability wrapper for the inner `(7.56)` ledger.  It deliberately has only
the two restarted bad events: `E*_used`/`E*_allowed` and slack-tuned `F*`.
The outer large-`j` contribution belongs to the separate `(7.54)` ledger.
-/
theorem taoSection7Case3_prob_lowWhite_le_of_inner756_budget
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    {LowWhite EStarUsed FSlack : Set Ω} {e f target : ℝ}
    (hsub : LowWhite ⊆ EStarUsed ∪ FSlack)
    (hE : pmfProb μ EStarUsed ≤ e)
    (hF : pmfProb μ FSlack ≤ f)
    (hbudget : e + f ≤ target) :
    pmfProb μ LowWhite ≤ target := by
  calc
    pmfProb μ LowWhite ≤ pmfProb μ (EStarUsed ∪ FSlack) :=
      pmfProb_mono μ hsub
    _ ≤ pmfProb μ EStarUsed + pmfProb μ FSlack :=
      pmfProb_union_le_add μ EStarUsed FSlack
    _ ≤ e + f := add_le_add hE hF
    _ ≤ target := hbudget

/--
Producer-visible alias for the inner `(7.56)` allocated-budget wrapper.

This form is intentionally abstract in the two bad-event budgets.  It records
the bookkeeping step without assigning source credit for either `E*_used` or
`F*`.
-/
theorem taoSection7Case3_prob_lowWhite_le_of_inner756_allocated_budget
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    {LowWhite EStarUsed FSlack : Set Ω}
    {eBudget fBudget target : ℝ}
    (hsub : LowWhite ⊆ EStarUsed ∪ FSlack)
    (hE : pmfProb μ EStarUsed ≤ eBudget)
    (hF : pmfProb μ FSlack ≤ fBudget)
    (hsum : eBudget + fBudget ≤ target) :
    pmfProb μ LowWhite ≤ target :=
  taoSection7Case3_prob_lowWhite_le_of_inner756_budget
    (μ := μ) (LowWhite := LowWhite) (EStarUsed := EStarUsed)
    (FSlack := FSlack) (e := eBudget) (f := fBudget)
    (target := target) hsub hE hF hsum

/--
Event-level `FSlack` probability packet from Lemma 7.9-style expectation data.

The theorem is intentionally source-neutral: it only applies finite-PMF Markov
to the strict cutoff event that the downstream inner `(7.56)` ledger consumes.
The separate `Amarkov` parameter records that Tao's printed `A + 2` Markov
exponent must be shifted before feeding the repaired `Aweight + 3` downstream
allocation.  It does not prove the expectation estimate, identify `moment` with
Tao's source variable, or derive the outside-`FSlack` pointwise count lower
bound.
-/
theorem taoSection7Lemma79_fSlackBudget_of_expect
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    (FSlack : Set Ω) (moment : Ω → ℝ)
    (Amarkov Aweight : ℕ) (epsilon : ℝ)
    (hAmarkov : Amarkov = Aweight + 1)
    (hFSlack :
      FSlack =
        {ω | (10 : ℝ) ^ (Amarkov + 2) * Real.exp epsilon < moment ω})
    (hmoment_nonneg : ∀ ω, 0 ≤ moment ω)
    (hmoment_expect : pmfExpectation μ moment ≤ Real.exp epsilon) :
    pmfProb μ FSlack ≤ 1 / ((10 : ℝ) ^ (Aweight + 3)) := by
  let cutoff : ℝ := (10 : ℝ) ^ (Amarkov + 2) * Real.exp epsilon
  let budgetMarkov : ℝ := 1 / ((10 : ℝ) ^ (Amarkov + 2))
  have hpow_ne : (10 : ℝ) ^ (Amarkov + 2) ≠ 0 :=
    pow_ne_zero _ (by norm_num : (10 : ℝ) ≠ 0)
  have hcutoff_pos : 0 < cutoff := by
    dsimp [cutoff]
    exact mul_pos (pow_pos (by norm_num : (0 : ℝ) < 10) _) (Real.exp_pos _)
  have hcutoff_budget :
      cutoff * budgetMarkov = Real.exp epsilon := by
    dsimp [cutoff, budgetMarkov]
    field_simp [hpow_ne]
  have hmean :
      pmfExpectation μ moment ≤ cutoff * budgetMarkov := by
    simpa [hcutoff_budget] using hmoment_expect
  have hmarkov :
      pmfProb μ FSlack ≤ budgetMarkov := by
    have hmarkov_raw :
        pmfProb μ {ω | cutoff < moment ω} ≤ budgetMarkov :=
      pmfProb_gt_le_of_expect_le_mul
        μ moment hmoment_nonneg hcutoff_pos hmean
    simpa [hFSlack, cutoff] using hmarkov_raw
  have hexponent : Amarkov + 2 = Aweight + 3 := by
    omega
  simpa [budgetMarkov, hexponent] using hmarkov

/-- Natural arithmetic core for the repaired Case 3 inner `(7.56)` allocation. -/
theorem taoSection7Case3_inner756_nat_Aweight_prefactor_le
    {Aweight : ℕ} (hA : 3 ≤ Aweight) :
    1000 * Aweight ^ 2 * 10 ^ Aweight ≤ 9 * 256 ^ Aweight := by
  induction Aweight, hA using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hratio : 10 * (n + 1) ^ 2 ≤ 256 * n ^ 2 := by
        nlinarith [sq_nonneg (n : ℤ)]
      calc
        1000 * (n + 1) ^ 2 * 10 ^ (n + 1)
            = (1000 * 10 ^ n) * (10 * (n + 1) ^ 2) := by
              ring_nf
        _ ≤ (1000 * 10 ^ n) * (256 * n ^ 2) :=
              Nat.mul_le_mul_left _ hratio
        _ = 256 * (1000 * n ^ 2 * 10 ^ n) := by
              ring
        _ ≤ 256 * (9 * 256 ^ n) := Nat.mul_le_mul_left 256 ih
        _ = 9 * 256 ^ (n + 1) := by
              ring_nf

/--
The strengthened `E*_used` allocation fits nine tenths of the repaired
`10^-(A+2)` budget when its exponential cutoff is at least `4*A`.
-/
theorem taoSection7Case3_inner756_AweightPrefactor_Kcut_Ebudget
    {Aweight Kcut : ℕ}
    (hA : 3 ≤ Aweight) (hK : 4 * Aweight ≤ Kcut) :
    (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) ≤
      (9 : ℝ) / (1000 * (10 : ℝ) ^ Aweight) := by
  have hcore :=
    taoSection7Case3_inner756_nat_Aweight_prefactor_le
      (Aweight := Aweight) hA
  have hpow256 : 256 ^ Aweight = 4 ^ (4 * Aweight) := by
    rw [show 256 = 4 ^ 4 by norm_num, pow_mul]
  have h4mono : 4 ^ (4 * Aweight) ≤ 4 ^ Kcut :=
    Nat.pow_le_pow_right (by decide) hK
  have hnat : 1000 * Aweight ^ 2 * 10 ^ Aweight ≤ 9 * 4 ^ Kcut := by
    calc
      1000 * Aweight ^ 2 * 10 ^ Aweight ≤ 9 * 256 ^ Aweight := hcore
      _ = 9 * 4 ^ (4 * Aweight) := by rw [hpow256]
      _ ≤ 9 * 4 ^ Kcut := Nat.mul_le_mul_left 9 h4mono
  have hreal :
      (1000 : ℝ) * (Aweight : ℝ) ^ 2 * (10 : ℝ) ^ Aweight ≤
        (9 : ℝ) * (4 : ℝ) ^ Kcut := by
    exact_mod_cast hnat
  have h4pos : 0 < (4 : ℝ) ^ Kcut := pow_pos (by norm_num) Kcut
  have hdenpos : 0 < (1000 : ℝ) * (10 : ℝ) ^ Aweight := by positivity
  rw [div_le_div_iff₀ h4pos hdenpos]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hreal

/--
Concrete scalar ledger for the repaired inner `(7.56)` allocation.

The `Aweight^2 / 4^Kcut` term is only an allocation target for a future
probability producer; this theorem does not produce that probability bound.
-/
theorem taoSection7Case3_inner756_AweightPrefactor_Kcut_FSlack_budget
    {Aweight Kcut : ℕ}
    (hA : 3 ≤ Aweight) (hK : 4 * Aweight ≤ Kcut) :
    (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) +
        1 / ((10 : ℝ) ^ (Aweight + 3)) ≤
      1 / ((10 : ℝ) ^ (Aweight + 2)) := by
  have hE :=
    taoSection7Case3_inner756_AweightPrefactor_Kcut_Ebudget
      (Aweight := Aweight) (Kcut := Kcut) hA hK
  have hden :
      (1000 : ℝ) * (10 : ℝ) ^ Aweight =
        (10 : ℝ) ^ (Aweight + 3) := by
    rw [show Aweight + 3 = 3 + Aweight by omega, pow_add]
    norm_num
  have hsum :
      (9 : ℝ) / (1000 * (10 : ℝ) ^ Aweight) +
          1 / ((10 : ℝ) ^ (Aweight + 3)) =
        1 / ((10 : ℝ) ^ (Aweight + 2)) := by
    rw [hden]
    have h10 :
        (10 : ℝ) ^ (Aweight + 3) =
          (10 : ℝ) ^ (Aweight + 2) * 10 := by
      rw [show Aweight + 3 = Aweight + 2 + 1 by omega, pow_succ]
    rw [h10]
    field_simp [pow_ne_zero _ (by norm_num : (10 : ℝ) ≠ 0)]
    ring
  calc
    (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) +
        1 / ((10 : ℝ) ^ (Aweight + 3))
        ≤ (9 : ℝ) / (1000 * (10 : ℝ) ^ Aweight) +
          1 / ((10 : ℝ) ^ (Aweight + 3)) := by
            exact add_le_add hE le_rfl
    _ = 1 / ((10 : ℝ) ^ (Aweight + 2)) := hsum

/--
Compatibility name for the Kcut/FSlack scalar budget gate.

The `Aweight^2 / 4^Kcut` term is still only a future producer target.
-/
theorem taoSection7Case3_inner756_Kcut_FSlack_budget
    {Aweight Kcut : ℕ}
    (hA : 3 ≤ Aweight) (hK : 4 * Aweight ≤ Kcut) :
    (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) +
        1 / ((10 : ℝ) ^ (Aweight + 3)) ≤
      1 / ((10 : ℝ) ^ (Aweight + 2)) :=
  taoSection7Case3_inner756_AweightPrefactor_Kcut_FSlack_budget
    (Aweight := Aweight) (Kcut := Kcut) hA hK

/--
Concrete inner `(7.56)` PMF wrapper with the strengthened `E*_used` producer
kept explicit.

The hypothesis `hEproducer` must be proved for the exact strengthened event
used by the future Lemma 7.10/finite-used-offset producer.  It is not derived
from the deterministic `Kcut` containment or from the printed same-parameter
`E*` estimate.
-/
theorem taoSection7Case3_prob_lowWhite_le_of_inner756_budget_of_AweightPrefactor_Kcut_producer
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    {LowWhite EStarUsed FSlack : Set Ω}
    {Aweight Kcut : ℕ}
    (hA : 3 ≤ Aweight) (hK : 4 * Aweight ≤ Kcut)
    (hsub : LowWhite ⊆ EStarUsed ∪ FSlack)
    (hEproducer :
      pmfProb μ EStarUsed ≤
        (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut))
    (hF :
      pmfProb μ FSlack ≤
        1 / ((10 : ℝ) ^ (Aweight + 3))) :
    pmfProb μ LowWhite ≤
      1 / ((10 : ℝ) ^ (Aweight + 2)) :=
  taoSection7Case3_prob_lowWhite_le_of_inner756_allocated_budget
    (μ := μ) (LowWhite := LowWhite) (EStarUsed := EStarUsed)
    (FSlack := FSlack)
    (eBudget := (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut))
    (fBudget := 1 / ((10 : ℝ) ^ (Aweight + 3)))
    (target := 1 / ((10 : ℝ) ^ (Aweight + 2)))
    hsub hEproducer hF
    (taoSection7Case3_inner756_AweightPrefactor_Kcut_FSlack_budget
      (Aweight := Aweight) (Kcut := Kcut) hA hK)

/--
Compatibility name for the Kcut/FSlack PMF gate.

The explicit `hEproducer` premise prevents this wrapper from crediting the
deterministic Kcut containment, the base-repair socket, or Tao's printed
same-parameter `E*` estimate as a probability proof.
-/
theorem taoSection7Case3_prob_lowWhite_le_of_inner756_Kcut_FSlack_budget
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    {LowWhite EStarUsed FSlack : Set Ω}
    {Aweight Kcut : ℕ}
    (hA : 3 ≤ Aweight) (hK : 4 * Aweight ≤ Kcut)
    (hsub : LowWhite ⊆ EStarUsed ∪ FSlack)
    (hEproducer :
      pmfProb μ EStarUsed ≤
        (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut))
    (hF :
      pmfProb μ FSlack ≤
        1 / ((10 : ℝ) ^ (Aweight + 3))) :
    pmfProb μ LowWhite ≤
      1 / ((10 : ℝ) ^ (Aweight + 2)) :=
  taoSection7Case3_prob_lowWhite_le_of_inner756_budget_of_AweightPrefactor_Kcut_producer
    (μ := μ) (LowWhite := LowWhite) (EStarUsed := EStarUsed)
    (FSlack := FSlack) (Aweight := Aweight) (Kcut := Kcut)
    hA hK hsub hEproducer hF

/--
Concrete inner `(7.56)` PMF wrapper with `FSlack` supplied by the shifted
Lemma 7.9/Markov expectation packet.

This removes the raw `hF` probability premise from the caller-facing inner
budget gate.  The source-specific moment construction and expectation bound
remain explicit inputs.
-/
theorem taoSection7Case3_prob_lowWhite_le_of_inner756_Kcut_FSlack_expect
    {Ω : Type*} [Fintype Ω] (μ : PMF Ω)
    {LowWhite EStarUsed FSlack : Set Ω}
    {Amarkov Aweight Kcut : ℕ} {epsilon : ℝ}
    (moment : Ω → ℝ)
    (hA : 3 ≤ Aweight) (hK : 4 * Aweight ≤ Kcut)
    (hsub : LowWhite ⊆ EStarUsed ∪ FSlack)
    (hEproducer :
      pmfProb μ EStarUsed ≤
        (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut))
    (hAmarkov : Amarkov = Aweight + 1)
    (hFSlack :
      FSlack =
        {ω | (10 : ℝ) ^ (Amarkov + 2) * Real.exp epsilon < moment ω})
    (hmoment_nonneg : ∀ ω, 0 ≤ moment ω)
    (hmoment_expect : pmfExpectation μ moment ≤ Real.exp epsilon) :
    pmfProb μ LowWhite ≤
      1 / ((10 : ℝ) ^ (Aweight + 2)) :=
  taoSection7Case3_prob_lowWhite_le_of_inner756_Kcut_FSlack_budget
    (μ := μ) (LowWhite := LowWhite) (EStarUsed := EStarUsed)
    (FSlack := FSlack) (Aweight := Aweight) (Kcut := Kcut)
    hA hK hsub hEproducer
    (taoSection7Lemma79_fSlackBudget_of_expect
      μ FSlack moment Amarkov Aweight epsilon hAmarkov hFSlack
      hmoment_nonneg hmoment_expect)

/--
Search-room immediately gives the block-fit premise needed to apply the
low-window finite-counting lemma to the later search block.
-/
theorem taoSection7Case3_laterSearchBlock_fits_of_searchRoom
    {gapBound : ℕ → ℕ} {P threshold q : ℕ}
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q) :
    taoSection7Case3LaterSearchStart gapBound q + threshold < P := by
  simpa [taoSection7Case3ExitRoom, taoSection7Case3LaterSearchBound]
    using hroom

/--
Every offset in the later search block is strictly beyond the height-exit
endpoint and remains inside the `P` window.
-/
theorem taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window
    {gapBound : ℕ → ℕ} {P threshold q p' : ℕ}
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q)
    (hp' :
      p' ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold)) :
    taoSection7Case3HeightExitBound gapBound q < p' ∧ p' < P := by
  have hfits :
      taoSection7Case3LaterSearchStart gapBound q + threshold < P :=
    taoSection7Case3_laterSearchBlock_fits_of_searchRoom hroom
  have hp'_bounds := Finset.mem_Icc.mp hp'
  constructor
  · dsimp [taoSection7Case3LaterSearchStart,
      taoSection7Case3HeightExitBound] at hp'_bounds ⊢
    omega
  · exact lt_of_le_of_lt hp'_bounds.2 hfits

/--
Low-window plus the stronger later-search room finds a non-white later offset
which is strictly after the height-exit endpoint.
-/
theorem taoSection7Case3_exists_later_nonwhite_after_exit_of_searchRoom
    (W : ℕ → Prop) [DecidablePred W]
    {gapBound : ℕ → ℕ} {P threshold q : ℕ}
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hroom :
      taoSection7Case3ExitRoom
        (taoSection7Case3LaterSearchBound gapBound threshold) P q) :
    ∃ p' : ℕ,
      p' ∈ Finset.Icc
        (taoSection7Case3LaterSearchStart gapBound q)
        (taoSection7Case3LaterSearchStart gapBound q + threshold) ∧
        ¬ W p' ∧
          taoSection7Case3HeightExitBound gapBound q < p' ∧ p' < P := by
  have hblock :
      taoSection7Case3LaterSearchStart gapBound q + threshold < P :=
    taoSection7Case3_laterSearchBlock_fits_of_searchRoom hroom
  rcases taoSection7Case3_low_window_forces_nonwhite_in_block W hlow hblock with
    ⟨p', hp', hnotW⟩
  exact
    ⟨p', hp', hnotW,
      taoSection7Case3_laterSearch_mem_strict_exit_and_lt_window hroom hp'⟩

theorem taoSection7Case3_exitRoom_of_startHeadroom_of_mem_window
    {ExitBound B : ℕ → ℕ} {P start threshold q : ℕ}
    (hroom : taoSection7Case3AdvanceHeadroom B P start)
    (hdominates :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        ExitBound q ≤ B start)
    (hq : q ∈ Finset.Icc start (start + threshold)) :
    taoSection7Case3ExitRoom ExitBound P q :=
  lt_of_le_of_lt (hdominates q hq) hroom

/--
Generic domination bridge for the full later-search endpoint: if the current
step budget dominates the whole later search block for every possible pivot in
the local window, then start headroom supplies q-room for that pivot.
-/
theorem taoSection7Case3_searchRoom_of_startHeadroom_of_windowBudget
    {B gapBound : ℕ → ℕ} {P start threshold q : ℕ}
    (hroom : taoSection7Case3AdvanceHeadroom B P start)
    (hdominates :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7Case3LaterSearchBound gapBound threshold q ≤ B start)
    (hq : q ∈ Finset.Icc start (start + threshold)) :
    taoSection7Case3ExitRoom
      (taoSection7Case3LaterSearchBound gapBound threshold) P q :=
  taoSection7Case3_exitRoom_of_startHeadroom_of_mem_window hroom hdominates hq

/--
The current-step budget dominates every possible pivot exit budget in the local
window.
-/
def taoSection7Case3WindowBudgetDominates
    (B ExitBound : ℕ → ℕ) (threshold p : ℕ) : Prop :=
  ∀ q : ℕ, q ∈ Finset.Icc p (p + threshold) → ExitBound q ≤ B p

/--
Window envelope for a local Case 3 step: the budget contains the current
low-window block and dominates the exit/search budget for every pivot selected
inside that block.
-/
def taoSection7Case3WindowEnvelope
    (B ExitBound : ℕ → ℕ) (threshold p : ℕ) : Prop :=
  p + threshold ≤ B p ∧
    taoSection7Case3WindowBudgetDominates B ExitBound threshold p

theorem taoSection7Case3_windowFits_of_windowEnvelope
    {B ExitBound : ℕ → ℕ} {P threshold p : ℕ}
    (hroom : taoSection7Case3AdvanceHeadroom B P p)
    (hwindow : taoSection7Case3WindowEnvelope B ExitBound threshold p) :
    p + threshold < P :=
  lt_of_le_of_lt hwindow.1 hroom

theorem taoSection7Case3_exitRoom_of_windowEnvelope
    {B ExitBound : ℕ → ℕ} {P threshold p q : ℕ}
    (hroom : taoSection7Case3AdvanceHeadroom B P p)
    (hwindow : taoSection7Case3WindowEnvelope B ExitBound threshold p)
    (hq : q ∈ Finset.Icc p (p + threshold)) :
    taoSection7Case3ExitRoom ExitBound P q :=
  lt_of_le_of_lt (hwindow.2 q hq) hroom

theorem taoSection7Case3_window_start_le_laterSearchBound_right
    (gapBound : ℕ → ℕ) (threshold start : ℕ) :
    start + threshold ≤
      taoSection7Case3LaterSearchBound gapBound threshold
        (start + threshold) := by
  dsimp [taoSection7Case3LaterSearchBound,
    taoSection7Case3LaterSearchStart,
    taoSection7Case3HeightExitBound]
  omega

/--
Monotonicity of the abstract gap makes the right edge of the current low
window dominate every possible selected pivot's full later-search endpoint.
-/
theorem taoSection7Case3_laterSearchBound_le_right_of_mem_window
    {gapBound : ℕ → ℕ} (hmono : Monotone gapBound)
    {threshold start q : ℕ}
    (hq : q ∈ Finset.Icc start (start + threshold)) :
    taoSection7Case3LaterSearchBound gapBound threshold q ≤
      taoSection7Case3LaterSearchBound gapBound threshold
        (start + threshold) := by
  have hq_le : q ≤ start + threshold := (Finset.mem_Icc.mp hq).2
  have hgap_le : gapBound q ≤ gapBound (start + threshold) := hmono hq_le
  dsimp [taoSection7Case3LaterSearchBound,
    taoSection7Case3LaterSearchStart,
    taoSection7Case3HeightExitBound]
  omega

/--
A single right-endpoint bound supplies the window-budget domination premise
for the full later-search endpoint.
-/
theorem taoSection7Case3_laterSearchWindowBudgetDominates
    {B gapBound : ℕ → ℕ} (hmono : Monotone gapBound)
    {threshold start : ℕ}
    (hright :
      taoSection7Case3LaterSearchBound gapBound threshold
          (start + threshold) ≤ B start) :
    taoSection7Case3WindowBudgetDominates B
      (taoSection7Case3LaterSearchBound gapBound threshold) threshold start := by
  intro q hq
  exact
    (taoSection7Case3_laterSearchBound_le_right_of_mem_window
      hmono hq).trans hright

/--
The same right-endpoint bound also contains the original low window, so it is
a drop-in abstract envelope for later q-room chain support.
-/
theorem taoSection7Case3_windowEnvelope_of_laterSearchRightBound
    {B gapBound : ℕ → ℕ} (hmono : Monotone gapBound)
    {threshold start : ℕ}
    (hright :
      taoSection7Case3LaterSearchBound gapBound threshold
          (start + threshold) ≤ B start) :
    taoSection7Case3WindowEnvelope B
      (taoSection7Case3LaterSearchBound gapBound threshold) threshold start :=
  ⟨(taoSection7Case3_window_start_le_laterSearchBound_right
      gapBound threshold start).trans hright,
    taoSection7Case3_laterSearchWindowBudgetDominates hmono hright⟩

theorem taoSection7Case3_windowEnvelope_of_concreteRightBound
    {B : ℕ → ℕ} {A threshold start : ℕ}
    (hright :
      taoSection7Case3LaterSearchBound
          (taoSection7Case3ExitGapBound A) threshold
          (start + threshold) ≤ B start) :
    taoSection7Case3WindowEnvelope B
      (taoSection7Case3LaterSearchBound
        (taoSection7Case3ExitGapBound A) threshold) threshold start :=
  taoSection7Case3_windowEnvelope_of_laterSearchRightBound
    (taoSection7Case3ExitGapBound_mono A) hright

/--
Start headroom plus the monotone right-endpoint envelope supplies q-room for
any pivot selected inside the current window.
-/
theorem taoSection7Case3_searchRoom_of_monotone_right_endpoint
    {B gapBound : ℕ → ℕ} {P start threshold q : ℕ}
    (hroom : taoSection7Case3AdvanceHeadroom B P start)
    (hmono : Monotone gapBound)
    (hright :
      taoSection7Case3LaterSearchBound gapBound threshold
          (start + threshold) ≤ B start)
    (hq : q ∈ Finset.Icc start (start + threshold)) :
    taoSection7Case3ExitRoom
      (taoSection7Case3LaterSearchBound gapBound threshold) P q :=
  taoSection7Case3_exitRoom_of_windowEnvelope hroom
    (taoSection7Case3_windowEnvelope_of_laterSearchRightBound
      hmono hright) hq

/--
Abstract bounded local advance used by the Case 3 iteration skeleton.  The
source step relation is intentionally an explicit parameter at this layer.
-/
def taoSection7Case3BoundedAdvance
    (B : ℕ → ℕ) (Step : ℕ → ℕ → Prop) (p next : ℕ) : Prop :=
  Step p next ∧ next ≤ B p

/--
Strict bounded local advance: the next offset is genuinely later and stays
within the budget supplied by `B`.
-/
def taoSection7Case3StrictBoundedAdvance
    (B : ℕ → ℕ) (Step : ℕ → ℕ → Prop) (p next : ℕ) : Prop :=
  Step p next ∧ p < next ∧ next ≤ B p

theorem taoSection7Case3_strictBoundedAdvance_lt_window
    {B : ℕ → ℕ} {Step : ℕ → ℕ → Prop} {P p next : ℕ}
    (hroom : taoSection7Case3AdvanceHeadroom B P p)
    (hnext : taoSection7Case3StrictBoundedAdvance B Step p next) :
    next < P :=
  lt_of_le_of_lt hnext.2.2 hroom

/--
One-step outside-large-event bounded-advance adapter.  The hypothesis
`hadvance` is the future source geometric exit argument; this theorem only
packages the already checked low-window and small-triangle support around it.
-/
theorem taoSection7Case3_oneStepBoundedAdvance_of_lowWindow_notEStar
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    (B : ℕ → ℕ) (Step : ℕ → ℕ → Prop)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {allowed : Set ℕ} {P start threshold : ℕ}
    (hroom : taoSection7Case3AdvanceHeadroom B P start)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hblock : start + threshold < P)
    (hallowed :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) → q ∈ allowed)
    (hnotUnion :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed
          (taoSection7Case3LargeTriangleBound A))
    (hWwhite :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        (W q ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt q)))
    (hdomain :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7SourcePointInDomain J (pointAt q))
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hadvance :
      ∀ q : ℕ, ∀ Δ : TaoSection7Triangle,
        q ∈ Finset.Icc start (start + threshold) →
          ¬ W q →
            Δ ∈ family →
              Δ.Mem (pointAt q) →
                Δ.size < taoSection7Case3LargeTriangleBound A q →
                  taoSection7Case3AdvanceHeadroom B P start →
                    ∃ next : ℕ,
                      taoSection7Case3BoundedAdvance B Step start next) :
    ∃ q : ℕ, q ∈ Finset.Icc start (start + threshold) ∧ ¬ W q ∧
      ∃ Δ : TaoSection7Triangle, Δ ∈ family ∧ Δ.Mem (pointAt q) ∧
        Δ.size < taoSection7Case3LargeTriangleBound A q ∧
          ∃ next : ℕ,
            taoSection7Case3BoundedAdvance B Step start next := by
  rcases taoSection7Case3_low_window_produces_small_source_triangle_offset
      W pointAt hlow hblock hallowed hnotUnion hWwhite hdomain hcover with
    ⟨q, hq, hnotW, Δ, hΔ, hmem, hsize⟩
  rcases hadvance q Δ hq hnotW hΔ hmem hsize hroom with ⟨next, hnext⟩
  exact ⟨q, hq, hnotW, Δ, hΔ, hmem, hsize, next, hnext⟩

/--
Strict one-step variant of the bounded-advance adapter.  This remains
support-only: the strict step is supplied by the explicit exit hypothesis.
-/
theorem taoSection7Case3_oneStepStrictBoundedAdvance_of_lowWindow_notEStar
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    (B : ℕ → ℕ) (Step : ℕ → ℕ → Prop)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {allowed : Set ℕ} {P start threshold : ℕ}
    (hroom : taoSection7Case3AdvanceHeadroom B P start)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hblock : start + threshold < P)
    (hallowed :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) → q ∈ allowed)
    (hnotUnion :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed
          (taoSection7Case3LargeTriangleBound A))
    (hWwhite :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        (W q ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt q)))
    (hdomain :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7SourcePointInDomain J (pointAt q))
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hadvance :
      ∀ q : ℕ, ∀ Δ : TaoSection7Triangle,
        q ∈ Finset.Icc start (start + threshold) →
          ¬ W q →
            Δ ∈ family →
              Δ.Mem (pointAt q) →
                Δ.size < taoSection7Case3LargeTriangleBound A q →
                  taoSection7Case3AdvanceHeadroom B P start →
                    ∃ next : ℕ,
                      taoSection7Case3StrictBoundedAdvance B Step start next) :
    ∃ q : ℕ, q ∈ Finset.Icc start (start + threshold) ∧ ¬ W q ∧
      ∃ Δ : TaoSection7Triangle, Δ ∈ family ∧ Δ.Mem (pointAt q) ∧
        Δ.size < taoSection7Case3LargeTriangleBound A q ∧
          ∃ next : ℕ,
            taoSection7Case3StrictBoundedAdvance B Step start next := by
  rcases taoSection7Case3_low_window_produces_small_source_triangle_offset
      W pointAt hlow hblock hallowed hnotUnion hWwhite hdomain hcover with
    ⟨q, hq, hnotW, Δ, hΔ, hmem, hsize⟩
  rcases hadvance q Δ hq hnotW hΔ hmem hsize hroom with ⟨next, hnext⟩
  exact ⟨q, hq, hnotW, Δ, hΔ, hmem, hsize, next, hnext⟩

/--
Extracts the strict local advance and the resulting `next < P` window bound
from the one-step adapter.  This is the form intended for the later chain
builder.
-/
theorem taoSection7Case3_exists_strictBoundedAdvance_lt_window
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    (B : ℕ → ℕ) (Step : ℕ → ℕ → Prop)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {allowed : Set ℕ} {P start threshold : ℕ}
    (hroom : taoSection7Case3AdvanceHeadroom B P start)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hblock : start + threshold < P)
    (hallowed :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) → q ∈ allowed)
    (hnotUnion :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed
          (taoSection7Case3LargeTriangleBound A))
    (hWwhite :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        (W q ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt q)))
    (hdomain :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7SourcePointInDomain J (pointAt q))
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hadvance :
      ∀ q : ℕ, ∀ Δ : TaoSection7Triangle,
        q ∈ Finset.Icc start (start + threshold) →
          ¬ W q →
            Δ ∈ family →
              Δ.Mem (pointAt q) →
                Δ.size < taoSection7Case3LargeTriangleBound A q →
                  taoSection7Case3AdvanceHeadroom B P start →
                    ∃ next : ℕ,
                      taoSection7Case3StrictBoundedAdvance B Step start next) :
    ∃ next : ℕ,
      taoSection7Case3StrictBoundedAdvance B Step start next ∧ next < P := by
  rcases taoSection7Case3_oneStepStrictBoundedAdvance_of_lowWindow_notEStar
      W pointAt B Step hroom hlow hblock hallowed hnotUnion hWwhite hdomain
      hcover hadvance with
    ⟨_q, _hq, _hnotW, _Δ, _hΔ, _hmem, _hsize, next, hnext⟩
  exact
    ⟨next, hnext,
      taoSection7Case3_strictBoundedAdvance_lt_window hroom hnext⟩

/--
Q-level room variant of the one-step adapter.  The future source exit lemma
consumes room at the actual non-white pivot `q`, while start-level headroom is
kept only for the derived `next < P` bound.
-/
theorem taoSection7Case3_oneStepStrictBoundedAdvance_of_lowWindow_notEStar_exitRoom
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    (ExitBound B : ℕ → ℕ) (Step : ℕ → ℕ → Prop)
    {n J A : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {allowed : Set ℕ} {P start threshold : ℕ}
    (hstartRoom : taoSection7Case3AdvanceHeadroom B P start)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hblock : start + threshold < P)
    (hallowed :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) → q ∈ allowed)
    (hnotUnion :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed
          (taoSection7Case3LargeTriangleBound A))
    (hWwhite :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        (W q ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt q)))
    (hdomain :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7SourcePointInDomain J (pointAt q))
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hexitRoom :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7Case3ExitRoom ExitBound P q)
    (hadvance :
      ∀ q : ℕ, ∀ Δ : TaoSection7Triangle,
        q ∈ Finset.Icc start (start + threshold) →
          ¬ W q →
            Δ ∈ family →
              Δ.Mem (pointAt q) →
                Δ.size < taoSection7Case3LargeTriangleBound A q →
                  taoSection7Case3ExitRoom ExitBound P q →
                    ∃ next : ℕ,
                      taoSection7Case3StrictBoundedAdvance B Step start next) :
    ∃ q : ℕ, q ∈ Finset.Icc start (start + threshold) ∧ ¬ W q ∧
      taoSection7Case3ExitRoom ExitBound P q ∧
        ∃ Δ : TaoSection7Triangle, Δ ∈ family ∧ Δ.Mem (pointAt q) ∧
          Δ.size < taoSection7Case3LargeTriangleBound A q ∧
            ∃ next : ℕ,
              taoSection7Case3StrictBoundedAdvance B Step start next ∧
                next < P := by
  rcases taoSection7Case3_low_window_produces_small_source_triangle_offset
      W pointAt hlow hblock hallowed hnotUnion hWwhite hdomain hcover with
    ⟨q, hq, hnotW, Δ, hΔ, hmem, hsize⟩
  have hqRoom : taoSection7Case3ExitRoom ExitBound P q := hexitRoom q hq
  rcases hadvance q Δ hq hnotW hΔ hmem hsize hqRoom with ⟨next, hnext⟩
  exact
    ⟨q, hq, hnotW, hqRoom, Δ, hΔ, hmem, hsize, next, hnext,
      taoSection7Case3_strictBoundedAdvance_lt_window hstartRoom hnext⟩

/--
Generic-bound q-room variant of the one-step adapter.  The future source exit
lemma remains an explicit `hadvance` hypothesis, but the no-large event and
triangle-size input now share one arbitrary threshold `bound`.
-/
theorem taoSection7Case3_oneStepStrictBoundedAdvance_of_lowWindow_notEStar_bound_exitRoom
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    (ExitBound B : ℕ → ℕ) (Step : ℕ → ℕ → Prop)
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {allowed : Set ℕ} {bound : ℕ → ℝ}
    {P start threshold : ℕ}
    (hstartRoom : taoSection7Case3AdvanceHeadroom B P start)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hblock : start + threshold < P)
    (hallowed :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) → q ∈ allowed)
    (hnotUnion :
      ¬ taoSection7Case3LargeTriangleUnion pointAt family allowed bound)
    (hWwhite :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        (W q ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt q)))
    (hdomain :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7SourcePointInDomain J (pointAt q))
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hexitRoom :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7Case3ExitRoom ExitBound P q)
    (hadvance :
      ∀ q : ℕ, ∀ Δ : TaoSection7Triangle,
        q ∈ Finset.Icc start (start + threshold) →
          ¬ W q →
            Δ ∈ family →
              Δ.Mem (pointAt q) →
                Δ.size < bound q →
                  taoSection7Case3ExitRoom ExitBound P q →
                    ∃ next : ℕ,
                      taoSection7Case3StrictBoundedAdvance B Step start next) :
    ∃ q : ℕ, q ∈ Finset.Icc start (start + threshold) ∧ ¬ W q ∧
      taoSection7Case3ExitRoom ExitBound P q ∧
        ∃ Δ : TaoSection7Triangle, Δ ∈ family ∧ Δ.Mem (pointAt q) ∧
          Δ.size < bound q ∧
            ∃ next : ℕ,
              taoSection7Case3StrictBoundedAdvance B Step start next ∧
                next < P := by
  rcases taoSection7Case3_low_window_produces_small_triangle_offset_of_bound
      W pointAt hlow hblock hallowed hnotUnion hWwhite hdomain hcover with
    ⟨q, hq, hnotW, Δ, hΔ, hmem, hsize⟩
  have hqRoom : taoSection7Case3ExitRoom ExitBound P q := hexitRoom q hq
  rcases hadvance q Δ hq hnotW hΔ hmem hsize hqRoom with ⟨next, hnext⟩
  exact
    ⟨q, hq, hnotW, hqRoom, Δ, hΔ, hmem, hsize, next, hnext,
      taoSection7Case3_strictBoundedAdvance_lt_window hstartRoom hnext⟩

/--
Sandwich-facing generic-bound one-step adapter.  This removes the explicit
`hnotUnion` obligation from callers that already know `ω ∉ EStarUsed` and have
a checked large-triangle sandwich for the same `bound`.
-/
theorem taoSection7Case3_oneStepStrictBoundedAdvance_of_lowWindow_notEStar_bound_exitRoom_of_sandwich
    {Ω : Type*} [Fintype Ω]
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : Ω → ℕ → TaoSection7Point)
    (ExitBound B : ℕ → ℕ) (Step : ℕ → ℕ → Prop)
    {ω : Ω}
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle}
    {EStarUsed : Set Ω}
    {used : Set ℕ} {allowed : Finset ℕ} {bound : ℕ → ℝ}
    {P start threshold : ℕ}
    (sandwich :
      TaoSection7Case3EStarUsedLargeTriangleSandwich
        pointAt family EStarUsed used allowed bound)
    (hω : ω ∉ EStarUsed)
    (hstartRoom : taoSection7Case3AdvanceHeadroom B P start)
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hblock : start + threshold < P)
    (hused :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) → q ∈ used)
    (hWwhite :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        (W q ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt ω q)))
    (hdomain :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7SourcePointInDomain J (pointAt ω q))
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family)
    (hexitRoom :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7Case3ExitRoom ExitBound P q)
    (hadvance :
      ∀ q : ℕ, ∀ Δ : TaoSection7Triangle,
        q ∈ Finset.Icc start (start + threshold) →
          ¬ W q →
            Δ ∈ family →
              Δ.Mem (pointAt ω q) →
                Δ.size < bound q →
                  taoSection7Case3ExitRoom ExitBound P q →
                    ∃ next : ℕ,
                      taoSection7Case3StrictBoundedAdvance B Step start next) :
    ∃ q : ℕ, q ∈ Finset.Icc start (start + threshold) ∧ ¬ W q ∧
      taoSection7Case3ExitRoom ExitBound P q ∧
        ∃ Δ : TaoSection7Triangle, Δ ∈ family ∧ Δ.Mem (pointAt ω q) ∧
          Δ.size < bound q ∧
            ∃ next : ℕ,
              taoSection7Case3StrictBoundedAdvance B Step start next ∧
                next < P :=
  taoSection7Case3_oneStepStrictBoundedAdvance_of_lowWindow_notEStar_bound_exitRoom
    W (pointAt ω) ExitBound B Step hstartRoom hlow hblock hused
    (sandwich.not_large_union_of_not_mem hω) hWwhite hdomain hcover
    hexitRoom hadvance

end Tao
end Erdos1135
