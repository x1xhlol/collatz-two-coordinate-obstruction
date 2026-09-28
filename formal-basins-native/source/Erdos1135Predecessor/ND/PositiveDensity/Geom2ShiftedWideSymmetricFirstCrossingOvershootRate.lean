/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.BoundedPMFDisintegration
import Erdos1135Predecessor.ND.PositiveDensity.CommonZLongRangeCoordinateCapFirstBad
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricFirstCrossingPhysicalShell

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

theorem ndGeom2ShiftedWideSymmetricHit_append_terminal_iff_of_lt
    {b a s t : ℕ} {pre : List ℕ+} (v w : ℕ+)
    (hpre : pre.length = s - 1) (hs : 0 < s) (ht : t < s) :
    ndGeom2ShiftedWideSymmetricHit b a t (pre ++ [v]) ↔
      ndGeom2ShiftedWideSymmetricHit b a t (pre ++ [w]) := by
  have htpre : t ≤ pre.length := by omega
  unfold ndGeom2ShiftedWideSymmetricHit
  rw [List.take_append_of_le_length htpre,
    List.take_append_of_le_length htpre]

private theorem ndBalancedTotal_mono_overshoot
    {j k : ℕ} (hjk : j ≤ k) :
    ndBalancedTotal j ≤ ndBalancedTotal k := by
  unfold ndBalancedTotal
  exact Nat.clog_monotone 2
    (Nat.pow_le_pow_right (by norm_num) hjk)

theorem ndGeom2ShiftedWideSymmetric_firstCrossing_overshoot_succ_le_terminal
    {b a s : ℕ} {word : List ℕ+}
    (hlen : word.length = s)
    (hfirst :
      ndFiniteFirstHitAt
        (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b)
        (ndGeom2ShiftedWideSymmetricCrossingEligibleHit b a) s word) :
    Tao.taoTupleWeight word + ndBalancedTotal (b - s) +
          ndGeom2ShiftedWideSymmetricShiftRadius b + 1 ≤
      2 * b + ndBalancedTotal (s - b) + a +
        Tao.geom2PNatListTerminalValue word := by
  have hsBounds := Finset.mem_Icc.mp hfirst.1
  have hsPos : 0 < s := by omega
  have hlowerMiss :
      ¬ndGeom2ShiftedWideSymmetricHit b a
        (ndGeom2ShiftedWideSymmetricLower b) word :=
    hfirst.2.1.1
  have hprev :
      ¬ndGeom2ShiftedWideSymmetricHit b a (s - 1) word := by
    by_cases hfirstDepth :
        s = ndGeom2ShiftedWideSymmetricLower b + 1
    · have heq : s - 1 = ndGeom2ShiftedWideSymmetricLower b := by omega
      simpa only [heq] using hlowerMiss
    · have hprevMem :
          s - 1 ∈ ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b := by
        apply Finset.mem_Icc.mpr
        constructor <;> omega
      intro hprevHit
      exact hfirst.2.2 (s - 1) hprevMem (by omega)
        ⟨hlowerMiss, hprevHit⟩
  have hprevStrict :
      Tao.taoTupleWeight (word.take (s - 1)) +
          ndBalancedTotal (b - (s - 1)) +
          ndGeom2ShiftedWideSymmetricShiftRadius b <
        2 * b + ndBalancedTotal ((s - 1) - b) + a := by
    unfold ndGeom2ShiftedWideSymmetricHit at hprev
    omega
  have hleftMono :
      ndBalancedTotal (b - s) ≤
        ndBalancedTotal (b - (s - 1)) :=
    ndBalancedTotal_mono_overshoot (by omega)
  have hrightMono :
      ndBalancedTotal ((s - 1) - b) ≤
        ndBalancedTotal (s - b) :=
    ndBalancedTotal_mono_overshoot (by omega)
  have hprefixStrict :
      Tao.taoTupleWeight (word.take (s - 1)) +
          ndBalancedTotal (b - s) +
          ndGeom2ShiftedWideSymmetricShiftRadius b <
        2 * b + ndBalancedTotal (s - b) + a := by
    omega
  have hdrop : word.dropLast = word.take (s - 1) := by
    rw [List.dropLast_eq_take, hlen]
  have hweight := Tao.taoTupleWeight_eq_dropLast_add_terminalValue word
  rw [hdrop] at hweight
  omega

theorem
    ndFiniteFirstShiftedWideSymmetricCrossing_raiseTerminal_iff_badOvershoot
    {b a s K : ℕ} {pre : List ℕ+} (v : ℕ+)
    (hpre : pre.length = s - 1) (hsPos : 0 < s) :
    (ndFiniteFirstHitAt
          (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b)
          (ndGeom2ShiftedWideSymmetricCrossingEligibleHit b a) s
          (pre ++ [ndPNatAddNat (K + 1) v]) ∧
        ¬ndGeom2ShiftedWideSymmetricBoundedOvershoot b a s K
          (pre ++ [ndPNatAddNat (K + 1) v])) ↔
      ndFiniteFirstHitAt
        (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b)
        (ndGeom2ShiftedWideSymmetricCrossingEligibleHit b a) s
        (pre ++ [v]) := by
  let raised := pre ++ [ndPNatAddNat (K + 1) v]
  let lower := pre ++ [v]
  have hlenRaised : raised.length = s := by
    dsimp only [raised]
    simp only [List.length_append, List.length_singleton, hpre]
    omega
  have hlenLower : lower.length = s := by
    dsimp only [lower]
    simp only [List.length_append, List.length_singleton, hpre]
    omega
  have hweightRaised :
      Tao.taoTupleWeight raised =
        Tao.taoTupleWeight lower + (K + 1) := by
    dsimp only [raised, lower]
    simp only [Tao.taoTupleWeight_append, Tao.taoTupleWeight_cons,
      Tao.taoTupleWeight_nil, add_zero, ndPNatAddNat_coe]
    omega
  constructor
  · rintro ⟨hfirstRaised, hnotCap⟩
    have hsBounds := Finset.mem_Icc.mp hfirstRaised.1
    have hlowerLt : ndGeom2ShiftedWideSymmetricLower b < s := by omega
    have hbefore (t : ℕ) (ht : t < s) :
        ndGeom2ShiftedWideSymmetricHit b a t raised ↔
          ndGeom2ShiftedWideSymmetricHit b a t lower := by
      simpa only [raised, lower] using
        ndGeom2ShiftedWideSymmetricHit_append_terminal_iff_of_lt
          (b := b) (a := a) (s := s) (t := t)
          (ndPNatAddNat (K + 1) v) v hpre hsPos ht
    have hlowerMiss :
        ¬ndGeom2ShiftedWideSymmetricHit b a
          (ndGeom2ShiftedWideSymmetricLower b) lower := by
      intro hhit
      exact hfirstRaised.2.1.1 ((hbefore _ hlowerLt).2 hhit)
    have hraisedHit := hfirstRaised.2.1.2
    have hlowerHit : ndGeom2ShiftedWideSymmetricHit b a s lower := by
      change ¬ndGeom2ShiftedWideSymmetricBoundedOvershoot
        b a s K raised at hnotCap
      unfold ndGeom2ShiftedWideSymmetricBoundedOvershoot at hnotCap
      unfold ndGeom2ShiftedWideSymmetricHit
      rw [show lower.take s = lower by
        rw [← hlenLower]
        exact List.take_length]
      change ndGeom2ShiftedWideSymmetricHit b a s raised at hraisedHit
      unfold ndGeom2ShiftedWideSymmetricHit at hraisedHit
      rw [show raised.take s = raised by
        rw [← hlenRaised]
        exact List.take_length] at hraisedHit
      omega
    refine ⟨hfirstRaised.1, ⟨hlowerMiss, hlowerHit⟩, ?_⟩
    intro t htI hts htEligible
    apply hfirstRaised.2.2 t htI hts
    refine ⟨?_, (hbefore t hts).2 htEligible.2⟩
    intro hhitRaised
    exact htEligible.1 ((hbefore _ hlowerLt).1 hhitRaised)
  · intro hfirstLower
    have hsBounds := Finset.mem_Icc.mp hfirstLower.1
    have hlowerLt : ndGeom2ShiftedWideSymmetricLower b < s := by omega
    have hbefore (t : ℕ) (ht : t < s) :
        ndGeom2ShiftedWideSymmetricHit b a t raised ↔
          ndGeom2ShiftedWideSymmetricHit b a t lower := by
      simpa only [raised, lower] using
        ndGeom2ShiftedWideSymmetricHit_append_terminal_iff_of_lt
          (b := b) (a := a) (s := s) (t := t)
          (ndPNatAddNat (K + 1) v) v hpre hsPos ht
    have hraisedHit : ndGeom2ShiftedWideSymmetricHit b a s raised := by
      have hlowerHit := hfirstLower.2.1.2
      unfold ndGeom2ShiftedWideSymmetricHit at hlowerHit ⊢
      rw [show lower.take s = lower by
        rw [← hlenLower]
        exact List.take_length] at hlowerHit
      change
        2 * b + ndBalancedTotal (s - b) + a ≤
          Tao.taoTupleWeight (raised.take s) +
            ndBalancedTotal (b - s) +
              ndGeom2ShiftedWideSymmetricShiftRadius b
      rw [show raised.take s = raised by
        rw [← hlenRaised]
        exact List.take_length]
      omega
    have hlowerMissRaised :
        ¬ndGeom2ShiftedWideSymmetricHit b a
          (ndGeom2ShiftedWideSymmetricLower b) raised := by
      intro hhit
      exact hfirstLower.2.1.1 ((hbefore _ hlowerLt).1 hhit)
    have hfirstRaised :
        ndFiniteFirstHitAt
          (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b)
          (ndGeom2ShiftedWideSymmetricCrossingEligibleHit b a) s raised := by
      refine ⟨hfirstLower.1, ⟨hlowerMissRaised, hraisedHit⟩, ?_⟩
      intro t htI hts htEligible
      apply hfirstLower.2.2 t htI hts
      refine ⟨?_, (hbefore t hts).1 htEligible.2⟩
      intro hhitLower
      exact htEligible.1 ((hbefore _ hlowerLt).2 hhitLower)
    refine ⟨hfirstRaised, ?_⟩
    intro hcap
    have hlowerHit := hfirstLower.2.1.2
    unfold ndGeom2ShiftedWideSymmetricHit at hlowerHit
    rw [show lower.take s = lower by
      rw [← hlenLower]
      exact List.take_length] at hlowerHit
    change ndGeom2ShiftedWideSymmetricBoundedOvershoot
      b a s K raised at hcap
    unfold ndGeom2ShiftedWideSymmetricBoundedOvershoot at hcap
    omega

def ndGeom2ShiftedWideSymmetricFirstCrossingAt
    (b a s : ℕ) (word : List ℕ+) : Prop :=
  ndFiniteFirstHitAt
    (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b)
    (ndGeom2ShiftedWideSymmetricCrossingEligibleHit b a) s word

def ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAt
    (b a s K : ℕ) (word : List ℕ+) : Prop :=
  ndGeom2ShiftedWideSymmetricFirstCrossingAt b a s word ∧
    ¬ndGeom2ShiftedWideSymmetricBoundedOvershoot b a s K word

def ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt
    (b a s K : ℕ) (word : List ℕ+) : Prop :=
  ndGeom2ShiftedWideSymmetricFirstCrossingAt b a s word ∧
    ndGeom2ShiftedWideSymmetricBoundedOvershoot b a s K word

noncomputable def ndGeom2ShiftedWideSymmetricFirstCrossingAtMass
    (b a s : ℕ) : ℝ :=
  ((Tao.geom2PNatListPMF s).toOuterMeasure
    {word | ndGeom2ShiftedWideSymmetricFirstCrossingAt b a s word}).toReal

noncomputable def ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAtMass
    (b a s K : ℕ) : ℝ :=
  ((Tao.geom2PNatListPMF s).toOuterMeasure
    {word |
      ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAt
        b a s K word}).toReal

noncomputable def
    ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass
    (b a s K : ℕ) : ℝ :=
  ((Tao.geom2PNatListPMF s).toOuterMeasure
    {word |
      ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt
        b a s K word}).toReal

theorem ndGeom2ShiftedWideSymmetric_terminal_gt_succ_of_badOvershoot
    {b a s K : ℕ} {word : List ℕ+}
    (hlen : word.length = s)
    (hbad :
    ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAt
        b a s K word) :
    K + 1 < Tao.geom2PNatListTerminalValue word := by
  have hfirst := hbad.1
  have hnotCap := hbad.2
  have hmargin :=
    ndGeom2ShiftedWideSymmetric_firstCrossing_overshoot_succ_le_terminal
      hlen hfirst
  unfold ndGeom2ShiftedWideSymmetricBoundedOvershoot at hnotCap
  omega

private noncomputable def ndPropIndicatorOvershoot (P : Prop) : ℝ :=
  @ite ℝ P (Classical.propDecidable P) 1 0

private theorem ndPMFEventMass_eq_expectation_indicator_overshoot
    {Alpha : Type*} (p : PMF Alpha) (P : Alpha → Prop) :
    (p.toOuterMeasure {x | P x}).toReal =
      ndPMFWeightedExpectation p (fun x => ndPropIndicatorOvershoot (P x)) := by
  classical
  rw [Tao.pmfOuterMass_toReal_eq_tsum_indicator]
  unfold ndPMFWeightedExpectation
  apply tsum_congr
  intro x
  by_cases hx : P x <;> simp [ndPropIndicatorOvershoot, hx]

private theorem geom2PNatListPMF_one_eq_map_singleton_overshoot :
    Tao.geom2PNatListPMF 1 =
      Tao.geom2PNat.map (fun a => [a]) := by
  change
    (Tao.geom2PNat.bind fun a =>
      (PMF.pure []).map fun as => a :: as) = _
  rw [show (fun a : ℕ+ =>
      (PMF.pure []).map fun as => a :: as) =
        PMF.pure ∘ (fun a : ℕ+ => [a]) by
    funext a
    exact PMF.pure_map (fun as : List ℕ+ => a :: as) []]
  exact PMF.bind_pure_comp _ _

private theorem ndPMFWeightedExpectation_geom2_one_indicator_overshoot
    (P : List ℕ+ → Prop) :
    ndPMFWeightedExpectation (Tao.geom2PNatListPMF 1)
        (fun word => ndPropIndicatorOvershoot (P word)) =
      ndPMFWeightedExpectation Tao.geom2PNat
        (fun v => ndPropIndicatorOvershoot (P [v])) := by
  classical
  rw [geom2PNatListPMF_one_eq_map_singleton_overshoot]
  exact ndPMFWeightedExpectation_map_of_abs_le
    Tao.geom2PNat (fun v => [v])
    (fun word => ndPropIndicatorOvershoot (P word)) 1 (by norm_num)
    (fun word => by
      by_cases h : P word <;> simp [ndPropIndicatorOvershoot, h])

private theorem ndPMFWeightedExpectation_congr_apply_ne_zero_overshoot
    {Alpha : Type*} (p : PMF Alpha) (f g : Alpha → ℝ)
    (h : ∀ x, p x ≠ 0 → f x = g x) :
    ndPMFWeightedExpectation p f = ndPMFWeightedExpectation p g := by
  unfold ndPMFWeightedExpectation
  apply tsum_congr
  intro x
  by_cases hx : p x = 0
  · rw [hx]
    simp
  · rw [h x hx]

private theorem ndPMFWeightedExpectation_add_of_abs_le_overshoot
    {Alpha : Type*} (p : PMF Alpha) (f g : Alpha → ℝ)
    (Hf Hg : ℝ) (hHf : 0 ≤ Hf) (hHg : 0 ≤ Hg)
    (hf : ∀ x, |f x| ≤ Hf) (hg : ∀ x, |g x| ≤ Hg) :
    ndPMFWeightedExpectation p (fun x => f x + g x) =
      ndPMFWeightedExpectation p f + ndPMFWeightedExpectation p g := by
  have hfs := summable_pmf_toReal_mul_of_abs_le p f Hf hHf hf
  have hgs := summable_pmf_toReal_mul_of_abs_le p g Hg hHg hg
  unfold ndPMFWeightedExpectation
  calc
    (∑' x, (p x).toReal * (f x + g x)) =
        ∑' x, ((p x).toReal * f x + (p x).toReal * g x) := by
      apply tsum_congr
      intro x
      ring
    _ = (∑' x, (p x).toReal * f x) +
          ∑' x, (p x).toReal * g x := hfs.tsum_add hgs

private theorem
    ndGeom2ShiftedWideSymmetric_terminalBadExpectation_eq_tailFactor
    {b a s K : ℕ} {pre : List ℕ+}
    (hpre : pre.length = s - 1) (hsPos : 0 < s) :
    ndPMFWeightedExpectation Tao.geom2PNat (fun v =>
        ndPropIndicatorOvershoot
          (ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAt
            b a s K (pre ++ [v]))) =
      (1 / 2 : ℝ) ^ (K + 1) *
        ndPMFWeightedExpectation Tao.geom2PNat (fun v =>
          ndPropIndicatorOvershoot
            (ndGeom2ShiftedWideSymmetricFirstCrossingAt
              b a s (pre ++ [v]))) := by
  classical
  let Bad : ℕ+ → Prop := fun v =>
    ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAt
      b a s K (pre ++ [v])
  let First : ℕ+ → Prop := fun v =>
    ndGeom2ShiftedWideSymmetricFirstCrossingAt b a s (pre ++ [v])
  let Tail : Set ℕ+ := {v | K + 1 < (v : ℕ)}
  have hlen (v : ℕ+) : (pre ++ [v]).length = s := by
    simp only [List.length_append, List.length_singleton, hpre]
    omega
  have hbadTail (v : ℕ+) (hv : Bad v) : v ∈ Tail := by
    have h := ndGeom2ShiftedWideSymmetric_terminal_gt_succ_of_badOvershoot
      (hlen v) hv
    simpa [Tail, Tao.geom2PNatListTerminalValue] using h
  have htailInsert :
      (fun v : ℕ+ => ndPropIndicatorOvershoot (Bad v)) =
        (fun v => Tail.indicator
          (fun x => ndPropIndicatorOvershoot (Bad x)) v) := by
    funext v
    by_cases hv : Bad v
    · simp [ndPropIndicatorOvershoot, hv, hbadTail v hv]
    · by_cases ht : v ∈ Tail
      · rw [Set.indicator_of_mem ht]
      · rw [Set.indicator_of_notMem ht]
        simp [ndPropIndicatorOvershoot, hv]
  have hshift (v : ℕ+) :
      Bad (ndPNatAddNat (K + 1) v) ↔ First v := by
    simpa only [Bad, First,
      ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAt,
      ndGeom2ShiftedWideSymmetricFirstCrossingAt] using
      (ndFiniteFirstShiftedWideSymmetricCrossing_raiseTerminal_iff_badOvershoot
        (b := b) (a := a) (s := s) (K := K) v hpre hsPos)
  change ndPMFWeightedExpectation Tao.geom2PNat
      (fun v => ndPropIndicatorOvershoot (Bad v)) = _
  rw [htailInsert]
  rw [ndPMFWeightedExpectation_geom2_tail_indicator_eq_shift
    (K + 1) (fun x => ndPropIndicatorOvershoot (Bad x))]
  apply congrArg (fun z : ℝ => (1 / 2 : ℝ) ^ (K + 1) * z)
  apply congrArg (ndPMFWeightedExpectation Tao.geom2PNat)
  funext v
  exact congrArg ndPropIndicatorOvershoot (propext (hshift v))

theorem
    ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAtMass_eq_tailFactor
    {b a s K : ℕ}
    (hs : s ∈ ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b) :
    ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAtMass b a s K =
      (1 / 2 : ℝ) ^ (K + 1) *
        ndGeom2ShiftedWideSymmetricFirstCrossingAtMass b a s := by
  classical
  have hsPos : 0 < s := by
    have hsBounds := Finset.mem_Icc.mp hs
    omega
  let Bad : List ℕ+ → Prop := fun word =>
    ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAt
      b a s K word
  let First : List ℕ+ → Prop := fun word =>
    ndGeom2ShiftedWideSymmetricFirstCrossingAt b a s word
  have hsSplit : s - 1 + 1 = s := by omega
  unfold ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAtMass
    ndGeom2ShiftedWideSymmetricFirstCrossingAtMass
  rw [ndPMFEventMass_eq_expectation_indicator_overshoot,
    ndPMFEventMass_eq_expectation_indicator_overshoot]
  change ndPMFWeightedExpectation (Tao.geom2PNatListPMF s)
      (fun word => ndPropIndicatorOvershoot (Bad word)) =
    (1 / 2 : ℝ) ^ (K + 1) *
      ndPMFWeightedExpectation (Tao.geom2PNatListPMF s)
        (fun word => ndPropIndicatorOvershoot (First word))
  calc
    ndPMFWeightedExpectation (Tao.geom2PNatListPMF s)
        (fun word => ndPropIndicatorOvershoot (Bad word)) =
      ndPMFWeightedExpectation (Tao.geom2PNatListPMF (s - 1))
        (fun pre =>
          ndPMFWeightedExpectation (Tao.geom2PNatListPMF 1)
            (fun future =>
              ndPropIndicatorOvershoot (Bad (pre ++ future)))) := by
        rw [← hsSplit]
        exact ndPMFWeightedExpectation_geom2_append
          (s - 1) 1 (fun word => ndPropIndicatorOvershoot (Bad word))
          1 (by norm_num) (fun word => by
            by_cases h : Bad word <;> simp [ndPropIndicatorOvershoot, h])
    _ = ndPMFWeightedExpectation (Tao.geom2PNatListPMF (s - 1))
        (fun pre =>
          ndPMFWeightedExpectation Tao.geom2PNat
            (fun v => ndPropIndicatorOvershoot (Bad (pre ++ [v])))) := by
        apply ndPMFWeightedExpectation_congr_apply_ne_zero_overshoot
        intro pre _hpreMass
        exact ndPMFWeightedExpectation_geom2_one_indicator_overshoot
          (fun future => Bad (pre ++ future))
    _ = ndPMFWeightedExpectation (Tao.geom2PNatListPMF (s - 1))
        (fun pre =>
          (1 / 2 : ℝ) ^ (K + 1) *
            ndPMFWeightedExpectation Tao.geom2PNat
              (fun v => ndPropIndicatorOvershoot (First (pre ++ [v])))) := by
        apply ndPMFWeightedExpectation_congr_apply_ne_zero_overshoot
        intro pre hpreMass
        have hpre : pre.length = s - 1 := by
          by_contra hne
          exact hpreMass
            (Tao.geom2PNatListPMF_apply_eq_zero_of_length_ne
              (s - 1) pre hne)
        simpa only [Bad, First] using
          ndGeom2ShiftedWideSymmetric_terminalBadExpectation_eq_tailFactor
            (b := b) (a := a) (s := s) (K := K) hpre hsPos
    _ = (1 / 2 : ℝ) ^ (K + 1) *
        ndPMFWeightedExpectation (Tao.geom2PNatListPMF (s - 1))
          (fun pre =>
            ndPMFWeightedExpectation Tao.geom2PNat
              (fun v => ndPropIndicatorOvershoot (First (pre ++ [v])))) := by
        exact ndPMFWeightedExpectation_const_mul
          (Tao.geom2PNatListPMF (s - 1))
          ((1 / 2 : ℝ) ^ (K + 1)) _
    _ = (1 / 2 : ℝ) ^ (K + 1) *
        ndPMFWeightedExpectation (Tao.geom2PNatListPMF (s - 1))
          (fun pre =>
            ndPMFWeightedExpectation (Tao.geom2PNatListPMF 1)
              (fun future =>
                ndPropIndicatorOvershoot (First (pre ++ future)))) := by
        congr 1
        apply ndPMFWeightedExpectation_congr_apply_ne_zero_overshoot
        intro pre _hpreMass
        symm
        exact ndPMFWeightedExpectation_geom2_one_indicator_overshoot
          (fun future => First (pre ++ future))
    _ = (1 / 2 : ℝ) ^ (K + 1) *
        ndPMFWeightedExpectation (Tao.geom2PNatListPMF s)
          (fun word => ndPropIndicatorOvershoot (First word)) := by
        congr 1
        rw [← hsSplit]
        symm
        exact ndPMFWeightedExpectation_geom2_append
          (s - 1) 1 (fun word => ndPropIndicatorOvershoot (First word))
          1 (by norm_num) (fun word => by
            by_cases h : First word <;>
              simp [ndPropIndicatorOvershoot, h])

theorem ndGeom2ShiftedWideSymmetricFirstCrossingAtMass_eq_bounded_add_bad
    (b a s K : ℕ) :
    ndGeom2ShiftedWideSymmetricFirstCrossingAtMass b a s =
      ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass
          b a s K +
        ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAtMass
          b a s K := by
  classical
  let First : List ℕ+ → Prop := fun word =>
    ndGeom2ShiftedWideSymmetricFirstCrossingAt b a s word
  let Good : List ℕ+ → Prop := fun word =>
    ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt
      b a s K word
  let Bad : List ℕ+ → Prop := fun word =>
    ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAt
      b a s K word
  unfold ndGeom2ShiftedWideSymmetricFirstCrossingAtMass
    ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass
    ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAtMass
  rw [ndPMFEventMass_eq_expectation_indicator_overshoot,
    ndPMFEventMass_eq_expectation_indicator_overshoot,
    ndPMFEventMass_eq_expectation_indicator_overshoot]
  change ndPMFWeightedExpectation (Tao.geom2PNatListPMF s)
      (fun word => ndPropIndicatorOvershoot (First word)) =
    ndPMFWeightedExpectation (Tao.geom2PNatListPMF s)
        (fun word => ndPropIndicatorOvershoot (Good word)) +
      ndPMFWeightedExpectation (Tao.geom2PNatListPMF s)
        (fun word => ndPropIndicatorOvershoot (Bad word))
  rw [← ndPMFWeightedExpectation_add_of_abs_le_overshoot
    (Tao.geom2PNatListPMF s)
    (fun word => ndPropIndicatorOvershoot (Good word))
    (fun word => ndPropIndicatorOvershoot (Bad word))
    1 1 (by norm_num) (by norm_num)
    (fun word => by
      by_cases h : Good word <;> simp [ndPropIndicatorOvershoot, h])
    (fun word => by
      by_cases h : Bad word <;> simp [ndPropIndicatorOvershoot, h])]
  apply congrArg (ndPMFWeightedExpectation (Tao.geom2PNatListPMF s))
  funext word
  by_cases hfirst : First word
  · by_cases hcap :
        ndGeom2ShiftedWideSymmetricBoundedOvershoot b a s K word
    · have hgood : Good word := by
        exact ⟨hfirst, hcap⟩
      have hbad : ¬Bad word := by
        intro h
        exact h.2 hcap
      simp [ndPropIndicatorOvershoot, hfirst, hgood, hbad]
    · have hgood : ¬Good word := by
        intro h
        exact hcap h.2
      have hbad : Bad word := ⟨hfirst, hcap⟩
      simp [ndPropIndicatorOvershoot, hfirst, hgood, hbad]
  · have hgood : ¬Good word := fun h => hfirst h.1
    have hbad : ¬Bad word := fun h => hfirst h.1
    simp [ndPropIndicatorOvershoot, hfirst, hgood, hbad]

theorem
    ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass_eq
    {b a s K : ℕ}
    (hs : s ∈ ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b) :
    ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass b a s K =
      (1 - (1 / 2 : ℝ) ^ (K + 1)) *
        ndGeom2ShiftedWideSymmetricFirstCrossingAtMass b a s := by
  have hsplit :=
    ndGeom2ShiftedWideSymmetricFirstCrossingAtMass_eq_bounded_add_bad
      b a s K
  rw [ndGeom2ShiftedWideSymmetricFirstCrossingBadOvershootAtMass_eq_tailFactor
    hs] at hsplit
  linarith

theorem
    ndGeom2ShiftedWideSymmetricFirstCrossingAtMass_eq_horizonMass
    {b a s : ℕ}
    (hs : s ∈ ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b) :
    ndGeom2ShiftedWideSymmetricFirstCrossingAtMass b a s =
      ((Tao.geom2PNatListPMF
          (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure
        {full |
          ndGeom2ShiftedWideSymmetricFirstCrossingAt b a s full}).toReal := by
  have hsH : s ≤ ndGeom2ShiftedWideSymmetricHorizon b :=
    (Finset.mem_Icc.mp hs).2
  let A : Set (List ℕ+) :=
    {pre | ndGeom2ShiftedWideSymmetricFirstCrossingAt b a s pre}
  have hset :
      {full : List ℕ+ |
        ndGeom2ShiftedWideSymmetricFirstCrossingAt b a s full} =
        (fun full : List ℕ+ => full.take s) ⁻¹' A := by
    ext full
    simpa only [A, ndGeom2ShiftedWideSymmetricFirstCrossingAt] using
      (ndFiniteFirstShiftedWideSymmetricCrossing_take_iff b a s full).symm
  change ((Tao.geom2PNatListPMF s).toOuterMeasure A).toReal = _
  rw [hset]
  symm
  exact geom2PNatListPMF_take_event_outerMeasure_toReal hsH A

theorem sum_firstCrossingAtMass_eq_shiftedWideSymmetricCrossingProbability
    (b a : ℕ) :
    (∑ s ∈ ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b,
        ndGeom2ShiftedWideSymmetricFirstCrossingAtMass b a s) =
      ndGeom2ShiftedWideSymmetricCrossingProbability b a := by
  classical
  let I := ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b
  let Hit := ndGeom2ShiftedWideSymmetricCrossingEligibleHit b a
  calc
    (∑ s ∈ I, ndGeom2ShiftedWideSymmetricFirstCrossingAtMass b a s) =
        ∑ s ∈ I,
          ((Tao.geom2PNatListPMF
              (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure
            {full | ndFiniteFirstHitAt I Hit s full}).toReal := by
      apply Finset.sum_congr rfl
      intro s hs
      simpa only [I, Hit,
        ndGeom2ShiftedWideSymmetricFirstCrossingAt] using
        ndGeom2ShiftedWideSymmetricFirstCrossingAtMass_eq_horizonMass
          (b := b) (a := a) hs
    _ = ((Tao.geom2PNatListPMF
          (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure
        {full | ndFiniteAnyHit I Hit full}).toReal :=
      sum_firstHit_pmfEventMass_eq_anyHit
        (Tao.geom2PNatListPMF
          (ndGeom2ShiftedWideSymmetricHorizon b)) I Hit
    _ = ndGeom2ShiftedWideSymmetricCrossingProbability b a := by
      unfold ndGeom2ShiftedWideSymmetricCrossingProbability
      apply congrArg (fun E : Set (List ℕ+) =>
        ((Tao.geom2PNatListPMF
          (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure E).toReal)
      ext full
      simpa only [I, Hit] using
        (ndGeom2ShiftedWideSymmetricCrossing_iff_anyEligibleHit
          b a full).symm

noncomputable def
    ndGeom2ShiftedWideSymmetricBoundedOvershootCrossingProbability
    (b a K : ℕ) : ℝ :=
  ∑ s ∈ ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b,
    ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass
      b a s K

theorem
    ndGeom2ShiftedWideSymmetricBoundedOvershootCrossingProbability_eq
    (b a K : ℕ) :
    ndGeom2ShiftedWideSymmetricBoundedOvershootCrossingProbability b a K =
      (1 - (1 / 2 : ℝ) ^ (K + 1)) *
        ndGeom2ShiftedWideSymmetricCrossingProbability b a := by
  classical
  unfold ndGeom2ShiftedWideSymmetricBoundedOvershootCrossingProbability
  calc
    (∑ s ∈ ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b,
        ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass
          b a s K) =
      ∑ s ∈ ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b,
        (1 - (1 / 2 : ℝ) ^ (K + 1)) *
          ndGeom2ShiftedWideSymmetricFirstCrossingAtMass b a s := by
        apply Finset.sum_congr rfl
        intro s hs
        exact
          ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass_eq hs
    _ = (1 - (1 / 2 : ℝ) ^ (K + 1)) *
        ∑ s ∈ ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b,
          ndGeom2ShiftedWideSymmetricFirstCrossingAtMass b a s := by
        rw [Finset.mul_sum]
    _ = (1 - (1 / 2 : ℝ) ^ (K + 1)) *
        ndGeom2ShiftedWideSymmetricCrossingProbability b a := by
      rw [sum_firstCrossingAtMass_eq_shiftedWideSymmetricCrossingProbability]

theorem
    one_sub_tailFactor_mul_shiftRate_le_boundedOvershootCrossingProbability
    {b a K : ℕ} (hb : 200 ≤ b)
    (ha : a ∈ ndGeom2ShiftedWideSymmetricShiftIndices b) :
    (1 - (1 / 2 : ℝ) ^ (K + 1)) *
        (1 - 4 * Real.exp (-(b : ℝ) / 2560000)) ≤
      ndGeom2ShiftedWideSymmetricBoundedOvershootCrossingProbability
        b a K := by
  rw [ndGeom2ShiftedWideSymmetricBoundedOvershootCrossingProbability_eq]
  apply mul_le_mul_of_nonneg_left
    (one_sub_four_mul_exp_le_shiftedWideSymmetricCrossingProbability
      hb ha)
  exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))

end

end PositiveDensity

end ND

end Erdos1135Predecessor
