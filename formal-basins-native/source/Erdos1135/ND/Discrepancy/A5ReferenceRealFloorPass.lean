import Erdos1135.ND.Discrepancy.A5ReferenceTotalizedSourceRate
import Erdos1135.ND.Discrepancy.A5FlatNoHitRate
import Erdos1135.ND.Probability.UniformFloorPerturbation

/-!
# A5 real/floor passage transport

This leaf transports the checked natural A5 flat/harmonic passage comparison
to the exact real source windows.  The two outer moves compare unequal finite
source carriers through ambient natural-number events and apply finite Hahn
once each.  The already checked natural middle keeps its factor `32`.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

/-- Ambient event discrepancy between two unrelated finite source carriers
controls the full-L1 distance between their pushforwards to one finite target.
-/
theorem taoTV_map_ambient_le_two_mul_of_pmfProb_discrepancy
    {sigma tau gamma delta : Type*}
    [Fintype sigma] [Fintype tau] [Fintype delta]
    (p : PMF sigma) (q : PMF tau)
    (i : sigma -> gamma) (j : tau -> gamma) (f : gamma -> delta)
    {epsilon : Real}
    (hsource : forall E : Set gamma,
      |Tao.pmfProb p (i ⁻¹' E) - Tao.pmfProb q (j ⁻¹' E)| <= epsilon) :
    Tao.taoTV (p.map (f ∘ i)) (q.map (f ∘ j)) <= 2 * epsilon := by
  apply Tao.taoTV_le_two_mul_of_event_discrepancy
  intro A
  rw [Tao.pmfProb_map_preimage, Tao.pmfProb_map_preimage]
  exact hsource (f ⁻¹' A)

/-- The two branch-indexed harmonic source windows obey the normalized
floor-to-real ambient-event discrepancy from the checked Tao endpoint lemmas.
-/
theorem abs_logFinsetProb_oddBlock_floor_transport_sub_le
    {x : Real} (facts : Tao.TaoProp111RealFloorWindowMassFacts x)
    (branch : Tao.TaoSection5SourceBranch) (E : Set Nat) :
    |Tao.logFinsetProb
        (oddBlock (Tao.taoSection5SourceY (Nat.floor x) branch)) E -
      Tao.logFinsetProb (oddBlock (transportSourceY x branch)) E| <=
      96000 /
        (((Nat.floor x : Nat) : Real) *
          Real.log ((Nat.floor x : Nat) : Real)) := by
  cases branch with
  | alpha =>
      simpa [oddBlock, transportSourceY, Tao.taoSection5SourceY, alpha] using
        Tao.abs_logFinsetProb_taoNyOddWindow_floor_taoAlpha_sub_le
          facts.one_le_x facts.log_floor_pos facts.alpha_floor
            facts.alpha_real E
  | alphaSq =>
      simpa [oddBlock, transportSourceY, Tao.taoSection5SourceY, alpha] using
        Tao.abs_logFinsetProb_taoNyOddWindow_floor_taoAlpha_sq_sub_le
          facts.one_le_x facts.log_floor_pos facts.alphaSq_floor
            facts.alphaSq_real E

/-- Uniform real/floor source transport survives the common real-threshold
pass map with exactly one finite-Hahn factor.
-/
theorem eventually_taoTV_uniformPassLaw_floor_transport_le :
    ∀ᶠ x : Real in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch)
        (hx : 1 <= x)
        (hFloor :
          (oddBlock
            (Tao.taoSection5SourceY (Nat.floor x) branch)).Nonempty)
        (hReal : (oddBlock (transportSourceY x branch)).Nonempty),
        Tao.taoTV
            (uniformPassLaw x
              (Tao.taoSection5SourceY (Nat.floor x) branch) hx hFloor)
            (uniformPassLaw x (transportSourceY x branch) hx hReal) <=
          2 * (96 * x ^ (-(99 / 100 : Real))) := by
  filter_upwards
      [eventually_abs_pmfProb_uniformOddBlock_floor_transport_sub_le]
      with x hsource
  intro branch hx hFloor hReal
  unfold uniformPassLaw
  simpa only [Function.comp_def] using
    (taoTV_map_ambient_le_two_mul_of_pmfProb_discrepancy
      (uniformOddBlockPMF
        (Tao.taoSection5SourceY (Nat.floor x) branch) hFloor)
      (uniformOddBlockPMF (transportSourceY x branch) hReal)
      Subtype.val Subtype.val (fun N => passLocationOrOne x N hx)
      (hsource branch hFloor hReal))

/-- The eventual uniform source comparison transfers the real no-hit event
with no Hahn factor.  Natural and real threshold events agree after flooring.
-/
theorem eventually_uniformNoHitProbability_floor_transport_le :
    ∀ᶠ x : Real in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch)
        (hFloor :
          (oddBlock
            (Tao.taoSection5SourceY (Nat.floor x) branch)).Nonempty)
        (hReal : (oddBlock (transportSourceY x branch)).Nonempty),
        uniformNoHitProbability x (transportSourceY x branch) hReal <=
          uniformNoHitProbability (Nat.floor x : Real)
              (Tao.taoSection5SourceY (Nat.floor x) branch) hFloor +
            96 * x ^ (-(99 / 100 : Real)) := by
  filter_upwards
      [eventually_abs_pmfProb_uniformOddBlock_floor_transport_sub_le,
        eventually_ge_atTop (1 : Real)]
      with x hsource hx
  intro branch hFloor hReal
  have hdisc := hsource branch hFloor hReal
    {N : Nat | ¬ Tao.syracuseHitsAtMostReal N x}
  have hdisc' :
      |Tao.pmfProb
          (uniformOddBlockPMF
            (Tao.taoSection5SourceY (Nat.floor x) branch) hFloor)
          {N | ¬ Tao.syracuseHitsAtMostReal N.1 x} -
        Tao.pmfProb
          (uniformOddBlockPMF (transportSourceY x branch) hReal)
          {N | ¬ Tao.syracuseHitsAtMostReal N.1 x}| <=
        96 * x ^ (-(99 / 100 : Real)) := by
    simpa only [Set.mem_setOf_eq] using hdisc
  have hFloorEvent :
      Tao.pmfProb
          (uniformOddBlockPMF
            (Tao.taoSection5SourceY (Nat.floor x) branch) hFloor)
          {N | ¬ Tao.syracuseHitsAtMostReal N.1 x} =
        Tao.pmfProb
          (uniformOddBlockPMF
            (Tao.taoSection5SourceY (Nat.floor x) branch) hFloor)
          {N | ¬ Tao.syracuseHitsAtMostReal N.1 (Nat.floor x : Real)} := by
    congr 1
    ext N
    simp only [Set.mem_setOf_eq]
    rw [Tao.syracuseHitsAtMostReal_iff_floor (zero_le_one.trans hx),
      Tao.syracuseHitsAtMostReal_iff_floor (Nat.cast_nonneg _),
      Nat.floor_natCast]
  unfold uniformNoHitProbability
  rw [hFloorEvent] at hdisc'
  calc
    Tao.pmfProb
        (uniformOddBlockPMF (transportSourceY x branch) hReal)
        {N | ¬ Tao.syracuseHitsAtMostReal N.1 x} <=
      Tao.pmfProb
          (uniformOddBlockPMF
            (Tao.taoSection5SourceY (Nat.floor x) branch) hFloor)
          {N | ¬ Tao.syracuseHitsAtMostReal N.1 (Nat.floor x : Real)} +
        |Tao.pmfProb
            (uniformOddBlockPMF
              (Tao.taoSection5SourceY (Nat.floor x) branch) hFloor)
            {N | ¬ Tao.syracuseHitsAtMostReal N.1 (Nat.floor x : Real)} -
          Tao.pmfProb
            (uniformOddBlockPMF (transportSourceY x branch) hReal)
            {N | ¬ Tao.syracuseHitsAtMostReal N.1 x}| := by
        linarith [neg_le_abs
          (Tao.pmfProb
              (uniformOddBlockPMF
                (Tao.taoSection5SourceY (Nat.floor x) branch) hFloor)
              {N | ¬ Tao.syracuseHitsAtMostReal N.1 (Nat.floor x : Real)} -
            Tao.pmfProb
              (uniformOddBlockPMF (transportSourceY x branch) hReal)
              {N | ¬ Tao.syracuseHitsAtMostReal N.1 x})]
    _ <= Tao.pmfProb
          (uniformOddBlockPMF
            (Tao.taoSection5SourceY (Nat.floor x) branch) hFloor)
          {N | ¬ Tao.syracuseHitsAtMostReal N.1 (Nat.floor x : Real)} +
        96 * x ^ (-(99 / 100 : Real)) :=
      add_le_add le_rfl hdisc'

/-- The real branch source has positive reciprocal mass under the common
eventual floor/real normalizer packet.
-/
theorem logFinsetMass_oddBlock_transportSourceY_pos
    {x : Real} (facts : Tao.TaoProp111RealFloorWindowMassFacts x)
    (branch : Tao.TaoSection5SourceBranch) :
    0 < Tao.logFinsetMass (oddBlock (transportSourceY x branch)) := by
  have hlower :
      0 < Real.log ((Nat.floor x : Nat) : Real) / 8000 :=
    div_pos facts.log_floor_pos (by norm_num)
  cases branch with
  | alpha =>
      exact hlower.trans_le (by
        simpa [oddBlock, transportSourceY, alpha] using facts.alpha_real)
  | alphaSq =>
      exact hlower.trans_le (by
        simpa [oddBlock, transportSourceY, alpha] using facts.alphaSq_real)

/-- Harmonic real/floor source transport survives the common real-threshold
pass map with exactly one finite-Hahn factor.
-/
theorem taoTV_logPassLaw_floor_transport_le
    {x : Real} (facts : Tao.TaoProp111RealFloorWindowMassFacts x)
    (branch : Tao.TaoSection5SourceBranch) (hx : 1 <= x)
    (hFloor : 0 < Tao.logFinsetMass
      (oddBlock (Tao.taoSection5SourceY (Nat.floor x) branch)))
    (hReal : 0 < Tao.logFinsetMass
      (oddBlock (transportSourceY x branch))) :
    Tao.taoTV
        (logPassLaw x
          (Tao.taoSection5SourceY (Nat.floor x) branch)
          hx hFloor)
        (logPassLaw x (transportSourceY x branch) hx hReal) <=
      2 * (96000 /
        (((Nat.floor x : Nat) : Real) *
          Real.log ((Nat.floor x : Nat) : Real))) := by
  unfold logPassLaw
  simpa only [Function.comp_def] using
    (taoTV_map_ambient_le_two_mul_of_pmfProb_discrepancy
      (logOddBlockPMF
        (Tao.taoSection5SourceY (Nat.floor x) branch) hFloor)
      (logOddBlockPMF (transportSourceY x branch) hReal)
      Subtype.val Subtype.val
      (fun N => passLocationOrOne x N hx)
      (by
        intro E
        unfold logOddBlockPMF
        change
          |Tao.pmfProb
              (Tao.logFinsetPMF
                (oddBlock
                  (Tao.taoSection5SourceY (Nat.floor x) branch)) hFloor)
              {N | N.1 ∈ E} -
            Tao.pmfProb
              (Tao.logFinsetPMF
                (oddBlock (transportSourceY x branch)) hReal)
              {N | N.1 ∈ E}| <= _
        rw [Tao.pmfProb_logFinsetPMF, Tao.pmfProb_logFinsetPMF]
        exact
          abs_logFinsetProb_oddBlock_floor_transport_sub_le facts branch E))

/-- At the floor source, the public uniform pass law is exactly the checked
flat A5 totalized law on the literal target `floor x`.
-/
theorem uniformPassLaw_floorSource_eq_ndTotalizedFlat
    {x : Real} (hx : 1 <= x) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount (Nat.floor x) branch) :
    uniformPassLaw x
        (Tao.taoSection5SourceY (Nat.floor x) branch) hx
        (ndA5OddBlock_sourceY_nonempty
          (Tao.one_le_floor_of_one_le hx) branch hcount) =
      ndTotalizedPassLaw (Nat.floor x) (Tao.one_le_floor_of_one_le hx)
        (ndA5FlatSourcePMF (Nat.floor x) branch
          (Tao.one_le_floor_of_one_le hx) hcount) := by
  unfold uniformPassLaw ndA5FlatSourcePMF ndTotalizedPassLaw
  rw [PMF.map_comp]
  congr 1

/-- At the floor source, the public harmonic pass law is exactly the checked
harmonic A5 totalized law on the literal target `floor x`.
-/
theorem logPassLaw_floorSource_eq_ndTotalizedHarmonic
    {x : Real} (hx : 1 <= x) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount (Nat.floor x) branch) :
    logPassLaw x
        (Tao.taoSection5SourceY (Nat.floor x) branch) hx
        (logFinsetMass_ndA5OddBlock_sourceY_pos
          (Tao.one_le_floor_of_one_le hx) branch hcount) =
      ndTotalizedPassLaw (Nat.floor x) (Tao.one_le_floor_of_one_le hx)
        (ndA5HarmonicSourcePMF (Nat.floor x) branch
          (Tao.one_le_floor_of_one_le hx) hcount) := by
  unfold logPassLaw ndA5HarmonicSourcePMF ndTotalizedPassLaw
  rw [PMF.map_comp]
  congr 1

/-- Raw real-source A5 rows needed by ND-M2: genuine flat escape pays one
uniform source error, while same-branch passage full L1 pays the two outer
Hahn factors around the already checked natural `32` middle.
-/
theorem eventually_ndA5RealSameBranchRawBounds
    {c kappa d : Real}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hd20 : d < 1 / 20)
    (hdk : d < 1 / (2 * kappa)) :
    ∀ᶠ x : Real in atTop,
      ∀ (hx : 1 <= x) (branch : Tao.TaoSection5SourceBranch),
        let B := Nat.floor x
        let y := transportSourceY x branch
        ∃ hwindow : (oddBlock y).Nonempty,
        ∃ hmass : 0 < Tao.logFinsetMass (oddBlock y),
          uniformNoHitProbability x y hwindow <=
              44 * (B : Real) ^ (-(1 / 32000 : Real)) +
                96 * x ^ (-(99 / 100 : Real)) ∧
            passFullL1 x y hx hwindow hmass <=
              2 * (96 * x ^ (-(99 / 100 : Real))) +
                32 * ndA5ReferenceInteriorScalarRate B d +
                  2 * (96000 /
                    ((B : Real) * Real.log (B : Real))) := by
  have hFloorTendsto :
      Tendsto (fun x : Real => Nat.floor x) atTop atTop :=
    tendsto_nat_floor_atTop
  have hFloorCastTendsto :
      Tendsto (fun x : Real => ((Nat.floor x : Nat) : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hFloorTendsto
  have hLogFloorTendsto :
      Tendsto
        (fun x : Real => Real.log ((Nat.floor x : Nat) : Real))
        atTop atTop :=
    Real.tendsto_log_atTop.comp hFloorCastTendsto
  filter_upwards
      [Tao.eventually_taoProp111RealFloorWindowMassFacts,
        eventually_taoTV_uniformPassLaw_floor_transport_le,
        eventually_uniformNoHitProbability_floor_transport_le,
        hFloorTendsto.eventually
          eventually_uniformNoHitProbability_natCast_taoSection5SourceY_le_forty_four,
        hFloorTendsto.eventually
          (eventually_ndA5FlatHarmonicTotalizedPassTV_le_thirty_two
            hPhase hd hd20 hdk),
        hLogFloorTendsto.eventually_ge_atTop (300000 : Real)]
      with x facts hUniformTV hNoHitTransport hNaturalNoHit hNaturalTV hlog
  intro hx branch
  dsimp only
  let B := Nat.floor x
  have hB : 1 <= B := Tao.one_le_floor_of_one_le hx
  have hcountThree : 3 <= ndA5BandCount B branch :=
    ndA5BandCount_ge_three_of_guards hB (by simpa only [B] using hlog)
  have hcount : 0 < ndA5BandCount B branch := by omega
  let hFloorWindow := ndA5OddBlock_sourceY_nonempty hB branch hcount
  let hFloorMass :=
    logFinsetMass_ndA5OddBlock_sourceY_pos hB branch hcount
  have hpacket := oddBlock_floor_transport_card_packet facts branch
  dsimp only at hpacket
  let hRealWindow := hpacket.2.1
  let hRealMass := logFinsetMass_oddBlock_transportSourceY_pos facts branch
  refine ⟨hRealWindow, hRealMass, ?_, ?_⟩
  · calc
      uniformNoHitProbability x (transportSourceY x branch) hRealWindow <=
          uniformNoHitProbability (B : Real)
              (Tao.taoSection5SourceY B branch) hFloorWindow +
            96 * x ^ (-(99 / 100 : Real)) := by
        simpa only [B, hFloorWindow, hRealWindow] using
          hNoHitTransport branch hFloorWindow hRealWindow
      _ <= 44 * (B : Real) ^ (-(1 / 32000 : Real)) +
          96 * x ^ (-(99 / 100 : Real)) := by
        exact add_le_add (hNaturalNoHit branch hB hcount) le_rfl
  · let uReal :=
      uniformPassLaw x (transportSourceY x branch) hx hRealWindow
    let uFloor :=
      uniformPassLaw x (Tao.taoSection5SourceY B branch) hx hFloorWindow
    let hFloor :=
      logPassLaw x (Tao.taoSection5SourceY B branch) hx hFloorMass
    let hReal :=
      logPassLaw x (transportSourceY x branch) hx hRealMass
    have huFloorReal :
        Tao.taoTV uFloor uReal <=
          2 * (96 * x ^ (-(99 / 100 : Real))) := by
      simpa only [uFloor, uReal, B, hFloorWindow, hRealWindow] using
        hUniformTV branch hx hFloorWindow hRealWindow
    have huRealFloor :
        Tao.taoTV uReal uFloor <=
          2 * (96 * x ^ (-(99 / 100 : Real))) := by
      rw [Tao.taoTV_comm]
      exact huFloorReal
    have hFloorMiddle :
        Tao.taoTV uFloor hFloor <=
          32 * ndA5ReferenceInteriorScalarRate B d := by
      have huFloor :
          uFloor =
            ndTotalizedPassLaw (Nat.floor x)
              (Tao.one_le_floor_of_one_le hx)
              (ndA5FlatSourcePMF (Nat.floor x) branch
                (Tao.one_le_floor_of_one_le hx) hcount) := by
        simpa only [uFloor, hFloorWindow, B] using
          uniformPassLaw_floorSource_eq_ndTotalizedFlat hx branch hcount
      have hhFloor :
          hFloor =
            ndTotalizedPassLaw (Nat.floor x)
              (Tao.one_le_floor_of_one_le hx)
              (ndA5HarmonicSourcePMF (Nat.floor x) branch
                (Tao.one_le_floor_of_one_le hx) hcount) := by
        simpa only [hFloor, hFloorMass, B] using
          logPassLaw_floorSource_eq_ndTotalizedHarmonic hx branch hcount
      rw [huFloor, hhFloor]
      simpa only [B] using
        hNaturalTV branch (Tao.one_le_floor_of_one_le hx) hcount
    have hhFloorReal :
        Tao.taoTV hFloor hReal <=
          2 * (96000 /
            ((B : Real) * Real.log (B : Real))) := by
      simpa only [hFloor, hReal, B, hFloorMass, hRealMass] using
        taoTV_logPassLaw_floor_transport_le
          facts branch hx hFloorMass hRealMass
    unfold passFullL1
    change Tao.taoTV uReal hReal <= _
    calc
      Tao.taoTV uReal hReal <=
          Tao.taoTV uReal uFloor + Tao.taoTV uFloor hReal :=
        Tao.taoTV_triangle uReal uFloor hReal
      _ <= Tao.taoTV uReal uFloor +
          (Tao.taoTV uFloor hFloor + Tao.taoTV hFloor hReal) :=
        add_le_add le_rfl (Tao.taoTV_triangle uFloor hFloor hReal)
      _ <= 2 * (96 * x ^ (-(99 / 100 : Real))) +
          (32 * ndA5ReferenceInteriorScalarRate B d +
            2 * (96000 / ((B : Real) * Real.log (B : Real)))) :=
        add_le_add huRealFloor (add_le_add hFloorMiddle hhFloorReal)
      _ = 2 * (96 * x ^ (-(99 / 100 : Real))) +
          32 * ndA5ReferenceInteriorScalarRate B d +
            2 * (96000 / ((B : Real) * Real.log (B : Real))) := by ring

end
end ND
end Erdos1135
