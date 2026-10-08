import Erdos1135.ND.Fourier.FixedTotalSplit
import Erdos1135.Tao.Section6.GatedSourceConvolution
import Erdos1135.Tao.Section6.FiniteFourierCollision

/-!
# Fixed-Total Two-Gated Collision

This leaf makes the first collision-consumer contact for P2.  It splits the
normalized iid Geom(2) list law into head and tail laws while retaining both
rejection routes in the aggregate `none` atom. Consequently the accepted
branches are defective submasses, and their accepted atom is a literal raw
cyclic convolution.

There is no hypergeometric or full-fiber normalization factor in this iid
identity.  A later presentation of the tail through its normalized
fixed-total fiber law must retain the separate endpoint-mass factor.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

open Tao

noncomputable section

private def ndOptionAdd {N : ℕ} :
    Option (ZMod N) → Option (ZMod N) → Option (ZMod N)
  | some y, some z => some (y + z)
  | _, _ => none

private noncomputable def ndOptionOptionConvolutionKernel
    {N : ℕ} [NeZero N] (tau : PMF (Option (ZMod N))) :
    Option (ZMod N) → PMF (Option (ZMod N))
  | none => PMF.pure none
  | some y => tau.map (ndOptionAdd (some y))

private noncomputable def ndOptionOptionConvolutionPMF
    {N : ℕ} [NeZero N]
    (h tau : PMF (Option (ZMod N))) :
    PMF (Option (ZMod N)) :=
  h.bind (ndOptionOptionConvolutionKernel tau)

private theorem ndOptionOptionConvolutionKernel_apply_some
    {N : ℕ} [NeZero N] (tau : PMF (Option (ZMod N)))
    (x y : ZMod N) :
    ndOptionOptionConvolutionKernel tau (some y) (some x) =
      tau (some (x - y)) := by
  unfold ndOptionOptionConvolutionKernel
  rw [PMF.map_apply]
  rw [tsum_eq_single (some (x - y))]
  · simp [ndOptionAdd]
  · intro z hz
    cases z with
    | none => simp [ndOptionAdd]
    | some z =>
        have hne : some x ≠ ndOptionAdd (some y) (some z) := by
          intro h
          apply hz
          congr 1
          simpa [ndOptionAdd, eq_sub_iff_add_eq, add_comm] using
            (Option.some.inj h).symm
        simp [hne]

private theorem ndOptionOptionConvolutionPMF_apply_some
    {N : ℕ} [NeZero N]
    (h tau : PMF (Option (ZMod N))) (x : ZMod N) :
    ndOptionOptionConvolutionPMF h tau (some x) =
      ∑ y : ZMod N, h (some y) * tau (some (x - y)) := by
  unfold ndOptionOptionConvolutionPMF
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  have hnone :
      (PMF.pure none : PMF (Option (ZMod N))) (some x) = 0 := by
    simp
  rw [show ndOptionOptionConvolutionKernel tau none =
      PMF.pure none by rfl]
  rw [hnone, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [ndOptionOptionConvolutionKernel_apply_some]

private theorem
    ndOptionOptionConvolutionPMF_apply_some_toReal_eq_rawConvolution
    {N : ℕ} [NeZero N]
    (h tau : PMF (Option (ZMod N))) (x : ZMod N) :
    (ndOptionOptionConvolutionPMF h tau (some x)).toReal =
      Tao.taoZModRawConvolution
        (fun y => (h (some y)).toReal)
        (fun z => (tau (some z)).toReal) x := by
  rw [ndOptionOptionConvolutionPMF_apply_some]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
    rfl
  · intro y _hy
    exact ENNReal.mul_ne_top (h.apply_ne_top (some y))
      (tau.apply_ne_top (some (x - y)))

/-- Tail law with the exact remaining-total gate. Rejected tail mass remains
at `none`. -/
noncomputable def ndSection6FixedSplitTailOptionPMF
    (q T l R : ℕ) : PMF (Option (ZMod (3 ^ (T + q)))) :=
  Tao.taoGatedOptionPMF
    (Tao.geom2PNatListPMF T)
    (fun tail => Tao.taoTupleWeight tail = R)
    (fun tail => Tao.taoSection6AmbientTailEmbed q T l
      (Tao.taoSection7OffsetZMod T tail))

/-- Accepted real tail mass. This is defective, not conditioned. -/
noncomputable def ndSection6FixedSplitTailSubmass
    (q T l R : ℕ) (z : ZMod (3 ^ (T + q))) : ℝ :=
  (ndSection6FixedSplitTailOptionPMF q T l R (some z)).toReal

/-- Factorized full-source gate: Tao's fixed head event and the exact tail
total selected by the split index. -/
def ndSection6FixedSplitSourceGate
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L)
    (full : List ℕ+) : Prop :=
  Tao.taoSection6HeadGate CA (T + (k + 1)) k s.headTotal
      (full.take (k + 1)) ∧
    Tao.taoTupleWeight (full.drop (k + 1)) = s.tailTotal

/-- The factorized gate is exactly Tao's head gate together with total weight
`L`. The reverse direction uses additive cancellation, not subtraction. -/
theorem ndSection6FixedSplitSourceGate_iff_headGate_and_weight
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L)
    (full : List ℕ+) :
    ndSection6FixedSplitSourceGate CA T k L s full ↔
      Tao.taoSection6HeadGate CA (T + (k + 1)) k s.headTotal
          (full.take (k + 1)) ∧
        Tao.taoTupleWeight full = L := by
  unfold ndSection6FixedSplitSourceGate
  constructor
  · rintro ⟨hhead, htail⟩
    refine ⟨hhead, ?_⟩
    calc
      Tao.taoTupleWeight full =
          Tao.taoTupleWeight (full.take (k + 1)) +
            Tao.taoTupleWeight (full.drop (k + 1)) :=
        (Tao.taoTupleWeight_take_add_drop_trajectory
          full (k + 1)).symm
      _ = s.headTotal + s.tailTotal := by
        rw [Tao.taoSection6HeadGate_weight hhead, htail]
      _ = L := s.total_eq
  · rintro ⟨hhead, hfull⟩
    refine ⟨hhead, ?_⟩
    exact Nat.add_left_cancel (n := s.headTotal) (by
      calc
        s.headTotal + Tao.taoTupleWeight (full.drop (k + 1)) =
            Tao.taoTupleWeight (full.take (k + 1)) +
              Tao.taoTupleWeight (full.drop (k + 1)) := by
          rw [Tao.taoSection6HeadGate_weight hhead]
        _ = Tao.taoTupleWeight full :=
          Tao.taoTupleWeight_take_add_drop_trajectory full (k + 1)
        _ = L := hfull
        _ = s.headTotal + s.tailTotal := s.total_eq.symm)

/-- Every accepted factorized source has the original fixed total. -/
theorem ndSection6FixedSplitSourceGate_weight
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L)
    {full : List ℕ+}
    (hgate : ndSection6FixedSplitSourceGate CA T k L s full) :
    Tao.taoTupleWeight full = L :=
  (ndSection6FixedSplitSourceGate_iff_headGate_and_weight
    CA T k L s full).mp hgate |>.2

/-- Full iid Option law with both rejection routes retained at the aggregate
`none` atom. -/
noncomputable def ndSection6FixedSplitSourcePMF
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L) :
    PMF (Option (ZMod (3 ^ (T + (k + 1))))) :=
  Tao.taoGatedOptionPMF
    (Tao.geom2PNatListPMF (T + (k + 1)))
    (ndSection6FixedSplitSourceGate CA T k L s)
    (Tao.taoSection7OffsetZMod (T + (k + 1)))

/-- Accepted real mass of the full fixed-split source law. -/
noncomputable def ndSection6FixedSplitSourceSubmass
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L)
    (x : ZMod (3 ^ (T + (k + 1)))) : ℝ :=
  (ndSection6FixedSplitSourcePMF CA T k L s (some x)).toReal

/-- Specialized two-rejection convolution law. -/
noncomputable def ndSection6FixedSplitConvolutionPMF
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L) :
    PMF (Option (ZMod (3 ^ (T + (k + 1))))) :=
  ndOptionOptionConvolutionPMF
    (Tao.taoSection6HeadOptionPMF
      CA (T + (k + 1)) k s.headTotal)
    (ndSection6FixedSplitTailOptionPMF
      (k + 1) T s.headTotal s.tailTotal)

private noncomputable def ndSection6FixedSplitPairKey
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L)
    (pair : List ℕ+ × List ℕ+) :
    Option (ZMod (3 ^ (T + (k + 1)))) :=
  ndOptionAdd
    (Tao.taoGatedOptionKey
      (Tao.taoSection6HeadGate CA (T + (k + 1)) k s.headTotal)
      (Tao.taoCor63SourceOffsetZMod
        (T + (k + 1)) s.headTotal)
      pair.1)
    (Tao.taoGatedOptionKey
      (fun tail => Tao.taoTupleWeight tail = s.tailTotal)
      (fun tail => Tao.taoSection6AmbientTailEmbed
        (k + 1) T s.headTotal
        (Tao.taoSection7OffsetZMod T tail))
      pair.2)

private theorem ndSection6FixedSplit_fullValue_eq_add
    {CA : ℝ} {T k L : ℕ}
    {s : NDFixedTotalSplitIndex (k + 1) T L}
    {full : List ℕ+}
    (hgate : ndSection6FixedSplitSourceGate CA T k L s full) :
    Tao.taoSection7OffsetZMod (T + (k + 1)) full =
      Tao.taoCor63SourceOffsetZMod
          (T + (k + 1)) s.headTotal (full.take (k + 1)) +
        Tao.taoSection6AmbientTailEmbed (k + 1) T s.headTotal
          (Tao.taoSection7OffsetZMod T (full.drop (k + 1))) := by
  have hlength := Tao.taoSection6HeadGate_length hgate.1
  have hweight := Tao.taoSection6HeadGate_weight hgate.1
  calc
    Tao.taoSection7OffsetZMod (T + (k + 1)) full =
        Tao.taoSection7OffsetZMod (T + (k + 1))
          (full.take (k + 1) ++ full.drop (k + 1)) := by
      rw [List.take_append_drop]
    _ = Tao.taoSection7OffsetPrefix
          (T + (k + 1)) (k + 1) (full.take (k + 1)) +
        Tao.taoSection6AmbientTailEmbed (k + 1) T s.headTotal
          (Tao.taoSection7OffsetZMod T (full.drop (k + 1))) :=
      Tao.taoSection6OffsetZMod_append_eq_head_add_ambientTail
        (k + 1) T s.headTotal (full.take (k + 1))
        (full.drop (k + 1)) hlength hweight
    _ = Tao.taoCor63SourceOffsetZMod
          (T + (k + 1)) s.headTotal (full.take (k + 1)) +
        Tao.taoSection6AmbientTailEmbed (k + 1) T s.headTotal
          (Tao.taoSection7OffsetZMod T (full.drop (k + 1))) := by
      rw [Tao.taoSection7OffsetPrefix_eq_taoCor63SourceOffsetZMod
        (T + (k + 1)) (k + 1) s.headTotal
        (full.take (k + 1)) hlength hweight]

private theorem ndSection6FixedSplitSourceKey_eq_pairKey
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L)
    (full : List ℕ+) :
    Tao.taoGatedOptionKey
        (ndSection6FixedSplitSourceGate CA T k L s)
        (Tao.taoSection7OffsetZMod (T + (k + 1))) full =
      ndSection6FixedSplitPairKey CA T k L s
        (full.take (k + 1), full.drop (k + 1)) := by
  classical
  by_cases hhead :
      Tao.taoSection6HeadGate CA (T + (k + 1)) k s.headTotal
        (full.take (k + 1))
  · by_cases htail :
      Tao.taoTupleWeight (full.drop (k + 1)) = s.tailTotal
    · have hvalue := ndSection6FixedSplit_fullValue_eq_add
        (s := s) (full := full) ⟨hhead, htail⟩
      simp [Tao.taoGatedOptionKey, ndSection6FixedSplitSourceGate,
        ndSection6FixedSplitPairKey, ndOptionAdd,
        hhead, htail, hvalue]
    · simp [Tao.taoGatedOptionKey, ndSection6FixedSplitSourceGate,
        ndSection6FixedSplitPairKey, ndOptionAdd, hhead, htail]
  · simp [Tao.taoGatedOptionKey, ndSection6FixedSplitSourceGate,
      ndSection6FixedSplitPairKey, ndOptionAdd, hhead]

private theorem ndSection6FixedSplitSourcePMF_eq_splitPairMap
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L) :
    ndSection6FixedSplitSourcePMF CA T k L s =
      ((Tao.geom2PNatListPMF (k + 1)).bind fun head =>
        (Tao.geom2PNatListPMF T).map fun tail => (head, tail)).map
          (ndSection6FixedSplitPairKey CA T k L s) := by
  unfold ndSection6FixedSplitSourcePMF Tao.taoGatedOptionPMF
  calc
    (Tao.geom2PNatListPMF (T + (k + 1))).map
        (Tao.taoGatedOptionKey
          (ndSection6FixedSplitSourceGate CA T k L s)
          (Tao.taoSection7OffsetZMod (T + (k + 1)))) =
      (Tao.geom2PNatListPMF (T + (k + 1))).map
        (ndSection6FixedSplitPairKey CA T k L s ∘
          fun full => (full.take (k + 1), full.drop (k + 1))) := by
            apply congrArg
              (fun f => (Tao.geom2PNatListPMF (T + (k + 1))).map f)
            funext full
            exact ndSection6FixedSplitSourceKey_eq_pairKey
              CA T k L s full
    _ = ((Tao.geom2PNatListPMF (T + (k + 1))).map
          (fun full => (full.take (k + 1), full.drop (k + 1)))).map
          (ndSection6FixedSplitPairKey CA T k L s) := by
            rw [PMF.map_comp]
    _ = ((Tao.geom2PNatListPMF (k + 1)).bind fun head =>
        (Tao.geom2PNatListPMF T).map fun tail => (head, tail)).map
          (ndSection6FixedSplitPairKey CA T k L s) := by
            have hsplit :
                (Tao.geom2PNatListPMF (T + (k + 1))).map
                    (fun full =>
                      (full.take (k + 1), full.drop (k + 1))) =
                  (Tao.geom2PNatListPMF (k + 1)).bind fun head =>
                    (Tao.geom2PNatListPMF T).map fun tail =>
                      (head, tail) := by
              simpa [Nat.add_comm] using
                Tao.geom2PNatListPMF_map_take_drop_eq (k + 1) T
            rw [hsplit]

private theorem ndGeom2_map_fixedSplitPairKey_eq_kernel
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L)
    (head : List ℕ+) :
    (Tao.geom2PNatListPMF T).map
        (fun tail =>
          ndSection6FixedSplitPairKey CA T k L s (head, tail)) =
      ndOptionOptionConvolutionKernel
        (ndSection6FixedSplitTailOptionPMF
          (k + 1) T s.headTotal s.tailTotal)
        (Tao.taoGatedOptionKey
          (Tao.taoSection6HeadGate
            CA (T + (k + 1)) k s.headTotal)
          (Tao.taoCor63SourceOffsetZMod
            (T + (k + 1)) s.headTotal) head) := by
  classical
  by_cases hhead :
      Tao.taoSection6HeadGate CA (T + (k + 1)) k s.headTotal head
  · unfold ndSection6FixedSplitPairKey Tao.taoGatedOptionKey
    simp only [if_pos hhead]
    simp only [ndOptionOptionConvolutionKernel]
    unfold ndSection6FixedSplitTailOptionPMF Tao.taoGatedOptionPMF
    rw [PMF.map_comp]
    apply congrArg (fun f => (Tao.geom2PNatListPMF T).map f)
    funext tail
    by_cases htail : Tao.taoTupleWeight tail = s.tailTotal <;>
      simp [Tao.taoGatedOptionKey, htail]
  · unfold ndSection6FixedSplitPairKey Tao.taoGatedOptionKey
    simp only [if_neg hhead]
    unfold ndOptionAdd ndOptionOptionConvolutionKernel
    exact PMF.map_const (Tao.geom2PNatListPMF T) none

/-- The full fixed-split iid law is the convolution of the two independently
gated Option laws. -/
theorem ndSection6FixedSplitSourcePMF_eq_optionConvolution
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L) :
    ndSection6FixedSplitSourcePMF CA T k L s =
      ndSection6FixedSplitConvolutionPMF CA T k L s := by
  rw [ndSection6FixedSplitSourcePMF_eq_splitPairMap]
  rw [PMF.map_bind]
  unfold ndSection6FixedSplitConvolutionPMF
  unfold ndOptionOptionConvolutionPMF Tao.taoSection6HeadOptionPMF
  unfold Tao.taoGatedOptionPMF
  rw [PMF.bind_map]
  apply congrArg (PMF.bind (Tao.geom2PNatListPMF (k + 1)))
  funext head
  rw [PMF.map_comp]
  exact ndGeom2_map_fixedSplitPairKey_eq_kernel CA T k L s head

/-- An accepted atom of the specialized two-rejection convolution is the
literal raw convolution of its two defective accepted submasses. -/
theorem ndSection6FixedSplitConvolutionPMF_apply_some_toReal
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L)
    (x : ZMod (3 ^ (T + (k + 1)))) :
    (ndSection6FixedSplitConvolutionPMF CA T k L s (some x)).toReal =
      Tao.taoZModRawConvolution
        (Tao.taoSection6HeadSubmass
          CA (T + (k + 1)) k s.headTotal)
        (ndSection6FixedSplitTailSubmass
          (k + 1) T s.headTotal s.tailTotal) x := by
  unfold ndSection6FixedSplitConvolutionPMF
  rw [ndOptionOptionConvolutionPMF_apply_some_toReal_eq_rawConvolution]
  rfl

/-- The accepted full source atom is the literal raw convolution of the head
and tail defective submasses, with tail argument `x - y`. -/
theorem ndSection6FixedSplitSubmass_eq_rawConvolution
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L)
    (x : ZMod (3 ^ (T + (k + 1)))) :
    ndSection6FixedSplitSourceSubmass CA T k L s x =
      Tao.taoZModRawConvolution
        (Tao.taoSection6HeadSubmass
          CA (T + (k + 1)) k s.headTotal)
        (ndSection6FixedSplitTailSubmass
          (k + 1) T s.headTotal s.tailTotal) x := by
  unfold ndSection6FixedSplitSourceSubmass
  rw [ndSection6FixedSplitSourcePMF_eq_optionConvolution]
  exact ndSection6FixedSplitConvolutionPMF_apply_some_toReal
    CA T k L s x

/-- Immediate contact with the inherited finite Fourier collision theorem.
The accepted-tail DFT estimate remains an explicit hypothesis for the next
P2 adapter. -/
theorem ndSection6FixedSplitOscillation_sq_le
    {CA : ℝ} {T k L m : ℕ}
    {s : NDFixedTotalSplitIndex (k + 1) T L}
    {delta : ℝ}
    (hmn : m ≤ T + (k + 1))
    (hdelta : 0 ≤ delta)
    (htail : ∀ xi : ZMod (3 ^ (T + (k + 1))),
      ¬ Tao.zmodThreePowMultiple
          (T + (k + 1)) (T + (k + 1) - m) xi →
      ‖ZMod.dft (fun z =>
        ((ndSection6FixedSplitTailSubmass
          (k + 1) T s.headTotal s.tailTotal z : ℝ) : ℂ)) xi‖ ≤
        delta) :
    Tao.taoZModPowOscillation m (T + (k + 1))
        (ndSection6FixedSplitSourceSubmass CA T k L s) ^ 2 ≤
      delta ^ 2 * (((3 ^ (T + (k + 1)) : ℕ) : ℝ)) *
        ∑ y, (Tao.taoSection6HeadSubmass
          CA (T + (k + 1)) k s.headTotal y) ^ 2 := by
  let tau := ndSection6FixedSplitTailSubmass
    (k + 1) T s.headTotal s.tailTotal
  have hsource :
      ndSection6FixedSplitSourceSubmass CA T k L s =
        Tao.taoZModRawConvolution
          (Tao.taoSection6HeadSubmass
            CA (T + (k + 1)) k s.headTotal) tau := by
    funext x
    simpa [tau] using
      ndSection6FixedSplitSubmass_eq_rawConvolution CA T k L s x
  rw [hsource]
  exact Tao.taoZModPowOscillation_rawConvolution_sq_le
    hmn
    (Tao.taoSection6HeadSubmass
      CA (T + (k + 1)) k s.headTotal)
    tau hdelta (by simpa [tau] using htail)

end

end ND
end Erdos1135
