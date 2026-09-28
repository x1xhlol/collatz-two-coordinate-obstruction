/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.MixingStatement
import Erdos1135Predecessor.Tao.Section6.AmbientOffsetAppend
import Erdos1135Predecessor.Tao.Section6.ConductorProjectivity
import Erdos1135Predecessor.Tao.Section6.Cor63HeadPrefix
import Erdos1135Predecessor.Tao.Section6.HeadSubmass
import Erdos1135Predecessor.Tao.Section6.OptionHeadTailConvolution

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def taoSection6GatedSourceKey
    (CA : ℝ) (T k l : ℕ) (full : List ℕ+) :
    Option (ZMod (3 ^ (T + (k + 1)))) :=
  taoGatedOptionKey
    (fun source =>
      taoSection6HeadGate CA (T + (k + 1)) k l
        (source.take (k + 1)))
    (taoSection7OffsetZMod (T + (k + 1)))
    full

noncomputable def taoSection6GatedSourcePMF
    (CA : ℝ) (T k l : ℕ) :
    PMF (Option (ZMod (3 ^ (T + (k + 1))))) :=
  taoGatedOptionPMF
    (geom2PNatListPMF (T + (k + 1)))
    (fun full =>
      taoSection6HeadGate CA (T + (k + 1)) k l
        (full.take (k + 1)))
    (taoSection7OffsetZMod (T + (k + 1)))

noncomputable def taoSection6GatedHeadTailPairKey
    (CA : ℝ) (T k l : ℕ) (pair : List ℕ+ × List ℕ+) :
    Option (ZMod (3 ^ (T + (k + 1)))) := by
  classical
  exact
    if taoSection6HeadGate CA (T + (k + 1)) k l pair.1 then
      some
        (taoCor63SourceOffsetZMod (T + (k + 1)) l pair.1 +
          taoSection6AmbientTailEmbed (k + 1) T l
            (taoSection7OffsetZMod T pair.2))
    else
      none

theorem taoSection6GatedSourceKey_eq_pairKey
    (CA : ℝ) (T k l : ℕ) (full : List ℕ+) :
    taoSection6GatedSourceKey CA T k l full =
      taoSection6GatedHeadTailPairKey CA T k l
        (full.take (k + 1), full.drop (k + 1)) := by
  unfold taoSection6GatedSourceKey taoGatedOptionKey
  unfold taoSection6GatedHeadTailPairKey
  by_cases hgate :
      taoSection6HeadGate CA (T + (k + 1)) k l
        (full.take (k + 1))
  · rw [if_pos hgate, if_pos hgate]
    congr 1
    have hheadLength := taoSection6HeadGate_length hgate
    have hweight := taoSection6HeadGate_weight hgate
    calc
      taoSection7OffsetZMod (T + (k + 1)) full =
          taoSection7OffsetZMod (T + (k + 1))
            (full.take (k + 1) ++ full.drop (k + 1)) := by
              rw [List.take_append_drop]
      _ = taoSection7OffsetPrefix (T + (k + 1)) (k + 1)
            (full.take (k + 1)) +
          taoSection6AmbientTailEmbed (k + 1) T l
            (taoSection7OffsetZMod T (full.drop (k + 1))) := by
              exact taoSection6OffsetZMod_append_eq_head_add_ambientTail
                (k + 1) T l (full.take (k + 1)) (full.drop (k + 1))
                  hheadLength hweight
      _ = taoCor63SourceOffsetZMod (T + (k + 1)) l
            (full.take (k + 1)) +
          taoSection6AmbientTailEmbed (k + 1) T l
            (taoSection7OffsetZMod T (full.drop (k + 1))) := by
              rw [taoSection7OffsetPrefix_eq_taoCor63SourceOffsetZMod
                (T + (k + 1)) (k + 1) l (full.take (k + 1))
                  hheadLength hweight]
  · rw [if_neg hgate, if_neg hgate]

theorem taoSection6GatedSourcePMF_eq_splitPairMap
    (CA : ℝ) (T k l : ℕ) :
    taoSection6GatedSourcePMF CA T k l =
      ((geom2PNatListPMF (k + 1)).bind fun head =>
        (geom2PNatListPMF T).map fun tail => (head, tail)).map
          (taoSection6GatedHeadTailPairKey CA T k l) := by
  unfold taoSection6GatedSourcePMF taoGatedOptionPMF
  change (geom2PNatListPMF (T + (k + 1))).map
      (taoSection6GatedSourceKey CA T k l) = _
  calc
    (geom2PNatListPMF (T + (k + 1))).map
        (taoSection6GatedSourceKey CA T k l) =
      (geom2PNatListPMF (T + (k + 1))).map
        (taoSection6GatedHeadTailPairKey CA T k l ∘
          fun full => (full.take (k + 1), full.drop (k + 1))) := by
            apply congrArg
              (fun f => (geom2PNatListPMF (T + (k + 1))).map f)
            funext full
            exact taoSection6GatedSourceKey_eq_pairKey CA T k l full
    _ = ((geom2PNatListPMF (T + (k + 1))).map
          (fun full => (full.take (k + 1), full.drop (k + 1)))).map
          (taoSection6GatedHeadTailPairKey CA T k l) := by
            rw [PMF.map_comp]
    _ = ((geom2PNatListPMF (k + 1)).bind fun head =>
        (geom2PNatListPMF T).map fun tail => (head, tail)).map
          (taoSection6GatedHeadTailPairKey CA T k l) := by
            have hsplit :
                (geom2PNatListPMF (T + (k + 1))).map
                    (fun full =>
                      (full.take (k + 1), full.drop (k + 1))) =
                  (geom2PNatListPMF (k + 1)).bind fun head =>
                    (geom2PNatListPMF T).map fun tail =>
                      (head, tail) := by
              simpa [Nat.add_comm] using
                geom2PNatListPMF_map_take_drop_eq (k + 1) T
            rw [hsplit]

theorem geom2PNatListPMF_map_gatedHeadTailPairKey_eq_kernel
    (CA : ℝ) (T k l : ℕ) (head : List ℕ+) :
    (geom2PNatListPMF T).map
        (fun tail =>
          taoSection6GatedHeadTailPairKey CA T k l (head, tail)) =
      taoOptionHeadTailKernel
        (taoSection6AmbientTailPMF (k + 1) T l)
        (taoGatedOptionKey
          (taoSection6HeadGate CA (T + (k + 1)) k l)
          (taoCor63SourceOffsetZMod (T + (k + 1)) l)
          head) := by
  classical
  by_cases hgate :
      taoSection6HeadGate CA (T + (k + 1)) k l head
  · unfold taoSection6GatedHeadTailPairKey taoGatedOptionKey
    simp only [if_pos hgate]
    change
      (geom2PNatListPMF T).map
          (fun tail =>
            some
              (taoCor63SourceOffsetZMod (T + (k + 1)) l head +
                taoSection6AmbientTailEmbed (k + 1) T l
                  (taoSection7OffsetZMod T tail))) =
        (taoSection6AmbientTailPMF (k + 1) T l).map
          (fun z =>
            some
              (taoCor63SourceOffsetZMod (T + (k + 1)) l head + z))
    unfold taoSection6AmbientTailPMF
    rw [syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod]
    rw [PMF.map_comp]
    rw [PMF.map_comp]
    rfl
  · unfold taoSection6GatedHeadTailPairKey taoGatedOptionKey
    simp only [if_neg hgate]
    unfold taoOptionHeadTailKernel
    exact PMF.map_const (geom2PNatListPMF T) none

theorem taoSection6GatedSourcePMF_eq_headTail
    (CA : ℝ) (T k l : ℕ) :
    taoSection6GatedSourcePMF CA T k l =
      taoOptionHeadTailPMF
        (taoSection6HeadOptionPMF CA (T + (k + 1)) k l)
        (taoSection6AmbientTailPMF (k + 1) T l) := by
  rw [taoSection6GatedSourcePMF_eq_splitPairMap]
  rw [PMF.map_bind]
  unfold taoOptionHeadTailPMF taoSection6HeadOptionPMF
  unfold taoGatedOptionPMF
  rw [PMF.bind_map]
  apply congrArg (PMF.bind (geom2PNatListPMF (k + 1)))
  funext head
  rw [PMF.map_comp]
  exact geom2PNatListPMF_map_gatedHeadTailPairKey_eq_kernel
    CA T k l head

noncomputable def taoSection6GatedSourceSubmass
    (CA : ℝ) (T k l : ℕ)
    (x : ZMod (3 ^ (T + (k + 1)))) : ℝ :=
  (taoSection6GatedSourcePMF CA T k l (some x)).toReal

theorem taoSection6GatedSourceSubmass_eq_rawConvolution
    (CA : ℝ) (T k l : ℕ)
    (x : ZMod (3 ^ (T + (k + 1)))) :
    taoSection6GatedSourceSubmass CA T k l x =
      taoZModRawConvolution
        (taoSection6HeadSubmass CA (T + (k + 1)) k l)
        (fun z =>
          (taoSection6AmbientTailPMF (k + 1) T l z).toReal)
        x := by
  unfold taoSection6GatedSourceSubmass
  rw [taoSection6GatedSourcePMF_eq_headTail]
  rw [taoOptionHeadTailPMF_apply_some_toReal_eq_rawConvolution]
  rfl

theorem taoSection6GatedSourceSubmass_eq_zero_of_headGate_empty
    {CA : ℝ} {T k l : ℕ}
    (hempty : ¬ ∃ head : List ℕ+,
      taoSection6HeadGate CA (T + (k + 1)) k l head)
    (x : ZMod (3 ^ (T + (k + 1)))) :
    taoSection6GatedSourceSubmass CA T k l x = 0 := by
  rw [taoSection6GatedSourceSubmass_eq_rawConvolution]
  apply taoZModRawConvolution_eq_zero_of_left
  intro y
  exact taoSection6HeadSubmass_eq_zero_of_headGate_empty hempty y

theorem taoSection6FixedSliceOscillation_eq_zero_of_headGate_empty
    {CA : ℝ} {T k l m : ℕ}
    (hempty : ¬ ∃ head : List ℕ+,
      taoSection6HeadGate CA (T + (k + 1)) k l head) :
    taoZModPowOscillation m (T + (k + 1))
      (taoSection6GatedSourceSubmass CA T k l) = 0 := by
  have hsource :
      taoSection6GatedSourceSubmass CA T k l = fun _ => 0 := by
    funext x
    exact taoSection6GatedSourceSubmass_eq_zero_of_headGate_empty hempty x
  rw [hsource]
  exact taoZModPowOscillation_zero m (T + (k + 1))

end

end Tao

end Erdos1135Predecessor
