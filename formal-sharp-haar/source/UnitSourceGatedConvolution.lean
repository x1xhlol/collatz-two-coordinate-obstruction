import UnitSourceAppend
import Erdos1135.Tao.Section6.GatedSourceConvolution

/-!
# Seeded fixed-slice convolution

This adapter keeps the native geometric list PMF, head gate, unnormalized
head mass, and rejected mass at none. Its normalized tail law is the literal
seeded affine PMF. The convolution identity requires a positive tail; empty
head gates are zero without that restriction, including the zero-tail case.
-/

set_option autoImplicit false

namespace Erdos1135.Tao

noncomputable def unitSourceGatedPMF
    (CA : ℝ) (T k l : ℕ) (z : ZMod (3 ^ (T + (k + 1)))) :
    PMF (Option (ZMod (3 ^ (T + (k + 1))))) :=
  taoGatedOptionPMF (geom2PNatListPMF (T + (k + 1)))
    (fun full => taoSection6HeadGate CA (T + (k + 1)) k l (full.take (k + 1)))
    (unitSourceLengthNMap (T + (k + 1)) z)

noncomputable def unitSourceGatedPairKey
    (CA : ℝ) (T k l : ℕ) (z : ZMod (3 ^ (T + (k + 1))))
    (pair : List ℕ+ × List ℕ+) : Option (ZMod (3 ^ (T + (k + 1)))) := by
  classical
  exact if taoSection6HeadGate CA (T + (k + 1)) k l pair.1 then
    some (taoCor63SourceOffsetZMod (T + (k + 1)) l pair.1 +
      taoSection6AmbientTailEmbed (k + 1) T l
        (unitSourceLengthNMap T
          (taoZModThreeProjection (Nat.le_add_right T (k + 1)) z) pair.2))
  else none

theorem unitSourceGatedKey_eq_pairKey
    (CA : ℝ) (T k l : ℕ) (hT : 1 ≤ T)
    (z : ZMod (3 ^ (T + (k + 1)))) (full : List ℕ+) :
    taoGatedOptionKey
        (fun source => taoSection6HeadGate CA (T + (k + 1)) k l
          (source.take (k + 1)))
        (unitSourceLengthNMap (T + (k + 1)) z) full =
      unitSourceGatedPairKey CA T k l z (full.take (k + 1), full.drop (k + 1)) := by
  unfold taoGatedOptionKey unitSourceGatedPairKey
  by_cases hgate : taoSection6HeadGate CA (T + (k + 1)) k l (full.take (k + 1))
  · rw [if_pos hgate, if_pos hgate]
    congr 1
    have hhead := taoSection6HeadGate_length hgate
    have hweight := taoSection6HeadGate_weight hgate
    conv_lhs => rw [← List.take_append_drop (k + 1) full]
    rw [unitSourceLengthNMap_append (k + 1) T l hT z
      (full.take (k + 1)) (full.drop (k + 1)) hhead hweight]
    rw [taoSection7OffsetPrefix_eq_taoCor63SourceOffsetZMod
      (T + (k + 1)) (k + 1) l (full.take (k + 1)) hhead hweight]
  · rw [if_neg hgate, if_neg hgate]

theorem unitSourceGatedPMF_eq_splitPairMap
    (CA : ℝ) (T k l : ℕ) (hT : 1 ≤ T)
    (z : ZMod (3 ^ (T + (k + 1)))) :
    unitSourceGatedPMF CA T k l z =
      ((geom2PNatListPMF (k + 1)).bind fun head =>
        (geom2PNatListPMF T).map fun tail => (head, tail)).map
          (unitSourceGatedPairKey CA T k l z) := by
  unfold unitSourceGatedPMF taoGatedOptionPMF
  have hfun :
      taoGatedOptionKey
        (fun full => taoSection6HeadGate CA (T + (k + 1)) k l (full.take (k + 1)))
        (unitSourceLengthNMap (T + (k + 1)) z) =
      unitSourceGatedPairKey CA T k l z ∘
        (fun full : List ℕ+ => (full.take (k + 1), full.drop (k + 1))) := by
    funext full
    exact unitSourceGatedKey_eq_pairKey CA T k l hT z full
  rw [hfun, ← PMF.map_comp]
  have hsplit :
      (geom2PNatListPMF (T + (k + 1))).map
          (fun full => (full.take (k + 1), full.drop (k + 1))) =
      (geom2PNatListPMF (k + 1)).bind fun head =>
        (geom2PNatListPMF T).map fun tail => (head, tail) := by
    simpa [Nat.add_comm] using geom2PNatListPMF_map_take_drop_eq (k + 1) T
  rw [hsplit]

theorem unitSourceGatedPairKey_map_eq_kernel
    (CA : ℝ) (T k l : ℕ) (z : ZMod (3 ^ (T + (k + 1)))) (head : List ℕ+) :
    (geom2PNatListPMF T).map (fun tail => unitSourceGatedPairKey CA T k l z (head, tail)) =
      taoOptionHeadTailKernel
        (unitSourceAmbientTailPMF (k + 1) T l
          (taoZModThreeProjection (Nat.le_add_right T (k + 1)) z))
        (taoGatedOptionKey (taoSection6HeadGate CA (T + (k + 1)) k l)
          (taoCor63SourceOffsetZMod (T + (k + 1)) l) head) := by
  classical
  by_cases hgate : taoSection6HeadGate CA (T + (k + 1)) k l head
  · unfold unitSourceGatedPairKey taoGatedOptionKey
    simp only [if_pos hgate]
    change (geom2PNatListPMF T).map
        (fun tail => some (taoCor63SourceOffsetZMod (T + (k + 1)) l head +
          taoSection6AmbientTailEmbed (k + 1) T l
            (unitSourceLengthNMap T
              (taoZModThreeProjection (Nat.le_add_right T (k + 1)) z) tail))) =
      (unitSourceAmbientTailPMF (k + 1) T l
        (taoZModThreeProjection (Nat.le_add_right T (k + 1)) z)).map
          (fun x => some (taoCor63SourceOffsetZMod (T + (k + 1)) l head + x))
    unfold unitSourceAmbientTailPMF
    rw [← unitSourceLengthNMap_pmf_eq]
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  · unfold unitSourceGatedPairKey taoGatedOptionKey
    simp only [if_neg hgate]
    unfold taoOptionHeadTailKernel
    exact PMF.map_const (geom2PNatListPMF T) none

theorem unitSourceGatedPMF_eq_headTail
    (CA : ℝ) (T k l : ℕ) (hT : 1 ≤ T)
    (z : ZMod (3 ^ (T + (k + 1)))) :
    unitSourceGatedPMF CA T k l z =
      taoOptionHeadTailPMF (taoSection6HeadOptionPMF CA (T + (k + 1)) k l)
        (unitSourceAmbientTailPMF (k + 1) T l
          (taoZModThreeProjection (Nat.le_add_right T (k + 1)) z)) := by
  rw [unitSourceGatedPMF_eq_splitPairMap CA T k l hT z, PMF.map_bind]
  unfold taoOptionHeadTailPMF taoSection6HeadOptionPMF taoGatedOptionPMF
  rw [PMF.bind_map]
  apply congrArg (PMF.bind (geom2PNatListPMF (k + 1)))
  funext head
  rw [PMF.map_comp]
  exact unitSourceGatedPairKey_map_eq_kernel CA T k l z head

noncomputable def unitSourceGatedSubmass
    (CA : ℝ) (T k l : ℕ) (z : ZMod (3 ^ (T + (k + 1))))
    (x : ZMod (3 ^ (T + (k + 1)))) : ℝ :=
  (unitSourceGatedPMF CA T k l z (some x)).toReal

theorem unitSourceGatedSubmass_eq_rawConvolution
    (CA : ℝ) (T k l : ℕ) (hT : 1 ≤ T)
    (z : ZMod (3 ^ (T + (k + 1)))) (x : ZMod (3 ^ (T + (k + 1)))) :
    unitSourceGatedSubmass CA T k l z x =
      taoZModRawConvolution (taoSection6HeadSubmass CA (T + (k + 1)) k l)
        (fun y => (unitSourceAmbientTailPMF (k + 1) T l
          (taoZModThreeProjection (Nat.le_add_right T (k + 1)) z) y).toReal) x := by
  unfold unitSourceGatedSubmass
  rw [unitSourceGatedPMF_eq_headTail CA T k l hT z,
    taoOptionHeadTailPMF_apply_some_toReal_eq_rawConvolution]
  rfl

/-- Empty head gates contribute zero, including the zero-tail boundary where
an affine head-tail decomposition is intentionally unavailable. -/
theorem unitSourceGatedSubmass_eq_zero_of_headGate_empty
    {CA : ℝ} {T k l : ℕ}
    (hempty : ¬ ∃ head : List ℕ+, taoSection6HeadGate CA (T + (k + 1)) k l head)
    (z : ZMod (3 ^ (T + (k + 1)))) (x : ZMod (3 ^ (T + (k + 1)))) :
    unitSourceGatedSubmass CA T k l z x = 0 := by
  have hfun : taoGatedOptionKey
      (fun full => taoSection6HeadGate CA (T + (k + 1)) k l (full.take (k + 1)))
      (unitSourceLengthNMap (T + (k + 1)) z) = fun _ => none := by
    funext full
    unfold taoGatedOptionKey
    exact if_neg (fun h => hempty ⟨full.take (k + 1), h⟩)
  unfold unitSourceGatedSubmass unitSourceGatedPMF taoGatedOptionPMF
  rw [hfun]
  have hm : (geom2PNatListPMF (T + (k + 1))).map
      (fun _ => (none : Option (ZMod (3 ^ (T + (k + 1)))))) = PMF.pure none :=
    PMF.map_const _ none
  rw [hm]
  simp

theorem unitSourceGatedOscillation_eq_zero_of_headGate_empty
    {CA : ℝ} {T k l m : ℕ}
    (hempty : ¬ ∃ head : List ℕ+, taoSection6HeadGate CA (T + (k + 1)) k l head)
    (z : ZMod (3 ^ (T + (k + 1)))) :
    taoZModPowOscillation m (T + (k + 1)) (unitSourceGatedSubmass CA T k l z) = 0 := by
  have hsource : unitSourceGatedSubmass CA T k l z = fun _ => 0 := by
    funext x
    exact unitSourceGatedSubmass_eq_zero_of_headGate_empty hempty z x
  rw [hsource]
  exact taoZModPowOscillation_zero m (T + (k + 1))

end Erdos1135.Tao
