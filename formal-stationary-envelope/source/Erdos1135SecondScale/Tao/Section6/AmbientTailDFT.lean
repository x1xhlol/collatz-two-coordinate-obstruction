/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section6.ConductorDFT
import Erdos1135SecondScale.Tao.Section6.ConductorFrequency
import Erdos1135SecondScale.Tao.Fourier.Section7SourceLaw

/-!
# Section 6 Ambient Tail DFT

This leaf embeds the normalized level-`T` Syracuse tail into ambient level
`q+T` with Tao's coefficient `3^q * 2^-l`, and identifies its ambient Fourier
coefficient with the checked scaled tail frequency.  No head event or
unnormalized head mass is introduced here.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The normalized tail residue embedded into ambient level `q+T`. -/
noncomputable def taoSection6AmbientTailEmbed
    (q T l : ℕ) (z : ZMod (3 ^ T)) : ZMod (3 ^ (T + q)) :=
  (3 : ZMod (3 ^ (T + q))) ^ q *
    (((taoCor63TwoPowUnit (T + q) l)⁻¹ :
      (ZMod (3 ^ (T + q)))ˣ) : ZMod (3 ^ (T + q))) *
    (z.val : ZMod (3 ^ (T + q)))

/-- The ambient tail is the pushforward of the normalized level-`T` Syracuse
law. -/
noncomputable def taoSection6AmbientTailPMF
    (q T l : ℕ) : PMF (ZMod (3 ^ (T + q))) :=
  (syracPMF T).map (taoSection6AmbientTailEmbed q T l)

/-- Projecting an ambient representative lift recovers the original tail
residue. -/
theorem taoSection6AmbientTailLift_projection
    (q T : ℕ) (z : ZMod (3 ^ T)) :
    taoZModThreeProjection (Nat.le_add_right T q)
        (z.val : ZMod (3 ^ (T + q))) = z := by
  rw [taoZModThreeProjection_natCast]
  exact ZMod.natCast_zmod_val z

/-- The ambient inverse power of two projects to the matching tail-level
unit. -/
theorem taoSection6AmbientTailTwoPowInv_projection
    (q T l : ℕ) :
    taoZModThreeProjection (Nat.le_add_right T q)
        ((((taoCor63TwoPowUnit (T + q) l)⁻¹ :
          (ZMod (3 ^ (T + q)))ˣ) : ZMod (3 ^ (T + q)))) =
      (((taoCor63TwoPowUnit T l)⁻¹ :
        (ZMod (3 ^ T))ˣ) : ZMod (3 ^ T)) := by
  rw [← ZMod.inv_coe_unit, ← ZMod.inv_coe_unit]
  simp only [taoCor63TwoPowUnit_coe]
  exact taoZModThreeProjection_inv_two_pow (Nat.le_add_right T q) l

/-- The ambient embedded-tail kernel is exactly the level-`T` kernel at
Tao's projected and `2^-l`-scaled frequency. -/
theorem taoForwardDFTKernel_ambientTailEmbed
    (q T l : ℕ) (z : ZMod (3 ^ T)) (xi : ZMod (3 ^ (T + q))) :
    taoForwardDFTKernel (taoSection6AmbientTailEmbed q T l z) xi =
      taoForwardDFTKernel z
        (taoSection6TailScaledFrequency
          (Nat.le_add_right T q) l xi) := by
  let uinv : ZMod (3 ^ (T + q)) :=
    (((taoCor63TwoPowUnit (T + q) l)⁻¹ :
      (ZMod (3 ^ (T + q)))ˣ) : ZMod (3 ^ (T + q)))
  let pi := taoZModThreeProjection (Nat.le_add_right T q)
  calc
    taoForwardDFTKernel (taoSection6AmbientTailEmbed q T l z) xi =
      taoForwardDFTKernel xi
        ((3 : ZMod (3 ^ (T + q))) ^ q *
          (uinv * (z.val : ZMod (3 ^ (T + q))))) := by
            unfold taoForwardDFTKernel taoSection6AmbientTailEmbed
            simp only [uinv]
            congr 1
            ring
    _ = taoForwardDFTKernel (pi xi)
        (pi (uinv * (z.val : ZMod (3 ^ (T + q))))) := by
          simpa [pi] using
            taoForwardDFTKernel_three_pow_mul_eq_projection
              T q xi (uinv * (z.val : ZMod (3 ^ (T + q))))
    _ = taoForwardDFTKernel (pi xi)
        ((((taoCor63TwoPowUnit T l)⁻¹ :
          (ZMod (3 ^ T))ˣ) : ZMod (3 ^ T)) * z) := by
            rw [map_mul]
            rw [show pi uinv =
                (((taoCor63TwoPowUnit T l)⁻¹ :
                  (ZMod (3 ^ T))ˣ) : ZMod (3 ^ T)) by
              exact taoSection6AmbientTailTwoPowInv_projection q T l]
            rw [show pi (z.val : ZMod (3 ^ (T + q))) = z by
              exact taoSection6AmbientTailLift_projection q T z]
    _ = taoForwardDFTKernel z
        (taoSection6TailScaledFrequency
          (Nat.le_add_right T q) l xi) := by
            unfold taoForwardDFTKernel taoSection6TailScaledFrequency
            simp only [pi]
            rw [ZMod.inv_coe_unit]
            congr 1
            ac_rfl

/-- The ambient tail DFT is the normalized level-`T` Syracuse DFT evaluated
at Tao's scaled projected frequency.  There is no cardinality multiplier. -/
theorem dft_taoSection6AmbientTailPMF
    (q T l : ℕ) (xi : ZMod (3 ^ (T + q))) :
    ZMod.dft (pmfComplexMass (taoSection6AmbientTailPMF q T l)) xi =
      ZMod.dft (pmfComplexMass (syracPMF T))
        (taoSection6TailScaledFrequency
          (Nat.le_add_right T q) l xi) := by
  unfold taoSection6AmbientTailPMF
  rw [tao_dft_pmfComplexMass_map_apply]
  have htail := tao_dft_pmfComplexMass_map_apply
    (syracPMF T) (fun z => z)
    (taoSection6TailScaledFrequency (Nat.le_add_right T q) l xi)
  have hid : (syracPMF T).map (fun z => z) = syracPMF T := by
    simpa only [id_eq] using PMF.map_id (syracPMF T)
  rw [hid] at htail
  rw [htail]
  apply tsum_congr
  intro z
  rw [taoForwardDFTKernel_ambientTailEmbed]

/-- A level-zero tail embeds at the ambient zero residue. -/
theorem taoSection6AmbientTailEmbed_zero_tail
    (q l : ℕ) (z : ZMod (3 ^ 0)) :
    taoSection6AmbientTailEmbed q 0 l z = 0 := by
  have hz : z.val = 0 := by
    fin_cases z
    rfl
  unfold taoSection6AmbientTailEmbed
  rw [hz]
  norm_num

/-- With no ambient head coordinates, embedding is only multiplication by
`2^-l`. -/
theorem taoSection6AmbientTailEmbed_zero_head
    (T l : ℕ) (z : ZMod (3 ^ T)) :
    taoSection6AmbientTailEmbed 0 T l z =
      (((taoCor63TwoPowUnit T l)⁻¹ :
        (ZMod (3 ^ T))ˣ) : ZMod (3 ^ T)) * z := by
  simp [taoSection6AmbientTailEmbed]

/-- At weight zero, ambient embedding is the pure `3^q` representative lift. -/
theorem taoSection6AmbientTailEmbed_zero_weight
    (q T : ℕ) (z : ZMod (3 ^ T)) :
    taoSection6AmbientTailEmbed q T 0 z =
      (3 : ZMod (3 ^ (T + q))) ^ q *
        (z.val : ZMod (3 ^ (T + q))) := by
  simp [taoSection6AmbientTailEmbed, taoCor63TwoPowUnit]

end

end Tao
end Erdos1135SecondScale
