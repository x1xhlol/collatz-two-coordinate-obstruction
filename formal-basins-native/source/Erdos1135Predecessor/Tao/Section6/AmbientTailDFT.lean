/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7SourceLaw
import Erdos1135Predecessor.Tao.Section6.ConductorDFT
import Erdos1135Predecessor.Tao.Section6.ConductorFrequency

open scoped BigOperators

open scoped ZMod

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def taoSection6AmbientTailEmbed
    (q T l : ℕ) (z : ZMod (3 ^ T)) : ZMod (3 ^ (T + q)) :=
  (3 : ZMod (3 ^ (T + q))) ^ q *
    (((taoCor63TwoPowUnit (T + q) l)⁻¹ :
      (ZMod (3 ^ (T + q)))ˣ) : ZMod (3 ^ (T + q))) *
    (z.val : ZMod (3 ^ (T + q)))

noncomputable def taoSection6AmbientTailPMF
    (q T l : ℕ) : PMF (ZMod (3 ^ (T + q))) :=
  (syracPMF T).map (taoSection6AmbientTailEmbed q T l)

theorem taoSection6AmbientTailLift_projection
    (q T : ℕ) (z : ZMod (3 ^ T)) :
    taoZModThreeProjection (Nat.le_add_right T q)
        (z.val : ZMod (3 ^ (T + q))) = z := by
  rw [taoZModThreeProjection_natCast]
  exact ZMod.natCast_zmod_val z

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

end

end Tao

end Erdos1135Predecessor
