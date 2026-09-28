import Erdos1135.ND.Fourier.FixedSplitCollision

/-!
# Fixed-Split Accepted-Tail DFT

This leaf identifies the Fourier transform of the defective accepted tail
from `FixedSplitCollision` with the checked unnormalized fixed-total
Section-7 numerator. The normalized presentation keeps the endpoint mass as
an explicit multiplier.  Its zero-head, zero-weight specialization also
records the literal raw fixed-total residue vector and the exact scalar
normalization consumed by the Section-7 FM1 core.

No conditioned projectivity or conductor descent occurs here. The scaled
tail frequency may still be imprimitive; the following P2 unit must retain
its exact conductor and remaining-total mixture.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

open Tao

noncomputable section

private noncomputable def ndFixedSplitAcceptedKernel
    {N : ℕ} [NeZero N] (xi : ZMod N) : Option (ZMod N) → ℂ
  | none => 0
  | some z => Tao.taoForwardDFTKernel z xi

/-- The DFT of the defective accepted tail is the raw fixed-total numerator
at Tao's projected and `2^-l`-scaled frequency. This identity is valid even
for empty or infeasible fibers; positivity is needed only for normalization. -/
theorem dft_ndSection6FixedSplitTailSubmass
    (q T l R : ℕ) (xi : ZMod (3 ^ (T + q))) :
    ZMod.dft (fun z =>
      ((ndSection6FixedSplitTailSubmass q T l R z : ℝ) : ℂ)) xi =
      ndSection7FiberNumerator T R
        (Tao.taoSection6TailScaledFrequency
          (Nat.le_add_right T q) l xi) := by
  classical
  let key : List ℕ+ → Option (ZMod (3 ^ (T + q))) :=
    Tao.taoGatedOptionKey
      (fun tail => Tao.taoTupleWeight tail = R)
      (fun tail =>
        Tao.taoSection6AmbientTailEmbed q T l
          (Tao.taoSection7OffsetZMod T tail))
  let w : Option (ZMod (3 ^ (T + q))) → ℂ :=
    ndFixedSplitAcceptedKernel xi
  have hsource :
      (∑ z : ZMod (3 ^ (T + q)),
        Tao.taoForwardDFTKernel z xi *
          ((ndSection6FixedSplitTailSubmass q T l R z : ℝ) : ℂ)) =
        ∑' tail : List ℕ+,
          w (key tail) *
            (((Tao.geom2PNatListPMF T tail).toReal : ℝ) : ℂ) := by
    have h := Tao.finite_kernel_indicator_sum
      (Tao.geom2PNatListPMF T) key w
    simpa only [Fintype.sum_option, w, ndFixedSplitAcceptedKernel,
      zero_mul, zero_add, ndSection6FixedSplitTailSubmass,
      ndSection6FixedSplitTailOptionPMF, Tao.taoGatedOptionPMF, key] using h
  rw [Tao.tao_dft_apply]
  simp only [smul_eq_mul]
  rw [ndSection7FiberNumerator_eq_restrictedCharacterSum]
  calc
    (∑ z : ZMod (3 ^ (T + q)),
        Tao.taoForwardDFTKernel z xi *
          ((ndSection6FixedSplitTailSubmass q T l R z : ℝ) : ℂ)) =
        ∑' tail : List ℕ+,
          w (key tail) *
            (((Tao.geom2PNatListPMF T tail).toReal : ℝ) : ℂ) :=
      hsource
    _ = ∑' tail : List ℕ+,
        if Tao.taoTupleWeight tail = R then
          ((Tao.geom2PNatListPMF T tail).toReal : ℂ) *
            Tao.taoSection7CharacterTerm T
              (Tao.taoSection6TailScaledFrequency
                (Nat.le_add_right T q) l xi) tail
        else 0 := by
      apply tsum_congr
      intro tail
      by_cases htail : Tao.taoTupleWeight tail = R
      · simp [key, w, ndFixedSplitAcceptedKernel, Tao.taoGatedOptionKey,
          htail, Tao.taoSection7CharacterTerm,
          Tao.taoForwardDFTKernel_ambientTailEmbed, mul_comm]
      · simp [key, w, ndFixedSplitAcceptedKernel, Tao.taoGatedOptionKey,
          htail]

/-- Normalized form of the accepted-tail identity. The endpoint mass
multiplies the conditioned fixed-fiber DFT; it is not omitted or divided out. -/
theorem dft_ndSection6FixedSplitTailSubmass_eq_endpointMass_mul_fiberDFT
    (q T l R : ℕ) (hT : 0 < T) (hR : T ≤ R)
    (xi : ZMod (3 ^ (T + q))) :
    ZMod.dft (fun z =>
      ((ndSection6FixedSplitTailSubmass q T l R z : ℝ) : ℂ)) xi =
      (ndGeom2EndpointMass T R : ℂ) *
        ZMod.dft (Tao.pmfComplexMass
          (ndSection7FiberPMF T R hT hR))
          (Tao.taoSection6TailScaledFrequency
            (Nat.le_add_right T q) l xi) := by
  rw [dft_ndSection6FixedSplitTailSubmass]
  exact (ndGeom2EndpointMass_mul_fiberDFT T R hT hR
    (Tao.taoSection6TailScaledFrequency
      (Nat.le_add_right T q) l xi)).symm

/-- A nonnegative scalar factors exactly out of Tao's fine-scale
oscillation. -/
theorem ndTaoZModPowOscillation_mul_nonneg
    (m n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (c : ZMod (3 ^ n) → ℝ) :
    Tao.taoZModPowOscillation m n (fun y => a * c y) =
      a * Tao.taoZModPowOscillation m n c := by
  classical
  unfold Tao.taoZModPowOscillation
  have hsum : ∀ y : ZMod (3 ^ n),
      Tao.zmodPowFiberSum m n (fun x => a * c x) y =
        a * Tao.zmodPowFiberSum m n c y := by
    intro y
    unfold Tao.zmodPowFiberSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxy : Tao.zmodSameResidueModPow m n x y <;> simp [hxy]
  simp_rw [hsum]
  calc
    (∑ y : ZMod (3 ^ n),
        |a * c y - Tao.zmodPowFiberAverageScale m n *
          (a * Tao.zmodPowFiberSum m n c y)|) =
        ∑ y : ZMod (3 ^ n),
          a * |c y - Tao.zmodPowFiberAverageScale m n *
            Tao.zmodPowFiberSum m n c y| := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [show a * c y - Tao.zmodPowFiberAverageScale m n *
            (a * Tao.zmodPowFiberSum m n c y) =
          a * (c y - Tao.zmodPowFiberAverageScale m n *
            Tao.zmodPowFiberSum m n c y) by ring,
        abs_mul, abs_of_nonneg ha]
    _ = a * ∑ y : ZMod (3 ^ n),
          |c y - Tao.zmodPowFiberAverageScale m n *
            Tao.zmodPowFiberSum m n c y| := by
      rw [Finset.mul_sum]

/-- The zero-head, zero-weight fixed-split tail is the literal raw
fixed-total Section-7 residue submass. -/
theorem ndSection6FixedSplitTailSubmass_zero_head_zero_weight_eq_gatedSubmass
    (n L : ℕ) (y : ZMod (3 ^ n)) :
    ndSection6FixedSplitTailSubmass 0 n 0 L y =
      Tao.taoGatedSubmass
        (Tao.geom2PNatListPMF n)
        (fun as => Tao.taoTupleWeight as = L)
        (Tao.taoSection7OffsetZMod n) y := by
  have hembed : (fun as : List ℕ+ =>
      Tao.taoSection6AmbientTailEmbed 0 n 0
        (Tao.taoSection7OffsetZMod n as)) =
      Tao.taoSection7OffsetZMod n := by
    funext as
    rw [Tao.taoSection6AmbientTailEmbed_zero_head]
    simp [Tao.taoCor63TwoPowUnit]
  unfold ndSection6FixedSplitTailSubmass
  unfold ndSection6FixedSplitTailOptionPMF
  unfold Tao.taoGatedSubmass
  rw [hembed]

/-- The raw fixed-total residue vector has exactly one endpoint-mass
multiplier relative to the conditioned fixed-fiber law. -/
theorem ndSection6FixedSplitTailSubmass_zero_head_zero_weight_eq
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (y : ZMod (3 ^ n)) :
    ndSection6FixedSplitTailSubmass 0 n 0 L y =
      ndGeom2EndpointMass n L *
        (ndSection7FiberPMF n L hn hL y).toReal := by
  have hcomplex :
      (fun z : ZMod (3 ^ n) =>
          ((ndSection6FixedSplitTailSubmass 0 n 0 L z : ℝ) : ℂ)) =
        fun z =>
          ((ndGeom2EndpointMass n L *
            (ndSection7FiberPMF n L hn hL z).toReal : ℝ) : ℂ) := by
    apply ZMod.dft.injective
    funext xi
    have hfreq : Tao.taoSection6TailScaledFrequency
        (Nat.le_add_right n 0) 0 xi = xi := by
      simp [Tao.taoSection6TailScaledFrequency, Tao.taoCor63TwoPowUnit]
      rw [Tao.taoZModThreeProjection_eq_natCast_val]
      exact ZMod.natCast_zmod_val xi
    calc
      ZMod.dft (fun z : ZMod (3 ^ n) =>
          ((ndSection6FixedSplitTailSubmass 0 n 0 L z : ℝ) : ℂ)) xi =
          (ndGeom2EndpointMass n L : ℂ) *
            ZMod.dft (Tao.pmfComplexMass
              (ndSection7FiberPMF n L hn hL)) xi := by
        simpa only [hfreq] using
          (dft_ndSection6FixedSplitTailSubmass_eq_endpointMass_mul_fiberDFT
            0 n 0 L hn hL xi)
      _ = ZMod.dft
          (fun z : ZMod (3 ^ n) =>
            ((ndGeom2EndpointMass n L *
              (ndSection7FiberPMF n L hn hL z).toReal : ℝ) : ℂ)) xi := by
        simp only [Complex.ofReal_mul]
        exact (congrFun (ZMod.dft_const_mul
          (ndGeom2EndpointMass n L : ℂ)
          (Tao.pmfComplexMass (ndSection7FiberPMF n L hn hL))) xi).symm
  exact_mod_cast congrFun hcomplex y

/-- The O3 raw-to-conditioned normalization seam: the raw oscillation is
exactly the endpoint mass times the conditioned-fiber oscillation. -/
theorem ndSection6FixedSplitTailSubmass_zero_head_zero_weight_oscillation_eq
    (m n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    Tao.taoZModPowOscillation m n
        (ndSection6FixedSplitTailSubmass 0 n 0 L) =
      ndGeom2EndpointMass n L *
        Tao.taoZModPowOscillation m n
          (fun y => (ndSection7FiberPMF n L hn hL y).toReal) := by
  rw [show ndSection6FixedSplitTailSubmass 0 n 0 L =
      fun y => ndGeom2EndpointMass n L *
        (ndSection7FiberPMF n L hn hL y).toReal by
    funext y
    exact ndSection6FixedSplitTailSubmass_zero_head_zero_weight_eq
      n L hn hL y]
  exact ndTaoZModPowOscillation_mul_nonneg m n
    (ndGeom2EndpointMass n L) (ndGeom2EndpointMass_pos hn hL).le _

/-- Zero frequency recovers exactly the total accepted tail mass. This
regression catches both a missing endpoint multiplier and false
renormalization of the defective submass. -/
theorem dft_ndSection6FixedSplitTailSubmass_zero
    (q T l R : ℕ) (hT : 0 < T) (hR : T ≤ R) :
    ZMod.dft (fun z =>
      ((ndSection6FixedSplitTailSubmass q T l R z : ℝ) : ℂ)) 0 =
      (ndGeom2EndpointMass T R : ℂ) := by
  rw [dft_ndSection6FixedSplitTailSubmass_eq_endpointMass_mul_fiberDFT
    q T l R hT hR]
  simp [Tao.taoSection6TailScaledFrequency,
    Tao.tao_dft_pmfComplexMass_apply_zero]

end

end ND
end Erdos1135
