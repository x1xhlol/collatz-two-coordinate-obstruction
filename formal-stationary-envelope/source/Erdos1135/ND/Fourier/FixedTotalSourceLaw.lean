import Erdos1135.ND.Fourier.FixedSplitTailDFT
import Erdos1135.Tao.Fourier.Section7SourceLaw
import Erdos1135.Tao.Section5.AffineSourceLaw

/-!
# Fixed-Total Source-Law Disintegration

This leaf supplies the exact endpoint law and its totalized conditioned
Section-7 kernel.  The main theorem is the countable fixed-total
disintegration of the complete Syracuse source law.  The proof remains in
`ENNReal` until the final pointwise real-valued corollary; no finite endpoint
cutoff is introduced.

The affine-orientation seam is stated separately.  It transports the
fixed-total gate through iid list reversal before using the checked affine to
Section-7 offset identity.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- Every positive valuation contributes at least one unit to the total
valuation weight. -/
theorem ndListLength_le_taoTupleWeight (as : List ℕ+) :
    as.length ≤ Tao.taoTupleWeight as := by
  induction as with
  | nil =>
      simp [Tao.taoTupleWeight]
  | cons a as ih =>
      have ha : 1 ≤ (a : ℕ) := a.2
      change as.length + 1 ≤ (a : ℕ) + Tao.taoTupleWeight as
      omega

/-- The law of the total valuation weight under the length-`n` iid Geom(2)
list source. -/
noncomputable def ndGeom2EndpointPMF (n : ℕ) : PMF ℕ :=
  (Tao.geom2PNatListPMF n).map Tao.taoTupleWeight

/-- An endpoint atom is exactly the previously checked real endpoint mass. -/
theorem ndGeom2EndpointPMF_apply_toReal_eq_endpointMass
    (n L : ℕ) :
    (ndGeom2EndpointPMF n L).toReal = ndGeom2EndpointMass n L := by
  rw [ndGeom2EndpointPMF, Tao.taoPMF_map_apply_toReal_tsum,
    ndGeom2EndpointMass_eq_weightSelector]
  apply tsum_congr
  intro as
  by_cases h : Tao.taoTupleWeight as = L
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

/-- Total valuation weight is at least the fixed list length on the endpoint
law's support. -/
theorem ndGeom2EndpointPMF_support_subset_Ici (n : ℕ) :
    (ndGeom2EndpointPMF n).support ⊆ Set.Ici n := by
  rw [ndGeom2EndpointPMF, PMF.support_map]
  rintro _ ⟨as, has, rfl⟩
  have hlen := Tao.geom2PNatListPMF_support_length_eq has
  simpa [hlen] using ndListLength_le_taoTupleWeight as

@[simp]
theorem ndGeom2EndpointPMF_apply_eq_zero_of_lt
    {n L : ℕ} (hL : L < n) :
    ndGeom2EndpointPMF n L = 0 := by
  classical
  by_contra hne
  exact (Nat.not_le_of_gt hL)
    (ndGeom2EndpointPMF_support_subset_Ici n
      (((ndGeom2EndpointPMF n).mem_support_iff L).2 hne))

/-- Endpoint masses below the physical support vanish. -/
theorem ndGeom2EndpointMass_eq_zero_of_lt
    {n L : ℕ} (hL : L < n) :
    ndGeom2EndpointMass n L = 0 := by
  calc
    ndGeom2EndpointMass n L =
        (ndGeom2EndpointPMF n L).toReal :=
      (ndGeom2EndpointPMF_apply_toReal_eq_endpointMass n L).symm
    _ = 0 := by simp [ndGeom2EndpointPMF_apply_eq_zero_of_lt hL]

/-- The conditioned Section-7 kernel, totalized on impossible endpoint
parameters.  At `n = 0` the fallback `pure 0` is the correct law on
`ZMod (3^0)`. -/
noncomputable def ndSection7FiberPMFTotal
    (n L : ℕ) : PMF (ZMod (3 ^ n)) :=
  if h : 0 < n ∧ n ≤ L then
    ndSection7FiberPMF n L h.1 h.2
  else
    PMF.pure 0

theorem ndSection7FiberPMFTotal_eq_of_pos_of_le
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    ndSection7FiberPMFTotal n L =
      ndSection7FiberPMF n L hn hL := by
  simp [ndSection7FiberPMFTotal, hn, hL]

theorem ndSection7FiberPMFTotal_eq_pure_zero_of_not_valid
    {n L : ℕ} (h : ¬ (0 < n ∧ n ≤ L)) :
    ndSection7FiberPMFTotal n L = PMF.pure 0 := by
  simp [ndSection7FiberPMFTotal, h]

theorem ndSection7FiberPMFTotal_eq_pure_zero_of_lt
    {n L : ℕ} (hL : L < n) :
    ndSection7FiberPMFTotal n L = PMF.pure 0 :=
  ndSection7FiberPMFTotal_eq_pure_zero_of_not_valid
    (fun h => (Nat.not_le_of_gt hL) h.2)

@[simp]
theorem ndSection7FiberPMFTotal_zero (L : ℕ) :
    ndSection7FiberPMFTotal 0 L = PMF.pure 0 := by
  simp [ndSection7FiberPMFTotal]

/-- A countable classifier partitions a source PMF into its exact gated
target atoms.  This is the native `ENNReal` form used by D6. -/
theorem nd_tsum_taoGatedOptionPMF_classifier
    {ι α β : Type*} (p : PMF α) (s : α → ι) (f : α → β)
    (y : β) :
    (∑' i : ι,
        Tao.taoGatedOptionPMF p (fun a => s a = i) f (some y)) =
      (p.map f) y := by
  classical
  unfold Tao.taoGatedOptionPMF
  simp_rw [PMF.map_apply]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  rw [tsum_eq_single (s a)]
  · simp [Tao.taoGatedOptionKey]
  · intro i hi
    have hne : s a ≠ i := fun h => hi h.symm
    simp [Tao.taoGatedOptionKey, hne]

private theorem ndPMF_map_eq_of_eq_on_support
    {α β : Type*} (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) :
    p.map f = p.map g := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro a
  by_cases hpa : p a = 0
  · simp [hpa]
  · have ha : a ∈ p.support := (p.mem_support_iff a).2 hpa
    rw [h a ha]

/-- Reversal transports the fixed-total affine gated submass to the
chronological Section-7 gated submass. -/
theorem ndAffineFixedTotalSubmass_eq_section7
    (n L : ℕ) (y : ZMod (3 ^ n)) :
    Tao.taoGatedSubmass
        (Tao.geom2PNatListPMF n)
        (fun as => Tao.taoTupleWeight as = L)
        (Tao.taoAffineOffsetZMod n) y =
      Tao.taoGatedSubmass
        (Tao.geom2PNatListPMF n)
        (fun as => Tao.taoTupleWeight as = L)
        (Tao.taoSection7OffsetZMod n) y := by
  let affineKey : List ℕ+ → Option (ZMod (3 ^ n)) :=
    Tao.taoGatedOptionKey
      (fun as => Tao.taoTupleWeight as = L)
      (Tao.taoAffineOffsetZMod n)
  let section7Key : List ℕ+ → Option (ZMod (3 ^ n)) :=
    Tao.taoGatedOptionKey
      (fun as => Tao.taoTupleWeight as = L)
      (Tao.taoSection7OffsetZMod n)
  have hkey : ∀ as ∈ (Tao.geom2PNatListPMF n).support,
      affineKey as.reverse = section7Key as := by
    intro as has
    have hlen := Tao.geom2PNatListPMF_support_length_eq has
    simp only [affineKey, section7Key, Tao.taoGatedOptionKey,
      Tao.taoTupleWeight_reverse]
    by_cases hweight : Tao.taoTupleWeight as = L
    · simp [hweight,
        Tao.taoAffineOffsetZMod_reverse_eq_taoSection7OffsetZMod hlen]
    · simp [hweight]
  have hpmf :
      (Tao.geom2PNatListPMF n).map affineKey =
        (Tao.geom2PNatListPMF n).map section7Key := by
    calc
      (Tao.geom2PNatListPMF n).map affineKey =
          ((Tao.geom2PNatListPMF n).map List.reverse).map affineKey := by
        rw [Tao.geom2PNatListPMF_map_reverse]
      _ = (Tao.geom2PNatListPMF n).map
          (fun as => affineKey as.reverse) := by
        rw [PMF.map_comp]
        rfl
      _ = (Tao.geom2PNatListPMF n).map section7Key := by
        apply ndPMF_map_eq_of_eq_on_support
        exact hkey
  exact congrArg ENNReal.toReal
    (congrArg (fun p : PMF (Option (ZMod (3 ^ n))) => p (some y)) hpmf)

/-- Native fixed-total target mass equals the endpoint atom times the
totalized conditioned fiber atom, including `n = 0` and infeasible totals. -/
theorem ndFixedTotalGatedOptionMass_eq_endpoint_mul_fiberTotal
    (n L : ℕ) (y : ZMod (3 ^ n)) :
    Tao.taoGatedOptionPMF
        (Tao.geom2PNatListPMF n)
        (fun as => Tao.taoTupleWeight as = L)
        (Tao.taoSection7OffsetZMod n) (some y) =
      ndGeom2EndpointPMF n L * ndSection7FiberPMFTotal n L y := by
  rcases n with _ | n
  · rcases L with _ | L
    · unfold Tao.taoGatedOptionPMF ndGeom2EndpointPMF
      simp only [Tao.geom2PNatListPMF, PMF.pure_map]
      simp [ndSection7FiberPMFTotal, Tao.taoGatedOptionKey,
        Tao.taoTupleWeight, Tao.taoSection7OffsetZMod]
    · unfold Tao.taoGatedOptionPMF ndGeom2EndpointPMF
      simp only [Tao.geom2PNatListPMF, PMF.pure_map]
      simp [ndSection7FiberPMFTotal, Tao.taoGatedOptionKey,
        Tao.taoTupleWeight]
  · have hn : 0 < n + 1 := by omega
    by_cases hL : n + 1 ≤ L
    · apply (ENNReal.toReal_eq_toReal_iff'
          ((Tao.taoGatedOptionPMF
            (Tao.geom2PNatListPMF (n + 1))
            (fun as => Tao.taoTupleWeight as = L)
            (Tao.taoSection7OffsetZMod (n + 1))).apply_ne_top (some y))
          (ENNReal.mul_ne_top
            ((ndGeom2EndpointPMF (n + 1)).apply_ne_top L)
            ((ndSection7FiberPMFTotal (n + 1) L).apply_ne_top y))).mp
      rw [ENNReal.toReal_mul]
      change Tao.taoGatedSubmass
          (Tao.geom2PNatListPMF (n + 1))
          (fun as => Tao.taoTupleWeight as = L)
          (Tao.taoSection7OffsetZMod (n + 1)) y =
        (ndGeom2EndpointPMF (n + 1) L).toReal *
          (ndSection7FiberPMFTotal (n + 1) L y).toReal
      rw [ndGeom2EndpointPMF_apply_toReal_eq_endpointMass,
        ndSection7FiberPMFTotal_eq_of_pos_of_le hn hL]
      rw [← ndSection6FixedSplitTailSubmass_zero_head_zero_weight_eq_gatedSubmass]
      exact ndSection6FixedSplitTailSubmass_zero_head_zero_weight_eq
        (n + 1) L hn hL y
    · have hlt : L < n + 1 := by omega
      rw [ndGeom2EndpointPMF_apply_eq_zero_of_lt hlt, zero_mul]
      unfold Tao.taoGatedOptionPMF
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro as
      by_cases hweight : Tao.taoTupleWeight as = L
      · have hlength : as.length ≠ n + 1 := by
          intro heq
          have hbound := ndListLength_le_taoTupleWeight as
          omega
        rw [Tao.geom2PNatListPMF_apply_eq_zero_of_length_ne
          (n + 1) as hlength]
        simp
      · simp [Tao.taoGatedOptionKey, hweight]

/-- Exact D6: the endpoint law bound to the totalized fixed-total fibers is
the complete Syracuse source law. -/
theorem ndGeom2EndpointPMF_bind_fiberTotal_eq_syracPMF (n : ℕ) :
    (ndGeom2EndpointPMF n).bind (ndSection7FiberPMFTotal n) =
      Tao.syracPMF n := by
  apply PMF.ext
  intro y
  rw [PMF.bind_apply]
  calc
    (∑' L : ℕ,
        ndGeom2EndpointPMF n L * ndSection7FiberPMFTotal n L y) =
        ∑' L : ℕ,
          Tao.taoGatedOptionPMF
            (Tao.geom2PNatListPMF n)
            (fun as => Tao.taoTupleWeight as = L)
            (Tao.taoSection7OffsetZMod n) (some y) := by
      apply tsum_congr
      intro L
      exact (ndFixedTotalGatedOptionMass_eq_endpoint_mul_fiberTotal
        n L y).symm
    _ = ((Tao.geom2PNatListPMF n).map
          (Tao.taoSection7OffsetZMod n)) y :=
      nd_tsum_taoGatedOptionPMF_classifier
        (Tao.geom2PNatListPMF n) Tao.taoTupleWeight
        (Tao.taoSection7OffsetZMod n) y
    _ = Tao.syracPMF n y :=
      congrArg (fun p : PMF (ZMod (3 ^ n)) => p y)
        (Tao.syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod n).symm

/-- Pointwise real D6, with exactly one endpoint-mass factor. -/
theorem tsum_ndGeom2EndpointMass_mul_fiberTotal_eq_syracPMF
    (n : ℕ) (y : ZMod (3 ^ n)) :
    (∑' L : ℕ,
        ndGeom2EndpointMass n L *
          (ndSection7FiberPMFTotal n L y).toReal) =
      (Tao.syracPMF n y).toReal := by
  have hbind := congrArg (fun p : PMF (ZMod (3 ^ n)) => p y)
    (ndGeom2EndpointPMF_bind_fiberTotal_eq_syracPMF n)
  change
    ((ndGeom2EndpointPMF n).bind (ndSection7FiberPMFTotal n)) y =
      Tao.syracPMF n y at hbind
  rw [PMF.bind_apply] at hbind
  rw [← hbind, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro L
    rw [ENNReal.toReal_mul,
      ndGeom2EndpointPMF_apply_toReal_eq_endpointMass]
  · intro L
    exact ENNReal.mul_ne_top
      ((ndGeom2EndpointPMF n).apply_ne_top L)
      ((ndSection7FiberPMFTotal n L).apply_ne_top y)

/-- The feasible affine fixed-total submass is the same endpoint-weighted
conditioned fiber atom used in D6. -/
theorem ndAffineFixedTotalSubmass_eq_endpointMass_mul_fiberPMF
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L)
    (y : ZMod (3 ^ n)) :
    Tao.taoGatedSubmass
        (Tao.geom2PNatListPMF n)
        (fun as => Tao.taoTupleWeight as = L)
        (Tao.taoAffineOffsetZMod n) y =
      ndGeom2EndpointMass n L *
        (ndSection7FiberPMF n L hn hL y).toReal := by
  rw [ndAffineFixedTotalSubmass_eq_section7]
  rw [← ndSection6FixedSplitTailSubmass_zero_head_zero_weight_eq_gatedSubmass]
  exact ndSection6FixedSplitTailSubmass_zero_head_zero_weight_eq
    n L hn hL y

end

end ND
end Erdos1135
