import Erdos1135.Tao.Section6.FixedSlicePolynomial

/-!
# Section 6 Fixed-Ambient Slice

The fixed-slice Fourier theorem is parametrized by a tail length `T`, so its
ambient group is written `ZMod (3^(T+(k+1)))`.  Aggregation instead fixes one
ambient level `n` while `k` varies.  This leaf defines the direct length-`n`
source gate, identifies it with the checked head-tail slice, and transports
the polynomial estimate to a single function space `ZMod (3^n) → ℝ`.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Direct fixed-ambient source gate.  Exact source length is retained in the
predicate even though the iid list PMF supplies it on support. -/
noncomputable def taoSection6FixedAmbientGate
    (CA : ℝ) (n k l : ℕ) (full : List ℕ+) : Prop :=
  full.length = n ∧
    taoSection6HeadGate CA n k l (full.take (k + 1))

/-- Direct fixed-ambient Option law, with rejected source mass at `none`. -/
noncomputable def taoSection6FixedAmbientPMF
    (CA : ℝ) (n k l : ℕ) : PMF (Option (ZMod (3 ^ n))) :=
  taoGatedOptionPMF
    (geom2PNatListPMF n)
    (taoSection6FixedAmbientGate CA n k l)
    (taoSection7OffsetZMod n)

/-- Accepted fixed-ambient source mass at one residue. -/
noncomputable def taoSection6FixedAmbientSubmass
    (CA : ℝ) (n k l : ℕ) (x : ZMod (3 ^ n)) : ℝ :=
  (taoSection6FixedAmbientPMF CA n k l (some x)).toReal

/-- At an additive ambient level, the direct exact-length law is the existing
head-tail gated source law.  Unsupported source lengths contribute zero to
both maps. -/
theorem taoSection6FixedAmbientPMF_add_eq_gatedSourcePMF
    (CA : ℝ) (T k l : ℕ) :
    taoSection6FixedAmbientPMF CA (T + (k + 1)) k l =
      taoSection6GatedSourcePMF CA T k l := by
  apply PMF.ext
  intro y
  unfold taoSection6FixedAmbientPMF taoSection6GatedSourcePMF
  unfold taoGatedOptionPMF
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro full
  by_cases hlength : full.length = T + (k + 1)
  · by_cases hgate :
        taoSection6HeadGate CA (T + (k + 1)) k l
          (full.take (k + 1))
    · simp [taoSection6FixedAmbientGate, taoGatedOptionKey, hlength, hgate]
    · simp [taoSection6FixedAmbientGate, taoGatedOptionKey, hlength, hgate]
  · have hzero : geom2PNatListPMF (T + (k + 1)) full = 0 :=
      geom2PNatListPMF_apply_eq_zero_of_length_ne _ _ hlength
    simp [hzero]

/-- Pointwise fixed-ambient identification with the checked head-tail slice. -/
theorem taoSection6FixedAmbientSubmass_add_eq_gatedSourceSubmass
    (CA : ℝ) (T k l : ℕ) (x : ZMod (3 ^ (T + (k + 1)))) :
    taoSection6FixedAmbientSubmass CA (T + (k + 1)) k l x =
      taoSection6GatedSourceSubmass CA T k l x := by
  unfold taoSection6FixedAmbientSubmass taoSection6GatedSourceSubmass
  rw [taoSection6FixedAmbientPMF_add_eq_gatedSourcePMF]

/-- One-coordinate head canary for the fixed-ambient identification. -/
theorem taoSection6FixedAmbientSubmass_zero_k
    (CA : ℝ) (T l : ℕ) (x : ZMod (3 ^ (T + 1))) :
    taoSection6FixedAmbientSubmass CA (T + 1) 0 l x =
      taoSection6GatedSourceSubmass CA T 0 l x := by
  simpa using
    taoSection6FixedAmbientSubmass_add_eq_gatedSourceSubmass CA T 0 l x

/-- Terminal crossing canary: a head of length `k+1` leaves the normalized
tail at level zero. -/
theorem taoSection6FixedAmbientSubmass_zero_tail
    (CA : ℝ) (k l : ℕ) (x : ZMod (3 ^ (0 + (k + 1)))) :
    taoSection6FixedAmbientSubmass CA (0 + (k + 1)) k l x =
      taoSection6GatedSourceSubmass CA 0 k l x := by
  exact taoSection6FixedAmbientSubmass_add_eq_gatedSourceSubmass CA 0 k l x

/-- The uniform polynomial fixed-slice rate transported to one fixed ambient
group.  The final surface contains no dependent cast or tail-length index. -/
theorem TaoProp117PrimitivePolynomialDecayStatement.exists_taoSection6FixedAmbientOscillation_le
    (h117 : TaoProp117PrimitivePolynomialDecayStatement)
    (CA : ℝ) (hCA : 17 ≤ CA) (A : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N0 : ℕ, ∀ n k l m : ℕ,
      N0 ≤ n →
      k + 1 ≤ n →
      m ≤ n →
      9 * n ≤ 10 * m →
      taoZModPowOscillation m n
          (taoSection6FixedAmbientSubmass CA n k l) ≤
        D / (n : ℝ) ^ (A + 3) := by
  obtain ⟨D, hD, N0, hslice⟩ :=
    h117.exists_taoSection6FixedSliceOscillation_le CA hCA A
  refine ⟨D, hD, N0, ?_⟩
  intro n k l m hn hk hmn hm
  let T := n - (k + 1)
  have hambient : T + (k + 1) = n := by
    dsimp [T]
    exact Nat.sub_add_cancel hk
  have hbound := hslice T k l m
    (by simpa [hambient] using hn)
    (by simpa [hambient] using hmn)
    (by simpa [hambient] using hm)
  have hsource :
      taoSection6FixedAmbientSubmass CA (T + (k + 1)) k l =
        taoSection6GatedSourceSubmass CA T k l := by
    funext x
    exact taoSection6FixedAmbientSubmass_add_eq_gatedSourceSubmass CA T k l x
  rw [← hsource] at hbound
  rw [hambient] at hbound
  exact hbound

end

end Tao
end Erdos1135
