/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.A5HistoricalAdjacentCylinderQOneRootDyadicPhysicalCensus
import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricBalancedCrossingAffineDensity
import Erdos1135Predecessor.Tao.Section5.EndpointRatio

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

def ndGeom2ShiftedWideSymmetricBoundedOvershoot
    (b a s K : ℕ) (word : List ℕ+) : Prop :=
  Tao.taoTupleWeight word + ndBalancedTotal (b - s) +
      ndGeom2ShiftedWideSymmetricShiftRadius b ≤
    2 * b + ndBalancedTotal (s - b) + a + K

theorem ndGeom2ShiftedWideSymmetricSelectedDepth_le_two_mul_add_one
    {b s : ℕ}
    (hs : s ∈ ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b) :
    s ≤ 2 * b + 1 := by
  have hsUpper := (Finset.mem_Icc.mp hs).2
  have hw := ndGeom2ShiftedWideSymmetricWidth_le_base b
  unfold ndGeom2ShiftedWideSymmetricHorizon at hsUpper
  omega

theorem ndGeom2ShiftedWideSymmetric_two_mul_three_pow_lt_root
    {b s M : ℕ} (hb : 9 ≤ b)
    (hs : s ∈ ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b)
    (hroot : 16 ^ b ≤ M) :
    2 * 3 ^ s < M := by
  have hsUpper :=
    ndGeom2ShiftedWideSymmetricSelectedDepth_le_two_mul_add_one hs
  have hpow : 3 ^ s ≤ 3 ^ (2 * b + 1) :=
    Nat.pow_le_pow_right (by norm_num) hsUpper
  have hgeom : 6 * 9 ^ b < 16 ^ b :=
    six_mul_nine_pow_lt_sixteen_pow (by omega)
  calc
    2 * 3 ^ s ≤ 2 * 3 ^ (2 * b + 1) := Nat.mul_le_mul_left 2 hpow
    _ = 6 * 9 ^ b := by
      rw [pow_add]
      rw [show 3 ^ (2 * b) = 9 ^ b by
        calc
          3 ^ (2 * b) = (3 ^ 2) ^ b := pow_mul 3 2 b
          _ = 9 ^ b := by norm_num]
      ring
    _ < 16 ^ b := hgeom
    _ ≤ M := hroot

private theorem four_pow_eq_two_pow_two_mul (b : ℕ) :
    4 ^ b = 2 ^ (2 * b) := by
  calc
    4 ^ b = (2 ^ 2) ^ b := by norm_num
    _ = 2 ^ (2 * b) := (pow_mul 2 2 b).symm

theorem shiftedWideSymmetric_affineSource_crossBounds_of_boundedOvershoot
    {b a s K N M : ℕ} {word : List ℕ+}
    (hlen : word.length = s)
    (hhit : ndGeom2ShiftedWideSymmetricHit b a s word)
    (hover : ndGeom2ShiftedWideSymmetricBoundedOvershoot b a s K word)
    (hroom : 2 * 3 ^ s < M)
    (hAff : Tao.taoAffList word (N : ℚ) = (M : ℚ)) :
    2 ^ a * 4 ^ b * M ≤
        4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b * N ∧
      2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b * N ≤
        2 * 2 ^ K * 2 ^ a * 4 ^ b * M := by
  let W := Tao.taoTupleWeight word
  let R := ndGeom2ShiftedWideSymmetricShiftRadius b
  let C := Tao.taoOffsetNum word
  have htake : word.take s = word := by
    rw [← hlen]
    exact List.take_length
  have hhitNat :
      2 * b + ndBalancedTotal (s - b) + a ≤
        W + ndBalancedTotal (b - s) + R := by
    unfold ndGeom2ShiftedWideSymmetricHit at hhit
    rw [htake] at hhit
    simpa only [W, R] using hhit
  have hoverNat :
      W + ndBalancedTotal (b - s) + R ≤
        2 * b + ndBalancedTotal (s - b) + a + K := by
    simpa only [ndGeom2ShiftedWideSymmetricBoundedOvershoot, W, R]
      using hover
  have hclearNat :=
    (Tao.taoAffList_eq_nat_iff_cleared word N M).mp hAff
  have hclear : 3 ^ s * N + C = 2 ^ W * M := by
    simpa only [hlen, W, C] using hclearNat
  have hoffset : C ≤ 2 ^ W * 3 ^ s := by
    simpa only [hlen, W, C] using
      Tao.taoOffsetNum_le_two_pow_weight_mul_three_pow_length word
  have hpowTwoPos : 0 < 2 ^ W := by positivity
  have hscaledRoom : 2 * (2 ^ W * 3 ^ s) < 2 ^ W * M := by
    calc
      2 * (2 ^ W * 3 ^ s) = 2 ^ W * (2 * 3 ^ s) := by ring
      _ < 2 ^ W * M := (Nat.mul_lt_mul_left hpowTwoPos).2 hroom
  have hterminalLeDoubleSource :
      2 ^ W * M ≤ 2 * (3 ^ s * N) := by
    omega
  have hsourceLeTerminal : 3 ^ s * N ≤ 2 ^ W * M := by
    omega
  by_cases hbs : b ≤ s
  · let j := s - b
    have hsSplit : s = b + j := by
      dsimp only [j]
      omega
    have hhitRight :
        2 * b + ndBalancedTotal j + a ≤ W + R := by
      simpa only [j, Nat.sub_eq_zero_of_le hbs, ndBalancedTotal_zero,
        Nat.add_zero] using hhitNat
    have hoverRight :
        W + R ≤ 2 * b + ndBalancedTotal j + a + K := by
      simpa only [j, Nat.sub_eq_zero_of_le hbs, ndBalancedTotal_zero,
        Nat.add_zero] using hoverNat
    have hexpLower :
        2 ^ (2 * b + ndBalancedTotal j + a) ≤ 2 ^ (W + R) :=
      Nat.pow_le_pow_right (by norm_num) hhitRight
    have hexpUpper :
        2 ^ (W + R) ≤ 2 ^ (2 * b + ndBalancedTotal j + a + K) :=
      Nat.pow_le_pow_right (by norm_num) hoverRight
    have hbalancedLower : 3 ^ j ≤ 2 ^ ndBalancedTotal j :=
      three_pow_le_two_pow_ndBalancedTotal j
    have hbalancedUpper : 2 ^ ndBalancedTotal j ≤ 2 * 3 ^ j :=
      two_pow_ndBalancedTotal_le_two_mul_three_pow j
    have hlowerTimes :
        (2 ^ a * 4 ^ b * M) * 3 ^ j ≤
          (2 * 2 ^ R * 3 ^ b * N) * 3 ^ j := by
      calc
        (2 ^ a * 4 ^ b * M) * 3 ^ j =
            (2 ^ a * 4 ^ b * 3 ^ j) * M := by ring
        _ ≤ (2 ^ a * 4 ^ b * 2 ^ ndBalancedTotal j) * M :=
          Nat.mul_le_mul_right M
            (Nat.mul_le_mul_left (2 ^ a * 4 ^ b) hbalancedLower)
        _ = 2 ^ (2 * b + ndBalancedTotal j + a) * M := by
          rw [four_pow_eq_two_pow_two_mul, pow_add, pow_add]
          ring
        _ ≤ 2 ^ (W + R) * M := Nat.mul_le_mul_right M hexpLower
        _ = 2 ^ R * (2 ^ W * M) := by
          rw [pow_add]
          ring
        _ ≤ 2 ^ R * (2 * (3 ^ s * N)) :=
          Nat.mul_le_mul_left (2 ^ R) hterminalLeDoubleSource
        _ = (2 * 2 ^ R * 3 ^ b * N) * 3 ^ j := by
          rw [hsSplit, pow_add]
          ring
    have hlowerSharp :
        2 ^ a * 4 ^ b * M ≤ 2 * 2 ^ R * 3 ^ b * N :=
      Nat.le_of_mul_le_mul_right hlowerTimes (by positivity)
    have hlower :
        2 ^ a * 4 ^ b * M ≤ 4 * 2 ^ R * 3 ^ b * N := by
      calc
        2 ^ a * 4 ^ b * M ≤ 2 * 2 ^ R * 3 ^ b * N := hlowerSharp
        _ ≤ 4 * 2 ^ R * 3 ^ b * N := by
          have htwoFour :
              2 * (2 ^ R * 3 ^ b * N) ≤
                4 * (2 ^ R * 3 ^ b * N) :=
            Nat.mul_le_mul_right (2 ^ R * 3 ^ b * N) (by norm_num)
          simpa only [mul_assoc] using htwoFour
    have hupperTimes :
        (2 ^ R * 3 ^ b * N) * 3 ^ j ≤
          (2 * 2 ^ K * 2 ^ a * 4 ^ b * M) * 3 ^ j := by
      calc
        (2 ^ R * 3 ^ b * N) * 3 ^ j =
            2 ^ R * (3 ^ s * N) := by
          rw [hsSplit, pow_add]
          ring
        _ ≤ 2 ^ R * (2 ^ W * M) :=
          Nat.mul_le_mul_left (2 ^ R) hsourceLeTerminal
        _ = 2 ^ (W + R) * M := by
          rw [pow_add]
          ring
        _ ≤ 2 ^ (2 * b + ndBalancedTotal j + a + K) * M :=
          Nat.mul_le_mul_right M hexpUpper
        _ = (2 ^ K * 2 ^ a * 4 ^ b * 2 ^ ndBalancedTotal j) * M := by
          rw [four_pow_eq_two_pow_two_mul, pow_add, pow_add, pow_add]
          ring
        _ ≤ (2 ^ K * 2 ^ a * 4 ^ b * (2 * 3 ^ j)) * M :=
          Nat.mul_le_mul_right M
            (Nat.mul_le_mul_left (2 ^ K * 2 ^ a * 4 ^ b)
              hbalancedUpper)
        _ = (2 * 2 ^ K * 2 ^ a * 4 ^ b * M) * 3 ^ j := by ring
    exact ⟨hlower,
      Nat.le_of_mul_le_mul_right hupperTimes (by positivity)⟩
  · have hsb : s ≤ b := Nat.le_of_lt (Nat.lt_of_not_ge hbs)
    let j := b - s
    have hsSplit : b = s + j := by
      dsimp only [j]
      omega
    have hhitLeft :
        2 * b + a ≤ W + ndBalancedTotal j + R := by
      simpa only [j, Nat.sub_eq_zero_of_le hsb, ndBalancedTotal_zero,
        Nat.zero_add] using hhitNat
    have hoverLeft :
        W + ndBalancedTotal j + R ≤ 2 * b + a + K := by
      simpa only [j, Nat.sub_eq_zero_of_le hsb, ndBalancedTotal_zero,
        Nat.zero_add] using hoverNat
    have hexpLower : 2 ^ (2 * b + a) ≤
        2 ^ (W + ndBalancedTotal j + R) :=
      Nat.pow_le_pow_right (by norm_num) hhitLeft
    have hexpUpper : 2 ^ (W + ndBalancedTotal j + R) ≤
        2 ^ (2 * b + a + K) :=
      Nat.pow_le_pow_right (by norm_num) hoverLeft
    have hbalancedLower : 3 ^ j ≤ 2 ^ ndBalancedTotal j :=
      three_pow_le_two_pow_ndBalancedTotal j
    have hbalancedUpper : 2 ^ ndBalancedTotal j ≤ 2 * 3 ^ j :=
      two_pow_ndBalancedTotal_le_two_mul_three_pow j
    have hlower :
        2 ^ a * 4 ^ b * M ≤ 4 * 2 ^ R * 3 ^ b * N := by
      calc
        2 ^ a * 4 ^ b * M = 2 ^ (2 * b + a) * M := by
          rw [four_pow_eq_two_pow_two_mul, pow_add]
          ring
        _ ≤ 2 ^ (W + ndBalancedTotal j + R) * M :=
          Nat.mul_le_mul_right M hexpLower
        _ = 2 ^ R * 2 ^ W * 2 ^ ndBalancedTotal j * M := by
          rw [pow_add, pow_add]
          ring
        _ ≤ 2 ^ R * 2 ^ W * (2 * 3 ^ j) * M :=
          Nat.mul_le_mul_right M
            (Nat.mul_le_mul_left (2 ^ R * 2 ^ W) hbalancedUpper)
        _ = 2 * 2 ^ R * 3 ^ j * (2 ^ W * M) := by ring
        _ ≤ 2 * 2 ^ R * 3 ^ j * (2 * (3 ^ s * N)) :=
          Nat.mul_le_mul_left (2 * 2 ^ R * 3 ^ j)
            hterminalLeDoubleSource
        _ = 4 * 2 ^ R * 3 ^ b * N := by
          rw [hsSplit, pow_add]
          ring
    have hupperSharp :
        2 ^ R * 3 ^ b * N ≤ 2 ^ K * 2 ^ a * 4 ^ b * M := by
      calc
        2 ^ R * 3 ^ b * N = 2 ^ R * 3 ^ j * (3 ^ s * N) := by
          rw [hsSplit, pow_add]
          ring
        _ ≤ 2 ^ R * 3 ^ j * (2 ^ W * M) :=
          Nat.mul_le_mul_left (2 ^ R * 3 ^ j) hsourceLeTerminal
        _ ≤ 2 ^ R * 2 ^ ndBalancedTotal j * (2 ^ W * M) :=
          Nat.mul_le_mul_right (2 ^ W * M)
            (Nat.mul_le_mul_left (2 ^ R) hbalancedLower)
        _ = 2 ^ (W + ndBalancedTotal j + R) * M := by
          rw [pow_add, pow_add]
          ring
        _ ≤ 2 ^ (2 * b + a + K) * M :=
          Nat.mul_le_mul_right M hexpUpper
        _ = 2 ^ K * 2 ^ a * 4 ^ b * M := by
          rw [four_pow_eq_two_pow_two_mul, pow_add, pow_add]
          ring
    have hupper :
        2 ^ R * 3 ^ b * N ≤
          2 * 2 ^ K * 2 ^ a * 4 ^ b * M := by
      calc
        2 ^ R * 3 ^ b * N ≤ 2 ^ K * 2 ^ a * 4 ^ b * M := hupperSharp
        _ ≤ 2 * 2 ^ K * 2 ^ a * 4 ^ b * M := by
          have honeTwo :
              1 * (2 ^ K * 2 ^ a * 4 ^ b * M) ≤
                2 * (2 ^ K * 2 ^ a * 4 ^ b * M) :=
            Nat.mul_le_mul_right (2 ^ K * 2 ^ a * 4 ^ b * M) (by norm_num)
          simpa only [one_mul, mul_assoc] using honeTwo
    exact ⟨hlower, hupper⟩

end

end PositiveDensity

end ND

end Erdos1135Predecessor
