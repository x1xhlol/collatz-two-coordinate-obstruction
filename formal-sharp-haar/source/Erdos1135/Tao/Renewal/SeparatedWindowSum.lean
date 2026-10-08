import Mathlib.Tactic

namespace Erdos1135
namespace Tao

open scoped BigOperators

noncomputable section

/-!
# One-Dimensional Separated Window Sums

This module provides a neutral finite-sum surface for the one-dimensional
local-average step in Tao Lemma 7.10.  It is intentionally not a probability
theorem and does not define the Gaussian kernel from `(7.48)`.
-/

/-- Integer window `[c - R, c + R]`. -/
def taoSection7IntIccWindow (R : ℕ) (c : ℤ) : Finset ℤ :=
  Finset.Icc (c - (R : ℤ)) (c + (R : ℤ))

theorem mem_taoSection7IntIccWindow {R : ℕ} {c x : ℤ} :
    x ∈ taoSection7IntIccWindow R c ↔ c - (R : ℤ) ≤ x ∧ x ≤ c + (R : ℤ) := by
  simp [taoSection7IntIccWindow]

/-- Nonnegativity socket for a one-dimensional kernel. -/
def TaoSection7KernelNonnegative (K : ℤ → ℝ) : Prop :=
  ∀ x : ℤ, 0 ≤ K x

/-- Near-window mass is controlled by the center value with loss `L`. -/
def TaoSection7NearWindowMassBound
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (center : ι → ℤ)
    (nearWindow : ι → Finset ℤ) (K : ℤ → ℝ) (L : ℝ) : Prop :=
  ∀ i ∈ S, (nearWindow i).sum (fun x => K x) ≤ L * K (center i)

/-- The kernel value at each center is controlled by a local average. -/
def TaoSection7LocalAverageAtCenters
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (center : ι → ℤ)
    (avgWindow : ι → Finset ℤ) (K : ℤ → ℝ) (lambda : ℝ) : Prop :=
  ∀ i ∈ S, K (center i) ≤ lambda * (avgWindow i).sum (fun x => K x)

/-- Total averaged-window mass budget.  Disjointness or bounded overlap should feed this socket. -/
def TaoSection7AverageWindowTotalBound
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (avgWindow : ι → Finset ℤ) (K : ℤ → ℝ) (M : ℝ) : Prop :=
  S.sum (fun i => (avgWindow i).sum (fun x => K x)) ≤ M

/--
Finite local-average summation for separated one-dimensional centers.

The theorem deliberately requires a local-average hypothesis; it cannot turn an
arbitrary spiky nonnegative kernel into Tao's `B / s'` gain.
-/
theorem taoSection7SeparatedWindowSum_localAverage
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (center : ι → ℤ)
    (nearWindow avgWindow : ι → Finset ℤ) (K : ℤ → ℝ)
    {L lambda M : ℝ}
    (_hK : TaoSection7KernelNonnegative K)
    (hL : 0 ≤ L) (hlambda : 0 ≤ lambda)
    (hnear : TaoSection7NearWindowMassBound S center nearWindow K L)
    (hlocal : TaoSection7LocalAverageAtCenters S center avgWindow K lambda)
    (htotal : TaoSection7AverageWindowTotalBound S avgWindow K M) :
    S.sum (fun i => (nearWindow i).sum (fun x => K x)) ≤ L * lambda * M := by
  have hpoint :
      ∀ i ∈ S,
        (nearWindow i).sum (fun x => K x) ≤
          (L * lambda) * (avgWindow i).sum (fun x => K x) := by
    intro i hi
    have hnear_i := hnear i hi
    have hlocal_i := hlocal i hi
    have hmul :
        L * K (center i) ≤
          L * (lambda * (avgWindow i).sum (fun x => K x)) :=
      mul_le_mul_of_nonneg_left hlocal_i hL
    calc
      (nearWindow i).sum (fun x => K x) ≤ L * K (center i) := hnear_i
      _ ≤ L * (lambda * (avgWindow i).sum (fun x => K x)) := hmul
      _ = (L * lambda) * (avgWindow i).sum (fun x => K x) := by ring
  have hsum :=
    Finset.sum_le_sum hpoint
  have hsum_eq :
      S.sum (fun i => (L * lambda) * (avgWindow i).sum (fun x => K x)) =
        (L * lambda) * S.sum (fun i => (avgWindow i).sum (fun x => K x)) := by
    simpa using
      (Finset.mul_sum S (fun i => (avgWindow i).sum (fun x => K x)) (L * lambda)).symm
  have hcoeff : 0 ≤ L * lambda := mul_nonneg hL hlambda
  have htotal_mul :
      (L * lambda) * S.sum (fun i => (avgWindow i).sum (fun x => K x)) ≤
        (L * lambda) * M :=
    mul_le_mul_of_nonneg_left htotal hcoeff
  calc
    S.sum (fun i => (nearWindow i).sum (fun x => K x))
        ≤ S.sum (fun i => (L * lambda) * (avgWindow i).sum (fun x => K x)) := hsum
    _ = (L * lambda) * S.sum (fun i => (avgWindow i).sum (fun x => K x)) := hsum_eq
    _ ≤ (L * lambda) * M := htotal_mul
    _ = L * lambda * M := by ring

end

end Tao
end Erdos1135
