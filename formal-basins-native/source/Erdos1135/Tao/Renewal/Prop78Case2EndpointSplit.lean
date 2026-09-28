import Erdos1135.Tao.Renewal.Prop78Case1White

/-!
# Proposition 7.8 Case 2 Endpoint Split

This proof leaf repairs the endpoint-gain step after Tao's stopped identity.
At a white endpoint with sufficiently large remaining horizontal level, the
uniform Case 1 theorem supplies the required half-discount.  The three
complementary branches are kept explicit for the later canonical
first-passage tail and white-exit estimates.
-/

namespace Erdos1135
namespace Tao

/-- A horizontal advance below the current level produces the exact boundary
at the remaining level. -/
theorem taoSection7QmBoundary_of_horizontalAdvance
    {J m r : ℕ} {p q : TaoSection7RenewalPoint}
    (hp : taoSection7QmBoundary J m p)
    (hjq : (q.j : ℕ) = (p.j : ℕ) + r)
    (hr : r < m) :
    taoSection7QmBoundary J (m - r) q := by
  unfold taoSection7QmBoundary at *
  omega

/-- Uniform repaired endpoint split for Proposition 7.8 Case 2.

The final branch is the honest endpoint half-gain.  It is obtained by one
additional Case 1 recursion at local level `m-r`, rather than by inserting the
stopped endpoint into the pre-endpoint white count in `(7.45)`.
-/
theorem exists_taoSection7Prop78_case2_endpointSplit_uniform
    (A : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, ∀ n : ℕ, ∀ xi : ZMod (3 ^ n),
      ∀ m r : ℕ, ∀ p q : TaoSection7RenewalPoint,
        taoSection7QmBoundary (n / 2) m p →
        (q.j : ℕ) = (p.j : ℕ) + r →
          m ≤ r ∨
          m - r < C ∨
          ¬ taoSection7SourceActualW n xi epsilon q ∨
          taoSection7SourceActualQ n xi epsilon q ≤
            Real.exp (-(epsilon ^ 3 / 2)) *
              (((m - r : ℕ) : ℝ) ^ A)⁻¹ *
              taoSection7SourceActualQmAtCutoff
                n A (m - r - 1) xi epsilon := by
  obtain ⟨C, hC⟩ :=
    exists_taoSection7Prop78_case1_cutoffWhite_halfDiscount_threshold_uniform
      A hepsilon
  refine ⟨C, fun n xi m r p q hp hjq => ?_⟩
  by_cases hover : m ≤ r
  · exact Or.inl hover
  · right
    have hr : r < m := Nat.lt_of_not_ge hover
    by_cases hsmall : m - r < C
    · exact Or.inl hsmall
    · right
      by_cases hwhite : taoSection7SourceActualW n xi epsilon q
      · right
        exact hC n xi (m - r) (Nat.le_of_not_gt hsmall) q
          (taoSection7QmBoundary_of_horizontalAdvance hp hjq hr) hwhite
      · exact Or.inl hwhite

end Tao
end Erdos1135
