import CollatzReversedRealOrderedPowers

namespace CollatzResearch.RealWeakStationaryObstruction

open Matrix CollatzCertificate RealAffine RealMixedGrowth RealOrderedPowers
open RealStationaryObstruction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weak_stationary_profile_excludes_strict
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (X Y : Mat ι) (v : Vec ι) (α β K : ℝ) (N : ℕ)
    (hX : EntrywiseLE 0 X) (hY : EntrywiseLE 0 Y)
    (hv : ∀ i, 0 < v i) (hα : 0 ≤ α) (hαβ : α < β) (hK : 0 ≤ K)
    (hscaleB : B.matrix = α • X) (hscaleG : G.matrix = β • Y)
    (hbound : ∀ n : ℕ, (D.matrix i₀ ᵥ* X ^ n) ⬝ᵥ v ≤ K)
    (hstationary : ∀ n : ℕ, N ≤ n → Y ^ n *ᵥ v = Y ^ N *ᵥ v) : False := by
  have hβ : 0 < β := lt_of_le_of_lt hα hαβ
  rcases eq_or_lt_of_le hα with hzero | hpos
  · have hBzero : B.matrix = 0 := by rw [hscaleB, ← hzero, zero_smul]
    have hz : D.matrix i₀ ᵥ* G.matrix = 0 := by
      apply le_antisymm
      · have hh := h.db.1 i₀
        change D.matrix i₀ ᵥ* G.matrix ≤ D.matrix i₀ ᵥ* B.matrix at hh
        simpa only [hBzero, vecMul_zero] using hh
      · exact rowMul_nonneg (fun j => hD.1 i₀ j) hG.1
    apply strict_reversed_maximal_ternary_row_nonzero A B C D E F G i₀
      hA hB hC hD hE hF hG h hstrict 1
    simpa only [pow_one] using hz
  have hXY : EntrywiseLE (X * Y) (Y * X) := by
    intro i j
    have hi := h.gb.1 i j
    change (B.matrix * G.matrix) i j ≤ (G.matrix * B.matrix) i j at hi
    rw [hscaleB, hscaleG] at hi
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Pi.smul_apply, smul_eq_mul] at hi
    change (β * α) * (X * Y) i j ≤ (α * β) * (Y * X) i j at hi
    rw [mul_comm β α] at hi
    exact le_of_mul_le_mul_left hi (mul_pos hpos hβ)
  have hrow : D.matrix i₀ ᵥ* Y ≤ (α / β) • (D.matrix i₀ ᵥ* X) := by
    intro j
    have hi := h.db.1 i₀ j
    change (D.matrix i₀ ᵥ* G.matrix) j ≤ (D.matrix i₀ ᵥ* B.matrix) j at hi
    rw [hscaleG, hscaleB, vecMul_smul, vecMul_smul] at hi
    change β * (D.matrix i₀ ᵥ* Y) j ≤ α * (D.matrix i₀ ᵥ* X) j at hi
    change (D.matrix i₀ ᵥ* Y) j ≤ (α / β) * (D.matrix i₀ ᵥ* X) j
    calc
      (D.matrix i₀ ᵥ* Y) j ≤ (α * (D.matrix i₀ ᵥ* X) j) / β :=
        (le_div_iff₀ hβ).mpr (by nlinarith [hi])
      _ = (α / β) * (D.matrix i₀ ᵥ* X) j := by ring
  have hz := ordered_stationary_profile_row_zero X Y (D.matrix i₀) v (α / β) K N
    hX hY (fun j => hD.1 i₀ j) hv (div_nonneg hα hβ.le)
    ((div_lt_one hβ).mpr hαβ) hK hXY hrow hbound hstationary
  have hGzero : D.matrix i₀ ᵥ* G.matrix ^ N = 0 := by
    rw [hscaleG, smul_pow, vecMul_smul, hz, smul_zero]
  exact strict_reversed_maximal_ternary_row_nonzero A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict N hGzero

end CollatzResearch.RealWeakStationaryObstruction

#print axioms CollatzResearch.RealWeakStationaryObstruction.weak_stationary_profile_excludes_strict
