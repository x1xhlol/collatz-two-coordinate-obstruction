import CollatzReversedRealStationaryProfile

namespace CollatzResearch.RealStationaryObstruction

open Matrix CollatzCertificate RealAffine RealMixedGrowth RealStationaryProfile

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixWord_replicate (maps : MixedSupport.Digit → Mat ι)
    (digit : MixedSupport.Digit) (n : ℕ) :
    matrixWord maps (List.replicate n digit) = maps digit ^ n := by
  induction n with
  | zero => simp [matrixWord]
  | succ n ih => simp [List.replicate_succ, matrixWord, ih, pow_succ']

theorem strict_reversed_maximal_ternary_row_nonzero
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) (n : ℕ) :
    D.matrix i₀ ᵥ* G.matrix ^ n ≠ 0 := by
  intro hz
  obtain ⟨N, hN⟩ := real_reversed_mixed_row_growth A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict (List.replicate n .g) 0
  have hi := hN N le_rfl
  rw [matrixWord_replicate] at hi
  change 0 < (D.matrix i₀ ᵥ* G.matrix ^ n) ⬝ᵥ ((eval B)^[N] C.offset) at hi
  rw [hz, zero_dotProduct] at hi
  exact lt_irrefl 0 hi

theorem stationary_profile_excludes_strict
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (X Y : Mat ι) (v : Vec ι) (α β K : ℝ) (N : ℕ)
    (hX : EntrywiseLE 0 X) (hY : EntrywiseLE 0 Y)
    (hv : ∀ i, 0 < v i) (hα : 0 ≤ α) (hαβ : α < β) (hK : 0 ≤ K)
    (hXY : Commute X Y) (hscaleB : B.matrix = α • X) (hscaleG : G.matrix = β • Y)
    (hbound : ∀ n : ℕ, (D.matrix i₀ ᵥ* X ^ n) ⬝ᵥ v ≤ K)
    (hstationary : ∀ n : ℕ, N ≤ n → Y ^ n *ᵥ v = Y ^ N *ᵥ v) : False := by
  have hβ : 0 < β := lt_of_le_of_lt hα hαβ
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
  have hz := stationary_profile_row_zero X Y (D.matrix i₀) v (α / β) K N
    hX hY (fun j => hD.1 i₀ j) hv (div_nonneg hα hβ.le)
    ((div_lt_one hβ).mpr hαβ) hK hXY hrow hbound hstationary
  have hGzero : D.matrix i₀ ᵥ* G.matrix ^ N = 0 := by
    rw [hscaleG, smul_pow, vecMul_smul, hz, smul_zero]
  exact strict_reversed_maximal_ternary_row_nonzero A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict N hGzero

end CollatzResearch.RealStationaryObstruction

#print axioms CollatzResearch.RealStationaryObstruction.matrixWord_replicate
#print axioms CollatzResearch.RealStationaryObstruction.strict_reversed_maximal_ternary_row_nonzero
#print axioms CollatzResearch.RealStationaryObstruction.stationary_profile_excludes_strict
