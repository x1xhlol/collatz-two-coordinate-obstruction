import DiophantineApproximation.SubspaceAffine
import DiophantineApproximation.RationalPlaces

open Finset Height IsDedekindDomain Module NumberField
open scoped Classical

namespace CollatzSubspaceBridge

theorem intHeight_le_max {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℤ) (hx : (fun i ↦ (x i : ℚ)) ≠ 0) :
    mulHeight (fun i ↦ (x i : ℚ)) ≤ ⨆ i, |(x i : ℝ)| := by
  have h := NumberField.mulHeight_le_prod_of_forall_mem_integer
    (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) hx
    (fun i ↦ by
      simpa only [Finset.coe_empty] using
        (Set.integer (∅ : Set (HeightOneSpectrum (𝓞 ℚ))) ℚ).intCast_mem (x i))
  simpa [Rat.infinitePlace_apply, Rat.isReal_infinitePlace.mult_eq_one, Int.norm_eq_abs] using h

noncomputable def rationalPrimeIdeal (p : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.finitePlace p).maximalIdeal

theorem rationalPrimeIdeal_injective : Function.Injective rationalPrimeIdeal :=
  FinitePlace.maximalIdeal_injective.comp Rat.finitePlace_injective

@[simp] theorem mk_rationalPrimeIdeal (p : Nat.Primes) :
    FinitePlace.mk (rationalPrimeIdeal p) = Rat.finitePlace p :=
  FinitePlace.mk_maximalIdeal _

theorem absValue_liesOver_self (v : AbsoluteValue ℚ ℝ) : v.LiesOver v :=
  ⟨by ext x; rfl⟩

theorem rational_affineProduct_eq {ι : Type*} [Fintype ι]
    (S : Finset Nat.Primes)
    (L : AbsoluteValue ℚ ℝ → ι → Dual ℚ (ι → ℚ)) (x : ι → ℚ) :
    affineProd (S.image rationalPrimeIdeal) (fun v ↦ v) L x =
      (∏ i, |(L Rat.infinitePlace.1 i x : ℝ)|) *
        ∏ p ∈ S, ∏ i, ((padicNorm (p : ℕ) (L (Rat.AbsoluteValue.padic (p : ℕ)) i x) : ℚ) : ℝ) := by
  classical
  have hdefault : (default : InfinitePlace ℚ) = Rat.infinitePlace := rfl
  have harch (y : ℚ) : Rat.infinitePlace.1 y = |(y : ℝ)| := by
    simpa only [NumberField.InfinitePlace.coe_apply, Rat.cast_abs] using
      Rat.infinitePlace_apply Rat.infinitePlace y
  rw [affineProd, Finset.prod_image]
  · simp [hdefault, harch, Rat.finitePlace_val, Rat.AbsoluteValue.padic_eq_padicNorm]
  · exact fun _ _ _ _ h ↦ rationalPrimeIdeal_injective h

theorem rational_integer_subspace_cover {ι : Type*} [Fintype ι] [Nontrivial ι]
    (S : Finset Nat.Primes)
    (L : AbsoluteValue ℚ ℝ → ι → Dual ℚ (ι → ℚ))
    (hLInf : LinearIndependent ℚ (L Rat.infinitePlace.1))
    (hLFin : ∀ p ∈ S, LinearIndependent ℚ (L (Rat.AbsoluteValue.padic (p : ℕ))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (ι → ℚ)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : ι → ℤ, (fun i ↦ (x i : ℚ)) ≠ 0 →
        (∏ i, |(L Rat.infinitePlace.1 i (fun j ↦ (x j : ℚ)) : ℝ)|) *
          (∏ p ∈ S, ∏ i,
            ((padicNorm (p : ℕ)
              (L (Rat.AbsoluteValue.padic (p : ℕ)) i (fun j ↦ (x j : ℚ))) : ℚ) : ℝ)) ≤
            (⨆ i, |(x i : ℝ)|) ^ (-ε) →
        ∃ W ∈ T, (fun i ↦ (x i : ℚ)) ∈ W := by
  classical
  have hI : ∀ v : InfinitePlace ℚ, LinearIndependent ℚ (L v.1) := by
    intro v
    have hv : v = Rat.infinitePlace := Subsingleton.elim _ _
    simpa [hv] using hLInf
  have hF : ∀ v ∈ S.image rationalPrimeIdeal,
      LinearIndependent ℚ (L (FinitePlace.mk v).1) := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    simpa [Rat.finitePlace_val] using hLFin p hp
  obtain ⟨T, hT, hcov⟩ :=
    NumberField.exists_finset_submodule_of_integer_of_affineProd_le
      (S.image rationalPrimeIdeal) (fun v ↦ v)
      (fun v ↦ absValue_liesOver_self v.1)
      (fun v _ ↦ absValue_liesOver_self (FinitePlace.mk v).1) L hI hF hε
  refine ⟨T, hT, fun x hx hprod ↦ hcov (fun i ↦ (x i : ℚ)) hx ?_ ?_⟩
  · exact fun i ↦ (Set.integer (S.image rationalPrimeIdeal : Set (HeightOneSpectrum (𝓞 ℚ)))
      ℚ).intCast_mem (x i)
  · rw [rational_affineProduct_eq]
    exact hprod.trans (Real.rpow_le_rpow_of_nonpos (mulHeight_pos _)
      (intHeight_le_max x hx) (neg_nonpos.mpr hε.le))

end CollatzSubspaceBridge

#print axioms NumberField.exists_finset_submodule_of_approxProd_le
#print axioms NumberField.exists_finset_submodule_of_integer_of_affineProd_le
#print axioms Rat.finitePlace_apply
#print axioms CollatzSubspaceBridge.intHeight_le_max
#print axioms CollatzSubspaceBridge.rational_integer_subspace_cover
