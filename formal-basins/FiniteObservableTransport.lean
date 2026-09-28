import FirstPassageWeightStability

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

noncomputable def finiteMean {ι : Type*} [Fintype ι] (p f : ι → ℝ) : ℝ :=
  ∑ i, p i * f i

noncomputable def finiteBadMass {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (bad : ι → Prop) : ℝ := by
  classical
  exact ∑ i, if bad i then p i else 0

noncomputable def finitePushforward {ι κ : Type*} [Fintype ι] (p : ι → ℝ)
    (landing : ι → κ) (z : κ) : ℝ := by
  classical
  exact ∑ i, if landing i = z then p i else 0

/-- A bounded observable can lose at most the probability of an exceptional
set, in addition to its uniform error on the complement. -/
theorem finiteMean_transport {ι : Type*} [Fintype ι] (p f g : ι → ℝ)
    (bad : ι → Prop) (ε : ℝ) (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i = 1)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (hg : ∀ i, 0 ≤ g i ∧ g i ≤ 1)
    (hε : 0 ≤ ε) (hgood : ∀ i, ¬bad i → |f i - g i| ≤ ε) :
    |finiteMean p f - finiteMean p g| ≤ ε + finiteBadMass p bad := by
  classical
  have hpoint (i : ι) : |f i - g i| ≤ ε + if bad i then 1 else 0 := by
    by_cases hi : bad i
    · simp only [if_pos hi]
      have ha : |f i - g i| ≤ 1 := abs_le.mpr ⟨by linarith [(hf i).1, (hg i).2],
        by linarith [(hf i).2, (hg i).1]⟩
      linarith
    · simpa only [if_neg hi, add_zero] using hgood i hi
  calc
    |finiteMean p f - finiteMean p g| = |∑ i, p i * (f i - g i)| := by
      unfold finiteMean
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, |p i * (f i - g i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, p i * |f i - g i| := by simp_rw [abs_mul, abs_of_nonneg (hp _)]
    _ ≤ ∑ i, p i * (ε + if bad i then 1 else 0) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hp i)
    _ = ε + finiteBadMass p bad := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hmass, one_mul]
      unfold finiteBadMass
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp

theorem finiteMean_pushforward {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (landing : ι → κ) (w : κ → ℝ) :
    finiteMean (finitePushforward p landing) w = finiteMean p (fun i => w (landing i)) := by
  classical
  unfold finiteMean finitePushforward
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_mul]

/-- Full L1 distance controls the expectation of every observable in [0,1]. -/
theorem finiteMean_sub_le_fullL1 {κ : Type*} [Fintype κ] (p q w : κ → ℝ)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) :
    |finiteMean p w - finiteMean q w| ≤ ∑ z, |p z - q z| := by
  unfold finiteMean
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ z, (p z * w z - q z * w z)| ≤ ∑ z, |p z * w z - q z * w z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z, |p z - q z| := by
      apply Finset.sum_le_sum
      intro z _
      rw [← sub_mul, abs_mul, abs_of_nonneg (hw z).1]
      exact mul_le_of_le_one_right (abs_nonneg _) (hw z).2

/-- Two first-passage couplings reduce a comparison of source expectations to
exceptional-set probabilities and the full L1 distance of the landing laws. -/
theorem finiteMean_two_passage_bound {ι κ η : Type*}
    [Fintype ι] [Fintype κ] [Fintype η]
    (p : ι → ℝ) (q : κ → ℝ) (f : ι → ℝ) (g : κ → ℝ)
    (landingP : ι → η) (landingQ : κ → η) (w : η → ℝ)
    (badP : ι → Prop) (badQ : κ → Prop) (εP εQ : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hmassP : ∑ i, p i = 1) (hmassQ : ∑ i, q i = 1)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) (hg : ∀ i, 0 ≤ g i ∧ g i ≤ 1)
    (hw : ∀ z, 0 ≤ w z ∧ w z ≤ 1) (hεP : 0 ≤ εP) (hεQ : 0 ≤ εQ)
    (hgoodP : ∀ i, ¬badP i → |f i - w (landingP i)| ≤ εP)
    (hgoodQ : ∀ i, ¬badQ i → |g i - w (landingQ i)| ≤ εQ) :
    |finiteMean p f - finiteMean q g| ≤
      εP + εQ + finiteBadMass p badP + finiteBadMass q badQ +
        ∑ z, |finitePushforward p landingP z - finitePushforward q landingQ z| := by
  have hP := finiteMean_transport p f (fun i => w (landingP i)) badP εP hp hmassP
    hf (fun i => hw (landingP i)) hεP hgoodP
  have hQ := finiteMean_transport q g (fun i => w (landingQ i)) badQ εQ hq hmassQ
    hg (fun i => hw (landingQ i)) hεQ hgoodQ
  have hTV := finiteMean_sub_le_fullL1 (finitePushforward p landingP)
    (finitePushforward q landingQ) w hw
  rw [finiteMean_pushforward, finiteMean_pushforward] at hTV
  have htri₁ := abs_sub_le (finiteMean p f)
    (finiteMean p (fun i => w (landingP i))) (finiteMean q g)
  have htri₂ := abs_sub_le (finiteMean p (fun i => w (landingP i)))
    (finiteMean q (fun i => w (landingQ i))) (finiteMean q g)
  rw [abs_sub_comm (finiteMean q (fun i => w (landingQ i))) (finiteMean q g)] at htri₂
  linarith

#print axioms finiteMean_transport
#print axioms finiteMean_pushforward
#print axioms finiteMean_two_passage_bound

end CollatzCylinderPacking.Arithmetic
