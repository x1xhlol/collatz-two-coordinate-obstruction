import NativeTaoProbabilityBridge
import Mathlib.Analysis.Normed.Lp.lpSpace

open scoped BigOperators

namespace CollatzCanonical.LabelLaw
open CollatzCylinderPacking.Arithmetic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def finiteMeanV {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (f : ι → V) : V := ∑ i, p i • f i

theorem finiteMeanV_norm_le {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (f : ι → V) (hp : ∀ i, 0 ≤ p i) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖finiteMeanV p f‖ ≤ ∑ i, p i := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp i)]
  exact mul_le_of_le_one_right (hp i) (hf i)

theorem finiteMeanV_sub {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (f g : ι → V) :
    finiteMeanV p f - finiteMeanV p g = finiteMeanV p (fun i => f i - g i) := by
  simp only [finiteMeanV, smul_sub, Finset.sum_sub_distrib]

theorem finiteMeanV_transport_exact {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (f g : ι → V) (bad : ι → Prop)
    (hp : ∀ i, 0 ≤ p i) (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1)
    (hgood : ∀ i, ¬bad i → f i = g i) :
    ‖finiteMeanV p f - finiteMeanV p g‖ ≤ 2 * finiteBadMass p bad := by
  classical
  have hpoint (i : ι) : ‖f i - g i‖ ≤ if bad i then 2 else 0 := by
    by_cases hi : bad i
    · rw [if_pos hi]
      exact (norm_sub_le _ _).trans (by linarith [hf i, hg i])
    · simp [hi, hgood i hi]
  rw [finiteMeanV_sub]
  calc
    ‖finiteMeanV p (fun i => f i - g i)‖ ≤ ∑ i, ‖p i • (f i - g i)‖ := norm_sum_le _ _
    _ = ∑ i, p i * ‖f i - g i‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hp _)]
    _ ≤ ∑ i, p i * (if bad i then 2 else 0) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hp i))
    _ = 2 * finiteBadMass p bad := by
      unfold finiteBadMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> ring

theorem finiteMeanV_pushforward {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (landing : ι → κ) (f : κ → V) :
    finiteMeanV (finitePushforward p landing) f = finiteMeanV p (fun i => f (landing i)) := by
  classical
  unfold finiteMeanV finitePushforward
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [ite_smul]

theorem finiteMeanV_sub_le_fullL1 {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (f : ι → V) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖finiteMeanV p f - finiteMeanV q f‖ ≤ ∑ i, |p i - q i| := by
  unfold finiteMeanV
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (hf i)

theorem finiteMeanV_two_passage_bound {ι κ η : Type*}
    [Fintype ι] [Fintype κ] [Fintype η]
    (p : ι → ℝ) (q : κ → ℝ) (f : ι → V) (g : κ → V)
    (landingP : ι → η) (landingQ : κ → η) (w : η → V)
    (badP : ι → Prop) (badQ : κ → Prop)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) (hw : ∀ z, ‖w z‖ ≤ 1)
    (hgoodP : ∀ i, ¬badP i → f i = w (landingP i))
    (hgoodQ : ∀ i, ¬badQ i → g i = w (landingQ i)) :
    ‖finiteMeanV p f - finiteMeanV q g‖ ≤
      2 * finiteBadMass p badP + 2 * finiteBadMass q badQ +
        ∑ z, |finitePushforward p landingP z - finitePushforward q landingQ z| := by
  have hP := finiteMeanV_transport_exact p f (fun i => w (landingP i)) badP hp hf
    (fun i => hw (landingP i)) hgoodP
  have hQ := finiteMeanV_transport_exact q g (fun i => w (landingQ i)) badQ hq hg
    (fun i => hw (landingQ i)) hgoodQ
  have hTV := finiteMeanV_sub_le_fullL1 (finitePushforward p landingP)
    (finitePushforward q landingQ) w hw
  rw [finiteMeanV_pushforward, finiteMeanV_pushforward] at hTV
  have htri₁ := dist_triangle (finiteMeanV p f)
    (finiteMeanV p (fun i => w (landingP i))) (finiteMeanV q g)
  have htri₂ := dist_triangle (finiteMeanV p (fun i => w (landingP i)))
    (finiteMeanV q (fun i => w (landingQ i))) (finiteMeanV q g)
  simp only [dist_eq_norm] at htri₁ htri₂
  rw [norm_sub_rev (finiteMeanV q (fun i => w (landingQ i))) (finiteMeanV q g)] at htri₂
  linarith

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.finiteMeanV_norm_le
#print axioms CollatzCanonical.LabelLaw.finiteMeanV_transport_exact
#print axioms CollatzCanonical.LabelLaw.finiteMeanV_pushforward
#print axioms CollatzCanonical.LabelLaw.finiteMeanV_sub_le_fullL1
#print axioms CollatzCanonical.LabelLaw.finiteMeanV_two_passage_bound
