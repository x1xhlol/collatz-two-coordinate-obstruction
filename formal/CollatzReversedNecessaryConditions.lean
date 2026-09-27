import CollatzReversedNaturalCertificate

namespace CollatzResearch

theorem even_strict_rank_power_two_lower_bound (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m < rank (2 * m)) (k : ℕ) :
    rank 1 + k ≤ rank (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := heven (2 ^ k) (by positivity)
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
    rw [hp]
    omega

theorem even_strict_rank_unbounded_on_odds (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m < rank (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) ≤ rank (2 * m + 1))
    (K : ℕ) : ∃ m : ℕ, 0 < m ∧ K < rank (2 * m + 1) := by
  let p := 2 ^ (2 * K + 3)
  have hpmod : p % 3 = 2 := by
    dsimp [p]
    rw [pow_add, pow_mul]
    simp [Nat.mul_mod, Nat.pow_mod]
  have hpmin : 8 ≤ p := by
    dsimp [p]
    have hx : 0 < 2 ^ (2 * K) := by positivity
    rw [pow_add]
    norm_num
    omega
  let m := (p - 2) / 3
  have hm : 0 < m := by dsimp [m]; omega
  have hform : 3 * m + 2 = p := by dsimp [m]; omega
  have hlower := even_strict_rank_power_two_lower_bound rank heven (2 * K + 3)
  have hupper := hodd m hm
  rw [hform] at hupper
  exact ⟨m, hm, by dsimp [p] at hupper; omega⟩

namespace ReversedCertificate

variable {α : Type*} [Preorder α]

theorem strict_da_readout_b_unbounded (c : Data α)
    (hda : ∀ x, c.readout x < c.readout (c.a x))
    (hdb : ∀ x, c.readout (c.g x) ≤ c.readout (c.b x))
    (K : ℕ) : ∃ x : α, K < c.readout (c.b x) := by
  let rank : ℕ → ℕ := fun n => c.readout (binaryInterp c.a c.b n c.initial)
  have heven : ∀ m : ℕ, 0 < m → rank m < rank (2 * m) := by
    intro m hm
    dsimp [rank]
    rw [binaryInterp_even c.a c.b hm]
    exact hda _
  have hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) ≤ rank (2 * m + 1) := by
    intro m hm
    dsimp [rank]
    rw [binaryInterp_odd c.a c.b hm]
    exact le_trans (c.readout_monotone (ternary_conversion_weak c m hm).2.2) (hdb _)
  obtain ⟨m, hm, hlarge⟩ := even_strict_rank_unbounded_on_odds rank heven hodd K
  refine ⟨binaryInterp c.a c.b m c.initial, ?_⟩
  simpa only [rank, binaryInterp_odd c.a c.b hm] using hlarge

theorem constant_b_excludes_first_removal (c : Data α) (K : ℕ)
    (hconstant : ∀ x, c.readout (c.b x) = K)
    (hdb : ∀ x, c.readout (c.g x) ≤ c.readout (c.b x)) :
    ¬ ((∀ x, c.readout x < c.readout (c.a x)) ∨
      (∀ x, c.readout (c.g x) < c.readout (c.b x))) := by
  intro hs
  rcases hs with hda | hdbs
  · obtain ⟨x, hx⟩ := strict_da_readout_b_unbounded c hda hdb K
    rw [hconstant x] at hx
    omega
  · have hinner := c.readout_monotone c.gc
    have houter := hdbs c.initial
    rw [hconstant (c.a c.initial)] at hinner
    rw [hconstant c.initial] at houter
    omega

theorem contextual_gap_bound (c : Data α) (δa δb : ℕ)
    (hda : ∀ x, c.readout x + δa ≤ c.readout (c.a x))
    (hdb : ∀ x, c.readout (c.g x) + δb ≤ c.readout (c.b x)) :
    c.readout (c.b (c.a c.initial)) + δa + δb ≤
      c.readout (c.a (c.b c.initial)) := by
  have hinner := c.readout_monotone c.gc
  have hfirst := hdb c.initial
  have hlast := hda (c.b c.initial)
  omega

end ReversedCertificate

namespace ReversedNaturalConditions

open Matrix

structure Model (ι : Type*) where
  a : NatAffine ι
  b : NatAffine ι
  c : NatAffine ι
  d : NatAffine ι
  e : NatAffine ι
  f : NatAffine ι
  g : NatAffine ι

variable {ι : Type*} [Fintype ι]

def WeakRules (m : Model ι) : Prop :=
  (m.d.comp m.a).Weak m.d ∧
  (m.d.comp m.b).Weak (m.d.comp m.g) ∧
  (m.e.comp m.a).Weak (m.a.comp m.e) ∧
  (m.f.comp m.a).Weak (m.b.comp m.e) ∧
  (m.g.comp m.a).Weak (m.a.comp m.f) ∧
  (m.e.comp m.b).Weak (m.b.comp m.f) ∧
  (m.f.comp m.b).Weak (m.a.comp m.g) ∧
  (m.g.comp m.b).Weak (m.b.comp m.g) ∧
  (m.e.comp m.c).Weak (m.b.comp m.c) ∧
  (m.f.comp m.c).Weak (m.a.comp (m.a.comp m.c)) ∧
  (m.g.comp m.c).Weak (m.b.comp (m.a.comp m.c))

def StrictOffset (m : Model ι) (i₀ : ι) : Prop :=
  m.d.offset i₀ < (m.d.comp m.a).offset i₀ ∨
    (m.d.comp m.g).offset i₀ < (m.d.comp m.b).offset i₀

def gapA (m : Model ι) (i₀ : ι) : ℕ :=
  (m.d.comp m.a).offset i₀ - m.d.offset i₀

def gapB (m : Model ι) (i₀ : ι) : ℕ :=
  (m.d.comp m.b).offset i₀ - (m.d.comp m.g).offset i₀

def ofModel (m : Model ι) (h : WeakRules m) (i₀ : ι) :
    ReversedCertificate.Data (ι → ℕ) where
  a := m.a.eval
  b := m.b.eval
  e := m.e.eval
  f := m.f.eval
  g := m.g.eval
  readout x := m.d.eval x i₀
  initial := m.c.offset
  a_monotone := m.a.eval_monotone
  b_monotone := m.b.eval_monotone
  readout_monotone := fun _ _ hx => m.d.eval_monotone hx i₀
  ea := fun x => by simpa only [NatAffine.eval_comp] using NatAffine.eval_weak h.2.2.1 x
  fa := fun x => by simpa only [NatAffine.eval_comp] using NatAffine.eval_weak h.2.2.2.1 x
  ga := fun x => by simpa only [NatAffine.eval_comp] using NatAffine.eval_weak h.2.2.2.2.1 x
  eb := fun x => by simpa only [NatAffine.eval_comp] using NatAffine.eval_weak h.2.2.2.2.2.1 x
  fb := fun x => by simpa only [NatAffine.eval_comp] using NatAffine.eval_weak h.2.2.2.2.2.2.1 x
  gb := fun x => by simpa only [NatAffine.eval_comp] using NatAffine.eval_weak h.2.2.2.2.2.2.2.1 x
  ec := h.2.2.2.2.2.2.2.2.1.2
  fc := h.2.2.2.2.2.2.2.2.2.1.2
  gc := h.2.2.2.2.2.2.2.2.2.2.2

theorem db_row_nonzero (m : Model ι) (i₀ : ι) (h : WeakRules m)
    (hs : StrictOffset m i₀) : ∃ j, 0 < (m.d.comp m.b).matrix i₀ j := by
  classical
  by_contra hn
  have hz : ∀ j, (m.d.comp m.b).matrix i₀ j = 0 := by
    intro j
    by_contra hne
    exact hn ⟨j, Nat.pos_of_ne_zero hne⟩
  let c := ofModel m h i₀
  have hc : ∀ x, c.readout (c.b x) = (m.d.comp m.b).offset i₀ := by
    intro x
    change m.d.eval (m.b.eval x) i₀ = (m.d.comp m.b).offset i₀
    rw [← NatAffine.eval_comp]
    change (∑ j, (m.d.comp m.b).matrix i₀ j * x j) +
      (m.d.comp m.b).offset i₀ = (m.d.comp m.b).offset i₀
    simp [hz]
  apply ReversedCertificate.constant_b_excludes_first_removal c
    ((m.d.comp m.b).offset i₀) hc
  · intro x
    simpa only [NatAffine.eval_comp] using NatAffine.eval_weak h.2.1 x i₀
  · rcases hs with ha | hb
    · left
      intro x
      simpa only [NatAffine.eval_comp] using NatAffine.eval_strict_at h.1 i₀ ha x
    · right
      intro x
      simpa only [NatAffine.eval_comp] using NatAffine.eval_strict_at h.2.1 i₀ hb x

theorem offset_gap_le {F G : NatAffine ι} (i₀ : ι) (h : F.Weak G) (x : ι → ℕ) :
    G.eval x i₀ + (F.offset i₀ - G.offset i₀) ≤ F.eval x i₀ := by
  have hm : (G.matrix *ᵥ x) i₀ ≤ (F.matrix *ᵥ x) i₀ :=
    Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right (x j) (h.1 i₀ j))
  have ho : G.offset i₀ ≤ F.offset i₀ := h.2 i₀
  change (G.matrix *ᵥ x) i₀ + G.offset i₀ + (F.offset i₀ - G.offset i₀) ≤
    (F.matrix *ᵥ x) i₀ + F.offset i₀
  omega

theorem observed_context_gap_bound (m : Model ι) (i₀ : ι) (h : WeakRules m) :
    m.d.matrix i₀ ⬝ᵥ m.b.eval (m.a.eval m.c.offset) + gapA m i₀ + gapB m i₀ ≤
      m.d.matrix i₀ ⬝ᵥ m.a.eval (m.b.eval m.c.offset) := by
  have ha : ∀ x, (ofModel m h i₀).readout x + gapA m i₀ ≤
      (ofModel m h i₀).readout ((ofModel m h i₀).a x) := by
    intro x
    simpa only [gapA, NatAffine.eval_comp] using offset_gap_le i₀ h.1 x
  have hb : ∀ x, (ofModel m h i₀).readout ((ofModel m h i₀).g x) + gapB m i₀ ≤
      (ofModel m h i₀).readout ((ofModel m h i₀).b x) := by
    intro x
    simpa only [gapB, NatAffine.eval_comp] using offset_gap_le i₀ h.2.1 x
  have bound := ReversedCertificate.contextual_gap_bound (ofModel m h i₀)
    (gapA m i₀) (gapB m i₀) ha hb
  change m.d.matrix i₀ ⬝ᵥ m.b.eval (m.a.eval m.c.offset) + m.d.offset i₀ +
    gapA m i₀ + gapB m i₀ ≤
    m.d.matrix i₀ ⬝ᵥ m.a.eval (m.b.eval m.c.offset) + m.d.offset i₀ at bound
  omega

theorem strict_observed_context (m : Model ι) (i₀ : ι) (h : WeakRules m)
    (hs : StrictOffset m i₀) :
    m.d.matrix i₀ ⬝ᵥ m.b.eval (m.a.eval m.c.offset) <
      m.d.matrix i₀ ⬝ᵥ m.a.eval (m.b.eval m.c.offset) := by
  have bound := observed_context_gap_bound m i₀ h
  have hpos : 0 < gapA m i₀ + gapB m i₀ := by
    rcases hs with ha | hb <;> dsimp [gapA, gapB] <;> omega
  omega

end ReversedNaturalConditions

#print axioms even_strict_rank_power_two_lower_bound
#print axioms even_strict_rank_unbounded_on_odds
#print axioms ReversedCertificate.strict_da_readout_b_unbounded
#print axioms ReversedCertificate.constant_b_excludes_first_removal
#print axioms ReversedCertificate.contextual_gap_bound
#print axioms ReversedNaturalConditions.ofModel
#print axioms ReversedNaturalConditions.db_row_nonzero
#print axioms ReversedNaturalConditions.offset_gap_le
#print axioms ReversedNaturalConditions.observed_context_gap_bound
#print axioms ReversedNaturalConditions.strict_observed_context

end CollatzResearch
