import InverseBranchCylinder
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

open MeasureTheory Preorder

namespace CollatzCylinderPacking.Arithmetic.InverseDoob

def IsActualInversePath (n : ℕ) (x : ℕ → ℕ) : Prop :=
  x 0 = n ∧ ∀ k, ∃ a : ℕ,
    (2 ^ a * x k) % 3 = 2 ∧ x (k + 1) = inverseEndpoint (x k) a

theorem IsActualInversePath.hit_clock {n : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) (k : ℕ) :
    ∃ A : ℕ, iterate A (x k) = n ∧ oddCount A (x k) = k := by
  induction k with
  | zero => exact ⟨0, hx.1, rfl⟩
  | succ k ih =>
    obtain ⟨A, hhit, hcount⟩ := ih
    obtain ⟨a, hguard, hnext⟩ := hx.2 k
    have hb := inverseEndpoint_block hguard
    rw [← hnext] at hb
    refine ⟨a + 1 + A, ?_, ?_⟩
    · rw [iterate_add, hb.2.1, hhit]
    · rw [oddCount_add, hb.2.1, hb.2.2, hcount]
      omega

theorem IsActualInversePath.firstHitOddDepth_eq {n : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) (hn : Nonperiodic n) (k : ℕ) :
    firstHitOddDepth n (x k) = k := by
  obtain ⟨A, hhit, hcount⟩ := hx.hit_clock k
  rw [firstHitOddDepth_of_first_hit (firstHit_of_nonperiodic hn hhit), hcount]

theorem IsActualInversePath.injective {n : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) (hn : Nonperiodic n) :
    Function.Injective x := by
  intro i j hij
  have h := congrArg (firstHitOddDepth n) hij
  simpa only [hx.firstHitOddDepth_eq hn] using h

theorem IsActualInversePath.odd {n : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) (hn : n % 2 = 1) (k : ℕ) :
    x k % 2 = 1 := by
  cases k with
  | zero => simpa only [hx.1] using hn
  | succ k =>
    obtain ⟨a, hguard, hnext⟩ := hx.2 k
    rw [hnext]
    exact (inverseEndpoint_block hguard).1

noncomputable def boundedHitEndpoints (n R : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (R + 1)).filter
    (fun y => y % 2 = 1 ∧ ∃ A : ℕ, iterate A y = n)

noncomputable def lastVisitDepthBound (n R : ℕ) : ℕ :=
  (boundedHitEndpoints n R).sup (firstHitOddDepth n)

theorem IsActualInversePath.visit_depth_le {n R k : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) (hn : Nonperiodic n) (ho : n % 2 = 1)
    (hk : x k ≤ R) : k ≤ lastVisitDepthBound n R := by
  classical
  have hmem : x k ∈ boundedHitEndpoints n R := by
    obtain ⟨A, hhit, _⟩ := hx.hit_clock k
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hx.odd ho k, A, hhit⟩
  have h := Finset.le_sup (f := firstHitOddDepth n) hmem
  simpa only [hx.firstHitOddDepth_eq hn] using h

theorem IsActualInversePath.no_visit_after_bound {n R k : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) (hn : Nonperiodic n) (ho : n % 2 = 1)
    (hk : lastVisitDepthBound n R < k) : R < x k := by
  by_contra h
  have hb := hx.visit_depth_le hn ho (Nat.le_of_not_gt h)
  omega

theorem IsActualInversePath.finite_visits {n R : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) (hn : Nonperiodic n) (ho : n % 2 = 1) :
    Set.Finite {k : ℕ | x k ≤ R} := by
  apply (Finset.finite_toSet (Finset.range (lastVisitDepthBound n R + 1))).subset
  intro k hk
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hx.visit_depth_le hn ho hk))

noncomputable def finiteLastVisit (R K : ℕ) (x : ℕ → ℕ) : ℕ :=
  ((Finset.range (K + 1)).filter (fun k => x k ≤ R)).sup id

noncomputable def lastVisitIndex (n R : ℕ) (x : ℕ → ℕ) : ℕ :=
  finiteLastVisit R (lastVisitDepthBound n R) x

theorem finiteLastVisit_le (R K : ℕ) (x : ℕ → ℕ) :
    finiteLastVisit R K x ≤ K := by
  unfold finiteLastVisit
  apply Finset.sup_le
  intro k hk
  have h := (Finset.mem_filter.mp hk).1
  simpa only [id_eq] using Nat.le_of_lt_succ (Finset.mem_range.mp h)

theorem le_finiteLastVisit {R K k : ℕ} {x : ℕ → ℕ}
    (hk : k ≤ K) (hvisit : x k ≤ R) : k ≤ finiteLastVisit R K x := by
  exact Finset.le_sup (f := id)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hvisit⟩)

theorem finiteLastVisit_mem {R K : ℕ} {x : ℕ → ℕ} (hzero : x 0 ≤ R) :
    x (finiteLastVisit R K x) ≤ R := by
  have hmem : 0 ∈ (Finset.range (K + 1)).filter (fun k => x k ≤ R) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hzero⟩
  have h := Finset.sup_mem_of_nonempty (f := id) ⟨0, hmem⟩
  obtain ⟨k, hk, he⟩ := h
  change k = finiteLastVisit R K x at he
  rw [← he]
  exact (Finset.mem_filter.mp hk).2

theorem IsActualInversePath.lastVisit_spec {n R : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) (hn : Nonperiodic n) (ho : n % 2 = 1)
    (hR : n ≤ R) :
    x (lastVisitIndex n R x) ≤ R ∧
      ∀ k, lastVisitIndex n R x < k → R < x k := by
  refine ⟨finiteLastVisit_mem (by simpa only [hx.1] using hR), ?_⟩
  intro k hk
  by_contra h
  have hvisit : x k ≤ R := Nat.le_of_not_gt h
  have hle := le_finiteLastVisit (hx.visit_depth_le hn ho hvisit) hvisit
  change k ≤ lastVisitIndex n R x at hle
  omega

theorem lastVisitIndex_le_bound (n R : ℕ) (x : ℕ → ℕ) :
    lastVisitIndex n R x ≤ lastVisitDepthBound n R :=
  finiteLastVisit_le R (lastVisitDepthBound n R) x

theorem IsActualInversePath.le_lastVisit_of_visit {n R k : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) (hn : Nonperiodic n) (ho : n % 2 = 1)
    (hk : x k ≤ R) : k ≤ lastVisitIndex n R x :=
  le_finiteLastVisit (hx.visit_depth_le hn ho hk) hk

theorem IsActualInversePath.lastVisit_mono {n R S : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) (hn : Nonperiodic n) (ho : n % 2 = 1)
    (hR : n ≤ R) (hRS : R ≤ S) : lastVisitIndex n R x ≤ lastVisitIndex n S x := by
  exact hx.le_lastVisit_of_visit hn ho ((hx.lastVisit_spec hn ho hR).1.trans hRS)

theorem IsActualInversePath.le_lastVisit_iff {n R k : ℕ} {x : ℕ → ℕ}
    (hx : IsActualInversePath n x) (hn : Nonperiodic n) (ho : n % 2 = 1)
    (hR : n ≤ R) :
    k ≤ lastVisitIndex n R x ↔ ∃ j, k ≤ j ∧ x j ≤ R := by
  constructor
  · intro hk
    exact ⟨lastVisitIndex n R x, hk, (hx.lastVisit_spec hn ho hR).1⟩
  · rintro ⟨j, hkj, hj⟩
    exact hkj.trans (hx.le_lastVisit_of_visit hn ho hj)

theorem finiteLastVisit_congr {R K : ℕ} {x y : ℕ → ℕ}
    (hxy : ∀ k ≤ K, x k = y k) : finiteLastVisit R K x = finiteLastVisit R K y := by
  unfold finiteLastVisit
  congr 1
  apply Finset.filter_congr
  intro k hk
  rw [hxy k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]

theorem lastVisitIndex_prefix_congr {n R : ℕ} {x y : ℕ → ℕ}
    (hxy : ∀ k ≤ lastVisitDepthBound n R, x k = y k) :
    lastVisitIndex n R x = lastVisitIndex n R y :=
  finiteLastVisit_congr hxy

noncomputable def lastVisitPrefixFunction (n R : ℕ)
    (v : Finset.Iic (lastVisitDepthBound n R) → ℕ) : ℕ :=
  finiteLastVisit R (lastVisitDepthBound n R) (fun k =>
    if h : k ≤ lastVisitDepthBound n R then v ⟨k, Finset.mem_Iic.mpr h⟩ else 0)

theorem lastVisitIndex_eq_prefixFunction (n R : ℕ) (x : ℕ → ℕ) :
    lastVisitIndex n R x =
      lastVisitPrefixFunction n R (frestrictLe (lastVisitDepthBound n R) x) := by
  unfold lastVisitIndex lastVisitPrefixFunction
  apply finiteLastVisit_congr
  intro k hk
  simp only [dif_pos hk, frestrictLe_apply]

theorem measurable_lastVisitIndex (n R : ℕ) : Measurable (lastVisitIndex n R) := by
  have he : lastVisitIndex n R =
      lastVisitPrefixFunction n R ∘ frestrictLe (lastVisitDepthBound n R) := by
    funext x
    exact lastVisitIndex_eq_prefixFunction n R x
  rw [he]
  exact (measurable_of_countable (lastVisitPrefixFunction n R)).comp
    (measurable_frestrictLe (X := fun _ : ℕ => ℕ) (lastVisitDepthBound n R))

theorem lastVisitIndex_event_preimage (n R : ℕ) (E : Set ℕ) :
    {x : ℕ → ℕ | lastVisitIndex n R x ∈ E} =
      (frestrictLe (lastVisitDepthBound n R)) ⁻¹'
        {v | lastVisitPrefixFunction n R v ∈ E} := by
  ext x
  exact iff_of_eq (congrArg (fun k => k ∈ E) (lastVisitIndex_eq_prefixFunction n R x))

theorem measurableSet_lastVisitIndex_event (n R : ℕ) (E : Set ℕ) :
    MeasurableSet {x : ℕ → ℕ | lastVisitIndex n R x ∈ E} :=
  (Set.to_countable E).measurableSet.preimage (measurable_lastVisitIndex n R)

#print axioms IsActualInversePath.hit_clock
#print axioms IsActualInversePath.firstHitOddDepth_eq
#print axioms IsActualInversePath.injective
#print axioms IsActualInversePath.visit_depth_le
#print axioms IsActualInversePath.no_visit_after_bound
#print axioms IsActualInversePath.finite_visits
#print axioms IsActualInversePath.lastVisit_spec
#print axioms IsActualInversePath.lastVisit_mono
#print axioms IsActualInversePath.le_lastVisit_iff
#print axioms lastVisitIndex_prefix_congr
#print axioms lastVisitIndex_eq_prefixFunction
#print axioms measurable_lastVisitIndex
#print axioms lastVisitIndex_event_preimage
#print axioms measurableSet_lastVisitIndex_event

end CollatzCylinderPacking.Arithmetic.InverseDoob
