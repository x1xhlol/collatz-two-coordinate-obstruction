import ActualPathSupport
import LastVisitGeometry

set_option autoImplicit false

open MeasureTheory Filter

namespace CollatzCylinderPacking.Arithmetic.InverseDoob

theorem pathLaw_isActualInversePath_ae {n : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0) :
    ∀ᵐ x ∂pathLaw n, IsActualInversePath n x := by
  filter_upwards [pathLaw_actual_steps_ae hn hu] with x hx
  exact ⟨hx.1, hx.2.2⟩

theorem pathLaw_injective_ae {n : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (hnp : Nonperiodic n) : ∀ᵐ x ∂pathLaw n, Function.Injective x := by
  filter_upwards [pathLaw_isActualInversePath_ae hn hu] with x hx
  exact hx.injective hnp

theorem pathLaw_lastVisit_spec_ae {n R : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (hnodd : n % 2 = 1) (hnp : Nonperiodic n) (hR : n ≤ R) :
    ∀ᵐ x ∂pathLaw n, x (lastVisitIndex n R x) ≤ R ∧
      ∀ k, lastVisitIndex n R x < k → R < x k := by
  filter_upwards [pathLaw_isActualInversePath_ae hn hu] with x hx
  exact hx.lastVisit_spec hnp hnodd hR

theorem pathLaw_finite_visits_ae {n : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (hnodd : n % 2 = 1) (hnp : Nonperiodic n) :
    ∀ᵐ x ∂pathLaw n, ∀ R, Set.Finite {k : ℕ | x k ≤ R} := by
  filter_upwards [pathLaw_isActualInversePath_ae hn hu] with x hx
  exact fun R => hx.finite_visits hnp hnodd

end CollatzCylinderPacking.Arithmetic.InverseDoob
