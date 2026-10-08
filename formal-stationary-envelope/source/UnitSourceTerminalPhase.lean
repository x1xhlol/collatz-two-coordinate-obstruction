import Erdos1135.Tao.Fourier.Section7PairExpectation

/-!
# Terminal phases in the actual geometric source

The terminal character depends only on the total exponent. This module
factors it through the native adjacent-pair expansion without altering the
geometric source distribution or pair cancellation factors.
-/

set_option autoImplicit false

namespace Erdos1135.Tao

def UnitSourceTerminalPhase := {f : ℕ → ℂ // ∀ s, ‖f s‖ = 1}

/-- The original pair recursion, retaining a unit phase of the final total
exponent. The exact geometric and raw Pascal source laws are unchanged. -/
noncomputable def unitSourcePairExpansionFrom
    (N : ℕ) (xi : ZMod (3 ^ N)) (τ : UnitSourceTerminalPhase) :
    ℕ+ → ℕ → List ℕ+ → ℂ
  | _j, s, [] => τ.1 s
  | j, s, [a] =>
      taoForwardDFTKernel
        (taoSection7PairX N j (Int.ofNat (s + (a : ℕ)))) xi *
          τ.1 (s + (a : ℕ))
  | j, s, a₁ :: a₂ :: as =>
      taoSection7PairPhase N xi
          (taoSection7PairX N j
            (Int.ofNat (s + (a₁ : ℕ) + (a₂ : ℕ)))) a₂ *
        unitSourcePairExpansionFrom N xi τ
          ⟨(j : ℕ) + 1, by omega⟩
          (s + (a₁ : ℕ) + (a₂ : ℕ)) as

theorem unitSourcePairExpansionFrom_eq_original_mul_terminal
    (N : ℕ) (xi : ZMod (3 ^ N)) (τ : UnitSourceTerminalPhase) :
    ∀ (j : ℕ+) (s : ℕ) (as : List ℕ+),
      unitSourcePairExpansionFrom N xi τ j s as =
        taoSection7PairExpansionFrom N xi j s as *
          τ.1 (s + taoTupleWeight as) := by
  intro j s as
  induction as using List.twoStepInduction generalizing j s with
  | nil => simp [unitSourcePairExpansionFrom, taoSection7PairExpansionFrom,
      taoTupleWeight]
  | singleton a => simp [unitSourcePairExpansionFrom, taoSection7PairExpansionFrom,
      taoTupleWeight]
  | cons_cons a₁ a₂ as ih =>
      rw [unitSourcePairExpansionFrom, taoSection7PairExpansionFrom, ih]
      simp [taoTupleWeight, add_assoc, mul_assoc]

theorem norm_unitSourcePairExpansionFrom_eq_one
    (N : ℕ) (xi : ZMod (3 ^ N)) (τ : UnitSourceTerminalPhase)
    (j : ℕ+) (s : ℕ) (as : List ℕ+) :
    ‖unitSourcePairExpansionFrom N xi τ j s as‖ = 1 := by
  rw [unitSourcePairExpansionFrom_eq_original_mul_terminal, norm_mul,
    norm_taoSection7PairExpansionFrom_eq_one, τ.2]
  norm_num

end Erdos1135.Tao
