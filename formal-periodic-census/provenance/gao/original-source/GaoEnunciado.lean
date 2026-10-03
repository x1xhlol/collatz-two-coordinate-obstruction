import Tejonas

/- Enunciado para revisión humana: la conjetura de Gao (1993), en el resumen
   de Lagarias, como límite de densidades naturales. Todo lo demás está en
   Tejonas.lean y sus dependencias. -/

open Filter Topology

namespace GaoEnunciado

/-- Mapa clásico de Collatz (A006370): n/2 si n es par, 3n+1 si es impar. -/
def f (n : ℕ) : ℕ := if n%2=0 then n/2 else 3*n+1

/-- m y m+1 se encuentran en a lo sumo log2 m pasos de f. -/
def encuentro (m : ℕ) : Prop := ∃ k, k≤Nat.log 2 m ∧ f^[k] m=f^[k] (m+1)

open Classical in
/-- Conjetura de Gao: el conjunto de los m con encuentro tiene densidad natural 1. -/
theorem conjetura_gao :
    Tendsto (fun N : ℕ => (((Finset.range N).filter encuentro).card:ℝ)/N) atTop (𝓝 1) := by
  have hf : f=TejonasGao.collatz := rfl
  have he : encuentro=TejonasGao.gao_encuentro := by
    funext m; simp only [encuentro,TejonasGao.gao_encuentro,hf]
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0,hN0⟩ := TejonasGao.gao (ε/2) (by linarith)
  refine ⟨max N0 1,fun N hN => ?_⟩
  have hN1 : 1≤N := le_trans (le_max_right _ _) hN
  have hNpos : (0:ℝ)<N := by exact_mod_cast hN1
  have hlow := hN0 N (le_trans (le_max_left _ _) hN)
  rw [← he] at hlow
  have hup : (((Finset.range N).filter encuentro).card:ℝ)≤N := by
    have : ((Finset.range N).filter encuentro).card≤N := by
      calc _ ≤ (Finset.range N).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = N := Finset.card_range N
    exact_mod_cast this
  rw [Real.dist_eq,abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt,lt_div_iff₀ hNpos]; nlinarith
  · rw [sub_lt_iff_lt_add,div_lt_iff₀ hNpos]; nlinarith

end GaoEnunciado

#print axioms GaoEnunciado.conjetura_gao
