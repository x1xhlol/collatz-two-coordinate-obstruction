import Hienas
import GaoEnunciado

/- Enunciado para revisión humana: la conjetura de Gao (1993) tal como él la escribe
   (págs. 264–265), no sólo en el resumen de Lagarias. Las definiciones (`C`, `mitades`,
   `coalescen`, `dbarra`, `d`) están en Hienas.lean, que sólo importa Mathlib. -/

namespace GaoLiteral

/-- La forma de Lagarias, escrita en Hienas sin nada del proyecto, es la que demuestra
    `GaoEnunciado.conjetura_gao`. -/
theorem lagarias : Hienas.FormaLagarias := by
  unfold Hienas.FormaLagarias
  exact GaoEnunciado.conjetura_gao

/-- Conjetura de Gao (1993): `d̄_k → 1`. Además `d(x) → 1`, el límite que Gao no sabía
    si existía. -/
theorem conjetura_gao_literal : Hienas.FormaGao ∧ Hienas.FormaGaoD :=
  ⟨Hienas.gao_de_lagarias lagarias, Hienas.d_de_lagarias lagarias⟩

end GaoLiteral

#print axioms GaoLiteral.lagarias
#print axioms GaoLiteral.conjetura_gao_literal

/- Cotejo con la tabla 3 de Gao (pág. 266), con las mismas definiciones de Hienas:
   `2^k · d̄_k` para k = 4..12. Gao da 0.063, 0.125, 0.172, 0.227, 0.254, 0.283, 0.298,
   0.313 y 0.322, que son 1/16, 4/32, 11/64, 29/128, 65/256, 145/512, 305/1024,
   641/2048 y 1317/4096 redondeados. Si la cuenta no coincide, el archivo no compila. -/
#guard (List.range 9).map (fun i => ((List.range (2 ^ (i + 4) - 1)).filter
    (fun n => decide (∃ j, j ≤ i + 4 ∧ Hienas.coalescen n j))).length) =
  [1, 4, 11, 29, 65, 145, 305, 641, 1317]
