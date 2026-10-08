/-
  MANGOSTAS: reloj de una racha compartida a altura fija.
  Algebra del paso entero y conteo general del automata de valuacion
  truncada. El enlace probabilistico con bits justos se explica en
  Mangostas.md; no incluye condicionamiento a supervivencia futura.
-/

namespace Mangostas

theorem hijos_altos (p u d : Int) :
    (2*p*u)/2 = p*u /\
    (3*(2*p*u)-2*p*d)/2 = p*(3*u-d) := by
  have h : 3*(2*p*u)-2*p*d = 2*(p*(3*u-d)) := by grind
  have h0 : 2*p*u = 2*(p*u) := by grind
  rw [h, h0]
  omega

theorem paridades_altas (u d : Int) (hd : d % 2 = 1) :
    (u % 2 = 0 /\ (3*u-d) % 2 = 1) \/
    (u % 2 = 1 /\ (3*u-d) % 2 = 0) := by omega

theorem factor_par (z : Int) (h : z % 2 = 0) :
    exists w, z = 2*w := by exact ⟨z/2, by omega⟩

theorem factor_impar (z : Int) (h : z % 2 = 1) :
    exists w, z = 2*w+1 := by exact ⟨z/2, by omega⟩

theorem hijos_bajos (p u d : Int) :
    (2*p*u)/2 = p*u /\
    (3*(2*p*u)-4*p*d)/2 = p*(3*u-2*d) := by
  have h : 3*(2*p*u)-4*p*d = 2*(p*(3*u-2*d)) := by grind
  have h0 : 2*p*u = 2*(p*u) := by grind
  rw [h, h0]
  omega

theorem paridades_bajas (u d : Int) (hu : u % 2 = 1) :
    u % 2 = 1 /\ (3*u-2*d) % 2 = 1 := by omega

-- Cuenta palabras de n bits cuyo estado aun es par DESPUES de n pasos.
-- r=0: impar (racha terminada); r=A: divisible por 2^A, incluido c=0.
def vivos (A r : Nat) : Nat -> Nat
  | 0 => if r = 0 then 0 else 1
  | n+1 => if r = 0 then 0 else
      if r < A then 2*vivos A (r-1) n
      else vivos A A n + vivos A (A-1) n

theorem conteo_bajo (A n r : Nat) (hr : r < A) :
    vivos A r n = if n < r then 2^n else 0 := by
  induction n generalizing r with
  | zero =>
    by_cases h : r = 0
    · simp [vivos, h]
    · have hp : 0 < r := by omega
      simp [vivos, h, hp]
  | succ n ih =>
    by_cases hz : r = 0
    · simp [vivos, hz]
    · rw [vivos, if_neg hz, if_pos hr, ih (r-1) (by omega)]
      by_cases hn : n+1 < r
      · have hnr : n < r-1 := by omega
        simp [hn, hnr, Nat.pow_succ, Nat.mul_comm]
      · have hnr : ¬ n < r-1 := by omega
        simp [hn, hnr]

theorem conteo_alto (A n : Nat) (ha : 0 < A) :
    vivos A A n = if n < A then 2^n else 2^(A-1) := by
  induction n with
  | zero => simp [vivos, Nat.ne_of_gt ha, ha]
  | succ n ih =>
    rw [vivos, if_neg (by omega : A ≠ 0), if_neg (by omega : ¬ A < A)]
    rw [ih, conteo_bajo A n (A-1) (by omega)]
    by_cases h : n+1 < A
    · have h1 : n < A := by omega
      have h2 : n < A-1 := by omega
      simp [h, h1, h2, Nat.pow_succ]
      omega
    · by_cases h1 : n < A
      · have he : n = A-1 := by omega
        have h2 : ¬ n < A-1 := by omega
        rw [if_pos h1, if_neg h2, if_neg h]
        simp [he]
      · have h2 : ¬ n < A-1 := by omega
        simp [h, h1, h2]

-- Adv: tras (2,1398101), bit 0 entra en (3,2^21).
-- Un bit compartido 1 YA produce c impar: no hay 21 pasos forzados.
theorem adversarial_entrada :
    (3*(1398101 : Int)+1)/2 = 2097152 := by decide

theorem adversarial_salida_rapida :
    ((3*(2097152 : Int)+1-3^3)/2) % 2 = 1 := by decide

theorem adversarial_cuenta : vivos 1 1 20 = 1 := by decide

#print axioms hijos_altos
#print axioms paridades_altas
#print axioms factor_par
#print axioms factor_impar
#print axioms hijos_bajos
#print axioms paridades_bajas
#print axioms conteo_bajo
#print axioms conteo_alto
#print axioms adversarial_entrada
#print axioms adversarial_salida_rapida
#print axioms adversarial_cuenta

end Mangostas
