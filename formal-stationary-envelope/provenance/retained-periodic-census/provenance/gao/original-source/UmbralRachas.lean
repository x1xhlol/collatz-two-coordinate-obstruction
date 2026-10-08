import RachasEnteras
import Mathlib.NumberTheory.Multiplicity

/- Umbral diádico de una racha: v2(3^k-1)<=2+floor(log2 k).
   La multiplicidad se aplica a un natural no nulo; c sigue siendo firmado. -/

noncomputable section

namespace UmbralRachasGao

open CadenaCompletaGao RachasEnterasGao

def orden (k : ℕ) : ℕ := padicValNat 2 (3^k-1)

theorem diferencia_positiva (k : ℕ) (hk : 1 ≤ k) : 1 ≤ 3^k-1 := by
  cases k with
  | zero => omega
  | succ k =>
    have hp : 0 < (3:ℕ)^k := pow_pos (by decide) k
    rw [pow_succ]
    omega

theorem orden_positivo (k : ℕ) (hk : 1 ≤ k) : 1 ≤ orden k := by
  have hn : 3^k-1 ≠ 0 := by have h := diferencia_positiva k hk; omega
  have hp : (3:ℕ)^k%2=1 := by norm_num [Nat.pow_mod]
  have hd : 2 ∣ 3^k-1 := Nat.dvd_of_mod_eq_zero (by omega)
  exact one_le_padicValNat_of_dvd hn hd

theorem orden_par (k : ℕ) (hk : 1 ≤ k) (he : Even k) :
    orden k = 2+padicValNat 2 k := by
  have h := padicValNat.pow_two_sub_one (x:=3) (n:=k)
    (by decide) (by decide) (by omega) he
  have h4 : padicValNat 2 4=2 := by
    change padicValNat 2 (2^2)=2
    exact padicValNat.prime_pow 2
  have h2 : padicValNat 2 2=1 := by
    change padicValNat 2 (2^1)=1
    exact padicValNat.prime_pow 1
  norm_num only at h
  rw [h4, h2] at h
  unfold orden
  omega

theorem orden_impar (k : ℕ) (hk : 1 ≤ k) (ho : Odd k) : orden k=1 := by
  have hn : 3^k-1 ≠ 0 := by have h := diferencia_positiva k hk; omega
  have hm : (3:ℕ)^k%4=3 := by
    obtain ⟨j,hj⟩ := ho.exists_bit1
    rw [hj, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have hN : (3^k-1)%4=2 := by omega
  have ha := orden_positivo k hk
  have hb : orden k < 2 := by
    by_contra hb
    have hdiv : 2^2 ∣ 3^k-1 := (padicValNat_dvd_iff_le hn).2 (show 2 ≤ orden k by omega)
    have hz := Nat.mod_eq_zero_of_dvd hdiv
    norm_num at hz
    omega
  omega

theorem orden_cota (k : ℕ) (hk : 1 ≤ k) : orden k ≤ 2+Nat.log 2 k := by
  rcases Nat.even_or_odd k with he | ho
  · rw [orden_par k hk he]
    have h := padicValNat_le_nat_log (p:=2) k
    omega
  · rw [orden_impar k hk ho]
    omega

theorem factor_impar (k : ℕ) (hk : 1 ≤ k) :
    ∃ d : ℤ, d%2=1 ∧ coef k-1=(2:ℤ)^(orden k)*d := by
  have hpos := diferencia_positiva k hk
  have hn : 3^k-1 ≠ 0 := by omega
  have hdiv : 2^(orden k) ∣ 3^k-1 := (padicValNat_dvd_iff_le hn).2 le_rfl
  obtain ⟨d,hd⟩ := hdiv
  have hnd : ¬2 ∣ d := by
    rintro ⟨e,he⟩
    apply pow_succ_padicValNat_not_dvd (p:=2) hn
    refine ⟨e,?_⟩
    change 3^k-1 = 2^(orden k+1)*e
    rw [hd, he, pow_succ]
    ring
  have hodd : d%2=1 := by
    have hm : d%2 ≠ 0 := by intro h; exact hnd (Nat.dvd_of_mod_eq_zero h)
    omega
  refine ⟨(d:ℤ),by exact_mod_cast hodd,?_⟩
  rw [coef_es_potencia]
  have he := congrArg (fun n : ℕ => (n:ℤ)) hd
  have hge : 1 ≤ 3^k := by omega
  simpa only [Nat.cast_sub hge, Nat.cast_pow, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] using he

theorem cola_con_orden (k s : ℕ) (c : ℤ) :
    racha_cadena (orden (k+2)+s) (.vivo (k+2) c) ≤ 1/(2:ℝ)^s := by
  obtain ⟨d,hd,hD⟩ := factor_impar (k+2) (by omega)
  exact cola_racha_original k (orden (k+2)) s c d (orden_positivo _ (by omega)) hd hD

theorem cola_umbral (k a s : ℕ) (c : ℤ) (ha : orden (k+2) ≤ a) :
    racha_cadena (a+s) (.vivo (k+2) c) ≤ 1/(2:ℝ)^s := by
  obtain ⟨d,hd,hD⟩ := factor_impar (k+2) (by omega)
  have he : orden (k+2)+(a-orden (k+2)+s)=a+s := by omega
  have hc := cuenta_uniforme (orden (k+2)) (a-orden (k+2)+s) d c
    (orden_positivo _ (by omega)) hd
  rw [he] at hc
  have hp : (2:ℕ)^(orden (k+2)) ≤ 2^a := Nat.pow_le_pow_right (by decide) ha
  have hR : (cuenta ((2:ℤ)^(orden (k+2))*d) (a+s) c:ℝ) ≤ (2:ℝ)^a := by
    exact_mod_cast hc.trans hp
  rw [racha_original, hD, probabilidad]
  calc
    _ ≤ (2:ℝ)^a/(2:ℝ)^(a+s) := div_le_div_of_nonneg_right hR (by positivity)
    _ = 1/(2:ℝ)^s := by rw [pow_add]; field_simp

#print axioms cola_umbral
#print axioms orden_positivo
#print axioms orden_par
#print axioms orden_impar
#print axioms orden_cota
#print axioms factor_impar
#print axioms cola_con_orden

end UmbralRachasGao
