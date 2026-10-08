import Banda
import rachas

/- Conteo de palabras que realizan n pasos compartidos consecutivos.
   Es P(L>=n), no P(L>n): la paridad se comprueba antes de cada paso. -/

noncomputable section

namespace RachasEnterasGao

open CadenaCompletaGao MomentosGao

def cuenta (D : ℤ) : ℕ → ℤ → ℕ
  | 0, _ => 1
  | n+1, c => if c%2=0 then cuenta D n (c/2)+cuenta D n ((3*c-D)/2) else 0

theorem cuenta_baja (r n : ℕ) (d u : ℤ) (hu : u%2=1) :
    cuenta ((2:ℤ)^(r+1)*d) n ((2:ℤ)^r*u) = if n ≤ r then 2^n else 0 := by
  induction r generalizing n d u with
  | zero => cases n <;> simp [cuenta, hu]
  | succ r ih =>
    have hcin : (2:ℤ)^(r+1)*u = 2*(2:ℤ)^r*u := by rw [pow_succ]; ring
    have hd : (2:ℤ)^(r+1+1)*d = 4*(2:ℤ)^r*d := by simp only [pow_succ]; ring
    have hc : ((2:ℤ)^(r+1)*u)%2=0 := by
      rw [show (2:ℤ)^(r+1)*u = 2*((2:ℤ)^r*u) by rw [pow_succ]; ring]
      omega
    cases n with
    | zero => simp [cuenta]
    | succ n =>
      rw [cuenta, if_pos hc, hcin, hd]
      rw [(Mangostas.hijos_bajos ((2:ℤ)^r) u d).1,
        (Mangostas.hijos_bajos ((2:ℤ)^r) u d).2]
      rw [show 4*(2:ℤ)^r*d = (2:ℤ)^(r+1)*(2*d) by rw [pow_succ]; ring]
      rw [ih n (2*d) u hu, ih n (2*d) (3*u-2*d) (by omega)]
      by_cases hn : n ≤ r
      · have hs : n+1 ≤ r+1 := by omega
        simp [hn, hs, pow_succ]
        omega
      · have hs : ¬n+1 ≤ r+1 := by omega
        simp [hn, hs]

theorem cuenta_alta (r n : ℕ) (d u : ℤ) (hd : d%2=1) :
    cuenta ((2:ℤ)^(r+1)*d) n ((2:ℤ)^(r+1)*u) =
      if n ≤ r+1 then 2^n else 2^(r+1) := by
  induction n generalizing u with
  | zero => simp [cuenta]
  | succ n ih =>
    have hcin : (2:ℤ)^(r+1)*u = 2*(2:ℤ)^r*u := by rw [pow_succ]; ring
    have hdin : (2:ℤ)^(r+1)*d = 2*(2:ℤ)^r*d := by rw [pow_succ]; ring
    have hc : ((2:ℤ)^(r+1)*u)%2=0 := by
      rw [show (2:ℤ)^(r+1)*u = 2*((2:ℤ)^r*u) by rw [pow_succ]; ring]
      omega
    have hrec : cuenta ((2:ℤ)^(r+1)*d) (n+1) ((2:ℤ)^(r+1)*u) =
        (if n ≤ r+1 then 2^n else 2^(r+1))+(if n ≤ r then 2^n else 0) := by
      rw [cuenta, if_pos hc, hcin, hdin]
      rw [(Mangostas.hijos_altos ((2:ℤ)^r) u d).1,
        (Mangostas.hijos_altos ((2:ℤ)^r) u d).2]
      rw [← hdin]
      by_cases hu : u%2=0
      · have he : u=2*(u/2) := by omega
        have hf : (2:ℤ)^r*u = (2:ℤ)^(r+1)*(u/2) := by
          calc
            _ = (2:ℤ)^r*(2*(u/2)) := congrArg (fun x => (2:ℤ)^r*x) he
            _ = _ := by rw [pow_succ]; ring
        rw [hf, ih (u/2), cuenta_baja r n d (3*u-d) (by omega)]
      · have hv : (3*u-d)%2=0 := by omega
        have he : 3*u-d=2*((3*u-d)/2) := by omega
        have hf : (2:ℤ)^r*(3*u-d) = (2:ℤ)^(r+1)*((3*u-d)/2) := by
          calc
            _ = (2:ℤ)^r*(2*((3*u-d)/2)) := congrArg (fun x => (2:ℤ)^r*x) he
            _ = _ := by rw [pow_succ]; ring
        rw [hf, ih ((3*u-d)/2), cuenta_baja r n d u (by omega)]
        omega
    rw [hrec]
    by_cases hn : n ≤ r
    · have ha : n ≤ r+1 := by omega
      have hb : n+1 ≤ r+1 := by omega
      simp [hn, ha, hb, pow_succ]
      omega
    · have hb : ¬n+1 ≤ r+1 := by omega
      by_cases ha : n ≤ r+1
      · have he : n=r+1 := by omega
        simp [he]
      · simp [hn, ha, hb]

theorem clasificacion (A : ℕ) (c : ℤ) :
    (∃ u, c=(2:ℤ)^A*u) ∨
      ∃ r, r<A ∧ ∃ u, u%2=1 ∧ c=(2:ℤ)^r*u := by
  induction A generalizing c with
  | zero => exact Or.inl ⟨c,by simp⟩
  | succ A ih =>
    by_cases hc : c%2=0
    · have he : c=2*(c/2) := by omega
      rcases ih (c/2) with ⟨u,hu⟩ | ⟨r,hr,u,hu,hf⟩
      · left
        refine ⟨u,?_⟩
        calc
          c = 2*((2:ℤ)^A*u) := by rw [← hu]; exact he
          _ = (2:ℤ)^(A+1)*u := by rw [pow_succ]; ring
      · right
        refine ⟨r+1,by omega,u,hu,?_⟩
        calc
          c = 2*((2:ℤ)^r*u) := by rw [← hf]; exact he
          _ = (2:ℤ)^(r+1)*u := by rw [pow_succ]; ring
    · right
      exact ⟨0,by omega,c,by omega,by simp⟩

theorem cuenta_uniforme (A s : ℕ) (d c : ℤ) (hA : 1 ≤ A) (hd : d%2=1) :
    cuenta ((2:ℤ)^A*d) (A+s) c ≤ 2^A := by
  rcases clasificacion A c with ⟨u,hc⟩ | ⟨r,hr,u,hu,hc⟩
  · rw [hc]
    cases A with
    | zero => omega
    | succ r =>
      rw [cuenta_alta r (r+1+s) d u hd]
      by_cases hs : s=0
      · subst s
        simp
      · simp [show ¬r+1+s ≤ r+1 by omega]
  · have ha : r+1+(A-(r+1))=A := by omega
    have hf : (2:ℤ)^A*d = (2:ℤ)^(r+1)*((2:ℤ)^(A-(r+1))*d) := by
      rw [← mul_assoc, ← pow_add, ha]
    rw [hc, hf, cuenta_baja r (A+s) ((2:ℤ)^(A-(r+1))*d) u hu]
    simp [show ¬ A+s ≤ r by omega]

def probabilidad (D : ℤ) (n : ℕ) (c : ℤ) : ℝ := (cuenta D n c:ℝ)/(2:ℝ)^n

theorem probabilidad_sucesor (D : ℤ) (n : ℕ) (c : ℤ) :
    probabilidad D (n+1) c = if c%2=0 then
      (probabilidad D n (c/2)+probabilidad D n ((3*c-D)/2))/2 else 0 := by
  by_cases hc : c%2=0
  · simp [probabilidad, cuenta, hc, pow_succ]
    ring
  · simp [probabilidad, cuenta, hc]

theorem cola_uniforme (A s : ℕ) (d c : ℤ) (hA : 1 ≤ A) (hd : d%2=1) :
    probabilidad ((2:ℤ)^A*d) (A+s) c ≤ 1/(2:ℝ)^s := by
  have hc : (cuenta ((2:ℤ)^A*d) (A+s) c:ℝ) ≤ (2:ℝ)^A := by
    exact_mod_cast cuenta_uniforme A s d c hA hd
  calc
    _ ≤ (2:ℝ)^A/(2:ℝ)^(A+s) := div_le_div_of_nonneg_right hc (by positivity)
    _ = 1/(2:ℝ)^s := by rw [pow_add]; field_simp

def racha_cadena : ℕ → Estado → ℝ
  | 0, _ => 1
  | n+1, .vivo (k+2) c => if c%2=0 then
      (racha_cadena n (paso (.vivo (k+2) c) false)+
        racha_cadena n (paso (.vivo (k+2) c) true))/2 else 0
  | _+1, _ => 0

theorem racha_original (k n : ℕ) (c : ℤ) :
    racha_cadena n (.vivo (k+2) c) = probabilidad (coef (k+2)-1) n c := by
  induction n generalizing c with
  | zero => simp [racha_cadena, probabilidad, cuenta]
  | succ n ih =>
    rw [probabilidad_sucesor]
    by_cases hc : c%2=0
    · simp only [racha_cadena, hc, if_true, paso, Bool.false_eq_true, if_false, ih]
      have he : (3*c+1-coef (k+2))/2 = (3*c-(coef (k+2)-1))/2 := by
        congr 1
        omega
      rw [he]
    · simp [racha_cadena, hc]

theorem cola_racha_original (k A s : ℕ) (c d : ℤ) (hA : 1 ≤ A)
    (hd : d%2=1) (hD : coef (k+2)-1=(2:ℤ)^A*d) :
    racha_cadena (A+s) (.vivo (k+2) c) ≤ 1/(2:ℝ)^s := by
  rw [racha_original, hD]
  exact cola_uniforme A s d c hA hd

#print axioms cuenta_baja
#print axioms cuenta_alta
#print axioms cuenta_uniforme
#print axioms cola_uniforme
#print axioms racha_original
#print axioms cola_racha_original

end RachasEnterasGao
