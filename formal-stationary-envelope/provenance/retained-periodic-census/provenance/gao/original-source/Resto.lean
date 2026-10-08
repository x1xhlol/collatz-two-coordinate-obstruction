import Maximos

/-!
Resto aditivo de la primera excursión interior. La base sigue la cadena
original; una marca persistente apaga el término aditivo después de salir.
El resto y el producto siguen multiplicándose por el siguiente A.
-/

noncomputable section

namespace RestoGao

open CadenaCompletaGao MomentosGao

def factor (b : Bool) : ℝ := if b then 3/2 else 1/2

def coordenada (z : Estado) : ℝ := ((datos z).2 : ℝ) / ((datos z).1 : ℝ)

def interior : Estado → Bool
  | .vivo (_+2) _ => true
  | _ => false

def error_paso (z : Estado) (b : Bool) : ℝ :=
  coordenada (paso z b)-factor b*coordenada z

def ErrorEntero (p c q d b : ℤ) : Prop :=
  -(p*q) ≤ 2*d*p-(1+2*b)*c*q ∧ 2*d*p-(1+2*b)*c*q ≤ p*q

theorem error_compartido_par (p c d : ℤ) (hp : 1 ≤ p) (hd : 2*d=c) :
    ErrorEntero p c p d 0 := by
  have hs := sq_nonneg p
  constructor <;> nlinarith [hd]

theorem error_compartido_impar (p c d : ℤ) (hp : 1 ≤ p)
    (hd : 2*d=3*c+1-p) : ErrorEntero p c p d 1 := by
  have hs := mul_nonneg (show 0 ≤ p by omega) (show 0 ≤ p-1 by omega)
  constructor <;> nlinarith [hd]

theorem error_ascenso (p c d : ℤ) (hp : 1 ≤ p)
    (hd : 2*d=3*c+1) : ErrorEntero p c (3*p) d 0 := by
  have hs := mul_nonneg (show 0 ≤ p by omega) (show 0 ≤ p-1 by omega)
  constructor <;> nlinarith [hd]

theorem error_descenso (p c d : ℤ) (hp : 1 ≤ p)
    (hd : 2*d=c-p) : ErrorEntero (3*p) c p d 1 := by
  have hs := sq_nonneg p
  constructor <;> nlinarith [hd]

theorem error_interior_entero (k : ℕ) (c : ℤ) (b : Bool) :
    ErrorEntero (coef (k+2)) c (datos (paso (.vivo (k+2) c) b)).1
      (datos (paso (.vivo (k+2) c) b)).2 (bitInt b) := by
  have hp := coef_positivo (k+2)
  have hi := coef_impar (k+2)
  by_cases hc : c%2=0
  · cases b with
    | false =>
      simp only [paso, hc, if_true, Bool.false_eq_true, if_false, datos, bitInt]
      exact error_compartido_par _ c (c/2) hp (by omega)
    | true =>
      simp only [paso, hc, if_true, datos, bitInt]
      exact error_compartido_impar (coef (k+2)) c ((3*c+1-coef (k+2))/2) hp (by omega)
  · cases b with
    | false =>
      simp only [paso, hc, if_false, Bool.false_eq_true, datos, bitInt]
      change ErrorEntero (coef (k+2)) c (3*coef (k+2)) ((3*c+1)/2) 0
      exact error_ascenso _ c _ hp (by omega)
    | true =>
      have hi1 := coef_impar (k+1)
      simp only [paso, hc, if_false, if_true, datos, bitInt]
      change ErrorEntero (3*coef (k+1)) c (coef (k+1)) ((c-coef (k+1))/2) 1
      exact error_descenso _ c _ (coef_positivo (k+1)) (by omega)

theorem error_interior_real (k : ℕ) (c : ℤ) (b : Bool) :
    |error_paso (.vivo (k+2) c) b| ≤ 1/2 := by
  let z := Estado.vivo (k+2) c
  let p : ℝ := ((datos z).1 : ℝ)
  let q : ℝ := ((datos (paso z b)).1 : ℝ)
  let x : ℝ := ((datos z).2 : ℝ)
  let y : ℝ := ((datos (paso z b)).2 : ℝ)
  have hp : 0 < p := denominador_positivo z
  have hq : 0 < q := denominador_positivo (paso z b)
  have hf : factor b = (1+2*(bitInt b:ℝ))/2 := by cases b <;> norm_num [factor, bitInt]
  have he := error_interior_entero k c b
  unfold ErrorEntero at he
  have hlo : -(p*q) ≤ 2*y*p-(1+2*(bitInt b:ℝ))*x*q := by
    dsimp only [p, q, x, y, z]
    exact_mod_cast he.1
  have hhi : 2*y*p-(1+2*(bitInt b:ℝ))*x*q ≤ p*q := by
    dsimp only [p, q, x, y, z]
    exact_mod_cast he.2
  have hden : 0 < 2*p*q := by positivity
  have hid : error_paso z b =
      (2*y*p-(1+2*(bitInt b:ℝ))*x*q)/(2*p*q) := by
    change y/q-factor b*(x/p) = _
    rw [hf]
    field_simp
  rw [show Estado.vivo (k+2) c = z from rfl, hid, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  apply abs_le.mpr
  constructor <;> nlinarith

def incremento (z : Estado) (b : Bool) : ℝ :=
  if interior z then error_paso z b else 0

theorem hijo_interior_o_salida (k : ℕ) (c : ℤ) (b : Bool) :
    interior (paso (.vivo (k+2) c) b)=true ∨
      ∃ d, paso (.vivo (k+2) c) b = .vivo 1 d := by
  cases k <;> cases b <;> by_cases hc : c%2=0 <;> simp [paso, hc, interior]

theorem incremento_acotado (z : Estado) (b : Bool) : |incremento z b| ≤ 1/2 := by
  cases z with
  | fusion => norm_num [incremento, interior]
  | vivo k c =>
    cases k with
    | zero => norm_num [incremento, interior]
    | succ k =>
      cases k with
      | zero => norm_num [incremento, interior]
      | succ k => simpa [incremento, interior] using error_interior_real k c b

structure EstadoW where
  base : Estado
  salio : Bool
  resto : ℝ
  producto : ℝ

def paso_w (s : EstadoW) (b : Bool) : EstadoW where
  base := paso s.base b
  salio := s.salio || !(interior (paso s.base b))
  resto := factor b*s.resto + if s.salio then 0 else incremento s.base b
  producto := factor b*s.producto

def inicial (c : ℤ) : EstadoW := ⟨.vivo 2 c, false, 0, 1⟩

theorem factor_no_negativo (b : Bool) : 0 ≤ factor b := by
  cases b <;> norm_num [factor]

theorem dominacion_resto (s : EstadoW) (b : Bool) :
    |(paso_w s b).resto| ≤ factor b*|s.resto|+1/2 := by
  have he : |(if s.salio then 0 else incremento s.base b : ℝ)| ≤ 1/2 := by
    cases s.salio
    · exact incremento_acotado s.base b
    · norm_num
  change |factor b*s.resto + (if s.salio then 0 else incremento s.base b)| ≤ _
  have ha := abs_add_le (factor b*s.resto) (if s.salio then 0 else incremento s.base b)
  rw [abs_mul, abs_of_nonneg (factor_no_negativo b)] at ha
  linarith

theorem momento_resto (n : ℕ) (c : ℤ) :
    promedio paso_w (fun s => Real.sqrt |s.resto|) n (inicial c) ≤ 32 := by
  have hd := deriva_raiz paso_w (fun s => |s.resto|) (fun _ => abs_nonneg _)
    (fun s => by simpa [factor] using dominacion_resto s false)
    (fun s => by simpa [factor] using dominacion_resto s true)
  have hm := momento_arbol paso_w (fun s => Real.sqrt |s.resto|) hd n (inicial c)
  have hp : 0 ≤ (31/32:ℝ)^n := pow_nonneg (by norm_num) n
  have hz : Real.sqrt |(inicial c).resto| = 0 := by simp [inicial]
  rw [hz, mul_zero, zero_add] at hm
  linarith

theorem maximo_resto (n : ℕ) (c : ℤ) (R : ℝ) :
    Real.sqrt R*MaximosGao.cruce paso_w (fun s => |s.resto|) R n (inicial c) ≤
      32*((n:ℝ)+1) := by
  exact MaximosGao.cola_maximo paso_w (fun s => |s.resto|) R 32 n (inicial c)
    (fun t => momento_resto t c)

theorem coste_resto_ventana (H : ℕ) (c : ℤ) (Q : ℝ) (hQ : 0 < Q) :
    MaximosGao.cruce paso_w (fun s => |s.resto|)
      ((128*((H:ℝ)+1)*Q)^2) H (inicial c) ≤ 1/(4*Q) := by
  have h := maximo_resto H c ((128*((H:ℝ)+1)*Q)^2)
  rw [Real.sqrt_sq (by positivity)] at h
  apply (le_div_iff₀ (show 0 < 4*Q by positivity)).2
  apply (mul_le_mul_iff_left₀ (show 0 < 32*((H:ℝ)+1) by positivity)).mp
  nlinarith

def recorre {S : Type} (f : S → Bool → S) : List Bool → S → S
  | [], s => s
  | b::bs, s => recorre f bs (f s b)

def prefijo_interior : Estado → List Bool → Prop
  | _, [] => True
  | z, b::bs => interior z = true ∧ prefijo_interior (paso z b) bs

theorem base_recorre (bs : List Bool) (s : EstadoW) :
    (recorre paso_w bs s).base = recorre paso bs s.base := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih => simpa [recorre, paso_w] using ih (paso_w s b)

theorem producto_recorre (bs : List Bool) (s : EstadoW) :
    (recorre paso_w bs s).producto = (bs.map factor).prod*s.producto := by
  induction bs generalizing s with
  | nil => simp [recorre]
  | cons b bs ih => simp only [recorre, ih, List.map_cons, List.prod_cons, paso_w]; ring

theorem salida_persiste (s : EstadoW) (b : Bool) (hs : s.salio=true) :
    (paso_w s b).salio=true := by simp [paso_w, hs]

theorem resto_continuacion (bs : List Bool) (s : EstadoW) (hs : s.salio=true) :
    (recorre paso_w bs s).resto = (bs.map factor).prod*s.resto := by
  induction bs generalizing s with
  | nil => simp [recorre]
  | cons b bs ih =>
    simp only [recorre, List.map_cons, List.prod_cons]
    rw [ih (paso_w s b) (salida_persiste s b hs)]
    simp [paso_w, hs]
    ring

theorem identidad_paso (s : EstadoW) (b : Bool) (u0 : ℝ)
    (hs : s.salio=false) (hi : interior s.base=true)
    (hu : coordenada s.base=s.producto*u0+s.resto) :
    coordenada (paso_w s b).base = (paso_w s b).producto*u0+(paso_w s b).resto := by
  simp only [paso_w, hs, Bool.false_eq_true, if_false, incremento, hi, if_true, error_paso]
  rw [hu]
  ring

theorem identidad_prefijo (bs : List Bool) (s : EstadoW) (u0 : ℝ)
    (hs : s.salio=false) (hi : prefijo_interior s.base bs)
    (hu : coordenada s.base=s.producto*u0+s.resto) :
    coordenada (recorre paso_w bs s).base =
      (recorre paso_w bs s).producto*u0+(recorre paso_w bs s).resto := by
  induction bs generalizing s with
  | nil => exact hu
  | cons b bs ih =>
    have hprim := identidad_paso s b u0 hs hi.1 hu
    cases bs with
    | nil => exact hprim
    | cons b' bs =>
      have hmarca : (paso_w s b).salio=false := by
        simp [paso_w, hs, hi.2.1]
      exact ih (paso_w s b) hmarca hi.2 hprim

theorem identidad_excursion (bs : List Bool) (c : ℤ)
    (hi : prefijo_interior (.vivo 2 c) bs) :
    coordenada (recorre paso bs (.vivo 2 c)) =
      (bs.map factor).prod*((c:ℝ)/9)+(recorre paso_w bs (inicial c)).resto := by
  have hu : coordenada (inicial c).base = (inicial c).producto*((c:ℝ)/9)+(inicial c).resto := by
    norm_num [inicial, coordenada, datos, coef]
  have h := identidad_prefijo bs (inicial c) ((c:ℝ)/9) rfl hi hu
  rw [base_recorre, producto_recorre] at h
  simpa [inicial] using h

theorem salida_controlada (bs : List Bool) (c d : ℤ) (R : ℝ)
    (hi : prefijo_interior (.vivo 2 c) bs)
    (hs : recorre paso bs (.vivo 2 c) = .vivo 1 d)
    (hprod : |(bs.map factor).prod*((c:ℝ)/9)| ≤ 1)
    (hresto : |(recorre paso_w bs (inicial c)).resto| ≤ R) :
    |(d:ℝ)| ≤ 3*(R+1) := by
  have hident := identidad_excursion bs c hi
  have htri : |coordenada (recorre paso bs (.vivo 2 c))| ≤ 1+R := by
    rw [hident]
    exact (abs_add_le _ _).trans (add_le_add hprod hresto)
  rw [hs] at htri
  norm_num [coordenada, datos, coef, abs_div] at htri
  linarith

#print axioms error_interior_entero
#print axioms error_interior_real
#print axioms hijo_interior_o_salida
#print axioms dominacion_resto
#print axioms momento_resto
#print axioms maximo_resto
#print axioms coste_resto_ventana
#print axioms base_recorre
#print axioms producto_recorre
#print axioms resto_continuacion
#print axioms identidad_excursion
#print axioms salida_controlada

end RestoGao
