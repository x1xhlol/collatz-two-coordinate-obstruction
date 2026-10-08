/- Cadena absorbente completa y dominación normalizada universal.
   Certifica E1/C1 algebraica, incluidos k=0,1, signos y cementerio.
   La esperanza y el transporte de medida no están formalizados aquí. -/
namespace CadenaCompletaGao

def mag (c : Int) : Int := if c < 0 then -c else c

theorem mag_no_negativa (c : Int) : 0 <= mag c := by
  unfold mag
  split <;> omega

theorem mag_mag (c : Int) : mag (mag c) = mag c := by
  have h := mag_no_negativa c
  change (if mag c < 0 then -(mag c) else mag c) = mag c
  rw [if_neg (by omega)]

def coef : Nat → Int
  | 0 => 1
  | k+1 => 3*coef k

theorem coef_positivo : ∀ k, 1 <= coef k := by
  intro k
  induction k with
  | zero => decide
  | succ k ih => simp only [coef]; omega

theorem coef_impar : ∀ k, coef k % 2 = 1 := by
  intro k
  induction k with
  | zero => decide
  | succ k ih => simp only [coef]; omega

theorem coef_es_potencia : ∀ k, coef k = (3 : Int)^k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp only [coef, ih, Int.pow_succ]; rw [Int.mul_comm]

-- Tras dividir por 2*p*q>0, esta es |d|/q <= ((1+2*b)/2)*|c|/p+1/2.
def Dominado (p c q d b : Int) : Prop :=
  2*mag d*p <= (1+2*b)*mag c*q+p*q

theorem compartido_par (p c d : Int) (hp : 1 <= p) (hd : 2*d=c) :
    Dominado p c p d 0 := by
  have hc : 2*mag d = mag c := by unfold mag; split <;> split <;> omega
  have hp2 : 0 <= p*p := Int.mul_nonneg (by omega) (by omega)
  simp only [Dominado, Int.mul_zero, Int.add_zero, Int.one_mul]
  rw [hc]
  omega

theorem compartido_impar (p c d : Int) (hp : 1 <= p)
    (hd : 2*d=3*c+1-p) : Dominado p c p d 1 := by
  have hc : 2*mag d <= 3*mag c+p := by
    unfold mag
    split <;> split <;> omega
  have hmul := Int.mul_le_mul_of_nonneg_right hc (show 0 <= p by omega)
  unfold Dominado
  grind

theorem ascenso (p c d : Int) (hp : 1 <= p)
    (hd : 2*d=3*c+1) : Dominado p c (3*p) d 0 := by
  have hc : 2*mag d <= 3*mag c+3*p := by
    unfold mag
    split <;> split <;> omega
  have hmul := Int.mul_le_mul_of_nonneg_right hc (show 0 <= p by omega)
  unfold Dominado
  grind

theorem descenso (p c d : Int) (hp : 1 <= p)
    (hd : 2*d=c-p) : Dominado (3*p) c p d 1 := by
  have hc : 2*mag d <= mag c+p := by
    unfold mag
    split <;> split <;> omega
  have hmul := Int.mul_le_mul_of_nonneg_right hc (show 0 <= 3*p by omega)
  unfold Dominado
  grind

theorem vuelco (c d : Int) (hd : 2*d=1-3*c) :
    Dominado 1 c 3 d 1 := by
  unfold Dominado mag
  split <;> split <;> omega

inductive Estado where
  | fusion
  | vivo (k : Nat) (c : Int)
deriving DecidableEq

def paso : Estado → Bool → Estado
  | .fusion, _ => .fusion
  | .vivo 0 c, b =>
      if c%2=0 then .vivo 0 (if b then 3*c/2 else c/2)
      else .vivo 1 (if b then (1-3*c)/2 else (3*c+1)/2)
  | .vivo (k+1) c, b =>
      if c%2=0 then .vivo (k+1) (if b then (3*c+1-coef (k+1))/2 else c/2)
      else if b then
        match k with
        | 0 => if c=1 then .fusion else .vivo 0 (mag ((c-1)/2))
        | j+1 => .vivo (j+1) ((c-coef (j+1))/2)
      else .vivo (k+2) ((3*c+1)/2)

def datos : Estado → Int × Int
  | .fusion => (1,0)
  | .vivo k c => (coef k,c)

def bitInt (b : Bool) : Int := if b then 1 else 0

theorem dominacion_cadena (z : Estado) (b : Bool) :
    Dominado (datos z).1 (datos z).2
      (datos (paso z b)).1 (datos (paso z b)).2 (bitInt b) := by
  cases z with
  | fusion => cases b <;> simp [Dominado, datos, paso, bitInt, mag]
  | vivo k c =>
    cases k with
    | zero =>
      by_cases hc : c%2=0
      · cases b with
        | false =>
          simp only [paso, hc, if_true, Bool.false_eq_true, if_false, datos, coef, bitInt]
          exact compartido_par 1 c (c/2) (by omega) (by omega)
        | true =>
          simp only [paso, hc, if_true, datos, coef, bitInt]
          exact compartido_impar 1 c (3*c/2) (by omega) (by omega)
      · cases b with
        | false =>
          simp only [paso, hc, if_false, Bool.false_eq_true, datos, coef, bitInt]
          exact ascenso 1 c ((3*c+1)/2) (by omega) (by omega)
        | true =>
          simp only [paso, hc, if_false, if_true, datos, coef, bitInt]
          exact vuelco c ((1-3*c)/2) (by omega)
    | succ k =>
      have hp := coef_positivo (k+1)
      have hi := coef_impar (k+1)
      by_cases hc : c%2=0
      · cases b with
        | false =>
          simp only [paso, hc, if_true, Bool.false_eq_true, if_false, datos, bitInt]
          exact compartido_par _ c (c/2) hp (by omega)
        | true =>
          simp only [paso, hc, if_true, datos, bitInt]
          exact compartido_impar _ c _ hp (by omega)
      · cases b with
        | false =>
          simp only [paso, hc, if_false, Bool.false_eq_true, datos, bitInt]
          change Dominado (coef (k+1)) c (3*coef (k+1)) ((3*c+1)/2) 0
          exact ascenso _ c _ hp (by omega)
        | true =>
          cases k with
          | zero =>
            by_cases hf : c=1
            · subst c
              simp [Dominado, datos, paso, coef, bitInt, mag]
            · simp only [paso, hc, hf, if_false, if_true, datos, coef, bitInt]
              have hd := descenso 1 c ((c-1)/2) (by omega) (by omega)
              unfold Dominado at hd ⊢
              rw [mag_mag]
              exact hd
          | succ j =>
            have hpi := coef_impar (j+1)
            simp only [paso, hc, if_false, if_true, datos, bitInt]
            change Dominado (3*coef (j+1)) c (coef (j+1)) ((c-coef (j+1))/2) 1
            exact descenso _ c _ (coef_positivo (j+1)) (by omega)

#print axioms coef_positivo
#print axioms coef_impar
#print axioms coef_es_potencia
#print axioms compartido_par
#print axioms compartido_impar
#print axioms ascenso
#print axioms descenso
#print axioms vuelco
#print axioms dominacion_cadena
end CadenaCompletaGao
