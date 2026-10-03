import Resto

/- Producto normalizado Q_t=Pi_t/(31/32)^t. La raíz de |Q_t| es
   superarmónica para el árbol de bits. Cota finita desde un tiempo T. -/

noncomputable section

namespace ProductoGao

open MomentosGao RestoGao

def rho : ℝ := 31/32
def razon : ℝ := 61/62
def paso_producto (x : ℝ) (b : Bool) : ℝ := factor b/rho*x
def potencial (x : ℝ) : ℝ := Real.sqrt |x|

theorem deriva_producto (x : ℝ) :
    (potencial (paso_producto x false)+potencial (paso_producto x true))/2 ≤
      razon*potencial x := by
  have h0 : Real.sqrt ((1/2:ℝ)/rho) ≤ 23/32 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    norm_num [rho]
  have h1 : Real.sqrt ((3/2:ℝ)/rho) ≤ 319/256 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    norm_num [rho]
  have hx := Real.sqrt_nonneg |x|
  have ha := mul_le_mul_of_nonneg_right h0 hx
  have hb := mul_le_mul_of_nonneg_right h1 hx
  have he0 : potencial (paso_producto x false) = Real.sqrt ((1/2:ℝ)/rho)*potencial x := by
    unfold potencial paso_producto
    rw [abs_mul, abs_of_nonneg (by norm_num [factor, rho])]
    rw [Real.sqrt_mul (by norm_num [factor, rho])]
    rfl
  have he1 : potencial (paso_producto x true) = Real.sqrt ((3/2:ℝ)/rho)*potencial x := by
    unfold potencial paso_producto
    rw [abs_mul, abs_of_nonneg (by norm_num [factor, rho])]
    rw [Real.sqrt_mul (by norm_num [factor, rho])]
    rfl
  rw [he0, he1]
  unfold razon potencial
  linarith

theorem momento_producto (n : ℕ) (x : ℝ) :
    promedio paso_producto potencial n x ≤ razon^n*potencial x := by
  induction n generalizing x with
  | zero => simp [promedio]
  | succ n ih =>
    have h0 := ih (paso_producto x false)
    have h1 := ih (paso_producto x true)
    have hp : 0 ≤ razon^n := pow_nonneg (by norm_num [razon]) n
    have hd := mul_le_mul_of_nonneg_left (deriva_producto x) hp
    simp only [promedio, pow_succ]
    nlinarith

theorem maximo_producto (n : ℕ) (x : ℝ) :
    MaximosGao.cruce paso_producto abs 1 n x ≤ potencial x := by
  apply MaximosGao.cruce_dominado
  · intro z
    unfold MaximosGao.indicador
    split
    · rename_i hz
      have h := Real.sqrt_le_sqrt (le_of_lt hz)
      simpa [potencial] using h
    · exact Real.sqrt_nonneg |z|
  · intro z
    have h := deriva_producto z
    have hz := Real.sqrt_nonneg |z|
    unfold razon at h
    unfold potencial at h ⊢
    linarith

/- Probabilidad de un cruce en los instantes T,...,T+H:
   primero se promedian T bits y luego H bits adicionales. -/
def cruce_desde (T H : ℕ) : ℝ :=
  promedio paso_producto (MaximosGao.cruce paso_producto abs 1 H) T 1

theorem producto_desde (T H : ℕ) : cruce_desde T H ≤ razon^T := by
  have hc := promedio_mono paso_producto _ potencial (maximo_producto H) T 1
  have hm := momento_producto T 1
  norm_num [potencial] at hm
  exact hc.trans hm

theorem producto_palabra (bs : List Bool) (x : ℝ) :
    recorre paso_producto bs x = (bs.map factor).prod / rho^bs.length*x := by
  induction bs generalizing x with
  | nil => simp [recorre]
  | cons b bs ih =>
    simp only [recorre, ih, List.map_cons, List.prod_cons, List.length_cons,
      pow_succ, paso_producto]
    field_simp

#print axioms deriva_producto
#print axioms momento_producto
#print axioms maximo_producto
#print axioms producto_desde
#print axioms producto_palabra

end ProductoGao
