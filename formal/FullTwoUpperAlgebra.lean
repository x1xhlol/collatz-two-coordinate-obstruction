import FullTwoUpperBasic
import Mathlib.Tactic.FieldSimp

namespace CollatzResearch.FullTwoUpper

set_option maxHeartbeats 800000

theorem triangular_resonance (α β ρ σ a b e f g : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hρ : 0 < ρ)
    (ae : α*e+a*σ=β*a+e*ρ)
    (af : α*f+a*σ=β*b+e*ρ)
    (ag : α*g+a*σ=β*a+f*ρ)
    (be : α*e+b*σ=β*b+f*ρ)
    (bg : α*g+b*σ=β*b+g*ρ) :
    (a=b ∧ e=f ∧ e=g ∧ (α-ρ)*e=(β-σ)*a) ∨
    (ρ=2*α ∧ σ=3*β) := by
  have hv : α*(f-e)=β*(b-a) := by nlinarith only [af,ae]
  have hd : (σ-β)*(b-a)=ρ*(f-e) := by nlinarith only [be,ae]
  have hw : α*(g-e)=ρ*(f-e) := by nlinarith only [ag,ae]
  have hz : (α-ρ)*(g-e)=(β-σ)*(b-a) := by nlinarith only [bg,ae]
  by_cases hab : a=b
  · left
    have hef : e=f := by
      have hmul : α*(f-e)=0 := by rw [hab,sub_self,mul_zero] at hv; exact hv
      have := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hα)
      linarith
    have heg : e=g := by
      have hmul : α*(g-e)=0 := by rw [← hef,sub_self,mul_zero] at hw; exact hw
      have := (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hα)
      linarith
    exact ⟨hab,hef,heg,by nlinarith only [ae]⟩
  · right
    have hba : b-a ≠ 0 := by intro h; apply hab; linarith
    have hfe : f-e ≠ 0 := by
      intro h
      rw [h,mul_zero] at hv
      exact hba ((mul_eq_zero.mp hv.symm).resolve_left (ne_of_gt hβ))
    have hge : g-e ≠ 0 := by
      intro h
      rw [h,mul_zero] at hw
      exact hfe ((mul_eq_zero.mp hw.symm).resolve_left (ne_of_gt hρ))
    have hmul : (2*α-ρ)*(g-e)=0 := by nlinarith only [hd,hw,hz]
    have hr : ρ=2*α := by
      have := (mul_eq_zero.mp hmul).resolve_right hge
      linarith
    have hmul : (σ-3*β)*(b-a)=0 := by
      rw [hr] at hd
      nlinarith only [hd,hv]
    have hs : σ=3*β := by
      have := (mul_eq_zero.mp hmul).resolve_right hba
      linarith
    exact ⟨hr,hs⟩

theorem common_form (t s x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : 0 < x+y)
    (hn : t < 1 ∨ s < 1) (heq : (1-t)*y=(1-s)*x) :
    ∃ l : ℝ, 0 < l ∧ x=l*(1-t) ∧ y=l*(1-s) := by
  by_cases ht : t < 1
  · have htp : 0 < 1-t := by linarith
    have hxp : 0 < x := by
      by_contra h
      have hx0 : x=0 := le_antisymm (le_of_not_gt h) hx
      rw [hx0,mul_zero] at heq
      have hy0 := (mul_eq_zero.mp heq).resolve_left (ne_of_gt htp)
      linarith
    refine ⟨x/(1-t),div_pos hxp htp,?_,?_⟩
    · exact (div_mul_cancel₀ x (ne_of_gt htp)).symm
    · apply (mul_right_cancel₀ (ne_of_gt htp))
      calc
        y*(1-t) = (1-s)*x := by nlinarith only [heq]
        _ = (x/(1-t)*(1-s))*(1-t) := by field_simp
  · have hs : s < 1 := hn.resolve_left ht
    have hsp : 0 < 1-s := by linarith
    have hyp : 0 < y := by
      by_contra h
      have hy0 : y=0 := le_antisymm (le_of_not_gt h) hy
      rw [hy0,mul_zero] at heq
      have hx0 := (mul_eq_zero.mp heq.symm).resolve_left (ne_of_gt hsp)
      linarith
    refine ⟨y/(1-s),div_pos hyp hsp,?_,?_⟩
    · apply (mul_right_cancel₀ (ne_of_gt hsp))
      calc
        x*(1-s) = (1-t)*y := by nlinarith only [heq]
        _ = (y/(1-s)*(1-t))*(1-s) := by field_simp
    · exact (div_mul_cancel₀ y (ne_of_gt hsp)).symm


structure QForm (m : Data) (l : ℝ) : Prop where
  a : m.qa=l*(1-m.za)
  b : m.qb=l*(1-m.zb)
  e : m.qe=l*(1-m.ze)
  f : m.qf=l*(1-m.zf)
  g : m.qg=l*(1-m.zg)

structure KForm (m : Data) (u : ℝ) : Prop where
  a : m.ka=u*(1-m.za)
  b : m.kb=u*(1-m.zb)
  e : m.ke=u*(1-m.ze)
  f : m.kf=u*(1-m.zf)
  g : m.kg=u*(1-m.zg)

theorem q_form_parameter_pos (m : Data) (l : ℝ) (hn : 0 ≤ l)
    (q : QForm m l) (hpos : 0 < m.qa+m.qb+(m.qe+m.qf+m.qg)) : 0 < l := by
  by_contra h
  have hz : l=0 := le_antisymm (le_of_not_gt h) hn
  have a := q.a
  have b := q.b
  have e := q.e
  have f := q.f
  have g := q.g
  rw [hz,zero_mul] at a b e f g
  rw [a,b,e,f,g] at hpos
  linarith


theorem projected_equalities (m : Data) (w : Weak m) (ex : ExactSwaps m)
    (l : ℝ) (hl : 0 ≤ l) (q : QForm m l) :
    m.ha+l*m.ka=m.hb+l*m.kb ∧
    m.he+l*m.ke=m.hf+l*m.kf ∧
    m.hg+l*m.kg=m.hf+l*m.kf ∧
    m.hg+l*m.kg ≤ m.hb+l*m.kb := by
  have af := ex.af_h
  have ag := ex.ag_h
  have be := ex.be_h
  rw [q.a,q.e] at af
  rw [q.f,q.a] at ag
  rw [q.f,q.b] at be
  have ak := congrArg (fun t : ℝ => l*t) ex.af_k
  have gk := congrArg (fun t : ℝ => l*t) ex.ag_k
  have bk := congrArg (fun t : ℝ => l*t) ex.be_k
  have he : m.he+l*m.ke=m.hf+l*m.kf := by nlinarith only [be,bk]
  have hg : m.hg+l*m.kg=m.hf+l*m.kf := by nlinarith only [ag,gk]
  have ha : m.ha+l*m.ka=m.hb+l*m.kb := by nlinarith only [af,ak,he]
  have dh := w.bd_h
  rw [q.b,q.g] at dh
  have dk := mul_le_mul_of_nonneg_left w.bd_k hl
  have hd : m.hg+l*m.kg ≤ m.hb+l*m.kb := by nlinarith only [dh,dk]
  exact ⟨ha,he,hg,hd⟩

theorem projected_zero_k (m : Data) (w : Weak m) (ex : ExactSwaps m)
    (l : ℝ) (hl : 0 < l) (q : QForm m l)
    (hbound : 2*(m.ha+l*m.ka) ≤ m.hf+l*m.kf) :
    m.ka=0 ∧ m.kb=0 ∧ m.ke=0 ∧ m.kf=0 ∧ m.kg=0 := by
  obtain ⟨ab,ef,gf,bd⟩ := projected_equalities m w ex l (le_of_lt hl) q
  have an := add_nonneg w.ha (mul_nonneg (le_of_lt hl) w.ka)
  have bn := add_nonneg w.hb (mul_nonneg (le_of_lt hl) w.kb)
  have en := add_nonneg w.he (mul_nonneg (le_of_lt hl) w.ke)
  have fn := add_nonneg w.hf (mul_nonneg (le_of_lt hl) w.kf)
  have gn := add_nonneg w.hg (mul_nonneg (le_of_lt hl) w.kg)
  have az : m.ha+l*m.ka=0 := by linarith only [ab,ef,gf,bd,hbound,an,fn]
  have bz : m.hb+l*m.kb=0 := by linarith only [ab,az]
  have fz : m.hf+l*m.kf=0 := by linarith only [ab,gf,bd,az,fn]
  have ez : m.he+l*m.ke=0 := by linarith only [ef,fz]
  have gz : m.hg+l*m.kg=0 := by linarith only [gf,fz]
  exact ⟨by nlinarith only [az,w.ha,w.ka,hl],
    by nlinarith only [bz,w.hb,w.kb,hl],
    by nlinarith only [ez,w.he,w.ke,hl],
    by nlinarith only [fz,w.hf,w.kf,hl],
    by nlinarith only [gz,w.hg,w.kg,hl]⟩

theorem fixed_form_zero_k (m : Data) (w : Weak m) (ex : ExactSwaps m)
    (l u : ℝ) (hl : 0 < l) (hu : 0 ≤ u)
    (q : QForm m l) (k : KForm m u) :
    m.ka=0 ∧ m.kb=0 ∧ m.ke=0 ∧ m.kf=0 ∧ m.kg=0 := by
  apply projected_zero_k m w ex l hl q
  have ch := w.cf_h
  have cq := mul_le_mul_of_nonneg_left w.cf_q hu
  rw [q.a,k.a,k.f] at ch
  rw [q.a,q.f] at cq
  rw [k.a,k.f]
  nlinarith only [ch,cq]

theorem matching_boundary_zero_k (m : Data) (w : Weak m) (ex : ExactSwaps m)
    (l : ℝ) (hl : 0 < l) (q : QForm m l) (hc : m.kap=l) :
    m.ka=0 ∧ m.kb=0 ∧ m.ke=0 ∧ m.kf=0 ∧ m.kg=0 := by
  apply projected_zero_k m w ex l hl q
  have ch := w.cf_h
  rw [q.a,hc] at ch
  nlinarith only [ch]

end CollatzResearch.FullTwoUpper
