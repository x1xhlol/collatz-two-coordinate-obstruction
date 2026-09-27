import FullTwoUpperAlgebra
import FullTwoUpperDegenerate

namespace CollatzResearch.FullTwoUpper

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

theorem zero_a_large_b_q (m : Data) (w : Weak m) (az : m.za=0) (bh : 1 < m.zb) :
    m.qa=0 ∧ m.qb=0 ∧ m.qe=0 ∧ m.qf=0 ∧ m.qg=0 := by
  obtain ⟨af,_,be,_⟩ := slope_equalities m w
  rw [az,zero_mul] at af
  have ez : m.ze=0 := (mul_eq_zero.mp af.symm).resolve_right (by linarith)
  have fz : m.zf=0 := by rw [ez,mul_zero] at be; nlinarith only [be,bh]
  have fq := w.af_q
  have eq := w.be_q
  have aq := w.ae_q
  have gq := w.bg_q
  rw [fz,mul_zero,add_zero] at fq
  rw [ez,mul_zero,add_zero] at eq
  have pe : m.qe+m.qf=0 := by
    nlinarith only [fq,eq,bh,w.qb,w.qe,w.qf]
  have qe : m.qe=0 := by linarith only [pe,w.qe,w.qf]
  have qf : m.qf=0 := by linarith only [pe,w.qe,w.qf]
  have qb : m.qb=0 := by rw [qe,qf,zero_mul,add_zero] at fq; linarith only [fq,w.qb]
  have qa : m.qa=0 := by simp only [az,ez,qe,mul_zero,zero_mul,add_zero,zero_add] at aq; linarith only [aq,w.qa]
  have qg : m.qg=0 := by rw [qb,zero_mul,add_zero,zero_add] at gq; nlinarith only [gq,bh,w.qg]
  exact ⟨qa,qb,qe,qf,qg⟩

theorem zero_b_large_a_q (m : Data) (w : Weak m) (bz : m.zb=0) (ah : 1 < m.za) :
    m.qa=0 ∧ m.qb=0 ∧ m.qe=0 ∧ m.qf=0 ∧ m.qg=0 := by
  obtain ⟨af,ag,_,bf⟩ := slope_equalities m w
  rw [bz,mul_zero] at af
  have fz : m.zf=0 := (mul_eq_zero.mp af).resolve_left (by linarith)
  have gz : m.zg=0 := by rw [fz,zero_mul] at ag; nlinarith only [ag,ah]
  have gq := w.ag_q
  have fq := w.bf_q
  have bq := w.af_q
  have eq := w.ae_q
  rw [gz,mul_zero,add_zero] at gq
  rw [fz,mul_zero,add_zero] at fq
  have pf : m.qf+m.qg=0 := by
    nlinarith only [gq,fq,ah,w.qa,w.qf,w.qg]
  have qf : m.qf=0 := by linarith only [pf,w.qf,w.qg]
  have qg : m.qg=0 := by linarith only [pf,w.qf,w.qg]
  have qa : m.qa=0 := by rw [qf,qg,zero_mul,add_zero] at gq; linarith only [gq,w.qa]
  have qb : m.qb=0 := by rw [bz,fz,qf,mul_zero,add_zero] at bq; linarith only [bq,w.qb]
  have qe : m.qe=0 := by rw [qa,zero_mul,zero_add,add_zero] at eq; nlinarith only [eq,ah,w.qe]
  exact ⟨qa,qb,qe,qf,qg⟩

theorem zero_a_exact_zero_k (m : Data) (w : Weak m) (ex : ExactSwaps m)
    (az : m.za=0) (bp : 0 < m.zb)
    (qpos : 0 < m.qa+m.qb+(m.qe+m.qf+m.qg)) :
    m.ka=0 ∧ m.kb=0 ∧ m.ke=0 ∧ m.kf=0 ∧ m.kg=0 := by
  obtain ⟨af,_,be,_⟩ := slope_equalities m w
  rw [az,zero_mul] at af
  have ez : m.ze=0 := (mul_eq_zero.mp af.symm).resolve_right (ne_of_gt bp)
  have fz : m.zf=0 := by rw [ez,mul_zero] at be; nlinarith only [be,bp]
  have aq := ex.ae_q
  have fq := ex.af_q
  have bq := ex.be_q
  have gq := ex.ag_q
  simp only [az,ez,fz,mul_zero,zero_mul,add_zero,zero_add] at aq fq bq gq
  have qe : m.qe=m.qa := by linarith only [aq]
  have qf : m.qf=m.qa := by
    rw [qe] at fq bq
    have hx : (1+m.zb)*(m.qf-m.qa)=0 := by nlinarith only [fq,bq]
    have := (mul_eq_zero.mp hx).resolve_left (by linarith)
    linarith
  have qb : m.qb=m.qa*(1-m.zb) := by rw [qe,qf] at fq; nlinarith only [fq]
  have qg : m.qg=m.qa*(1-m.zg) := by nlinarith only [gq]
  have qform : QForm m m.qa :=
    ⟨by simp [az],qb,by simp [ez,qe],by simp [fz,qf],qg⟩
  have qp := q_form_parameter_pos m m.qa w.qa qform qpos
  have ak := ex.ae_k
  have fk := ex.ag_k
  have bk := ex.be_k
  have gk := ex.bf_k
  simp only [az,ez,fz,mul_zero,zero_mul,add_zero,zero_add] at ak fk bk gk
  have ke : m.ke=m.ka := ak
  have kf : m.kf=m.ka := fk
  have kb : m.kb=m.ka*(1-m.zb) := by rw [ke,kf] at bk; nlinarith only [bk]
  have kg : m.kg=m.ka*(1-m.zg) := by rw [kb,kf] at gk; nlinarith only [gk]
  have kform : KForm m m.ka :=
    ⟨by simp [az],kb,by simp [ez,ke],by simp [fz,kf],kg⟩
  exact fixed_form_zero_k m w ex m.qa m.ka qp w.ka qform kform

theorem zero_b_exact_zero_k (m : Data) (w : Weak m) (ex : ExactSwaps m)
    (bz : m.zb=0) (ap : 0 < m.za)
    (qpos : 0 < m.qa+m.qb+(m.qe+m.qf+m.qg)) :
    m.ka=0 ∧ m.kb=0 ∧ m.ke=0 ∧ m.kf=0 ∧ m.kg=0 := by
  obtain ⟨af,ag,_,_⟩ := slope_equalities m w
  rw [bz,mul_zero] at af
  have fz : m.zf=0 := (mul_eq_zero.mp af).resolve_left (ne_of_gt ap)
  have gz : m.zg=0 := by rw [fz,zero_mul] at ag; nlinarith only [ag,ap]
  have fq := ex.af_q
  have gq := ex.ag_q
  have bq := ex.bf_q
  have eq := ex.be_q
  simp only [bz,fz,gz,mul_zero,zero_mul,add_zero,zero_add] at fq gq bq eq
  have qf : m.qf=m.qb := fq.symm
  have qg : m.qg=m.qb := by
    rw [qf] at gq bq
    have hx : (1+m.za)*(m.qg-m.qb)=0 := by nlinarith only [gq,bq]
    have := (mul_eq_zero.mp hx).resolve_left (by linarith)
    linarith
  have qa : m.qa=m.qb*(1-m.za) := by rw [qf,qg] at gq; nlinarith only [gq]
  have qe : m.qe=m.qb*(1-m.ze) := by nlinarith only [eq]
  have qform : QForm m m.qb :=
    ⟨qa,by simp [bz],qe,by simp [fz,qf],by simp [gz,qg]⟩
  have qp := q_form_parameter_pos m m.qb w.qb qform qpos
  have fk := ex.be_k
  have gk := ex.bf_k
  have ak := ex.ag_k
  have ek := ex.af_k
  simp only [bz,fz,gz,mul_zero,zero_mul,add_zero,zero_add] at fk gk ak ek
  have kf : m.kf=m.kb := fk
  have kg : m.kg=m.kb := gk
  have ka : m.ka=m.kb*(1-m.za) := by rw [kf,kg] at ak; nlinarith only [ak]
  have ke : m.ke=m.kb*(1-m.ze) := by rw [ka,kf] at ek; nlinarith only [ek]
  have kform : KForm m m.kb :=
    ⟨ka,by simp [bz],ke,by simp [fz,kf],by simp [gz,kg]⟩
  exact fixed_form_zero_k m w ex m.qb m.kb qp w.kb qform kform


theorem both_zero_exact_zero_k (m : Data) (w : Weak m) (ex : ExactSwaps m)
    (az : m.za=0) (bz : m.zb=0)
    (qpos : 0 < m.qa+m.qb+(m.qe+m.qf+m.qg)) :
    m.ka=0 ∧ m.kb=0 ∧ m.ke=0 ∧ m.kf=0 ∧ m.kg=0 := by
  have aq := ex.ae_q
  have fq := ex.af_q
  have xq := ex.bf_q
  have gq := ex.bg_q
  simp only [az,bz,mul_zero,zero_mul,add_zero,zero_add] at aq fq xq gq
  have qb : m.qb=m.qa := by
    have hx : (1+m.zf)*(m.qa-m.qb)=0 := by nlinarith only [fq,xq]
    have hp : 0 < 1+m.zf := by linarith only [w.zf]
    have := (mul_eq_zero.mp hx).resolve_left (ne_of_gt hp)
    linarith
  have qe : m.qe=m.qa*(1-m.ze) := by nlinarith only [aq]
  have qf : m.qf=m.qa*(1-m.zf) := by nlinarith only [fq,qb]
  have qg : m.qg=m.qa*(1-m.zg) := by rw [qb] at gq; nlinarith only [gq]
  have qform : QForm m m.qa :=
    ⟨by simp [az],by simp [bz,qb],qe,qf,qg⟩
  have qp := q_form_parameter_pos m m.qa w.qa qform qpos
  have ak := ex.ae_k
  have fk := ex.af_k
  have gk := ex.ag_k
  have ek := ex.be_k
  have xk := ex.bf_k
  have bk := ex.bg_k
  simp only [az,bz,mul_zero,zero_mul,add_zero,zero_add] at ak fk gk ek xk bk
  by_cases kab : m.ka=m.kb
  · have ke : m.ke=m.ka*(1-m.ze) := by nlinarith only [ak]
    have kf : m.kf=m.ka*(1-m.zf) := by nlinarith only [gk]
    have kg : m.kg=m.ka*(1-m.zg) := by rw [← kab] at bk; nlinarith only [bk]
    have kform : KForm m m.ka :=
      ⟨by simp [az],by simp [bz,kab],ke,kf,kg⟩
    exact fixed_form_zero_k m w ex m.qa m.ka qp w.ka qform kform
  · have hd : m.ka-m.kb ≠ 0 := sub_ne_zero.mpr kab
    have he : m.ze*(m.ka-m.kb)=0 := by nlinarith only [ak,fk]
    have hf : (1-m.zf)*(m.ka-m.kb)=0 := by nlinarith only [gk,ek]
    have hg : m.zg*(m.ka-m.kb)=0 := by nlinarith only [xk,bk]
    have ez : m.ze=0 := (mul_eq_zero.mp he).resolve_right hd
    have fz : m.zf=1 := by
      have := (mul_eq_zero.mp hf).resolve_right hd
      linarith
    have gz : m.zg=0 := (mul_eq_zero.mp hg).resolve_right hd
    have kfz : m.kf=0 := by rw [fz,one_mul] at gk; linarith only [gk]
    have qfz : m.qf=0 := by rw [fz] at qf; nlinarith only [qf]
    have cq := w.cf_q
    rw [az,fz,qfz,mul_zero,mul_one,add_zero,zero_mul,zero_add] at cq
    apply projected_zero_k m w ex m.qa qp qform
    have ch := w.cf_h
    rw [az,kfz,mul_zero,zero_mul,add_zero] at ch
    rw [kfz,mul_zero,add_zero]
    nlinarith only [ch,mul_nonneg (sub_nonneg.mpr cq) w.ka]

theorem zero_binary_zero_gaps (m : Data) (w : Weak m)
    (hzero : m.za=0 ∨ m.zb=0) : ZeroGaps m := by
  by_cases hq : 0 < m.qa+m.qb+(m.qe+m.qf+m.qg)
  swap
  · have a : m.qa=0 := by linarith only [hq,w.qa,w.qb,w.qe,w.qf,w.qg]
    have b : m.qb=0 := by linarith only [hq,w.qa,w.qb,w.qe,w.qf,w.qg]
    have e : m.qe=0 := by linarith only [hq,w.qa,w.qb,w.qe,w.qf,w.qg]
    have f : m.qf=0 := by linarith only [hq,w.qa,w.qb,w.qe,w.qf,w.qg]
    have g : m.qg=0 := by linarith only [hq,w.qa,w.qb,w.qe,w.qf,w.qg]
    exact q_zero_gaps m w a b e f g
  by_cases hk : 0 < m.ka+m.kb+(m.ke+m.kf+m.kg)
  swap
  · have a : m.ka=0 := by linarith only [hk,w.ka,w.kb,w.ke,w.kf,w.kg]
    have b : m.kb=0 := by linarith only [hk,w.ka,w.kb,w.ke,w.kf,w.kg]
    have e : m.ke=0 := by linarith only [hk,w.ka,w.kb,w.ke,w.kf,w.kg]
    have f : m.kf=0 := by linarith only [hk,w.ka,w.kb,w.ke,w.kf,w.kg]
    have g : m.kg=0 := by linarith only [hk,w.ka,w.kb,w.ke,w.kf,w.kg]
    exact k_zero_gaps m w a b e f g
  rcases hzero with az | bz
  · by_cases bh : 1 < m.zb
    · obtain ⟨a,b,e,f,g⟩ := zero_a_large_b_q m w az bh
      exact q_zero_gaps m w a b e f g
    · have ex := exact_of_negative m w (Or.inl (by rw [az]; linarith)) hq hk
      by_cases bz : m.zb=0
      · obtain ⟨a,b,e,f,g⟩ := both_zero_exact_zero_k m w ex az bz hq
        exact k_zero_gaps m w a b e f g
      · have bp : 0 < m.zb := lt_of_le_of_ne w.zb (Ne.symm bz)
        obtain ⟨a,b,e,f,g⟩ := zero_a_exact_zero_k m w ex az bp hq
        exact k_zero_gaps m w a b e f g
  · by_cases ah : 1 < m.za
    · obtain ⟨a,b,e,f,g⟩ := zero_b_large_a_q m w bz ah
      exact q_zero_gaps m w a b e f g
    · have ex := exact_of_negative m w (Or.inl (by rw [bz]; linarith)) hq hk
      by_cases az : m.za=0
      · obtain ⟨a,b,e,f,g⟩ := both_zero_exact_zero_k m w ex az bz hq
        exact k_zero_gaps m w a b e f g
      · have ap : 0 < m.za := lt_of_le_of_ne w.za (Ne.symm az)
        obtain ⟨a,b,e,f,g⟩ := zero_b_exact_zero_k m w ex bz ap hq
        exact k_zero_gaps m w a b e f g

#print axioms zero_binary_zero_gaps

end CollatzResearch.FullTwoUpper
