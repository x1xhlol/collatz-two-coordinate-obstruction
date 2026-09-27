import FullTwoUpperBasic

namespace CollatzResearch.FullTwoUpper

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

theorem unit_zero_gaps (m : Data) (w : Weak m)
    (za : m.za = 1) (zb : m.zb = 1) (ze : m.ze = 1)
    (zf : m.zf = 1) (zg : m.zg = 1) : ZeroGaps m := by
  have qa := w.qa
  have qb := w.qb
  have qe := w.qe
  have qf := w.qf
  have qg := w.qg
  have ha := w.ha
  have hb := w.hb
  have he := w.he
  have hf := w.hf
  have hg := w.hg
  have ka := w.ka
  have kb := w.kb
  have ke := w.ke
  have kf := w.kf
  have kg := w.kg
  have kap := w.kap
  have tau := w.tau
  have af_z := w.af_z
  have ag_z := w.ag_z
  have be_z := w.be_z
  have bf_z := w.bf_z
  have ae_q := w.ae_q
  have af_q := w.af_q
  have ag_q := w.ag_q
  have be_q := w.be_q
  have bf_q := w.bf_q
  have bg_q := w.bg_q
  have ae_k := w.ae_k
  have af_k := w.af_k
  have ag_k := w.ag_k
  have be_k := w.be_k
  have bf_k := w.bf_k
  have bg_k := w.bg_k
  have ae_h := w.ae_h
  have af_h := w.af_h
  have ag_h := w.ag_h
  have be_h := w.be_h
  have bf_h := w.bf_h
  have bg_h := w.bg_h
  have ad_k := w.ad_k
  have bd_k := w.bd_k
  have ad_h := w.ad_h
  have bd_h := w.bd_h
  have ce_q := w.ce_q
  have cf_q := w.cf_q
  have cg_q := w.cg_q
  have ce_h := w.ce_h
  have cf_h := w.cf_h
  have cg_h := w.cg_h
  simp only [za,zb,ze,zf,zg,mul_one,one_mul] at qa qb qe qf qg ha hb he hf hg ka kb ke kf kg kap tau af_z ag_z be_z bf_z ae_q af_q ag_q be_q bf_q bg_q ae_k af_k ag_k be_k bf_k bg_k ae_h af_h ag_h be_h bf_h bg_h ad_k bd_k ad_h bd_h ce_q cf_q cg_q ce_h cf_h cg_h
  have qb0 : m.qb = m.qa := by linarith only [ae_q,af_q,ag_q,be_q,bf_q,bg_q]
  have qf0 : m.qf = m.qe := by linarith only [ae_q,af_q,ag_q,be_q,bf_q,bg_q]
  have qg0 : m.qg = m.qe := by linarith only [ae_q,af_q,ag_q,be_q,bf_q,bg_q]
  have kb0 : m.kb = m.ka := by linarith only [ae_k,af_k,ag_k,be_k,bf_k,bg_k]
  have kf0 : m.kf = m.ke := by linarith only [ae_k,af_k,ag_k,be_k,bf_k,bg_k]
  have kg0 : m.kg = m.ke := by linarith only [ae_k,af_k,ag_k,be_k,bf_k,bg_k]
  simp only [qb0,qf0,qg0,kb0,kf0,kg0] at qa qb qe qf qg ha hb he hf hg ka kb ke kf kg kap tau af_z ag_z be_z bf_z ae_q af_q ag_q be_q bf_q bg_q ae_k af_k ag_k be_k bf_k bg_k ae_h af_h ag_h be_h bf_h bg_h ad_k bd_k ad_h bd_h ce_q cf_q cg_q ce_h cf_h cg_h
  have shear : 2*m.qa ≤ m.qe := by linarith only [cf_q]
  have offs : m.ke ≤ m.ka := by linarith only [bd_k]
  have cross : m.qe*m.ka ≤ m.qa*m.ke := by
    linarith only [ae_h]
  have c1 := mul_nonneg (sub_nonneg.mpr shear) ka
  have c2 := mul_nonneg qa (sub_nonneg.mpr offs)
  have c3 := mul_nonneg qa ke
  have c4 := mul_nonneg qe ka
  have qake : m.qa*m.ke=0 := by nlinarith only [cross,c1,c2,c3,c4]
  have qeka : m.qe*m.ka=0 := by nlinarith only [cross,qake,c4]
  have qaka : m.qa*m.ka=0 := by nlinarith only [qeka,c1,mul_nonneg qa ka]
  have qeke : m.qe*m.ke=0 := by
    nlinarith only [qeka,mul_nonneg qe (sub_nonneg.mpr offs),mul_nonneg qe ke]
  simp only [qake,qeka,qaka,qeke] at qa qb qe qf qg ha hb he hf hg ka kb ke kf kg kap tau af_z ag_z be_z bf_z ae_q af_q ag_q be_q bf_q bg_q ae_k af_k ag_k be_k bf_k bg_k ae_h af_h ag_h be_h bf_h bg_h ad_k bd_k ad_h bd_h ce_q cf_q cg_q ce_h cf_h cg_h
  have hb0 : m.hb=m.ha := by linarith only [af_h,ag_h,be_h,bf_h]
  have hf0 : m.hf=m.he := by linarith only [af_h,ag_h,be_h,bf_h]
  have hg0 : m.hg=m.he := by linarith only [af_h,ag_h,be_h,bf_h]
  simp only [hb0,hf0,hg0] at qa qb qe qf qg ha hb he hf hg ka kb ke kf kg kap tau af_z ag_z be_z bf_z ae_q af_q ag_q be_q bf_q bg_q ae_k af_k ag_k be_k bf_k bg_k ae_h af_h ag_h be_h bf_h bg_h ad_k bd_k ad_h bd_h ce_q cf_q cg_q ce_h cf_h cg_h
  have kt : 0 ≤ m.kap*(m.ka-m.ke) := mul_nonneg kap (sub_nonneg.mpr offs)
  have qt : 0 ≤ (m.qe-m.qa)*m.tau :=
    mul_nonneg (by linarith only [shear,qa]) tau
  have hh : m.ha=m.he := by nlinarith only [bd_h,ce_h,kt,qt]
  have qt0 : (m.qe-m.qa)*m.tau=0 := by nlinarith only [hh,bd_h,qt]
  have kr : 0 ≤ m.kap*m.ka := mul_nonneg kap ka
  have ku : 0 ≤ m.kap*m.ke := mul_nonneg kap ke
  have ha0 : m.ha=0 := by nlinarith only [hh,cf_h,ha,kr,ku,kt]
  have he0 : m.he=0 := by linarith only [hh,ha0]
  have kr0 : m.kap*m.ka=0 := by nlinarith only [hh,cf_h,ha0,kr,ku,kt]
  have ku0 : m.kap*m.ke=0 := by nlinarith only [kt,kr0,ku]
  have qat : m.qa*m.tau=0 := by
    nlinarith only [qt0,mul_nonneg (sub_nonneg.mpr shear) tau,mul_nonneg qa tau]
  have qet : m.qe*m.tau=0 := by nlinarith only [qt0,qat]
  constructor <;> simp only [za,zb,ze,zf,zg,mul_one,one_mul,qb0,qf0,qg0,kb0,kf0,kg0,
    hb0,hf0,hg0,ha0,he0,qake,qeka,qaka,qeke,kr0,ku0,qat,qet] <;>
    nlinarith only [kr0,ku0]

#print axioms unit_zero_gaps

end CollatzResearch.FullTwoUpper
