import FullTwoUpperBasic
import FullTwoLowerScalar

namespace CollatzResearch.FullTwoUpper

set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

theorem q_zero_gaps (m : Data) (w : Weak m)
    (qa0 : m.qa=0) (qb0 : m.qb=0) (qe0 : m.qe=0)
    (qf0 : m.qf=0) (qg0 : m.qg=0) : ZeroGaps m := by
  have za := w.za
  have zb := w.zb
  have ze := w.ze
  have zf := w.zf
  have zg := w.zg
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
  simp only [qa0,qb0,qe0,qf0,qg0,mul_zero,zero_mul,add_zero,zero_add] at za zb ze zf zg qa qb qe qf qg ha hb he hf hg ka kb ke kf kg kap tau af_z ag_z be_z bf_z ae_q af_q ag_q be_q bf_q bg_q ae_k af_k ag_k be_k bf_k bg_k ae_h af_h ag_h be_h bf_h bg_h ad_k bd_k ad_h bd_h ce_q cf_q cg_q ce_h cf_h cg_h
  have hb0 : m.hb=m.ha := by linarith only [af_h,ag_h,be_h,bf_h]
  have hf0 : m.hf=m.he := by linarith only [af_h,ag_h,be_h,bf_h]
  have hg0 : m.hg=m.he := by linarith only [af_h,ag_h,be_h,bf_h]
  simp only [hb0,hf0,hg0] at za zb ze zf zg qa qb qe qf qg ha hb he hf hg ka kb ke kf kg kap tau af_z ag_z be_z bf_z ae_q af_q ag_q be_q bf_q bg_q ae_k af_k ag_k be_k bf_k bg_k ae_h af_h ag_h be_h bf_h bg_h ad_k bd_k ad_h bd_h ce_q cf_q cg_q ce_h cf_h cg_h
  have heha : m.he ≤ m.ha := bd_h
  have hz : m.ha=0 ∧ m.he=0 ∧
      m.kap*m.ke=m.kap*m.kb ∧
      m.kap*m.kf=m.kap*(m.ka+m.za*m.ka) ∧
      m.kap*m.kg=m.kap*(m.ka+m.za*m.kb) := by
    by_cases hk : m.kap=0
    · simp only [hk,zero_mul,add_zero] at ce_h cf_h cg_h
      have ha0 : m.ha=0 := by linarith only [ha,he,heha,cf_h]
      have he0 : m.he=0 := by linarith only [he,heha,ha0]
      exact ⟨ha0,he0,by simp [hk],by simp [hk],by simp [hk]⟩
    · have kp : 0 < m.kap := lt_of_le_of_ne kap (Ne.symm hk)
      have ez : m.zb ≤ m.ze := by nlinarith only [ce_q,kp]
      have fz : m.za*m.za ≤ m.zf := by
        exact le_of_mul_le_mul_left cf_q kp
      have ek : m.kb ≤ m.ke := by nlinarith only [ce_h,heha,kp]
      have fk : m.za*m.ka+m.ka ≤ m.kf := by
        have hh : m.kap*(m.za*m.ka+m.ka) ≤ m.kap*m.kf := by
          nlinarith only [cf_h,heha,ha]
        exact le_of_mul_le_mul_left hh kp
      have gk : m.za*m.kb+m.ka ≤ m.kg := by
        have hh : m.kap*(m.za*m.kb+m.ka) ≤ m.kap*m.kg := by
          nlinarith only [cg_h,heha,ha]
        exact le_of_mul_le_mul_left hh kp
      have sw : FullTwoLowerScalar.ForwardWeak m.za m.zb m.ze m.zf m.zg
          m.ka m.kb m.ke m.kf m.kg m.tau :=
        ⟨za,zb,ze,zf,zg,ka,kb,ke,kf,kg,tau,ez,fz,af_z,ag_z,be_z,bf_z,
         bd_k,by linarith only [ae_k],by linarith only [af_k],
         by linarith only [ag_k],by linarith only [be_k],by linarith only [bf_k],ek,fk,gk⟩
      obtain ⟨ek0,fk0,gk0⟩ := FullTwoLowerScalar.forward_gaps_zero sw
      have fk' : m.kap*m.kf=m.kap*(m.ka+m.za*m.ka) := by rw [fk0]; ring
      have gk' : m.kap*m.kg=m.kap*(m.ka+m.za*m.kb) := by rw [gk0]; ring
      have ha0 : m.ha=0 := by nlinarith only [cf_h,fk',heha,ha]
      have he0 : m.he=0 := by linarith only [he,heha,ha0]
      exact ⟨ha0,he0,by rw [ek0],fk',gk'⟩
  obtain ⟨ha0,he0,ke0,kf0,kg0⟩ := hz
  constructor <;> simp only [qa0,qb0,qe0,qf0,qg0,hb0,hf0,hg0,ha0,he0,
    mul_zero,zero_mul,add_zero,zero_add] <;> assumption

theorem k_zero_gaps (m : Data) (w : Weak m)
    (ka0 : m.ka=0) (kb0 : m.kb=0) (ke0 : m.ke=0)
    (kf0 : m.kf=0) (kg0 : m.kg=0) : ZeroGaps m := by
  have za := w.za
  have zb := w.zb
  have ze := w.ze
  have zf := w.zf
  have zg := w.zg
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
  simp only [ka0,kb0,ke0,kf0,kg0,mul_zero,zero_mul,add_zero,zero_add] at za zb ze zf zg qa qb qe qf qg ha hb he hf hg ka kb ke kf kg kap tau af_z ag_z be_z bf_z ae_q af_q ag_q be_q bf_q bg_q ae_k af_k ag_k be_k bf_k bg_k ae_h af_h ag_h be_h bf_h bg_h ad_k bd_k ad_h bd_h ce_q cf_q cg_q ce_h cf_h cg_h
  have hb0 : m.hb=m.ha := by linarith only [af_h,ag_h,be_h,bf_h]
  have hf0 : m.hf=m.he := by linarith only [af_h,ag_h,be_h,bf_h]
  have hg0 : m.hg=m.he := by linarith only [af_h,ag_h,be_h,bf_h]
  simp only [hb0,hf0,hg0] at za zb ze zf zg qa qb qe qf qg ha hb he hf hg ka kb ke kf kg kap tau af_z ag_z be_z bf_z ae_q af_q ag_q be_q bf_q bg_q ae_k af_k ag_k be_k bf_k bg_k ae_h af_h ag_h be_h bf_h bg_h ad_k bd_k ad_h bd_h ce_q cf_q cg_q ce_h cf_h cg_h
  have hz : m.ha=0 ∧ m.he=0 ∧ m.qa*m.tau=0 ∧ m.qb*m.tau=m.qg*m.tau := by
    by_cases ht : m.tau=0
    · simp only [ht,mul_zero,zero_add] at bd_h
      have ha0 : m.ha=0 := by linarith only [ha,he,cf_h,bd_h]
      have he0 : m.he=0 := by linarith only [he,ha0,bd_h]
      exact ⟨ha0,he0,by simp [ht],by simp [ht]⟩
    · have tp : 0 < m.tau := lt_of_le_of_ne tau (Ne.symm ht)
      have az : 1 ≤ m.za := by nlinarith only [ad_k,tp]
      have bz : m.zg ≤ m.zb := le_of_mul_le_mul_right bd_k tp
      have bq : m.qg ≤ m.qb := by nlinarith only [bd_h,cf_h,ha,tp]
      obtain ⟨aq0,bq0⟩ := FullTwoLowerScalar.reversed_gaps_zero
        m.za m.zb m.zf m.zg m.qa m.qb m.qf m.qg m.kap
        az zb zf zg qa qb qf qg kap bz bq
        (by nlinarith only [ag_z]) (by nlinarith only [cg_q]) (by nlinarith only [ag_q]) (by nlinarith only [bf_q])
      have bt : m.qb*m.tau=m.qg*m.tau := by rw [bq0]
      have ha0 : m.ha=0 := by nlinarith only [ha,he,cf_h,bd_h,bt]
      have he0 : m.he=0 := by nlinarith only [he,ha0,bd_h,bt]
      exact ⟨ha0,he0,by rw [aq0,zero_mul],bt⟩
  obtain ⟨ha0,he0,qat,qbt⟩ := hz
  constructor <;> simp only [ka0,kb0,ke0,kf0,kg0,hb0,hf0,hg0,ha0,he0,
    mul_zero,zero_mul,add_zero,zero_add,qat,qbt]

#print axioms q_zero_gaps
#print axioms k_zero_gaps

end CollatzResearch.FullTwoUpper
