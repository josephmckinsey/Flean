import Flean.FloatCfg
import Flean.Subnorm
import Flean.FloatRep

variable {C : FloatCfg}

def to_float (q : ℚ) : Flean.Float C :=
  match sem_def : (round_down q : FloatRep C) with
  | ⟨s, e, m⟩ =>
  if q_nonneg : q = 0 then
    Flean.Float.subnormal false 0 (C.prec_pos)
  else if h : e < C.emin then
    let sm := subnormal_round_nearest q
    if h_eq_prec : sm.2 = C.prec then by
      refine Flean.Float.normal s (C.emin + 1) 0 ?_
      refine ⟨by linarith, by linarith [C.emin_lt_emax], by linarith [C.prec_pos]⟩
    else by
      refine Flean.Float.subnormal sm.1 sm.2 ?_
      · have : e = (round_down q : FloatRep C).e := by
          rw [sem_def]
        have : Int.log 2 |q| = e := by
          rw [this, round_down]
        refine lt_of_le_of_ne ?_ h_eq_prec
        apply subnormal_round_nearest_valid q q_nonneg
        rw [this]
        exact h
  else if h' : e > C.emax then
    Flean.Float.inf s
  else by
    refine Flean.Float.normal s e m ?_
    refine ⟨Int.not_lt.mp h, Int.not_lt.mp h', ?_⟩
    have : m = (round_down q : FloatRep C).m := by
      rw [sem_def]
    rw [this]
    exact round_down_valid q (q_nonneg)


def to_rat : Flean.Float C → ℚ
| Flean.Float.inf _ => 0
| Flean.Float.nan => 0
| Flean.Float.normal s e m _ => coe_q (⟨s, e, m⟩ : FloatRep C)
| Flean.Float.subnormal s m _ => subnormal_to_q (⟨s, m⟩ : SubnormRep C)


def IsFinite : Flean.Float C → Prop
| Flean.Float.inf _ => false
| Flean.Float.nan => false
| _ => true

def IsZero : Flean.Float C → Prop
| Flean.Float.subnormal _ 0 _ => true
| _ => false


def DoubleCfg : FloatCfg := FloatCfg.mk (1 <<< 52) (-1022) 1023 (by norm_num) (
  Nat.zero_lt_succ 4503599627370495
)


def frep : FloatCfg := FloatCfg.mk 256 (-127) 127 (by norm_num) (by norm_num)

def frep64 := FloatRep frep

#eval ((@round_down frep 3.5) : frep64)
#check (round_down 3.5 : frep64)
#check (coe_q (⟨false, 0, 0⟩ : frep64))
--#eval @to_rat C (@to_float C 3.528123042)
--#eval @coe_q C (@round_down C 3.5)
--#eval @round_down C 0


-- Ideally I'd like to prove it for all FloatRep's with the corresponding
--
