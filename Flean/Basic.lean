import Flean.FloatCfg
import Flean.Subnorm
import Flean.FloatRep

variable {C : FloatCfg}

def subnormal_round [R : Rounding] (q : ℚ) : SubnormRep C :=
  match R.mode with
  | RoundingMode.nearest => subnormal_round_nearest q
  | RoundingMode.down => subnormal_round_down q
  | RoundingMode.up => subnormal_round_up q

def subnormal_round_valid [R : Rounding] :
  ValidSubnormalRounding (subnormal_round : ℚ → SubnormRep C) := by
  unfold subnormal_round
  split
  · exact subnormal_round_nearest_valid
  · exact subnormal_round_down_valid
  exact subnormal_round_up_valid

def round_rep [R : Rounding] (q : ℚ) : FloatRep C :=
  match R.mode with
  | RoundingMode.nearest => round_nearest q
  | RoundingMode.down => round_down q
  | RoundingMode.up => round_up q

def FloatRep.valid_e (f : FloatRep C) : Prop := C.emin ≤ f.e ∧ f.e ≤ C.emax

inductive Flean.Float (C : FloatCfg) where
  | inf : Bool → Float C
  | nan : Float C
  | normal : (f : FloatRep C) → f.valid_e → f.valid_m → Float C
  | subnormal : Bool → ∀ m, m < C.prec → Float C

lemma round_valid_m [R : Rounding] (q : ℚ) (q_nezero: q ≠ 0) :
  (round_rep q : FloatRep C).valid_m := by
  unfold round_rep
  split
  · exact round_nearest_valid q q_nezero
  · exact round_down_valid q q_nezero
  exact round_up_valid q q_nezero

lemma round_min_e [R : Rounding] (q : ℚ) :
  Int.log 2 |q| ≤ (round_rep q : FloatRep C).e := by
  suffices Int.log 2 |q| ≤ (round_up q : FloatRep C).e ∧
    Int.log 2 |q| ≤ (round_down q : FloatRep C).e by
    unfold round_rep
    split <;> (try exact this.1; try exact this.2)
    rcases round_nearest_eq_or q with h | h <;> rw [h]
    · exact this.2
    · exact this.1
    exact this.2
  refine ⟨?_, by simp [round_down]⟩
  rw [round_up]
  split <;> simp


def to_float [R : Rounding] (q : ℚ) : Flean.Float C :=
  if q_nonneg : q = 0 then
    Flean.Float.subnormal false 0 (C.prec_pos)
  else if h : Int.log 2 |q| < C.emin then
    let sp := subnormal_round q
    if h_eq_prec : sp.2 = C.prec then by
      refine Flean.Float.normal ⟨q < 0, C.emin + 1, 0⟩ ?_ ?_
      <;> simp only [FloatRep.valid_e, FloatRep.valid_m]
      · refine ⟨by linarith, by linarith [C.emin_lt_emax]⟩
      linarith [C.prec_pos]
    else by
      refine Flean.Float.subnormal sp.1 sp.2 ?_
      · refine lt_of_le_of_ne ?_ h_eq_prec
        apply subnormal_round_valid q q_nonneg
        exact h
  else match sem_def : round_rep q with
  | (⟨s, e, m⟩ : FloatRep C) => if h': e > C.emax then
      Flean.Float.inf (q < 0)
    else by
      refine Flean.Float.normal ⟨s, e, m⟩ ?_ ?_
      <;> simp only [FloatRep.valid_e, FloatRep.valid_m]
      · refine ⟨?_, by linarith [h', C.emin_lt_emax]⟩
        have := round_min_e (C := C) q
        rw [sem_def] at this
        linarith
      have := round_valid_m (C := C) q q_nonneg
      rw [sem_def] at this
      exact this

def to_rat : Flean.Float C → ℚ
| Flean.Float.inf _ => 0
| Flean.Float.nan => 0
| Flean.Float.normal f _ _ => coe_q f
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
