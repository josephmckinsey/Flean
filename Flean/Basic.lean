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

lemma subnormal_round_coe [R : Rounding] (s : SubnormRep C) (h : s.nonzero) :
  subnormal_round (subnormal_to_q s) = s := by
  unfold subnormal_round
  split
  · exact subnormal_round_nearest_coe s h
  · exact subnormal_round_down_coe s h
  exact subnormal_round_up_coe s h

def round_rep [R : Rounding] (q : ℚ) : FloatRep C :=
  match R.mode with
  | RoundingMode.nearest => round_nearest q
  | RoundingMode.down => round_down q
  | RoundingMode.up => round_up q

lemma round_rep_coe [R : Rounding] (f : FloatRep C) (h : f.valid_m) :
  round_rep (coe_q f) = f := by
  rw [round_rep]
  split
  · exact round_nearest_coe f h
  · exact round_down_coe f h
  exact round_up_coe f h

def FloatRep.valid_e (f : FloatRep C) : Prop := C.emin ≤ f.e ∧ f.e ≤ C.emax

inductive Flean.Float (C : FloatCfg) where
  | inf : Bool → Float C
  | nan : Float C
  | normal : (f : FloatRep C) → f.valid_e → f.valid_m → Float C
  | subnormal : (sm : SubnormRep C) → sm.m < C.prec → Float C

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
    Flean.Float.subnormal ⟨false, 0⟩ C.prec_pos
  else if h : Int.log 2 |q| < C.emin then
    let sp := subnormal_round q
    if h_eq_prec : sp.2 = C.prec then by
      refine Flean.Float.normal ⟨q < 0, C.emin + 1, 0⟩ ?_ ?_
      <;> simp only [FloatRep.valid_e, FloatRep.valid_m]
      · refine ⟨by linarith, by linarith [C.emin_lt_emax]⟩
      linarith [C.prec_pos]
    else by
      refine Flean.Float.subnormal ⟨sp.1, sp.2⟩ ?_
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
| Flean.Float.subnormal sm _ => subnormal_to_q sm

def Flean.Float.IsFinite : Flean.Float C → Prop
| Flean.Float.inf _ => false
| Flean.Float.nan => false
| _ => true

def Flean.Float.IsZero : Flean.Float C → Prop
| Flean.Float.subnormal ⟨_, 0⟩ _ => true
| _ => false

lemma subnorm_eq_0_iff_to_q (sm : SubnormRep C) :
  subnormal_to_q sm = 0 ↔ sm.m = 0 := by
  symm
  constructor
  · intro h
    rw [subnormal_to_q, h]
    simp
  contrapose!
  intro h
  have : sm.m > 0 := Nat.zero_lt_of_ne_zero h
  rw [subnormal_to_q]
  by_cases h': sm.s = false
  <;> {
    simp at h'
    rw [h']
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul,
      Nat.cast_eq_zero, not_or]
    have := C.prec_pos
    positivity
  }


lemma is_zero_iff_subnormal_to_q (sm : SubnormRep C) (h : sm.m < C.prec) :
  subnormal_to_q sm = 0 ↔ (Flean.Float.subnormal sm h).IsZero := by
  rw [subnorm_eq_0_iff_to_q]
  constructor
  · intro h'
    simp [Flean.Float.IsZero]
    rcases sm with ⟨s, m⟩
    split
    · simp at *
    simp [C.prec_pos] at *
    contradiction
  intro h'
  rcases sm with ⟨s, m⟩
  simp only [Flean.Float.IsZero] at h'
  split at h'
  next s m h_again sm_def =>
    rw [Flean.Float.subnormal.injEq] at sm_def
    rw [sm_def]
  simp at h'

lemma log_zero_to_one_lt (x : ℚ) (e : ℤ) (h : 0 < x) (h' : x < 1) :
  Int.log 2 |x * 2 ^ e| < e := by
  rw [<-Int.lt_zpow_iff_log_lt (by norm_num)]
  · rw [abs_of_nonneg (by positivity)]
    simp only [Nat.cast_ofNat]
    rw [mul_lt_iff_lt_one_left (by positivity)]
    exact h'
  positivity

lemma normal_range (f : FloatRep C) (ve : f.valid_e) (vm : f.valid_m) :
  C.emin ≤ Int.log 2 |coe_q f| ∧ Int.log 2 |coe_q f| ≤ C.emax := by
  rw [coe_q]
  rcases f with ⟨s, e, m⟩
  cases s <;> {
    constructor
    <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, neg_mul, abs_neg, q_exp_eq_exp vm]
    · exact ve.1
    exact ve.2
  }


lemma subnormal_range (f : SubnormRep C) (vm : f.m < C.prec) (ne_zero : f.nonzero) :
  Int.log 2 |subnormal_to_q f| < C.emin := by
  rw [subnormal_to_q]
  rw [SubnormRep.nonzero] at ne_zero
  rcases f with ⟨s, m⟩
  cases s <;> {
    simp only [Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul, abs_neg]
    have man_ge_0 : 0 < (m : ℚ) / C.prec := by
      have := C.prec_pos
      positivity
    have man_lt_1 : (m : ℚ) / C.prec < 1 := by
      rw [div_lt_one (by norm_cast; exact C.prec_pos)]
      norm_cast
    exact log_zero_to_one_lt ((m : ℚ) / C.prec) C.emin man_ge_0 man_lt_1
  }


lemma to_floar_to_rat [R : Rounding] (f : Flean.Float C) (finite : f.IsFinite) (nonzero : ¬f.IsZero) :
  to_float (to_rat f) = f := by
  simp [Flean.Float.IsFinite] at finite
  --simp [Flean.Float.IsZero] at nonzero
  rcases f with _ | _ | ⟨f, ve, vm⟩ | ⟨sm, vm⟩
  <;> simp only at finite nonzero
  · have : coe_q f ≠ 0 := by
      rcases f with ⟨s, e, m⟩
      cases s
      · linarith [coe_q_false_pos (C := C) (e := e) (m := m)]
      linarith [coe_q_true_neg (C := C) (e := e) (m := m)]
    simp only [to_rat]
    unfold to_float
    split_ifs
    · contradiction
    · linarith [(normal_range f ve vm).1]
    have : round_rep (coe_q f) = f := round_rep_coe f vm
    dsimp
    split_ifs
    · rw [this] at *
      linarith [ve.2]
    simp [this]
  have sm_nonzero : sm.m ≠ 0 := by
    rw [<-is_zero_iff_subnormal_to_q _ vm] at nonzero
    rw [subnorm_eq_0_iff_to_q] at nonzero
    exact nonzero
  have := subnormal_range sm vm sm_nonzero
  simp only [to_rat]
  unfold to_float
  have snormal_eq := subnormal_round_coe sm sm_nonzero
  if mzero : subnormal_to_q sm = 0 then
    rw [is_zero_iff_subnormal_to_q _ vm] at mzero
    contradiction
  else
    if h_eq_pres : sm.2 = C.prec then
      rw [<-snormal_eq] at h_eq_pres
      simp only [mzero, this, h_eq_pres, ↓reduceDIte, reduceCtorEq]
      rw [snormal_eq] at h_eq_pres
      linarith
    else
      rw [<-snormal_eq] at h_eq_pres
      simp only [mzero, this, h_eq_pres, ↓reduceDIte, Flean.Float.subnormal.injEq]
      rw [snormal_eq]



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
