import Flean.FloatRep
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Int.Log
import Flean.FloatCfg
import Flean.LogRules
import Mathlib.Tactic

variable {C : FloatCfg}

def round_down (q : ℚ) : FloatRep C :=
  let exp := Int.log 2 |q|
  let mantissa := ⌊(|q| * 2^(-exp) - 1) * C.prec⌋
  ⟨q < 0, exp, mantissa.natAbs⟩

lemma round_down_neg (q : ℚ) (h : q ≠ 0) :
  round_down (-q) = Flean.neg (round_down q : FloatRep C) := by
  by_cases h' : q ≥ 0
  · have : q > 0 := lt_of_le_of_ne h' (Ne.symm h)
    simp [round_down, Flean.neg, h', this]
  have : q < 0 := not_le.mp h'
  simp [round_down, Flean.neg, this, le_of_lt this]


lemma round_down_coe (f : FloatRep C) (h : f.valid_m) :
  round_down (coe_q f) = f := by
  revert h
  apply floatrep_of_false₁ (f := f)
  · intro f
    rw [coe_q_of_neg, neg_valid_m, round_down_neg (coe_q f) coe_q_nezero, neg_invertible.injective.eq_iff]
    tauto
  intro e m h
  simp only [round_down, coe_q, Bool.false_eq_true, ↓reduceIte, one_mul,
    zpow_neg, FloatRep.mk.injEq, decide_eq_false_iff_not, not_lt]
  refine ⟨?_, ?_, ?_⟩
  · positivity
  · exact q_exp_eq_exp h
  rw [<-zpow_neg, q_mantissa_eq_mantissa h]
  rw [add_sub_cancel_right, div_mul_cancel₀, Int.floor_natCast, Int.natAbs_ofNat]
  norm_cast
  exact ne_of_gt C.prec_pos

lemma coe_q_inj_valid {f1 f2 : FloatRep C}
  (h : f1.valid_m) (h' : f2.valid_m) :
  coe_q f1 = coe_q f2 → f1 = f2 := by
  nth_rw 2 [<- round_down_coe (h := h), <- round_down_coe (h := h')]
  exact fun a ↦ congrArg round_down a

lemma round_down_valid (q : ℚ) (h : q ≠ 0):
  (round_down q : FloatRep C).valid_m := by
  simp only [round_down, zpow_neg]
  have m_nonneg : 0 ≤ |q| * (2 ^ Int.log 2 |q|)⁻¹ - 1 := by
    linarith [(mantissa_size_aux q h).1]
  have m_small : |q| * (2 ^ Int.log 2 |q|)⁻¹ - 1 < 1 := by
    linarith [(mantissa_size_aux q h).2]
  exact small_floor_aux m_small m_nonneg C.prec_pos

lemma round_down_of_pos (q : ℚ) (h : 0 < q) :
  0 < coe_q (round_down q : FloatRep C) := by
  simp [coe_q, round_down]
  split
  · linarith
  positivity

lemma round_down_of_pos' (q : ℚ) (h : 0 < q) :
  (round_down q : FloatRep C).s = false := by
  simp [round_down]
  linarith

lemma round_down_of_neg (q : ℚ) (h : q < 0) :
  coe_q (round_down q : FloatRep C) < 0 := by
  suffices 0 < -coe_q (round_down q : FloatRep C) by
    exact Left.neg_pos_iff.mp this
  rw [<-coe_q_of_neg, <-round_down_neg q (by linarith)]
  apply round_down_of_pos
  exact Left.neg_pos_iff.mpr h

lemma round_down_of_neg' (q : ℚ) (h : q < 0) :
  (round_down q : FloatRep C).s = true := by
  simpa [round_down]

lemma casesQPlane (P : ℚ → ℚ → Prop)
  (h1 : ∀q1 > 0, ∀q2 > 0, P q1 q2)
  (h2 : ∀q1 < 0, ∀q2 > 0, P q1 q2)
  (h3 : ∀q1 > 0, ∀q2 < 0, P q1 q2)
  (h4 : ∀q1 < 0, ∀q2 < 0, P (-q1) (-q2) → P q2 q1) (q1 q2 : ℚ)
  (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) : P q1 q2 := by
  have h : ∀q ≠ (0 : ℚ), q > 0 ∨ q < 0 := by
    intro q qnezero
    by_cases h : q > 0
    · exact Or.inl h
    exact lt_or_gt_of_ne (Ne.symm qnezero)
  rcases (h q1 q1_nezero) with h' | h'
  · rcases (h q2 q2_nezero) with h'' | h''
    · exact h1 q1 h' q2 h''
    exact h3 q1 h' q2 h''
  · rcases (h q2 q2_nezero) with h'' | h''
    · exact h2 q1 h' q2 h''
    apply h4 q2 h'' q1 h'
    apply h1
    · exact Left.neg_pos_iff.mpr h''
    exact Left.neg_pos_iff.mpr h'

lemma abs_le_round_down_of_le (q1 q2 : ℚ) (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) :
  |q1| ≤ |q2| → |coe_q (round_down q1 : FloatRep C)| ≤ |coe_q (round_down q2 : FloatRep C)| := by
  intro h
  apply floatrep_le_pos_coe_q (vm1 := le_of_lt (round_down_valid q1 q1_nezero))
  rw [floatrep_pos_equiv]
  unfold floatrep_le_pos'
  constructor
  · simp [round_down]
    apply Int.log_mono_right
    · exact abs_pos.mpr q1_nezero
    exact h
  intro h
  simp only [round_down] at *
  zify
  apply abs_le_abs_of_nonneg
  · have := (mantissa_size_aux q1 q1_nezero).1
    rw [zpow_neg]
    refine Int.floor_nonneg.mpr ?_
    exact mul_nonneg (by linarith) (by linarith)
  apply Int.floor_le_floor
  gcongr
  · norm_num
  exact Int.le_of_eq (h.symm)

lemma le_round_down_of_le (q1 q2 : ℚ) (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) :
  q1 ≤ q2 → coe_q (round_down q1 : FloatRep C) ≤ coe_q (round_down q2 : FloatRep C) := by
  rw [<-floatrep_le_iff_coe_q_le (vm1 := round_down_valid q1 q1_nezero)
    (vm2 := round_down_valid q2 q2_nezero)]
  apply casesQPlane (q1_nezero := q1_nezero) (q2_nezero := q2_nezero)
  · intro q1 q1h q2 q2h h
    simp only [floatrep_le]
    rw [round_down_of_pos' q1 q1h, round_down_of_pos' q2 q2h]
    apply coe_q_le_floatrep_pos
    · exact round_down_valid q2 (by linarith)
    · apply abs_le_round_down_of_le q1 q2 (by linarith) (by linarith)
      rw [abs_of_pos q1h, abs_of_pos q2h]
      exact h
  · intro q1 q1h q2 q2h h
    simp_rw [floatrep_le, round_down_of_neg' q1 q1h, round_down_of_pos' q2 q2h]
  · intro q1 q1h q2 q2h h
    exfalso
    linarith
  · intro q1 q1h q2 q2h h h'
    have : -q1 ≤ -q2 := by
      linarith
    replace h := h this
    rw [floatrep_le, round_down_of_neg' q1 q1h, round_down_of_neg' q2 q2h]
    dsimp
    rw [round_down_neg q1 (by linarith), round_down_neg q2 (by linarith)] at h
    simp [floatrep_le, Flean.neg,
      round_down_of_neg' q1 q1h, round_down_of_neg' q2 q2h] at h
    exact h

lemma round_down_false_of_le_coe_aux (q : ℚ) (e : ℤ) (m : ℕ) (vm : m < C.prec) (q_pos : 0 < q)
  (h : q ≤ coe_q (⟨false, e, m⟩ : FloatRep C)) :
  coe_q (round_down q : FloatRep C) ≤ coe_q (⟨false, e, m⟩ : FloatRep C) := by
  rw [<-round_down_coe ⟨false, e, m⟩ vm]
  apply le_round_down_of_le q _ (ne_of_gt q_pos) coe_q_nezero h


def round_up (q : ℚ) : FloatRep C :=
  let exp := Int.log 2 |q|
  let mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs
  if mantissa = C.prec then
    ⟨q < 0, exp + 1, 0⟩
  else
    ⟨q < 0, exp, mantissa⟩

lemma round_up_def (q : ℚ) :
  let exp := Int.log 2 |q|
  let mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs
  coe_q (round_up q : FloatRep C) = coe_q (⟨(q < 0), exp, mantissa⟩ : FloatRep C) := by
  set exp := Int.log 2 |q| with exp_def
  set mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs with mantissa_def
  dsimp
  by_cases h' : mantissa = C.prec
  · simp only [round_up, <-exp_def, <-mantissa_def, h', ↓reduceIte]
    rw [coe_q_of_Cprec]
    simp [coe_q]
  simp only [round_up, <-exp_def, <-mantissa_def, ↓reduceIte, h']

lemma round_up_neg (q : ℚ) (h : q ≠ 0) :
  round_up (-q) = Flean.neg (round_up q : FloatRep C) := by
  by_cases h' : q ≥ 0
  · have : q > 0 := lt_of_le_of_ne h' (Ne.symm h)
    by_cases h'' : ⌈(|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) * C.prec⌉.natAbs = C.prec
    <;> simp [round_up, this, h', h'', Flean.neg]
  have : q < 0 := not_le.mp h'
  by_cases h'' : ⌈(|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) * C.prec⌉.natAbs = C.prec
  <;> simp [round_up, Flean.neg, this, le_of_lt this, h'']

lemma round_up_valid (q : ℚ) (h' : q ≠ 0):
  (round_up q : FloatRep C).valid_m := by
  by_cases h : ⌈(|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) * C.prec⌉.natAbs = C.prec
  <;> simp only [round_up, zpow_neg, h, ↓reduceIte]
  · exact C.prec_pos
  rw [FloatRep.valid_m]; dsimp
  have : (|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) ≤ 1 := by
    linarith [(mantissa_size_aux q h').2]
  apply lt_of_le_of_ne
  · apply small_ceil this
    linarith [(mantissa_size_aux q h').1]
    exact Nat.zero_le _
  exact h

lemma round_up_coe (f : FloatRep C) (h : f.valid_m) :
  round_up (coe_q f) = f := by
  revert h
  apply floatrep_of_false₁ (f := f)
  · intro f
    rw [coe_q_of_neg, neg_valid_m, round_up_neg (coe_q f) coe_q_nezero, neg_invertible.injective.eq_iff]
    tauto
  intro e m h
  simp only [coe_q, Bool.false_eq_true, ↓reduceIte, one_mul]
  refine coe_q_inj_valid ?_ h ?_
  · refine round_up_valid _ ?_
    positivity
  rw [round_up_def]
  congr 2
  · simp; positivity
  · exact q_exp_eq_exp h
  rw [q_mantissa_eq_mantissa h]
  rw [add_sub_cancel_right, div_mul_cancel₀, Int.ceil_natCast, Int.natAbs_ofNat]
  norm_cast
  exact ne_of_gt C.prec_pos

lemma round_up_of_pos (q : ℚ) (h : 0 < q) :
  0 < coe_q (round_up q : FloatRep C) := by
  rw [round_up_def, coe_q]
  split
  · simp at *; linarith
  positivity

lemma round_up_of_pos' (q : ℚ) (h : 0 < q) :
  (round_up q : FloatRep C).s = false := by
  simp only [round_up]
  split <;> (simp; linarith)


lemma round_up_of_neg (q : ℚ) (h : q < 0) :
  coe_q (round_up q : FloatRep C) < 0 := by
  suffices 0 < -coe_q (round_up q : FloatRep C) by
    exact Left.neg_pos_iff.mp this
  rw [<-coe_q_of_neg, <-round_up_neg q (by linarith)]
  apply round_up_of_pos
  exact Left.neg_pos_iff.mpr h

lemma round_up_of_neg' (q : ℚ) (h : q < 0) :
  (round_up q : FloatRep C).s = true := by
  simp [round_up]
  split <;> simpa

lemma e_le_iff_log (f1 f2 : FloatRep C) (vm1 : f1.valid_m) (vm2 : f2.valid_m) :
  f1.e ≤ f2.e ↔ Int.log 2 |coe_q f1| ≤ Int.log 2 |coe_q f2| := by
  revert vm1 vm2
  apply floatrep_of_false₂ (f1 := f1) (f2 := f2)
  · simp_rw [coe_q_of_neg, neg_valid_m]
    simp [Flean.neg]
  · simp_rw [coe_q_of_neg, neg_valid_m]
    simp [Flean.neg]
  intro e1 e2 m1 m2 vm1 vm2
  simp only [coe_q, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [q_exp_eq_exp vm1, q_exp_eq_exp vm2]

lemma mantissa_nonneg (C : FloatCfg) (q : ℚ) (q_nezero : q ≠ 0) :
  0 ≤ (|q| * ((2 : ℚ)^Int.log 2 |q|)⁻¹ - 1) * C.prec := by
  apply mul_nonneg
  · linarith [(mantissa_size_aux q q_nezero).1]
  exact_mod_cast le_of_lt C.prec_pos


lemma abs_le_round_up_of_le (q1 q2 : ℚ) (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) :
  |q1| ≤ |q2| → |coe_q (round_up q1 : FloatRep C)| ≤ |coe_q (round_up q2 : FloatRep C)| := by
  intro q_le_than
  rw [round_up_def, round_up_def]
  apply floatrep_le_pos_coe_q
  · simp only [zpow_neg]
    apply small_ceil
    · linarith [(mantissa_size_aux q1 q1_nezero).2]
    · linarith [(mantissa_size_aux q1 q1_nezero).1]
    exact le_of_lt C.prec_pos
  rw [floatrep_pos_equiv]
  unfold floatrep_le_pos'
  constructor
  · dsimp
    apply Int.log_mono_right (abs_pos.mpr q1_nezero) q_le_than
  dsimp
  intro h
  simp only [zpow_neg]
  zify
  rw [abs_of_nonneg (Int.ceil_nonneg (mantissa_nonneg C q1 q1_nezero))]
  rw [abs_of_nonneg (Int.ceil_nonneg (mantissa_nonneg C q2 q2_nezero))]
  rw [h]
  gcongr

lemma le_round_up_of_le (q1 q2 : ℚ) (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) :
  q1 ≤ q2 → coe_q (round_up q1 : FloatRep C) ≤ coe_q (round_up q2 : FloatRep C) := by
  rw [<-floatrep_le_iff_coe_q_le (vm1 := round_up_valid q1 q1_nezero)
    (vm2 := round_up_valid q2 q2_nezero)]
  apply casesQPlane (q1_nezero := q1_nezero) (q2_nezero := q2_nezero)
  · intro q1 q1h q2 q2h h
    simp only [floatrep_le]
    rw [round_up_of_pos' q1 q1h, round_up_of_pos' q2 q2h]
    apply coe_q_le_floatrep_pos
    · exact round_up_valid q2 (by linarith)
    · apply abs_le_round_up_of_le q1 q2 (by linarith) (by linarith)
      rw [abs_of_pos q1h, abs_of_pos q2h]
      exact h
  · intro q1 q1h q2 q2h h
    simp_rw [floatrep_le, round_up_of_neg' q1 q1h, round_up_of_pos' q2 q2h]
  · intro q1 q1h q2 q2h h
    exfalso
    linarith
  · intro q1 q1h q2 q2h h h'
    have : -q1 ≤ -q2 := by
      linarith
    replace h := h this
    rw [floatrep_le, round_up_of_neg' q1 q1h, round_up_of_neg' q2 q2h]
    dsimp
    rw [round_up_neg q1 (by linarith), round_up_neg q2 (by linarith)] at h
    simp [floatrep_le, Flean.neg,
      round_up_of_neg' q1 q1h, round_up_of_neg' q2 q2h] at h
    exact h


-- gross casework
def round_nearest (q : ℚ) : FloatRep C :=
  let f1 : FloatRep C := round_down q -- round towards zero
  let f2 : FloatRep C := round_up q -- round away from zero
  -- Find which one is closest
  if |coe_q f1| - |q| > |q| - |coe_q f2| then
    f2
  else if |coe_q f1| - |q| < |q| - |coe_q f2| then
    f1
  else if f2.m % 2 = 0 then
    f1
  else
    f2


lemma round_nearest_eq_or (q : ℚ) :
  (round_nearest q : FloatRep C) = round_down q ∨ (round_nearest q : FloatRep C) = round_up q := by
  unfold round_nearest
  dsimp
  split_ifs
  repeat (first | split | tauto)


def round_q_to_int (q : ℚ) : ℤ :=
  let i1 := ⌊q⌋
  let i2 := ⌈q⌉
  if q - i1 < i2 - q then
    i1
  else if q - i1 > i2 - q then
    i2
  else if i2 % 2 = 0 then
    i1
  else
    i2

/-lemma round_eq_def (q : ℚ) :
  let exp := Int.log 2 |q|
  let mantissa := (round_q_to_int (|q| * 2^(-exp) - 1) * C.prec).natAbs
  coe_q (round_up q : FloatRep C) = coe_q (⟨(q < 0), exp, mantissa⟩ : FloatRep C) := by sorry
  -/


lemma round_nearest_coe (f : FloatRep C) (h : f.valid_m) :
  round_nearest (coe_q f) = f := by
  rcases round_nearest_eq_or (coe_q f) with h' | h'
  · rw [h', round_down_coe f h]
  rw [h', round_up_coe f h]

lemma round_nearest_valid (q : ℚ) (h' : q ≠ 0) :
  (round_nearest q : FloatRep C).valid_m := by
  rcases round_nearest_eq_or q with h | h <;> rw [h]
  · exact round_down_valid q h'
  exact round_up_valid q h'


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
