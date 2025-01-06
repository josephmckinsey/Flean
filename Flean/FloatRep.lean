import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Int.Log
import Flean.FloatCfg
import Flean.LogRules


structure FloatRep (α : FloatCfg) where
  (s : Bool) (e : ℤ) (m : ℕ)

variable {C : FloatCfg}

instance : Repr (FloatRep C) where
  reprPrec := fun ⟨s, e, m⟩ _ => "⟨" ++ repr s ++ ", " ++ repr e ++ ", " ++ repr m ++ "⟩"


def FloatRep.decEq (f1 f2 : FloatRep C) : Decidable (Eq f1 f2) := by
  rw [FloatRep.mk.injEq]
  exact instDecidableAnd

def FloatRep.valid_m (f : FloatRep C) : Prop := f.m < C.prec

def round_down (q : ℚ) : FloatRep C :=
  let exp := Int.log 2 |q|
  let mantissa := ⌊(|q| * 2^(-exp) - 1) * C.prec⌋
  ⟨q < 0, exp, mantissa.natAbs⟩

def round_up (q : ℚ) : FloatRep C :=
  let exp := Int.log 2 |q|
  let mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs
  if mantissa = C.prec then
    ⟨q < 0, exp + 1, 0⟩
  else
    ⟨q < 0, exp, mantissa⟩

-- gross casework
def round_nearest (q : ℚ) : FloatRep C :=
  let ⟨b, e, m⟩ : FloatRep C := round_down q -- round towards zero
  let ⟨b', e', m'⟩ : FloatRep C := round_up q -- round away from zero
  -- Find which one is closest
  if 2^e * m - |q| > |q| - 2^e' * m' then
    ⟨b', e', m'⟩
  else if 2^e * m - |q| < |q| - 2^e' * m' then
    ⟨b, e, m⟩
  else if m % 2 = 0 then
    ⟨b, e, m⟩
  else
    ⟨b', e', m'⟩

def coe_q : FloatRep C → ℚ
| ⟨b, e, m⟩ =>
  let s := if b then -1 else 1
  s * (m / C.prec + 1) * 2^e

--instance : Coe (FloatRep C) ℚ where
  --coe := coe_q

lemma coe_q_false_pos {e : ℤ} {m : ℕ} :
  0 < coe_q (⟨false, e, m⟩ : FloatRep C) := by
  simp [coe_q]
  suffices ((m : ℚ) / C.prec + 1) > 0 by
    exact mul_pos this (zpow_pos (by norm_num) e)
  calc
    (0 : ℚ) ≤ m / C.prec := by simp [div_nonneg, Nat.cast_nonneg']
    _ < m/C.prec + 1 := lt_add_one _

def Flean.neg {C  : FloatCfg} : FloatRep C → FloatRep C
| ⟨s, e, m⟩ => ⟨!s, e, m⟩

lemma Flean.neg_neg : (@Flean.neg C) ∘ (@Flean.neg C) = id := by
  funext ⟨s, e, m⟩
  simp [Flean.neg]

lemma neg_invertible : Function.Bijective (@Flean.neg C) := by
  apply Function.bijective_iff_has_inverse.2
  refine ⟨Flean.neg, Function.leftInverse_iff_comp.2 ?_, Function.rightInverse_iff_comp.2 ?_⟩
  <;> exact Flean.neg_neg


lemma coe_q_of_neg (f : FloatRep C) :
  coe_q (Flean.neg f) = -coe_q f:= by
  by_cases h : f.s <;> simp [coe_q, h, Flean.neg]
  · ring
  ring

lemma round_down_of_neg (q : ℚ) (h : q ≠ 0) :
  round_down (-q) = Flean.neg (round_down q : FloatRep C) := by
  by_cases h' : q ≥ 0
  · have : q > 0 := lt_of_le_of_ne h' (Ne.symm h)
    simp [round_down, Flean.neg, h', this]
  have : q < 0 := not_le.mp h'
  simp [round_down, Flean.neg, this, le_of_lt this]

lemma neg_false (e : ℤ) (m : ℕ) : ⟨true, e, m⟩ = (Flean.neg ⟨false, e, m⟩ : FloatRep C) := rfl
lemma neg_true (e : ℤ) (m : ℕ) : ⟨false, e, m⟩ = (Flean.neg ⟨true, e, m⟩ : FloatRep C) := rfl

lemma coe_q_true_neg {e : ℤ} {m : ℕ} :
  coe_q (⟨true, e, m⟩ : FloatRep C) < 0 := by
  rw [neg_false, coe_q_of_neg]
  simp only [Left.neg_neg_iff, gt_iff_lt, coe_q_false_pos]

lemma coe_q_of_Cprec (b : Bool) (e : ℤ) :
  coe_q (⟨b, e, C.prec⟩ : FloatRep C) = (if b then -1 else 1) * 2^(e + 1) := by
  wlog h : b = false
  · simp only [ite_mul, neg_mul, one_mul, Bool.forall_bool, Bool.false_eq_true, ↓reduceIte,
    forall_const, Bool.true_eq_false, IsEmpty.forall_iff, implies_true, and_true] at this
    simp only [h, ↓reduceIte, neg_mul, one_mul]
    rw [neg_false, coe_q_of_neg, this]
  simp only [h, coe_q, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [div_self]
  · simp [zpow_add_one₀]
    ring
  exact Nat.cast_ne_zero.mpr (by linarith [C.prec_pos])

lemma round_up_def (q : ℚ) :
  let exp := Int.log 2 |q|
  let mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs
  coe_q (round_up q : FloatRep C) = coe_q (⟨(q < 0), exp, mantissa⟩ : FloatRep C):= by
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

lemma round_down_coe (f : FloatRep C) (h : f.valid_m) :
  round_down (coe_q f) = f := by
  rcases f with ⟨s, e, m⟩
  suffices round_down (coe_q ⟨false, e, m⟩) = ⟨false, e, m⟩ by
    cases s
    · exact this
    rw [neg_false, coe_q_of_neg, round_down_of_neg,
      neg_invertible.injective.eq_iff]
    · exact this
    symm; apply ne_of_lt coe_q_false_pos
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
  rcases f with ⟨s, e, m⟩
  suffices round_up (coe_q ⟨false, e, m⟩) = ⟨false, e, m⟩ by
    cases s
    · exact this
    rw [neg_false, coe_q_of_neg, round_up_neg,
      neg_invertible.injective.eq_iff]
    · exact this
    symm; apply ne_of_lt coe_q_false_pos
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

lemma round_nearest_eq_or (q : ℚ) :
  (round_nearest q : FloatRep C) = round_down q ∨ (round_nearest q : FloatRep C) = round_up q := by
  unfold round_nearest
  rcases round_down q with ⟨s, e, m⟩
  rcases round_up q with ⟨s', e', m'⟩
  repeat (first | split | tauto)


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

def FloatRep.valid_e (f : FloatRep C) : Prop := C.emin ≤ f.e ∧ f.e ≤ C.emax

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

lemma floatrep_le_aux (e1 e2 : ℤ) (m1 m2 : ℕ) (vm2 : m2 < C.prec)
  (h : coe_q (⟨false, e1, m1⟩ : FloatRep C) ≤ coe_q (⟨false, e2, m2⟩ : FloatRep C)) :
  e1 ≤ e2 := by
  simp only [coe_q, Bool.false_eq_true, ↓reduceIte, one_mul] at h
  contrapose! h
  calc
    ((m2 : ℚ) / ↑C.prec + 1) * 2 ^ e2 < 2 * 2^e2 := by
      gcongr
      exact mantissa_lt_two vm2
    2 * 2^e2 ≤ 2^e1 := by
      rw [mul_comm, <-zpow_add_one₀ (by norm_num)]
      exact (zpow_le_zpow_iff_right₀ rfl).mpr h
    2^e1 ≤ ((m1 : ℚ) / C.prec + 1) * 2^e1 := by
      nth_rw 1 [<-one_mul (2^e1)]
      gcongr
      exact mantissa_ge_one

lemma neg_valid_m {f : FloatRep C} (vm : f.valid_m) :
  (Flean.neg f).valid_m := by simpa [FloatRep.valid_m, Flean.neg] using vm


lemma floatrep_le (f1 f2 : FloatRep C) (vm2 : f2.valid_m) (h : |coe_q f1| ≤ |coe_q f2|) :
  f1.e ≤ f2.e := by
  wlog h' : (f1.s = false) ∧ f2.s = false
  · have : (f1.s = true ∧ f2.s = false) ∨
      (f1.s = false ∧ f2.s = true) ∨
      (f1.s = true ∧ f2.s = true) := by
        rw [not_and_or] at h'
        rcases h' with h' | h'
        <;> simp at h'
        <;> rw [h']
        <;> simp
    rcases this with h' | h' | h'
    · have := this (Flean.neg f1) f2 (neg_valid_m vm2)
      rw [coe_q_of_neg, abs_neg] at this
      have := this h
      apply this
      simp only [Flean.neg, h', Bool.not_true, and_self]
    · have := this f1 (Flean.neg f2) (neg_valid_m vm2)
      rw [coe_q_of_neg, abs_neg] at this
      have := this h
      apply this
      simp only [Flean.neg, h', Bool.not_true, and_self]
    have := this (Flean.neg f1) (Flean.neg f2) (neg_valid_m vm2)
    rw [coe_q_of_neg, coe_q_of_neg, abs_neg, abs_neg] at this
    have := this h
    apply this
    simp [h', Flean.neg]
  rcases f1 with ⟨s, e, m⟩
  rcases f2 with ⟨s', e', m'⟩
  dsimp at h'
  rw [h'.1, h'.2] at h
  rw [h'.1, h'.2]
  rw [abs_of_pos coe_q_false_pos, abs_of_pos coe_q_false_pos] at h
  exact floatrep_le_aux e e' m m' vm2 h

lemma max_mantissa_q (C : FloatCfg) : (1 ≤ 2 - (1 : ℚ) / C.prec) ∧ (2 - (1 : ℚ) / C.prec < 2) := by
  have := C.prec_pos
  have : (1 : ℚ) / C.prec ≤ 1 := by
    rw [one_div_le]
    · simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, Nat.one_le_cast]
      exact this
    · exact Nat.cast_pos'.mpr this
    norm_num
  have : 0 < (1 : ℚ) / C.prec := by positivity
  constructor
  · linarith
  linarith


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

lemma normal_range' (m : ℕ) (e : ℤ) (vm : m < C.prec) (ve2 : e ≤ C.emax) :
  |((m : ℚ) / ↑C.prec + 1) * 2 ^ e| ≤ (2 - 1 / ↑C.prec) * 2 ^ C.emax := by
  have := C.prec_pos
  have : (1 : ℚ) / C.prec ≤ 1 := by
    rw [one_div_le]
    · simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, Nat.one_le_cast]
      exact this
    · exact Nat.cast_pos'.mpr this
    norm_num
  have := (max_mantissa_q C).1
  rw [abs_mul]
  gcongr
  · rw [abs_of_nonneg (by positivity)]
    suffices (m + (1 : ℚ)) / C.prec ≤ 1 by
      rw [add_div] at this
      linarith
    rw [div_le_one (by norm_cast)]
    suffices m + 1 < C.prec + 1 by
      norm_cast
    linarith [vm]
  rw [abs_of_nonneg (by positivity)]
  rw [zpow_le_zpow_iff_right₀ (by norm_num)]
  exact ve2

def max_float_q (C : FloatCfg) : ℚ := (2 - (1 : ℚ) / C.prec) * 2^C.emax

def max_float_rep (C : FloatCfg) : FloatRep C := ⟨false, C.emax, C.prec - 1⟩

lemma coe_q_max_float_rep : coe_q (max_float_rep C) = max_float_q C := by
  simp [coe_q, max_float_rep, max_float_q]
  left
  have : ((C.prec - 1 : ℕ) : ℚ) = C.prec - 1 := by
    simp only [C.prec_pos, Nat.cast_pred]
  simp only [C.prec_pos, Nat.cast_pred, sub_div, div_self (by linarith : (C.prec : ℚ) ≠ 0), one_div]
  linarith

lemma round_le_of_le_coe [R : Rounding] (q : ℚ) (f : FloatRep C) (q_nonneg : q ≠ 0)
  (h : q ≤ coe_q f) : coe_q (round_rep q : FloatRep C) ≤ coe_q f := sorry

lemma le_round_of_coe_le [R : Rounding] (q : ℚ) (f : FloatRep C) (q_nonneg : q ≠ 0)
  (h : coe_q f ≤ q) : coe_q f ≤ coe_q (round_rep q : FloatRep C) := sorry

lemma round_max_e [R : Rounding] (q : ℚ) (e : ℤ) (h : |q| ≤ (1 + (C.prec - 1 : ℕ) / C.prec) * 2^e) :
  (round_rep q : FloatRep C).e ≤ e := by
  set q' := coe_q (⟨false, e, C.prec - 1⟩ : FloatRep C) with q_def
  have : q' = (1 + (C.prec - 1 : ℕ) / C.prec) * 2^e := by
    rw [q_def, coe_q]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, mul_eq_mul_right_iff]
    left; rw [add_comm]
  rw [<-this] at h
  sorry

lemma round_in_range [R : Rounding] (q : ℚ) (h : |q| ≤ max_float_q C) :
  (round_rep q : FloatRep C).e ≤ C.emax := by
  rw [round_rep]
  split
  · sorry
  · sorry
  sorry
