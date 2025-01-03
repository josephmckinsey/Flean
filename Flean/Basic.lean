import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor
import Qq
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Int.Log

class FloatCfg where
  (prec : ℕ) (emin emax : ℤ)
  emin_le_emax : emin < emax
  prec_pos : 0 < prec

structure FloatRep where
  (s : Bool) (e : ℤ) (m : ℕ)

instance : Repr FloatRep where
  reprPrec := fun ⟨s, e, m⟩ _ => "⟨" ++ repr s ++ ", " ++ repr e ++ ", " ++ repr m ++ "⟩"

def FloatRep.valid [C : FloatCfg] (f : FloatRep) : Prop := f.m < C.prec

def ValidNormal [C : FloatCfg] (e : ℤ) (m : ℕ) : Prop :=
  C.emin ≤ e ∧ e ≤ C.emax ∧ m < C.prec

inductive Flean.Float [C : FloatCfg] where
  | inf : Bool → Float
  | nan : Float
  | normal : Bool → ∀ e m, ValidNormal e m → Float
  | subnormal : Bool → ∀ m, m < C.prec → Float

def to_sign_exp_mantissa [C : FloatCfg] (q : ℚ) : FloatRep :=
  let exp := Int.log 2 |q|
  let mantissa := ⌊(|q| * 2^(-exp) - 1) * C.prec⌋
  ⟨q < 0, exp, mantissa.natAbs⟩

def to_sign_exp_mantissa' [C : FloatCfg] (q : ℚ) : FloatRep :=
  let exp := Int.log 2 |q|
  let mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs
  if mantissa = C.prec then
    ⟨q < 0, exp + 1, 0⟩
  else
    ⟨q < 0, exp, mantissa⟩

-- gross casework
def to_sign_exp_mantissa'' [C : FloatCfg] (q : ℚ) : FloatRep :=
  let ⟨b, e, m⟩ := to_sign_exp_mantissa q -- round towards zero
  let ⟨b', e', m'⟩ := to_sign_exp_mantissa' q -- round away from zero
  -- Find which one is closest
  if 2^e * m - |q| > |q| - 2^e' * m' then
    ⟨b', e', m'⟩
  else if 2^e * m - |q| < |q| - 2^e' * m' then
    ⟨b, e, m⟩
  else if m % 2 = 0 then
    ⟨b, e, m⟩
  else
    ⟨b', e', m'⟩

def sign_mantissa_exp_to_q [C : FloatCfg] : FloatRep → ℚ
| ⟨b, e, m⟩ =>
  let s := if b then -1 else 1
  s * (m / C.prec + 1) * 2^e

lemma mantissa_exp_to_q_pos [C : FloatCfg] {e : ℤ} {m : ℕ} :
  sign_mantissa_exp_to_q ⟨false, e, m⟩ > 0 := by
  simp [sign_mantissa_exp_to_q]
  suffices ((m : ℚ) / C.prec + 1) > 0 by
    exact mul_pos this (zpow_pos (by norm_num) e)
  calc
    (0 : ℚ) ≤ m / C.prec := by simp [div_nonneg, Nat.cast_nonneg']
    _ < m/C.prec + 1 := lt_add_one _

def subnormal_to_q [C : FloatCfg] (b : Bool) (m : ℕ) : ℚ :=
  let s := if b then -1 else 1
  s * (m / C.prec) * 2^C.emin

lemma log_one_to_two_eq {b : ℕ} {e : ℤ} (h : 1 < b) {x : ℚ} (h' : 1 ≤ x) (h'' : x < b) :
  Int.log b (x * b ^ e) = e := by
  have bpos : (0 : ℚ) < b := by norm_cast; linarith
  have x_be_pos : 0 < x * b^e := mul_pos (by linarith) (zpow_pos bpos e)
  apply le_antisymm
  · suffices x * b^e < b^(e + 1) by
      have : Int.log b (x * b^e) < e + 1 := by
        apply (Int.lt_zpow_iff_log_lt (b := b) h (x_be_pos)).1
        exact this
      linarith
    rw [zpow_add_one₀ (by linarith), mul_comm]
    exact (mul_lt_mul_left (zpow_pos bpos e)).mpr h''
  suffices b^e ≤ x * b^e by
    apply (Int.zpow_le_iff_le_log (b := b) h (x_be_pos)).1
    exact this
  nth_rw 1 [<-one_mul ((b : ℚ)^e)]
  exact (mul_le_mul_right (zpow_pos bpos e)).mpr h'

def Flean.neg : FloatRep → FloatRep
| ⟨s, e, m⟩ => ⟨!s, e, m⟩

lemma Flean.neg_neg : Flean.neg ∘ Flean.neg = id := by
  funext ⟨s, e, m⟩
  simp [Flean.neg]

lemma neg_invertible : Function.Bijective Flean.neg := by
  apply Function.bijective_iff_has_inverse.2
  refine ⟨Flean.neg, Function.leftInverse_iff_comp.2 ?_, Function.rightInverse_iff_comp.2 ?_⟩
  <;> exact Flean.neg_neg


lemma sign_mantissa_exp_to_q_neg [C : FloatCfg] (f : FloatRep) :
  sign_mantissa_exp_to_q (Flean.neg f) = -sign_mantissa_exp_to_q f:= by
  by_cases h : f.s <;> simp [sign_mantissa_exp_to_q, h, Flean.neg]
  · ring
  ring

lemma to_sign_exp_mantissa_neg [C : FloatCfg] (q : ℚ) (h : q ≠ 0) :
  to_sign_exp_mantissa (-q) = Flean.neg (to_sign_exp_mantissa q) := by
  by_cases h' : q ≥ 0
  · have : q > 0 := lt_of_le_of_ne h' (Ne.symm h)
    simp [to_sign_exp_mantissa, Flean.neg, h', this]
  have : q < 0 := not_le.mp h'
  simp [to_sign_exp_mantissa, Flean.neg, this, le_of_lt this]

lemma neg_false (e : ℤ) (m : ℕ) : ⟨true, e, m⟩ = Flean.neg ⟨false, e, m⟩ := rfl
lemma neg_true (e : ℤ) (m : ℕ) : ⟨false, e, m⟩ = Flean.neg ⟨true, e, m⟩ := rfl

lemma mantissa_exp_to_q_neg [C : FloatCfg] {e : ℤ} {m : ℕ} :
  sign_mantissa_exp_to_q ⟨true, e, m⟩ < 0 := by
  rw [neg_false, sign_mantissa_exp_to_q_neg]
  simp only [Left.neg_neg_iff, gt_iff_lt, mantissa_exp_to_q_pos]

lemma sign_mantissa_exp'_of_Cprec [C : FloatCfg] (b : Bool) (e : ℤ) :
  sign_mantissa_exp_to_q ⟨b, e, C.prec⟩ = (if b then -1 else 1) * 2^(e + 1) := by
  wlog h : b = false
  · simp only [ite_mul, neg_mul, one_mul, Bool.forall_bool, Bool.false_eq_true, ↓reduceIte,
    forall_const, Bool.true_eq_false, IsEmpty.forall_iff, implies_true, and_true] at this
    simp only [h, ↓reduceIte, neg_mul, one_mul]
    rw [neg_false, sign_mantissa_exp_to_q_neg, this]
  simp only [h, sign_mantissa_exp_to_q, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [div_self]
  · simp [zpow_add_one₀]
    ring
  exact Nat.cast_ne_zero.mpr (by linarith [C.prec_pos])

lemma to_sign_exp_mantissa'_def [C : FloatCfg] (q : ℚ) :
  let exp := Int.log 2 |q|
  let mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs
  sign_mantissa_exp_to_q (to_sign_exp_mantissa' q) = sign_mantissa_exp_to_q ⟨(q < 0), exp, mantissa⟩ := by
  set exp := Int.log 2 |q| with exp_def
  set mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs with mantissa_def
  dsimp
  by_cases h' : mantissa = C.prec
  · simp only [to_sign_exp_mantissa', <-exp_def, <-mantissa_def, h', ↓reduceIte]
    rw [sign_mantissa_exp'_of_Cprec]
    simp [sign_mantissa_exp_to_q]
  simp only [to_sign_exp_mantissa', <-exp_def, <-mantissa_def, ↓reduceIte, h']

lemma to_sign_exp_mantissa'_neg [C : FloatCfg] (q : ℚ) (h : q ≠ 0) :
  to_sign_exp_mantissa' (-q) = Flean.neg (to_sign_exp_mantissa' q) := by
  by_cases h' : q ≥ 0
  · have : q > 0 := lt_of_le_of_ne h' (Ne.symm h)
    by_cases h'' : ⌈(|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) * C.prec⌉.natAbs = C.prec
    <;> simp [to_sign_exp_mantissa', this, h', h'', Flean.neg]
  have : q < 0 := not_le.mp h'
  by_cases h'' : ⌈(|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) * C.prec⌉.natAbs = C.prec
  <;> simp [to_sign_exp_mantissa', Flean.neg, this, le_of_lt this, h'']


lemma mantissa_ge_one [C : FloatCfg] {m : ℕ} : 1 ≤ ((m : ℚ) / C.prec + 1) := by
  suffices 0 ≤ (m : ℚ) / C.prec by linarith
  exact div_nonneg (by linarith) (by linarith)

lemma mantissa_2e_pos [C : FloatCfg] {e : ℤ} {m : ℕ} : 0 < ((m : ℚ) / C.prec + 1) * 2^e := by
  have mantissa_ge_one : 1 ≤ ((m : ℚ) / C.prec + 1) := by
    suffices 0 ≤ (m : ℚ) / C.prec by linarith
    exact div_nonneg (by linarith) (by linarith)
  have := lt_of_lt_of_le (rfl : 0 < (1 : ℚ)) mantissa_ge_one
  exact (mul_pos_iff_of_pos_right (zpow_pos rfl e)).mpr this

def q_exp_eq_exp [C : FloatCfg] {e : ℤ} {m : ℕ} (h : m < C.prec) :
  Int.log 2 |((m : ℚ) / ↑C.prec + 1) * 2 ^ e| = e := by
  have mantissa_lt : ((m : ℚ) / C.prec + 1) < 2 := by
    suffices (m : ℚ) / C.prec < 1 by linarith
    suffices (m : ℚ) < C.prec by
      apply Bound.div_lt_one_of_pos_of_lt
      · norm_cast; exact Nat.zero_lt_of_lt h
      exact this
    norm_cast
  rw [abs_of_nonneg (le_of_lt mantissa_2e_pos)]
  exact log_one_to_two_eq (by norm_num) mantissa_ge_one (by norm_cast)

lemma q_mantissa_eq_mantissa [C : FloatCfg] {e : ℤ} {m : ℕ} (h : m < C.prec) :
  |(((m : ℚ)/C.prec) + 1) * 2^e| * 2^(-Int.log 2 |(((m : ℚ)/C.prec) + 1) * 2^e|) = (m : ℚ) / C.prec + 1 := by
  have mantissa_ge_one : 1 ≤ ((m : ℚ) / C.prec + 1) := by
    suffices 0 ≤ (m : ℚ) / C.prec by linarith
    exact div_nonneg (by linarith) (by linarith)
  have mantissa_2e_pos : 0 < ((m : ℚ) / C.prec + 1) * 2^e := by
    have := lt_of_lt_of_le (rfl : 0 < (1 : ℚ)) mantissa_ge_one
    exact (mul_pos_iff_of_pos_right (zpow_pos rfl e)).mpr this
  set man := ((m : ℚ)/C.prec) + 1 with man_def
  rw [q_exp_eq_exp h, abs_of_pos mantissa_2e_pos, zpow_neg, mul_assoc, mul_inv_cancel₀, mul_one]
  exact zpow_ne_zero e (by norm_num)


lemma left_inv_sign_exp_mantissa [C : FloatCfg] (f : FloatRep) (h : f.valid) :
  to_sign_exp_mantissa (sign_mantissa_exp_to_q f) = f := by
  set s := f.s
  set e := f.e
  set m := f.m
  have : f = ⟨s, e, m⟩ := by cases f; rfl
  rw [this]
  suffices to_sign_exp_mantissa (sign_mantissa_exp_to_q ⟨false, e, m⟩) = ⟨false, e, m⟩ by
    cases s
    · exact this
    rw [neg_false, sign_mantissa_exp_to_q_neg, to_sign_exp_mantissa_neg,
      neg_invertible.injective.eq_iff]
    · exact this
    symm; apply ne_of_lt mantissa_exp_to_q_pos
  simp only [to_sign_exp_mantissa, sign_mantissa_exp_to_q, Bool.false_eq_true, ↓reduceIte, one_mul,
    zpow_neg, FloatRep.mk.injEq, decide_eq_false_iff_not, not_lt]
  refine ⟨?_, ?_, ?_⟩
  · positivity
  · exact q_exp_eq_exp h
  rw [<-zpow_neg, q_mantissa_eq_mantissa h]
  rw [add_sub_cancel_right, div_mul_cancel₀, Int.floor_natCast, Int.natAbs_ofNat]
  norm_cast
  exact ne_of_gt C.prec_pos

lemma sign_mantissa_exp_to_q_inj [C : FloatCfg] {f1 f2 : FloatRep}
  (h : f1.valid) (h' : f2.valid) :
  sign_mantissa_exp_to_q f1 = sign_mantissa_exp_to_q f2 → f1 = f2 := by
  nth_rw 2 [<- left_inv_sign_exp_mantissa (h := h), <- left_inv_sign_exp_mantissa (h := h')]
  exact fun a ↦ congrArg to_sign_exp_mantissa a


lemma mantissa_size_aux (q : ℚ) (h : q ≠ 0): 1 ≤ |q| * (2 ^ Int.log 2 |q|)⁻¹ ∧
  |q| * (2 ^ Int.log 2 |q|)⁻¹ < 2 := by
  constructor
  · suffices (2 ^ Int.log 2 |q|) ≤ |q| by
      rw [<-mul_one (2 ^ _)] at this
      rw [mul_comm]
      exact (le_inv_mul_iff₀ (zpow_pos rfl _ : (0 : ℚ) < 2 ^ Int.log 2 |q|)).2 this
    exact Int.zpow_log_le_self (by norm_num) (abs_pos.mpr h)
  suffices |q| < 2 ^ (Int.log 2 |q| + 1) by
    rw [zpow_add_one₀ (by norm_num), mul_comm] at this
    exact (mul_inv_lt_iff₀ (zpow_pos rfl _ : (0 : ℚ) < 2 ^ Int.log 2 |q|)).2 this
  apply Int.lt_zpow_succ_log_self (by norm_num : 1 < 2)


lemma small_floor_aux {q : ℚ} {n : ℕ} (h : q < 1) (h' : 0 ≤ q) (n_pos : 0 < n):
  ⌊q * n⌋.natAbs < n := by
  have : 0 ≤ (q * n) := by
    exact mul_nonneg h' (Nat.cast_nonneg' n)
  have floor_nonneg : 0 ≤ ⌊q * n⌋ := by
    exact Int.floor_nonneg.mpr this
  suffices ⌊q * n⌋.natAbs < (n : ℤ) by
    norm_cast at this
  rw [Int.natAbs_of_nonneg floor_nonneg]
  suffices q * n < n by
    exact Int.floor_lt.mpr this
  exact (mul_lt_iff_lt_one_left (by norm_cast : 0 < (n : ℚ))).2 h

lemma to_sign_exp_mantissa_valid_m [C : FloatCfg] (q : ℚ) (h : q ≠ 0):
  (to_sign_exp_mantissa q).valid := by
  simp only [to_sign_exp_mantissa, zpow_neg]
  have m_nonneg : 0 ≤ |q| * (2 ^ Int.log 2 |q|)⁻¹ - 1 := by
    linarith [(mantissa_size_aux q h).1]
  have m_small : |q| * (2 ^ Int.log 2 |q|)⁻¹ - 1 < 1 := by
    linarith [(mantissa_size_aux q h).2]
  exact small_floor_aux m_small m_nonneg C.prec_pos

lemma small_ceil {q : ℚ} {n : ℕ} (h : q ≤ 1) (h' : 0 ≤ q) (n_nonneg : 0 ≤ n):
  ⌈q * n⌉.natAbs ≤ n := by
  have : 0 ≤ (q * n) := by
    exact mul_nonneg h' (Nat.cast_nonneg' n)
  have ceil_nonneg : 0 ≤ ⌈q * n⌉ := by
    exact Int.ceil_nonneg this
  suffices ⌈q * n⌉.natAbs ≤ (n : ℤ) by
    norm_cast at this
  rw [Int.natAbs_of_nonneg ceil_nonneg]
  apply Int.ceil_le.mpr
  exact mul_le_of_le_one_left (by norm_cast) h


lemma to_sign_exp_mantissa'_valid_m [C : FloatCfg] (q : ℚ) (h' : q ≠ 0):
  (to_sign_exp_mantissa' q).valid := by
  by_cases h : ⌈(|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) * C.prec⌉.natAbs = C.prec
  <;> simp only [to_sign_exp_mantissa', zpow_neg, h, ↓reduceIte]
  · exact C.prec_pos
  have : (|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) ≤ 1 := by
    linarith [(mantissa_size_aux q h').2]
  apply lt_of_le_of_ne
  · apply small_ceil this
    linarith [(mantissa_size_aux q h').1]
    exact Nat.zero_le _
  exact h

lemma left_inv_sign_exp_mantissa' [C : FloatCfg] (f : FloatRep) (h : f.valid) :
  to_sign_exp_mantissa' (sign_mantissa_exp_to_q f) = f := by
  set s := f.s
  set e := f.e
  set m := f.m
  have : f = ⟨s, e, m⟩ := by cases f; rfl
  rw [this]
  suffices to_sign_exp_mantissa' (sign_mantissa_exp_to_q ⟨false, e, m⟩) = ⟨false, e, m⟩ by
    cases s
    · exact this
    rw [neg_false, sign_mantissa_exp_to_q_neg, to_sign_exp_mantissa'_neg,
      neg_invertible.injective.eq_iff]
    · exact this
    symm; apply ne_of_lt mantissa_exp_to_q_pos
  simp only [sign_mantissa_exp_to_q, Bool.false_eq_true, ↓reduceIte, one_mul]
  refine sign_mantissa_exp_to_q_inj ?_ h ?_
  · refine to_sign_exp_mantissa'_valid_m _ ?_
    linarith [mantissa_2e_pos (m := m) (e := e)]
  rw [to_sign_exp_mantissa'_def]
  congr 2
  · simp [le_of_lt (mantissa_2e_pos (m := m) (e := e))]
  · exact q_exp_eq_exp h
  rw [q_mantissa_eq_mantissa h]
  rw [add_sub_cancel_right, div_mul_cancel₀, Int.ceil_natCast, Int.natAbs_ofNat]
  norm_cast
  exact ne_of_gt C.prec_pos

def q_to_subnormal [C : FloatCfg] (q : ℚ) : Bool × ℕ :=
  (q ≥ 0, ⌊|q| * 2^(-C.emin) * C.prec⌋.natAbs)

lemma q_to_subnormal_valid [C : FloatCfg] (q : ℚ) (q_nonneg : q ≠ 0)
  (h : Int.log 2 |q| < C.emin) : (q_to_subnormal q).2 < C.prec := by
  simp only [q_to_subnormal]
  set e := Int.log 2 |q|
  have q_term_small : |q| * 2^(-e) < 2 := by
    rw [zpow_neg]
    exact (mantissa_size_aux q q_nonneg).2
  have emin_smaller_than_e : (2: ℚ)^(-C.emin) ≤ 2^(-e - 1) := by
    rw [zpow_le_zpow_iff_right₀ (by norm_num)]
    linarith
  apply small_floor_aux ?_ ?nonneg C.prec_pos
  case nonneg =>
    exact mul_nonneg (abs_nonneg _) (zpow_nonneg (by norm_num) (-C.emin : ℤ))
  calc
    |q| * 2 ^ (-C.emin) ≤ |q| * 2^(-e - 1) := by
      exact mul_le_mul_of_nonneg_left emin_smaller_than_e (abs_nonneg _)
    _ = |q| * 2^(-e) / 2 := by
      rw [zpow_sub₀ (by norm_num)]
      ring
    _ < 1 := by linarith

lemma to_sign_exp_mantissa''_eq_or [C : FloatCfg] (q : ℚ) :
  to_sign_exp_mantissa'' q = to_sign_exp_mantissa q ∨
    to_sign_exp_mantissa'' q = to_sign_exp_mantissa' q := by
  unfold to_sign_exp_mantissa''
  rcases to_sign_exp_mantissa q with ⟨s, e, m⟩
  rcases to_sign_exp_mantissa' q with ⟨s', e', m'⟩
  repeat (first | split | tauto)


lemma left_inv_sign_exp_mantissa'' [C : FloatCfg] (f : FloatRep) (h : f.valid) :
  to_sign_exp_mantissa'' (sign_mantissa_exp_to_q f) = f := by
  rcases to_sign_exp_mantissa''_eq_or (sign_mantissa_exp_to_q f) with h' | h'
  · rw [h', left_inv_sign_exp_mantissa f h]
  rw [h', left_inv_sign_exp_mantissa' f h]

lemma to_sign_exp_mantissa''_valid_m [C : FloatCfg] (q : ℚ) (h' : q ≠ 0) :
  (to_sign_exp_mantissa'' q).valid := by
  rcases to_sign_exp_mantissa''_eq_or q with h | h <;> rw [h]
  · exact to_sign_exp_mantissa_valid_m q h'
  exact to_sign_exp_mantissa'_valid_m q h'


def to_float [C : FloatCfg] (q : ℚ) : Flean.Float :=
  match sem_def : to_sign_exp_mantissa q with
  | ⟨s, e, m⟩ =>
  if q_nonneg : q = 0 then
    Flean.Float.subnormal false 0 (C.prec_pos)
  else if h : e < C.emin then by
    let sm := q_to_subnormal q
    refine Flean.Float.subnormal sm.1 sm.2 ?_
    · have : e = (to_sign_exp_mantissa q).e := by
        rw [sem_def]
      simp only [to_sign_exp_mantissa] at this
      rw [this] at h
      exact q_to_subnormal_valid q q_nonneg h
  else if h' : e > C.emax then
    Flean.Float.inf s
  else by
    refine Flean.Float.normal s e m ?_
    refine ⟨Int.not_lt.mp h, Int.not_lt.mp h', ?_⟩
    have : m = (to_sign_exp_mantissa q).m := by
      rw [sem_def]
    rw [this]
    exact to_sign_exp_mantissa_valid_m q (q_nonneg)

def to_rat [C : FloatCfg] : Flean.Float → ℚ
| Flean.Float.inf _ => 0
| Flean.Float.nan => 0
| Flean.Float.normal s e m _ => sign_mantissa_exp_to_q ⟨s, e, m⟩
| Flean.Float.subnormal s m _ => subnormal_to_q s m

def IsFinite [C : FloatCfg] : Flean.Float → Prop
| Flean.Float.inf _ => false
| Flean.Float.nan => false
| _ => true

def IsZero [C : FloatCfg] : Flean.Float → Prop
| Flean.Float.subnormal _ 0 _ => true
| _ => false

def DoubleCfg : FloatCfg := FloatCfg.mk (1 <<< 52) (-1022) 1023 (by norm_num) (
  Nat.zero_lt_succ 4503599627370495
)

def C : FloatCfg := FloatCfg.mk 256 (-127) 127 (by norm_num) (by norm_num)

--#eval @to_rat C (@to_float C 3.528123042)
--#eval @to_sign_exp_mantissa'' C 3.5 = ⟨false, 1, 24⟩
--#eval @to_sign_exp_mantissa C 0
