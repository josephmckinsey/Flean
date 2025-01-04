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
  emin_lt_emax : emin < emax
  prec_pos : 0 < prec

structure FloatRep where
  (s : Bool) (e : ℤ) (m : ℕ)

instance : Repr FloatRep where
  reprPrec := fun ⟨s, e, m⟩ _ => "⟨" ++ repr s ++ ", " ++ repr e ++ ", " ++ repr m ++ "⟩"

def FloatRep.decEq (f1 f2 : FloatRep) : Decidable (Eq f1 f2) := by
  rw [FloatRep.mk.injEq]
  exact instDecidableAnd

def FloatRep.valid [C : FloatCfg] (f : FloatRep) : Prop := f.m < C.prec

def ValidNormal [C : FloatCfg] (e : ℤ) (m : ℕ) : Prop :=
C.emin ≤ e ∧ e ≤ C.emax ∧ m < C.prec

inductive Flean.Float [C : FloatCfg] where
  | inf : Bool → Float
  | nan : Float
  | normal : Bool → ∀ e m, ValidNormal e m → Float
  | subnormal : Bool → ∀ m, m < C.prec → Float

def round_down [C : FloatCfg] (q : ℚ) : FloatRep :=
  let exp := Int.log 2 |q|
  let mantissa := ⌊(|q| * 2^(-exp) - 1) * C.prec⌋
  ⟨q < 0, exp, mantissa.natAbs⟩

def round_up [C : FloatCfg] (q : ℚ) : FloatRep :=
  let exp := Int.log 2 |q|
  let mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs
  if mantissa = C.prec then
    ⟨q < 0, exp + 1, 0⟩
  else
    ⟨q < 0, exp, mantissa⟩

-- gross casework
def round_nearest [C : FloatCfg] (q : ℚ) : FloatRep :=
  let ⟨b, e, m⟩ := round_down q -- round towards zero
  let ⟨b', e', m'⟩ := round_up q -- round away from zero
  -- Find which one is closest
  if 2^e * m - |q| > |q| - 2^e' * m' then
    ⟨b', e', m'⟩
  else if 2^e * m - |q| < |q| - 2^e' * m' then
    ⟨b, e, m⟩
  else if m % 2 = 0 then
    ⟨b, e, m⟩
  else
    ⟨b', e', m'⟩

def coe_q [C : FloatCfg] : FloatRep → ℚ
| ⟨b, e, m⟩ =>
  let s := if b then -1 else 1
  s * (m / C.prec + 1) * 2^e

instance [C : FloatCfg] : Coe FloatRep ℚ where
  coe := coe_q

lemma coe_false_pos [C : FloatCfg] {e : ℤ} {m : ℕ} :
  coe_q ⟨false, e, m⟩ > 0 := by
  simp [coe_q]
  suffices ((m : ℚ) / C.prec + 1) > 0 by
    exact mul_pos this (zpow_pos (by norm_num) e)
  calc
    (0 : ℚ) ≤ m / C.prec := by simp [div_nonneg, Nat.cast_nonneg']
    _ < m/C.prec + 1 := lt_add_one _

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


lemma coe_q_of_neg [C : FloatCfg] (f : FloatRep) :
  coe_q (Flean.neg f) = -coe_q f:= by
  by_cases h : f.s <;> simp [coe_q, h, Flean.neg]
  · ring
  ring

lemma round_down_of_neg [C : FloatCfg] (q : ℚ) (h : q ≠ 0) :
  round_down (-q) = Flean.neg (round_down q) := by
  by_cases h' : q ≥ 0
  · have : q > 0 := lt_of_le_of_ne h' (Ne.symm h)
    simp [round_down, Flean.neg, h', this]
  have : q < 0 := not_le.mp h'
  simp [round_down, Flean.neg, this, le_of_lt this]

lemma neg_false (e : ℤ) (m : ℕ) : ⟨true, e, m⟩ = Flean.neg ⟨false, e, m⟩ := rfl
lemma neg_true (e : ℤ) (m : ℕ) : ⟨false, e, m⟩ = Flean.neg ⟨true, e, m⟩ := rfl

lemma coe_q_false_neg [C : FloatCfg] {e : ℤ} {m : ℕ} :
  coe_q ⟨true, e, m⟩ < 0 := by
  rw [neg_false, coe_q_of_neg]
  simp only [Left.neg_neg_iff, gt_iff_lt, coe_false_pos]

lemma coe_q_of_Cprec [C : FloatCfg] (b : Bool) (e : ℤ) :
  coe_q ⟨b, e, C.prec⟩ = (if b then -1 else 1) * 2^(e + 1) := by
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

lemma round_up_def [C : FloatCfg] (q : ℚ) :
  let exp := Int.log 2 |q|
  let mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs
  coe_q (round_up q) = coe_q ⟨(q < 0), exp, mantissa⟩ := by
  set exp := Int.log 2 |q| with exp_def
  set mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs with mantissa_def
  dsimp
  by_cases h' : mantissa = C.prec
  · simp only [round_up, <-exp_def, <-mantissa_def, h', ↓reduceIte]
    rw [coe_q_of_Cprec]
    simp [coe_q]
  simp only [round_up, <-exp_def, <-mantissa_def, ↓reduceIte, h']

lemma round_up_neg [C : FloatCfg] (q : ℚ) (h : q ≠ 0) :
  round_up (-q) = Flean.neg (round_up q) := by
  by_cases h' : q ≥ 0
  · have : q > 0 := lt_of_le_of_ne h' (Ne.symm h)
    by_cases h'' : ⌈(|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) * C.prec⌉.natAbs = C.prec
    <;> simp [round_up, this, h', h'', Flean.neg]
  have : q < 0 := not_le.mp h'
  by_cases h'' : ⌈(|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) * C.prec⌉.natAbs = C.prec
  <;> simp [round_up, Flean.neg, this, le_of_lt this, h'']


lemma mantissa_ge_one [C : FloatCfg] {m : ℕ} : 1 ≤ ((m : ℚ) / C.prec + 1) := by
  suffices 0 ≤ (m : ℚ) / C.prec by linarith
  positivity

--lemma mantissa_2e_pos [C : FloatCfg] {e : ℤ} {m : ℕ} : 0 < ((m : ℚ) / C.prec + 1) * 2^e := by
--  positivity

def q_exp_eq_exp [C : FloatCfg] {e : ℤ} {m : ℕ} (h : m < C.prec) :
  Int.log 2 |((m : ℚ) / ↑C.prec + 1) * 2 ^ e| = e := by
  have mantissa_lt : ((m : ℚ) / C.prec + 1) < 2 := by
    suffices (m : ℚ) / C.prec < 1 by linarith
    suffices (m : ℚ) < C.prec by
      apply Bound.div_lt_one_of_pos_of_lt
      · norm_cast; exact Nat.zero_lt_of_lt h
      exact this
    norm_cast
  rw [abs_of_nonneg (by positivity)]
  exact log_one_to_two_eq (by norm_num) mantissa_ge_one (by norm_cast)

lemma q_mantissa_eq_mantissa [C : FloatCfg] {e : ℤ} {m : ℕ} (h : m < C.prec) :
  |(((m : ℚ)/C.prec) + 1) * 2^e| * 2^(-Int.log 2 |(((m : ℚ)/C.prec) + 1) * 2^e|) = (m : ℚ) / C.prec + 1 := by
  rw [q_exp_eq_exp h, abs_of_pos (by positivity), zpow_neg, mul_assoc,
    mul_inv_cancel₀, mul_one]
  positivity


lemma round_down_coe [C : FloatCfg] (f : FloatRep) (h : f.valid) :
  round_down (coe_q f) = f := by
  rcases f with ⟨s, e, m⟩
  suffices round_down (coe_q ⟨false, e, m⟩) = ⟨false, e, m⟩ by
    cases s
    · exact this
    rw [neg_false, coe_q_of_neg, round_down_of_neg,
      neg_invertible.injective.eq_iff]
    · exact this
    symm; apply ne_of_lt coe_false_pos
  simp only [round_down, coe_q, Bool.false_eq_true, ↓reduceIte, one_mul,
    zpow_neg, FloatRep.mk.injEq, decide_eq_false_iff_not, not_lt]
  refine ⟨?_, ?_, ?_⟩
  · positivity
  · exact q_exp_eq_exp h
  rw [<-zpow_neg, q_mantissa_eq_mantissa h]
  rw [add_sub_cancel_right, div_mul_cancel₀, Int.floor_natCast, Int.natAbs_ofNat]
  norm_cast
  exact ne_of_gt C.prec_pos

lemma coe_q_inj_valid [C : FloatCfg] {f1 f2 : FloatRep}
  (h : f1.valid) (h' : f2.valid) :
  coe_q f1 = coe_q f2 → f1 = f2 := by
  nth_rw 2 [<- round_down_coe (h := h), <- round_down_coe (h := h')]
  exact fun a ↦ congrArg round_down a


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
  suffices ⌊q * n⌋.natAbs < (n : ℤ) by
    norm_cast at this
  rw [Int.natAbs_of_nonneg (by positivity)]
  suffices q * n < n by
    exact Int.floor_lt.mpr this
  exact (mul_lt_iff_lt_one_left (by norm_cast : 0 < (n : ℚ))).2 h

lemma round_down_valid [C : FloatCfg] (q : ℚ) (h : q ≠ 0):
  (round_down q).valid := by
  simp only [round_down, zpow_neg]
  have m_nonneg : 0 ≤ |q| * (2 ^ Int.log 2 |q|)⁻¹ - 1 := by
    linarith [(mantissa_size_aux q h).1]
  have m_small : |q| * (2 ^ Int.log 2 |q|)⁻¹ - 1 < 1 := by
    linarith [(mantissa_size_aux q h).2]
  exact small_floor_aux m_small m_nonneg C.prec_pos

lemma small_ceil {q : ℚ} {n : ℕ} (h : q ≤ 1) (h' : 0 ≤ q) (n_nonneg : 0 ≤ n):
  ⌈q * n⌉.natAbs ≤ n := by
  suffices ⌈q * n⌉.natAbs ≤ (n : ℤ) by
    norm_cast at this
  rw [Int.natAbs_of_nonneg (by positivity)]
  apply Int.ceil_le.mpr
  exact mul_le_of_le_one_left (by norm_cast) h


lemma round_up_valid [C : FloatCfg] (q : ℚ) (h' : q ≠ 0):
  (round_up q).valid := by
  by_cases h : ⌈(|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) * C.prec⌉.natAbs = C.prec
  <;> simp only [round_up, zpow_neg, h, ↓reduceIte]
  · exact C.prec_pos
  rw [FloatRep.valid]; dsimp
  have : (|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) ≤ 1 := by
    linarith [(mantissa_size_aux q h').2]
  apply lt_of_le_of_ne
  · apply small_ceil this
    linarith [(mantissa_size_aux q h').1]
    exact Nat.zero_le _
  exact h

lemma round_up_coe [C : FloatCfg] (f : FloatRep) (h : f.valid) :
  round_up (coe_q f) = f := by
  rcases f with ⟨s, e, m⟩
  suffices round_up (coe_q ⟨false, e, m⟩) = ⟨false, e, m⟩ by
    cases s
    · exact this
    rw [neg_false, coe_q_of_neg, round_up_neg,
      neg_invertible.injective.eq_iff]
    · exact this
    symm; apply ne_of_lt coe_false_pos
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

lemma round_nearest_eq_or [C : FloatCfg] (q : ℚ) :
  round_nearest q = round_down q ∨ round_nearest q = round_up q := by
  unfold round_nearest
  rcases round_down q with ⟨s, e, m⟩
  rcases round_up q with ⟨s', e', m'⟩
  repeat (first | split | tauto)


lemma round_nearest_coe [C : FloatCfg] (f : FloatRep) (h : f.valid) :
  round_nearest (coe_q f) = f := by
  rcases round_nearest_eq_or (coe_q f) with h' | h'
  · rw [h', round_down_coe f h]
  rw [h', round_up_coe f h]

lemma round_nearest_valid [C : FloatCfg] (q : ℚ) (h' : q ≠ 0) :
  (round_nearest q).valid := by
  rcases round_nearest_eq_or q with h | h <;> rw [h]
  · exact round_down_valid q h'
  exact round_up_valid q h'

def subnormal_to_q [C : FloatCfg] : Bool × ℕ →  ℚ
| (b, m) =>
  let s := if b then -1 else 1
  s * (m / C.prec) * 2^C.emin

def subnormal_round_down [C : FloatCfg] (q : ℚ) : Bool × ℕ :=
  (q < 0, ⌊|q| * 2^(-C.emin) * C.prec⌋.natAbs)

lemma subnormal_round_down_coe [C : FloatCfg] (b : Bool) (m : ℕ) (m_nonneg : m > 0) :
  subnormal_round_down (subnormal_to_q (b, m)) = (b, m) := by
  cases b <;> {
    simp only [subnormal_round_down, subnormal_to_q, Bool.false_eq_true, ↓reduceIte, one_mul,
      zpow_neg, Prod.mk.injEq, decide_eq_false_iff_not, not_lt, ge_iff_le, neg_mul, one_mul, Left.neg_neg_iff,
      decide_eq_true_iff, abs_neg]
    have : C.prec > 0 := C.prec_pos
    constructor
    · positivity
    rw [abs_of_pos (by positivity), mul_assoc, mul_assoc, <-mul_assoc (2 ^ _),
      mul_inv_cancel₀, one_mul]
    rw [div_mul_cancel₀, Int.floor_natCast, Int.natAbs_ofNat]
    · positivity
    positivity
  }

lemma subnormal_exp_small [C: FloatCfg] {q : ℚ} (q_nonneg : q ≠ 0)
  (h : Int.log 2 |q| < C.emin) : |q| * 2 ^ (-C.emin) < 1 := by
  set e := Int.log 2 |q|
  have q_term_small : |q| * 2^(-e) < 2 := by
    rw [zpow_neg]
    exact (mantissa_size_aux q q_nonneg).2
  have emin_smaller_than_e : (2: ℚ)^(-C.emin) ≤ 2^(-e - 1) := by
    rw [zpow_le_zpow_iff_right₀ (by norm_num)]
    linarith
  calc
    |q| * 2 ^ (-C.emin) ≤ |q| * 2^(-e - 1) := by
      exact mul_le_mul_of_nonneg_left emin_smaller_than_e (abs_nonneg _)
    _ = |q| * 2^(-e) / 2 := by
      rw [zpow_sub₀ (by norm_num)]
      ring
    _ < 1 := by linarith

def ValidSubnormalRounding [C : FloatCfg] (f : ℚ → Bool × ℕ) : Prop :=
  ∀ q : ℚ, q ≠ 0 → Int.log 2 |q| < C.emin → (f q).2 ≤ C.prec

lemma subnormal_round_down_valid [C : FloatCfg] :
  ValidSubnormalRounding subnormal_round_down := by
  simp only [ValidSubnormalRounding, subnormal_round_down]
  intro q q_nonneg h
  apply le_of_lt
  exact small_floor_aux (subnormal_exp_small q_nonneg h) (by positivity) C.prec_pos

def subnormal_round_up [C : FloatCfg] (q : ℚ) : Bool × ℕ :=
  (q < 0, ⌈|q| * 2^(-C.emin) * C.prec⌉.natAbs)

-- This is essentially a copy of subnormal_round_down_coe
-- FIX
lemma subnormal_round_up_coe [C : FloatCfg] (b : Bool) (m : ℕ) (m_nonneg : m > 0) :
  subnormal_round_up (subnormal_to_q (b, m)) = (b, m) := by
  cases b <;> {
    simp only [subnormal_round_up, subnormal_to_q, Bool.false_eq_true, ↓reduceIte, one_mul,
      zpow_neg, Prod.mk.injEq, decide_eq_false_iff_not, not_lt, neg_mul, one_mul, Left.neg_neg_iff, decide_eq_true_eq, abs_neg]
    have : C.prec > 0 := C.prec_pos
    constructor
    · positivity
    rw [abs_of_pos (by positivity), mul_assoc, mul_assoc, <-mul_assoc (2 ^ _),
      mul_inv_cancel₀, one_mul]
    rw [div_mul_cancel₀, Int.ceil_natCast, Int.natAbs_ofNat]
    · positivity
    positivity
  }

lemma subnormal_round_up_valid [C : FloatCfg] :
  ValidSubnormalRounding subnormal_round_up := by
  rw [ValidSubnormalRounding]
  intro q q_nonneg h
  rw [subnormal_round_up]
  apply small_ceil (le_of_lt (subnormal_exp_small q_nonneg h)) (by positivity) (le_of_lt C.prec_pos)

def subnormal_round_nearest [C : FloatCfg] (q : ℚ) : Bool × ℕ :=
  let sm := subnormal_round_down q
  let sm' := subnormal_round_up q
  if _ : |q| - sm.2 / C.prec < sm'.2 / C.prec - |q| then
    sm
  else if _ : |q| - sm.2 / C.prec > sm'.2 / C.prec - |q| then
    sm'
  else if _ : sm.2 % 2 = 0 then
    sm
  else
    sm'

lemma subnormal_round_nearest_eq [C : FloatCfg] (q : ℚ) :
  subnormal_round_nearest q = subnormal_round_down q ∨
  subnormal_round_nearest q = subnormal_round_up q := by
  unfold subnormal_round_nearest
  simp only [gt_iff_lt, ite_eq_left_iff, not_lt, tsub_le_iff_right]
  repeat (first | split | tauto)

lemma subnormal_round_nearest_coe [C : FloatCfg] (f : Bool × ℕ) (h : f.2 > 0) :
  subnormal_round_nearest (subnormal_to_q f) = f := by
  rcases subnormal_round_nearest_eq (subnormal_to_q f) with h' | h' <;> rw [h']
  · apply subnormal_round_down_coe f.1 f.2 h
  exact subnormal_round_up_coe f.1 f.2 h

lemma subnormal_round_nearest_valid [C : FloatCfg] :
  ValidSubnormalRounding subnormal_round_nearest := by
  simp only [ValidSubnormalRounding]
  intro q q_nonneg h
  rcases subnormal_round_nearest_eq q with h' | h' <;> rw [h']
  · exact subnormal_round_down_valid q q_nonneg h
  exact subnormal_round_up_valid q q_nonneg h


def to_float [C : FloatCfg] (q : ℚ) : Flean.Float :=
  match sem_def : round_down q with
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
      apply lt_of_le_of_ne ?_ h_eq_prec
      have : e = (round_down q).2 := by
        rw [sem_def]
      rw [this] at h
      exact subnormal_round_nearest_valid q q_nonneg h
  else if h' : e > C.emax then
    Flean.Float.inf s
  else by
    refine Flean.Float.normal s e m ?_
    refine ⟨Int.not_lt.mp h, Int.not_lt.mp h', ?_⟩
    have : m = (round_down q).m := by
      rw [sem_def]
    rw [this]
    exact round_down_valid q (q_nonneg)

def to_rat [C : FloatCfg] : Flean.Float → ℚ
| Flean.Float.inf _ => 0
| Flean.Float.nan => 0
| Flean.Float.normal s e m _ => coe_q ⟨s, e, m⟩
| Flean.Float.subnormal s m _ => subnormal_to_q ⟨s, m⟩


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
--#eval @coe_q C (@round_down C 3.5)
--#eval @round_down C 0
