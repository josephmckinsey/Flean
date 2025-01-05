import Flean.FloatCfg
import Flean.LogRules

variable {C : FloatCfg}

structure SubnormRep (C : FloatCfg) where
  (s : Bool) (m : ℕ)

def SubnormRep.nonzero (f : SubnormRep C) : Prop := f.m > 0

def subnormal_to_q : SubnormRep C →  ℚ
| ⟨b, m⟩ =>
  let s := if b then -1 else 1
  s * (m / C.prec) * 2^C.emin

def subnormal_round_down (q : ℚ) : SubnormRep C :=
  ⟨q < 0, ⌊|q| * 2^(-C.emin) * C.prec⌋.natAbs⟩


lemma subnormal_round_down_coe (s : SubnormRep C) (h : s.nonzero) :
  subnormal_round_down (subnormal_to_q s) = s := by
  rcases s with ⟨b, m⟩
  cases b <;> {
    simp only [subnormal_round_down, subnormal_to_q, Bool.false_eq_true, ↓reduceIte, one_mul,
      zpow_neg, SubnormRep.mk.injEq, decide_eq_false_iff_not, not_lt, ge_iff_le, neg_mul, one_mul, Left.neg_neg_iff,
      decide_eq_true_iff, abs_neg]
    have : C.prec > 0 := C.prec_pos
    have m_nonneg : m > 0 := h
    constructor
    · positivity
    rw [abs_of_pos (by positivity), mul_assoc, mul_assoc, <-mul_assoc (2 ^ _),
      mul_inv_cancel₀, one_mul]
    rw [div_mul_cancel₀, Int.floor_natCast, Int.natAbs_ofNat]
    · positivity
    positivity
  }

lemma subnormal_exp_small {q : ℚ} (q_nonneg : q ≠ 0)
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

def ValidSubnormalRounding (f : ℚ → SubnormRep C) : Prop :=
  ∀ q : ℚ, q ≠ 0 → Int.log 2 |q| < C.emin → (f q).2 ≤ C.prec

lemma subnormal_round_down_valid :
  ValidSubnormalRounding (subnormal_round_down : ℚ → SubnormRep C) := by
  simp only [ValidSubnormalRounding, subnormal_round_down]
  intro q q_nonneg h
  apply le_of_lt
  exact small_floor_aux (subnormal_exp_small q_nonneg h) (by positivity) C.prec_pos

def subnormal_round_up (q : ℚ) : SubnormRep C :=
  ⟨q < 0, ⌈|q| * 2^(-C.emin) * C.prec⌉.natAbs⟩

-- This is essentially a copy of subnormal_round_down_coe
-- FIX
lemma subnormal_round_up_coe (s : SubnormRep C) (h : s.nonzero) :
  subnormal_round_up (subnormal_to_q s) = s := by
  rcases s with ⟨b, m⟩
  cases b <;> {
    simp only [subnormal_round_up, subnormal_to_q, Bool.false_eq_true, ↓reduceIte, one_mul,
      zpow_neg, SubnormRep.mk.injEq, decide_eq_false_iff_not, not_lt, neg_mul, one_mul, Left.neg_neg_iff, decide_eq_true_eq, abs_neg]
    have : C.prec > 0 := C.prec_pos
    have : m > 0 := h
    constructor
    · positivity
    rw [abs_of_pos (by positivity), mul_assoc, mul_assoc, <-mul_assoc (2 ^ _),
      mul_inv_cancel₀, one_mul]
    rw [div_mul_cancel₀, Int.ceil_natCast, Int.natAbs_ofNat]
    · positivity
    positivity
  }

lemma subnormal_round_up_valid :
  ValidSubnormalRounding (subnormal_round_up : ℚ → SubnormRep C) := by
  rw [ValidSubnormalRounding]
  intro q q_nonneg h
  rw [subnormal_round_up]
  apply small_ceil (le_of_lt (subnormal_exp_small q_nonneg h)) (by positivity) (le_of_lt C.prec_pos)

def subnormal_round_nearest (q : ℚ) : SubnormRep C :=
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

lemma subnormal_round_nearest_eq (q : ℚ) :
  (subnormal_round_nearest q : SubnormRep C) = subnormal_round_down q ∨
  (subnormal_round_nearest q : SubnormRep C) = subnormal_round_up q := by
  unfold subnormal_round_nearest
  simp only [gt_iff_lt, ite_eq_left_iff, not_lt, tsub_le_iff_right]
  repeat (first | split | tauto)

lemma subnormal_round_nearest_coe (s : SubnormRep C) (h : s.nonzero) :
  subnormal_round_nearest (subnormal_to_q s) = s := by
  rcases subnormal_round_nearest_eq (subnormal_to_q s) with h' | h' <;> rw [h']
  · apply subnormal_round_down_coe s h
  exact subnormal_round_up_coe s h

lemma subnormal_round_nearest_valid :
  ValidSubnormalRounding (subnormal_round_nearest : ℚ → SubnormRep C) := by
  simp only [ValidSubnormalRounding]
  intro q q_nonneg h
  rcases subnormal_round_nearest_eq q with h' | h' <;> rw [h']
  · exact subnormal_round_down_valid q q_nonneg h
  exact subnormal_round_up_valid q q_nonneg h
