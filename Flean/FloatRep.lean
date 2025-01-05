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
  coe_q (⟨false, e, m⟩ : FloatRep C) > 0 := by
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
