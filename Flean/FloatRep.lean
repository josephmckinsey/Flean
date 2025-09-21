import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Int.Log
import Flean.FloatCfg
import Flean.LogRules
import Mathlib.Tactic


structure FloatRep (α : FloatCfg) where
  (s : Bool) (e : ℤ) (m : ℕ)

variable {C : FloatCfg}

instance : Repr (FloatRep C) where
  reprPrec := fun ⟨s, e, m⟩ _ => "⟨" ++ repr s ++ ", " ++ repr e ++ ", " ++ repr m ++ "⟩"


def FloatRep.decEq (f1 f2 : FloatRep C) : Decidable (Eq f1 f2) := by
  rw [FloatRep.mk.injEq]
  exact instDecidableAnd

def FloatRep.valid_m (f : FloatRep C) : Prop := f.m < C.prec

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
    (0 : ℚ) ≤ m / C.prec := by simp [div_nonneg]
    _ < m/C.prec + 1 := lt_add_one _

def FloatRep.neg {C  : FloatCfg} : FloatRep C → FloatRep C
| ⟨s, e, m⟩ => ⟨!s, e, m⟩

lemma Flean.neg_neg : (@FloatRep.neg C) ∘ (@FloatRep.neg C) = id := by
  funext ⟨s, e, m⟩
  simp [FloatRep.neg]

lemma neg_invertible : Function.Bijective (@FloatRep.neg C) := by
  apply Function.bijective_iff_has_inverse.2
  refine ⟨FloatRep.neg, Function.leftInverse_iff_comp.2 ?_, Function.rightInverse_iff_comp.2 ?_⟩
  <;> exact Flean.neg_neg

lemma neg_valid_m {f : FloatRep C} :
  (FloatRep.neg f).valid_m ↔ (f.valid_m) := by
  simp [FloatRep.valid_m, FloatRep.neg]

lemma coe_q_of_neg (f : FloatRep C) :
  coe_q (FloatRep.neg f) = -coe_q f:= by
  by_cases h : f.s <;> simp [coe_q, h, FloatRep.neg]
  · ring
  ring


lemma neg_false (e : ℤ) (m : ℕ) : ⟨true, e, m⟩ = (FloatRep.neg ⟨false, e, m⟩ : FloatRep C) := rfl
lemma neg_true (e : ℤ) (m : ℕ) : ⟨false, e, m⟩ = (FloatRep.neg ⟨true, e, m⟩ : FloatRep C) := rfl

lemma coe_q_true_neg {e : ℤ} {m : ℕ} :
  coe_q (⟨true, e, m⟩ : FloatRep C) < 0 := by
  rw [neg_false, coe_q_of_neg]
  simp only [Left.neg_neg_iff, coe_q_false_pos]

lemma coe_q_nezero {f : FloatRep C} :
  coe_q f ≠ 0 := by
  rcases f with ⟨s, e, m⟩
  cases s
  · linarith [coe_q_false_pos (C := C) (e := e) (m := m)]
  linarith [coe_q_true_neg (C := C) (e := e) (m := m)]

lemma floatrep_of_false₁ (P : FloatRep C → Prop)
  (h1 : ∀ f, P (FloatRep.neg f) → P f)
  (h2 : ∀ e m, P ⟨false, e, m⟩) (f : FloatRep C) :
  P f := by
  rcases f with ⟨s, e, m⟩
  cases s
  · exact h2 e m
  apply h1
  rw [<-neg_true]
  exact h2 e m

lemma floatrep_of_false₂ (P : FloatRep C → FloatRep C → Prop)
  (h1 : ∀ f1 f2, P (FloatRep.neg f1) f2 → P f1 f2)
  (h2 : ∀ f1 f2, P f1 (FloatRep.neg f2) → P f1 f2)
  (h3 : ∀ e e' m m', P ⟨false, e, m⟩ ⟨false, e', m'⟩) (f1 f2 : FloatRep C) :
  P f1 f2 := by
  apply floatrep_of_false₁ (f := f2)
  · apply h2
  apply floatrep_of_false₁ (f := f1)
  · intro f h e m
    apply h1
    apply h
  intro e m e' m'
  apply h3

lemma coe_q_of_Cprec (b : Bool) (e : ℤ) :
  coe_q (⟨b, e, C.prec⟩ : FloatRep C) = (if b then -1 else 1) * 2^(e + 1) := by
  wlog h : b = false
  · simp [h, neg_false, coe_q_of_neg, this]
  simp only [h, coe_q, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [div_self]
  · simp [zpow_add_one₀]
    ring
  exact Nat.cast_ne_zero.mpr (by linarith [C.prec_pos])

def FloatRep.valid_e (f : FloatRep C) : Prop := C.emin ≤ f.e ∧ f.e ≤ C.emax

lemma neg_valid_e {f : FloatRep C} :
  (FloatRep.neg f).valid_e ↔ (f.valid_e) := by
  simp [FloatRep.valid_e, FloatRep.neg]

lemma floatrep_e_le_of_coe_q (f1 f2 : FloatRep C) (vm2 : f2.valid_m) (h : |coe_q f1| ≤ |coe_q f2|) :
  f1.e ≤ f2.e := by
  revert h vm2
  apply floatrep_of_false₂ (f1 := f1) (f2 := f2)
  · simp_rw [coe_q_of_neg]; simp [FloatRep.neg]
  · intro f1 f2 h
    rw [neg_valid_m, coe_q_of_neg, abs_neg, FloatRep.neg] at h
    exact h
  intro e1 e2 m1 m2 vm2 h
  rw [abs_of_pos coe_q_false_pos, abs_of_pos coe_q_false_pos] at h
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
  revert ve vm
  apply floatrep_of_false₁ (f := f)
  · simp [neg_valid_m, neg_valid_e, coe_q_of_neg, abs_neg]
  intro e m ve vm
  rw [coe_q]
  constructor
  <;> simp only [Bool.false_eq_true, ↓reduceIte, one_mul, q_exp_eq_exp vm]
  · exact ve.1
  exact ve.2

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


def floatrep_le_pos (f1 f2 : FloatRep C) : Prop :=
  (f1.e < f2.e) ∨ (f1.e = f2.e ∧ f1.m ≤ f2.m)

def floatrep_le_pos' (f1 f2 : FloatRep C) : Prop :=
  (f1.e ≤ f2.e) ∧ (f1.e = f2.e → f1.m ≤ f2.m)

lemma floatrep_pos_equiv (f1 f2 : FloatRep C) :
  (floatrep_le_pos f1 f2) ↔ (floatrep_le_pos' f1 f2) := by
  simp [floatrep_le_pos, floatrep_le_pos']
  constructor
  · rintro (h | h)
    · refine ⟨le_of_lt h, ?_⟩
      intro h
      linarith
    refine ⟨le_of_eq h.1, ?_⟩
    intro _
    exact h.2
  intro h
  by_cases h' : f1.e = f2.e
  · right; tauto
  left; exact lt_of_le_of_ne h.1 h'

lemma floatrep_le_pos_neg₁ (f1 f2 : FloatRep C) :
  floatrep_le_pos (FloatRep.neg f1) f2 ↔ floatrep_le_pos f1 f2 := by
  simp [FloatRep.neg, floatrep_le_pos]

lemma floatrep_le_pos_neg₂ (f1 f2 : FloatRep C) :
  floatrep_le_pos f1 (FloatRep.neg f2) ↔ floatrep_le_pos f1 f2 := by
  simp [FloatRep.neg, floatrep_le_pos]

lemma floatrep_le_pos_coe_q (f1 f2 : FloatRep C) (vm1 : f1.m ≤ C.prec) :
  (floatrep_le_pos f1 f2) → |coe_q f1| ≤ |coe_q f2| := by
  revert vm1
  have almost_valid_neg {C : FloatCfg} (f : FloatRep C) : (FloatRep.neg f).m ≤ C.prec ↔ f.m ≤ C.prec := by
    simp [FloatRep.neg]
  apply floatrep_of_false₂ (f1 := f1) (f2 := f2)
  · simp [floatrep_le_pos_neg₁, almost_valid_neg, coe_q_of_neg]
  · simp [floatrep_le_pos_neg₂, coe_q_of_neg]
  intro e e' m m' vm1 h
  rw [abs_of_pos coe_q_false_pos, abs_of_pos coe_q_false_pos]
  rw [coe_q, coe_q]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  simp_rw [floatrep_le_pos] at h
  rcases h with h | h'
  · calc
      (↑m / ↑C.prec + 1) * (2 : ℚ) ^ e ≤ 2 * 2^e := by
        gcongr
        if h : m = C.prec then
          rw [h]
          have := C.prec_pos
          field_simp
          linarith
        else
          have : m < C.prec := by simp at vm1; apply lt_of_le_of_ne vm1 h
          apply le_of_lt
          exact mantissa_lt_two this
      _ ≤ 2^e' := by
        rw [mul_comm, <-zpow_add_one₀ (by norm_num), zpow_le_zpow_iff_right₀ (by norm_num)]
        exact h
      _ ≤ ((m' : ℚ) / C.prec + 1) * 2^e' := by
        rw [le_mul_iff_one_le_left (by positivity)]
        exact mantissa_ge_one
  gcongr
  exact h'.2
  norm_num
  rw [h'.1]

lemma coe_q_le_floatrep_pos (f1 f2 : FloatRep C) (vm2 : f2.valid_m) :
  |coe_q f1| ≤ |coe_q f2| → floatrep_le_pos f1 f2 := by
  revert vm2
  apply floatrep_of_false₂ (f1 := f1) (f2 := f2)
  · simp [floatrep_le_pos_neg₁, coe_q_of_neg]
  · simp [floatrep_le_pos_neg₂, neg_valid_m, coe_q_of_neg]
  intro e e' m m' vm2 h
  rw [floatrep_pos_equiv]
  refine ⟨floatrep_e_le_of_coe_q _ _ vm2 h, ?_⟩
  simp only [FloatRep.valid_m, coe_q] at *
  intro e_eq
  rw [e_eq] at h
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at h
  have := C.prec_pos
  rw [abs_of_pos (by positivity), abs_of_pos (by positivity)] at h
  suffices (m : ℚ) / C.prec ≤ (m' : ℚ) / C.prec by
    rw [div_le_div_iff_of_pos_right (by norm_cast)] at this
    exact_mod_cast this
  rw [mul_le_mul_iff_of_pos_right (by positivity)] at h
  linarith

lemma floatrep_le_pos_iff_coe_q (f1 f2 : FloatRep C) (vm1 : f1.m ≤ C.prec) (vm2 : f2.valid_m) :
  floatrep_le_pos f1 f2 ↔ |coe_q f1| ≤ |coe_q f2| := by
  refine ⟨floatrep_le_pos_coe_q f1 f2 vm1, coe_q_le_floatrep_pos f1 f2 vm2⟩


def floatrep_le (f1 f2 : FloatRep C) : Prop :=
  match (f1.s, f2.s) with
  | (false, false) => floatrep_le_pos f1 f2
  | (false, true) => False
  | (true, false) => True
  | (true, true) => (floatrep_le_pos (FloatRep.neg f2) (FloatRep.neg f1))

lemma floatrep_le_iff_coe_q_le (f1 f2 : FloatRep C) (vm1 : f1.valid_m) (vm2 : f2.valid_m) :
  floatrep_le f1 f2 ↔ coe_q f1 ≤ coe_q f2 := by
  -- We could extract the logic here, but we'll only do that for q
  rcases f1 with ⟨s, e, m⟩
  rcases f2 with ⟨s', e', m'⟩
  rcases s <;> rcases s'
  · rw [<-abs_of_pos (coe_q_false_pos (e := e) (m := m))]
    rw [<-abs_of_pos (coe_q_false_pos (e := e') (m := m'))]
    apply floatrep_le_pos_iff_coe_q (vm1 := le_of_lt vm1) (vm2 := vm2)
  · simp [floatrep_le]
    simp [coe_q]
    apply lt_trans (b := 0)
    · rw [<-neg_add, neg_mul, neg_lt_zero]; positivity
    positivity
  · simp [floatrep_le]
    simp [coe_q]
    apply le_of_lt
    apply lt_trans (b := 0)
    · rw [<-neg_add, neg_mul, neg_lt_zero]; positivity
    positivity
  rw [neg_false, neg_false]
  rw [coe_q_of_neg, coe_q_of_neg]
  rw [neg_le_neg_iff]
  simp [floatrep_le, FloatRep.neg]
  rw [<-abs_of_pos (coe_q_false_pos (e := e) (m := m))]
  rw [<-abs_of_pos (coe_q_false_pos (e := e') (m := m'))]
  exact floatrep_le_pos_iff_coe_q ⟨false, e', m'⟩ _ (le_of_lt vm2) vm1
