import Flean.FloatRep
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Int.Log
import Flean.FloatCfg
import Flean.LogRules
import Flean.IntRounding
import Mathlib.Tactic


variable {C : FloatCfg}


def FloatRep.normalize (f : FloatRep C) : FloatRep C :=
  if f.m = C.prec then
    ⟨f.s, f.e + 1, 0⟩
  else
    f

lemma normalize_valid (f : FloatRep C) (h : f.m ≤ C.prec) :
  f.normalize.valid_m := by
  simp only [FloatRep.valid_m, FloatRep.normalize]
  split_ifs with h'
  · simp [C.prec_pos]
  exact lt_of_le_of_ne h h'

lemma coe_normalize (f : FloatRep C) (h : f.m ≤ C.prec) :
  coe_q f.normalize = coe_q f := by
  simp only [FloatRep.normalize]
  split_ifs with h'
  · rcases f with ⟨s, e, m⟩
    simp only [coe_q]
    dsimp at h'
    rw [h', div_self (by exact_mod_cast ne_of_gt C.prec_pos)]
    rw [zpow_add_one₀ (by norm_num)]
    ring
  rfl


lemma normalize_neg (f : FloatRep C) :
  (Flean.neg f).normalize = Flean.neg f.normalize := by
  rcases f with ⟨s, e, m⟩
  simp only [FloatRep.normalize, Flean.neg]
  split_ifs <;> simp

def roundf (r : IntRounder) (q : ℚ) : FloatRep C :=
  let exp := Int.log 2 |q|
  let mantissa := (|q| * (2^exp)⁻¹ - 1) * C.prec
  FloatRep.normalize ⟨q < 0, exp, r (q < 0) mantissa⟩



lemma roundf_neg (r : IntRounder) {q : ℚ}
  (h : q ≠ 0) :
  roundf (r.neg) (-q) = Flean.neg (roundf r q : FloatRep C) := by
  rw [roundf, roundf, <-normalize_neg]
  apply congrArg FloatRep.normalize
  by_cases h' : q ≥ 0
  · have : q > 0 := lt_of_le_of_ne h' (Ne.symm h)
    simp only [roundf, Left.neg_neg_iff, this, decide_true, abs_neg, IntRounder.neg, Bool.not_true,
      zpow_neg, Flean.neg, decide_eq_false h'.not_lt, Bool.not_false]
  have : q < 0 := not_le.mp h'
  simp [roundf, IntRounder.neg, decide_eq_false, Flean.neg, this, le_of_lt this]

lemma round_symmetry₁ (P : (r : IntRounder) → FloatRep C → Prop)
  (h1 : ∀ r f, P (r.neg) (Flean.neg f) → P r f)
  (h2 : ∀ r e m, P r ⟨false, e, m⟩) (r : IntRounder) (f : FloatRep C) :
  P r f := by
  rcases f with ⟨s, e, m⟩
  cases s
  · exact h2 r e m
  apply h1
  rw [<-neg_true]
  exact h2 r.neg e m

lemma roundf_coe (r : IntRounder) [rh : ValidRounder r]
  (f : FloatRep C) (h : f.valid_m) :
  roundf r (coe_q f) = f := by
  revert h rh
  apply round_symmetry₁ (r := r) (f := f)
  · intro r
    intro f
    rw [coe_q_of_neg, neg_valid_rounder, neg_valid_m, roundf_neg r coe_q_nezero, neg_invertible.injective.eq_iff]
    tauto
  intro r e m rh h
  simp only [roundf, FloatRep.normalize, coe_q, Bool.false_eq_true, ↓reduceIte, one_mul, zpow_neg, FloatRep.mk.injEq,
    decide_eq_false_iff_not, not_lt]
  rw [q_mantissa_eq_mantissa h, add_sub_cancel_right,
    div_mul_cancel₀, ValidRounder.leftInverse (f := r)]
  split_ifs with h'
  · simp only at h'
    simp [FloatRep.valid_m] at h h'
    linarith
  simp only [FloatRep.mk.injEq, decide_eq_false_iff_not, not_lt]
  refine ⟨?_, ?_, ?_⟩
  · positivity
  · exact q_exp_eq_exp h
  · trivial
  norm_cast
  exact ne_of_gt C.prec_pos


def round_down : ℚ → FloatRep C := roundf round0

lemma round0_neg :
  IntRounder.neg round0 = round0 := rfl

lemma round_down_neg (q : ℚ) (h : q ≠ 0) :
  round_down (-q) = Flean.neg (round_down q : FloatRep C) := by
  rw [round_down, <-round0_neg, roundf_neg, round0_neg]
  exact h

lemma round_down_coe (f : FloatRep C) (h : f.valid_m) :
  round_down (coe_q f) = f := roundf_coe round0 f h

lemma coe_q_inj_valid {f1 f2 : FloatRep C}
  (h : f1.valid_m) (h' : f2.valid_m) :
  coe_q f1 = coe_q f2 → f1 = f2 := by
  nth_rw 2 [<- roundf_coe round0 (h := h), <- roundf_coe round0 (h := h')]
  exact fun a ↦ congrArg (roundf round0) a

lemma roundf_almost_valid (r : IntRounder) [rh : ValidRounder r] (q : ℚ) (h : q ≠ 0) :
  r (decide (q < 0)) ((|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) * ↑C.prec) ≤ C.prec := by
  nth_rw 2 [<-ValidRounder.leftInverse (f := r) (q < 0) C.prec]
  apply ValidRounder.le_iff_le
  · apply mantissa_nonneg (q_nezero := h)
  nth_rw 2 [<-one_mul (C.prec : ℚ)]
  gcongr -- magic
  linarith [(mantissa_size_aux q h).2]

lemma roundf_valid (r : IntRounder) [rh : ValidRounder r] (q : ℚ) (h : q ≠ 0) :
  (roundf r q : FloatRep C).valid_m := by
  simp [roundf, FloatRep.valid_m]
  have m_nonneg : 0 ≤ |q| * (2 ^ Int.log 2 |q|)⁻¹ - 1 := by
    linarith [(mantissa_size_aux q h).1]
  have m_small : |q| * (2 ^ Int.log 2 |q|)⁻¹ - 1 < 1 := by
    linarith [(mantissa_size_aux q h).2]
  apply normalize_valid
  apply roundf_almost_valid (r := r) (h := h)

lemma round_down_valid (q : ℚ) (h : q ≠ 0):
  (round_down q : FloatRep C).valid_m := by
  apply roundf_valid (r := round0) (h := h)

lemma roundf_of_pos (r : IntRounder) [rh : ValidRounder r] (q : ℚ) (h : 0 < q) :
  0 < coe_q (roundf r q : FloatRep C) := by
  rw [roundf, coe_normalize, coe_q]
  simp only [decide_eq_true_eq, ite_mul, neg_mul, one_mul, neg_add_rev]
  split
  · linarith
  positivity
  apply roundf_almost_valid (r := r) (h := ne_of_gt h)

lemma round_down_of_pos (q : ℚ) (h : 0 < q) :
  0 < coe_q (round_down q : FloatRep C) := roundf_of_pos round0 q h

lemma roundf_of_pos' (r : IntRounder) (q : ℚ) (h : 0 < q) :
  (roundf r q : FloatRep C).s = false := by
  simp [roundf, FloatRep.normalize]
  rw [decide_eq_false (not_lt_of_gt h)]
  split <;> simp

lemma round_down_of_pos' (q : ℚ) (h : 0 < q) :
  (round_down q : FloatRep C).s = false := roundf_of_pos' round0 q h

lemma roundf_of_neg (r : IntRounder) [rh : ValidRounder r] (q : ℚ) (h : q < 0) :
  coe_q (roundf r q : FloatRep C) < 0 := by
  suffices 0 < -coe_q (roundf r q : FloatRep C) by
    exact Left.neg_pos_iff.mp this
  rw [<-coe_q_of_neg, <-roundf_neg r (by linarith)]
  apply roundf_of_pos (rh := ?_)
  · exact Left.neg_pos_iff.mpr h
  exact (neg_valid_rounder r).mpr rh

lemma round_down_of_neg (q : ℚ) (h : q < 0) :
  coe_q (round_down q : FloatRep C) < 0 := roundf_of_neg round0 q h

lemma roundf_of_neg' (r : IntRounder) (q : ℚ) (h : q < 0) :
  (roundf r q : FloatRep C).s = true := by
  simp [roundf, FloatRep.normalize, h]
  split_ifs <;> dsimp

lemma round_down_of_neg' (q : ℚ) (h : q < 0) :
  (round_down q : FloatRep C).s = true := roundf_of_neg' round0 q h



lemma le_roundf_of_le (r : IntRounder) [rh : ValidRounder r] (q1 q2 : ℚ) (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) :
  q1 ≤ q2 → coe_q (roundf r q1 : FloatRep C) ≤ coe_q (roundf r q2 : FloatRep C) := by
  rw [<-floatrep_le_iff_coe_q_le (vm1 := roundf_valid r q1 q1_nezero)
    (vm2 := roundf_valid r q2 q2_nezero)]
  revert r
  apply casesQPlane (q1_nezero := q1_nezero) (q2_nezero := q2_nezero)
  · intro q1 q1h q2 q2h r rh h
    rw [floatrep_le_iff_coe_q_le (vm1 := roundf_valid r q1 (ne_of_gt q1h))
      (vm2 := roundf_valid r q2 (ne_of_gt q2h))]
    rw [roundf, roundf, coe_normalize _ (roundf_almost_valid r q1 (ne_of_gt q1h)),
      coe_normalize _ (roundf_almost_valid r q2 (ne_of_gt q2h))]
    rw [decide_eq_false (not_lt_of_gt q1h), decide_eq_false (not_lt_of_gt q2h)]
    rw [<-abs_of_pos coe_q_false_pos]
    nth_rw 2 [<-abs_of_pos coe_q_false_pos]
    apply floatrep_le_pos_coe_q
    · dsimp
      convert roundf_almost_valid (C := C) r q1 (ne_of_gt q1h)
      simp
      linarith
    rw [floatrep_pos_equiv]
    constructor
    · dsimp
      rw [abs_of_pos q1h, abs_of_pos q2h]
      apply Int.log_mono_right q1h h
    dsimp
    intro h
    apply ValidRounder.le_iff_le (f := r)
    · apply mantissa_nonneg q1 (ne_of_gt q1h) (C := C)
    rw [h]
    gcongr
  · intro q1 q1h q2 q2h r rh h
    simp_rw [floatrep_le, roundf_of_neg' r q1 q1h, roundf_of_pos' r q2 q2h]
  · intro q1 q1h q2 q2h r rh h
    exfalso
    linarith
  · intro q1 q1h q2 q2h ih r rh h
    replace ih := ih (r.neg) (by linarith) (rh := (neg_valid_rounder r).mpr rh)
    rw [roundf_neg r, roundf_neg] at ih
    simp_rw [floatrep_le, roundf_of_neg' r q1 q1h, roundf_of_neg' r q2 q2h]
    simp_rw [floatrep_le, Flean.neg] at ih
    simp_rw [roundf_of_neg' r q1 q1h, roundf_of_neg' r q2 q2h] at ih
    convert ih
    · exact Ne.symm (ne_of_gt q2h)
    exact Ne.symm (ne_of_gt q1h)

lemma le_round_down_of_le (q1 q2 : ℚ) (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) :
  q1 ≤ q2 → coe_q (round_down q1 : FloatRep C) ≤ coe_q (round_down q2 : FloatRep C) :=
  le_roundf_of_le round0 q1 q2 q1_nezero q2_nezero

lemma round_down_false_of_le_coe_aux (q : ℚ) (e : ℤ) (m : ℕ) (vm : m < C.prec) (q_pos : 0 < q)
  (h : q ≤ coe_q (⟨false, e, m⟩ : FloatRep C)) :
  coe_q (round_down q : FloatRep C) ≤ coe_q (⟨false, e, m⟩ : FloatRep C) := by
  rw [<-round_down_coe ⟨false, e, m⟩ vm]
  apply le_round_down_of_le q _ (ne_of_gt q_pos) coe_q_nezero h


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

def round_function (R : Rounding) :=
  match R.mode with
  | RoundingMode.nearest => roundnearest
  | RoundingMode.tozero => round0
  | RoundingMode.toinf => roundinf
  | RoundingMode.up => roundup
  | RoundingMode.down => rounddown

instance (R : Rounding) : ValidRounder (round_function R) := by
  rw [round_function]
  cases R.mode
  <;> infer_instance

def round_rep [R : Rounding] (q : ℚ) : FloatRep C := roundf (round_function R) q

lemma round_rep_coe [R : Rounding] (f : FloatRep C) (h : f.valid_m) :
  round_rep (coe_q f) = f := by
  rw [round_rep]
  apply roundf_coe
  exact h

lemma round_valid_m [R : Rounding] (q : ℚ) (q_nezero: q ≠ 0) :
  (round_rep q : FloatRep C).valid_m := roundf_valid (round_function R) q q_nezero

lemma roundf_min_abs_e (r : IntRounder) [rh : ValidRounder r] {q : ℚ} (h : q ≠ 0) :
  Int.log 2 |q| ≤ (roundf r |q| : FloatRep C).e := by
  have t1 : 2^(Int.log 2 |q|) ≤ |q| := by
    apply Int.zpow_log_le_self (by norm_num) (abs_pos.mpr h)
  have t2 : 2 ^ Int.log 2 |q| = coe_q (C := C) ⟨false, Int.log 2 |q|, 0⟩ := by
    simp [coe_q]
  have : coe_q (roundf r (2^(Int.log 2 |q|)) : FloatRep C) ≤ coe_q (roundf r |q| : FloatRep C) := by
    apply le_roundf_of_le
    · positivity
    · exact abs_ne_zero.mpr h
    exact t1
  rw [t2] at this
  rw [roundf_coe _ _ (by simp [FloatRep.valid_m, C.prec_pos])] at this
  rw [<-abs_of_pos coe_q_false_pos] at this
  rw [<-abs_of_pos (a := coe_q (roundf r |q|)) ?roundreppos] at this
  case roundreppos =>
    apply roundf_of_pos
    exact abs_pos.mpr h
  replace this := coe_q_le_floatrep_pos _ _ ?_ this
  · rw [floatrep_pos_equiv] at this
    unfold floatrep_le_pos' at this
    exact this.1
  apply roundf_valid r |q|
  positivity

lemma round_min_e (r: IntRounder) [rh : ValidRounder r] {q : ℚ} (h : q ≠ 0) :
  Int.log 2 |q| ≤ (roundf r q : FloatRep C).e := by
  by_cases h' : q > 0
  · nth_rw 2 [←abs_of_pos (a := q) h']
    apply roundf_min_abs_e (r := r) h
  rw [show (roundf (C := C) r q).e = (Flean.neg (roundf (C := C) r q)).e by simp [Flean.neg]]
  rw [<-roundf_neg r h]
  rw [←abs_of_nonneg (a := (-q))]
  · rw [<-abs_neg]
    apply roundf_min_abs_e r.neg (q := -q) (rh := (neg_valid_rounder r).mpr rh)
    exact neg_ne_zero.mpr h
  linarith

lemma round_min_e' [R : Rounding] (q : ℚ) (h : q ≠ 0):
  Int.log 2 |q| ≤ (round_rep q : FloatRep C).e := by
  rw [round_rep]
  apply round_min_e (r := round_function R) (h := h)
