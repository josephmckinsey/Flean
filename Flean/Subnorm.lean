import Flean.FloatCfg
import Flean.LogRules
import Flean.IntRounding


variable {C : FloatCfg}

structure SubnormRep (C : FloatCfg) where
  (s : Bool) (m : ℕ)

def SubnormRep.neg (f : SubnormRep C) : SubnormRep C :=
  ⟨¬f.s, f.m⟩

lemma neg_subnorm_involutive : Function.Involutive (@SubnormRep.neg C) := by
  unfold Function.Involutive
  simp [SubnormRep.neg]

def SubnormRep.nonzero (f : SubnormRep C) : Prop := f.m ≠ 0

lemma neg_subnorm_nonzero {f : SubnormRep C} (h : f.nonzero) :
  (f.neg).nonzero := by
  simp [SubnormRep.nonzero, SubnormRep.neg] at *
  exact h

def subnormal_to_q : SubnormRep C →  ℚ
| ⟨b, m⟩ =>
  let s := if b then -1 else 1
  s * (m / C.prec) * 2^C.emin

lemma neg_subnormal_to_q (s : SubnormRep C) :
  subnormal_to_q s.neg = -subnormal_to_q s := by
  rw [subnormal_to_q, subnormal_to_q, SubnormRep.neg]
  cases s.s <;> simp

lemma subnormal_to_q_nonzero (s : SubnormRep C) :
  subnormal_to_q s ≠ 0 ↔ s.nonzero := by
  rw [not_iff_comm]
  simp only [SubnormRep.nonzero, ne_eq, Decidable.not_not]
  constructor
  · intro h
    rw [subnormal_to_q, h]
    simp
  intro h
  rw [subnormal_to_q] at h
  rcases s with ⟨b, m⟩
  cases b <;> simp at h <;> dsimp <;> {
    rcases h with (h | h) | h
    · exact h
    · linarith [C.prec_pos]
    linarith [zpow_pos (a := (2 : ℚ)) rfl C.emin]
  }


def subnormal_round (r : IntRounder) (q : ℚ) : SubnormRep C :=
  ⟨q < 0, r (q < 0) (|q| * 2^(-C.emin) * C.prec)⟩

lemma neg_subnormal_round (r : IntRounder) {q : ℚ} (h : q ≠ 0) :
  subnormal_round (C := C) (r.neg) (-q) = SubnormRep.neg (subnormal_round r q) := by
  rw [subnormal_round, subnormal_round, SubnormRep.neg, IntRounder.neg]
  simp
  have not_to_ge : 0 < q ↔ 0 ≤ q := by
    exact Iff.symm (Ne.le_iff_lt (id (Ne.symm h)))
  have lt_to_lt : 0 < q ↔ ¬(q < 0) := by
    rw [not_to_ge]
    exact Iff.symm not_lt
  refine ⟨not_to_ge, ?_⟩
  simp_rw [lt_to_lt]
  rw [decide_not]
  simp

def subnormal_round_down (q : ℚ) : SubnormRep C :=
  subnormal_round round0 q

lemma subnormal_round_coe (r : IntRounder) [rh : ValidRounder r]
  {s : SubnormRep C}  (h : s.nonzero):
  subnormal_round r (subnormal_to_q s) = s := by
  --rw [subnormal_round, subnormal_to_q]
  wlog h' : s.s = false generalizing r s
  · have t1 := this (r := r.neg) (rh := (neg_valid_rounder r).2 rh) (neg_subnorm_nonzero h)
    have t2 : s.neg.s = false := by simp [SubnormRep.neg, h']
    replace t1 := t1 t2
    rw [neg_subnormal_to_q, neg_subnormal_round] at t1
    · apply neg_subnorm_involutive.injective t1
    rw [subnormal_to_q_nonzero]
    exact h
  rcases s with ⟨b, m⟩
  dsimp at h'
  rw [h'] at h ⊢
  rw [subnormal_round, subnormal_to_q]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, zpow_neg, SubnormRep.mk.injEq,
    decide_eq_false_iff_not, not_lt]
  have : 0 ≤ ↑m / ↑C.prec * (2 : ℚ) ^ C.emin := by positivity
  constructor
  · exact this
  nth_rw 4 [show m = r false m by symm; apply ValidRounder.leftInverse]
  congr
  · apply decide_eq_false
    exact not_lt_of_ge this
  rw [abs_of_nonneg (by positivity), mul_assoc, mul_assoc, <-mul_assoc (2 ^ _),
    mul_inv_cancel₀, one_mul]
  rw [div_mul_cancel₀]
  · norm_cast
    linarith [C.prec_pos]
  positivity



lemma subnormal_round_down_coe (s : SubnormRep C) (h : s.nonzero) :
  subnormal_round_down (subnormal_to_q s) = s :=
  subnormal_round_coe round0 h

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

lemma subnormal_round_valid (r : IntRounder) [rh : ValidRounder r] :
  ValidSubnormalRounding (subnormal_round r : ℚ → SubnormRep C) := by
  simp only [ValidSubnormalRounding, subnormal_round]
  intro q q_nonneg h
  nth_rw 2 [show C.prec = r (decide (q < 0)) C.prec by symm; apply ValidRounder.leftInverse]
  apply ValidRounder.le_iff_le
  · positivity
  nth_rw 2 [<-one_mul (C.prec : ℚ)]
  apply mul_le_mul_of_nonneg_right
  · apply le_of_lt
    apply subnormal_exp_small q_nonneg h
  linarith [C.prec_pos]
