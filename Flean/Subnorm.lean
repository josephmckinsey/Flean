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

lemma subnorm_neg_nonzero {f : SubnormRep C} (h : f.nonzero) :
  (f.neg).nonzero := by
  simp [SubnormRep.nonzero, SubnormRep.neg] at *
  exact h

def subnormal_to_q : SubnormRep C →  ℚ
| ⟨b, m⟩ =>
  let s := if b then -1 else 1
  s * (m / C.prec) * 2^C.emin

lemma subnormal_to_q_neg (s : SubnormRep C) :
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
  · have t1 := this (r := r.neg) (rh := (neg_valid_rounder r).2 rh) (subnorm_neg_nonzero h)
    have t2 : s.neg.s = false := by simp [SubnormRep.neg, h']
    replace t1 := t1 t2
    rw [subnormal_to_q_neg, neg_subnormal_round] at t1
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

lemma subnormal_round_le_of_le (r : IntRounder) [rh : ValidRounder r] (q1 q2 : ℚ)
  (h : q1 ≤ q2) :
  subnormal_to_q (C := C) (subnormal_round r q1) ≤ subnormal_to_q (C := C) (subnormal_round r q2) := by
  by_cases h1 : q1 = 0
  · rw [h1, subnormal_round]
    simp only [lt_self_iff_false, decide_false, abs_zero, zero_mul]
    nth_rw 1 [show (0 : ℚ) = ↑(0 : ℕ) by rfl]
    rw [rh.leftInverse false]
    rw [subnormal_to_q]
    simp only [Bool.false_eq_true, ↓reduceIte, CharP.cast_eq_zero, zero_div, mul_zero, zero_mul]
    have : decide (q2 < 0) = false := by simp; linarith
    rw [subnormal_to_q, subnormal_round, this]
    dsimp
    positivity
  by_cases h2 : q2 = 0
  · rw [h2]
    nth_rw 2 [subnormal_round]
    simp only [lt_self_iff_false, decide_false, abs_zero, zpow_neg, zero_mul]
    rw [show (0 : ℚ) = ↑(0 : ℕ) by rfl, rh.leftInverse false]
    rw [subnormal_to_q, subnormal_to_q, subnormal_round]
    simp only [↓reduceIte, CharP.cast_eq_zero, zero_div, mul_zero, zero_mul]
    have : decide (q1 < 0) = true := by
      apply decide_eq_true
      apply lt_of_le_of_ne ?_ h1
      exact h2 ▸ h
    rw [this]
    simp only [↓reduceIte, neg_mul, one_mul, Left.neg_nonpos_iff, ge_iff_le]
    positivity
  revert h r
  apply casesQPlane (q1 := q1) (q2 := q2)
  · intro q1 q1pos q2 q2pos r rh h
    rw [subnormal_round, subnormal_round]
    rw [subnormal_to_q, subnormal_to_q]
    rw [decide_eq_false (by linarith), decide_eq_false (by linarith)]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
    gcongr
    apply rh.le_iff_le
    · positivity
    gcongr
  · intro q1 q1neg q2 q2pos r rh h
    rw [subnormal_round, subnormal_round]
    rw [subnormal_to_q, subnormal_to_q]
    rw [decide_eq_true (by linarith), decide_eq_false (by linarith)]
    simp only [↓reduceIte, zpow_neg, neg_mul, one_mul, Bool.false_eq_true]
    have : ∀a b, (0 : ℚ) ≤ a → 0 ≤ b → -a ≤ b := by
      intros a b ha hb
      linarith
    apply this
    · positivity
    positivity
  · intro q1 q1pos q2 q2neg r rh h
    exfalso
    linarith
  · intro q1 q1neg q2 q2neg ih r rh h
    have : -q1 ≤ -q2 := by linarith
    replace ih := ih (r.neg) (rh := rh.neg) this
    rw [neg_subnormal_round, neg_subnormal_round,
      subnormal_to_q_neg, subnormal_to_q_neg] at ih
    · linarith
    · exact Ne.symm (ne_of_gt q2neg)
    exact Ne.symm (ne_of_gt q1neg)
  · exact h1
  exact h2

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

lemma subnorm_zero {s : Bool} :
  subnormal_to_q (⟨s, 0⟩ : SubnormRep C) = 0 := by
  simp [subnormal_to_q]

lemma roundsub_zero (r : IntRounder) [rh : ValidRounder r] :
  subnormal_to_q (subnormal_round r (C := C) 0) = 0 := by
  rw [subnormal_to_q, subnormal_round]
  simp only [lt_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte, abs_zero, zpow_neg,
    zero_mul, one_mul, mul_eq_zero, div_eq_zero_iff, Nat.cast_eq_zero]
  left
  left
  apply ValidRounder.leftInverse

lemma rounddownsub_le (q : ℚ) :
  subnormal_to_q (subnormal_round rounddown (C := C) q) ≤ q := by
  rw [subnormal_to_q, subnormal_round, rounddown]
  have t1 : 0 < (C.prec : ℚ) := by norm_cast; exact C.prec_pos
  have t2 : 0 < (2 : ℚ)^C.emin := by positivity
  have t3 := div_pos t1 t2
  by_cases h : q < 0
  · simp only [h, decide_true, ↓reduceIte, zpow_neg, neg_mul, one_mul]
    rw [roundinf, neg_le]
    rw [<-abs_of_pos (a := -q) (Left.neg_pos_iff.mpr h)]
    rw [abs_neg]
    rw [Nat.cast_natAbs]
    simp only [Int.cast_abs, ge_iff_le]
    rw [abs_of_neg, abs_of_pos]
    · rw [<-div_eq_mul_inv]
      rw [div_mul]--, <-div_le_div_iff_of_pos_right t3]
      rw [le_div_iff₀ t3]
      field_simp
      apply Int.le_ceil
    · norm_cast
      apply Int.lt_ceil.mpr
      apply mul_pos ?_ t1
      apply mul_pos ?_ (inv_pos.mpr t2)
      exact Left.neg_pos_iff.mpr h
    exact h
  simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, zpow_neg, one_mul]
  replace h := le_of_not_lt h
  rw [round0, abs_of_nonneg h, Nat.cast_natAbs]
  rw [abs_of_nonneg]
  · rw [<-div_eq_mul_inv]
    rw [div_mul]
    rw [div_le_iff₀ t3]
    field_simp
    apply Int.floor_le
  positivity

lemma le_roundupsub (q : ℚ) :
  q ≤ subnormal_to_q (subnormal_round roundup (C := C) q) := by
  rw [subnormal_to_q, subnormal_round]
  have t1 : 0 < (C.prec : ℚ) := by norm_cast; exact C.prec_pos
  by_cases h : q < 0
  · rw [roundup]
    simp only [h, decide_true, ↓reduceIte, zpow_neg, neg_mul, one_mul]
    rw [le_neg]
    rw [abs_of_neg h, round0, Nat.cast_natAbs]
    rw [Int.cast_abs]
    rw [abs_of_nonneg]
    · rw [<-div_eq_mul_inv]
      rw [div_mul]--, <-div_le_div_iff_of_pos_right t3]
      rw [div_le_iff₀ (div_pos t1 (by positivity))]
      field_simp
      apply Int.floor_le
    norm_cast
    apply Int.le_floor.mpr
    apply mul_nonneg ?_ ?_
    · apply mul_nonneg
      · apply le_neg.mpr
        exact le_of_lt h
      positivity
    apply le_of_lt
    exact_mod_cast C.prec_pos
  rw [roundup]
  simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, zpow_neg, one_mul, ge_iff_le]
  replace h := le_of_not_lt h
  rw [roundinf, abs_of_nonneg h, Nat.cast_natAbs]
  rw [abs_of_nonneg]
  · rw [<-div_eq_mul_inv]
    rw [div_mul]--, <-div_le_div_iff_of_pos_right t3]
    rw [le_div_iff₀ (div_pos t1 (by positivity))]
    field_simp
    apply Int.le_ceil
  positivity

lemma subnormal_up_minus_down (q : ℚ) :
  subnormal_to_q (subnormal_round (C := C) roundup q) -
    subnormal_to_q (subnormal_round (C := C) rounddown q) ≤ 2^C.emin * (↑C.prec)⁻¹ := by
  simp_rw [subnormal_to_q, subnormal_round, roundup, rounddown]
  simp_rw [round0, roundinf]
  wlog h : q ≥ 0 generalizing q
  · simp at h
    replace this := this (q := -q) (by linarith)
    have h' : ¬(-q < 0) := by linarith
    simp [h]
    simp [h'] at this
    rw [add_comm]
    exact this
  have h' : ¬(q < 0) := by linarith
  simp only [h', decide_false, Bool.false_eq_true, ↓reduceIte, zpow_neg, one_mul, tsub_le_iff_right,
    ge_iff_le]
  rw [Int.cast_natAbs, Int.cast_natAbs]
  rw [abs_of_nonneg (by positivity)]
  nth_rw 2 [abs_of_nonneg (by positivity)]
  have := Int.ceil_le_floor_add_one (|q| * ((2 : ℚ)^C.emin)⁻¹ * C.prec)
  have h : StrictMono (fun x => x / C.prec * (2 : ℚ)^C.emin) := by
    apply StrictMono.mul_const
    apply StrictMono.div_const
    · exact fun ⦃a b⦄ a ↦ a
    · exact_mod_cast C.prec_pos
    positivity
  qify at this
  apply h.monotone at this
  simp at this
  field_simp at this
  field_simp
  rw [add_comm, add_mul, add_div, one_mul] at this
  field_simp at this
  exact this

lemma subnormal_round_neg (r : IntRounder) {q : ℚ} (h : q ≠ 0) :
  subnormal_round r.neg (-q) = (subnormal_round (C := C) r q).neg := by
  simp only [subnormal_round, SubnormRep.neg, IntRounder.neg]
  congr 2
  · simp [h.symm.le_iff_lt]
  · simp [<-decide_not, h.le_iff_lt]
  simp

lemma subnormal_round_eq_up_down (r : IntRounder) [rh : ValidRounder r] (q : ℚ) :
  subnormal_round r q = subnormal_round (C := C) rounddown q ∨
  subnormal_round r q = subnormal_round (C := C) roundup q := by
  unfold subnormal_round
  set x := |q| * 2^(-C.emin) * C.prec
  have := round_eq_or' (r := r) (b := q < 0)
      (q := x) (h := by positivity)
  rcases this with this | this
  · simp [this]
  simp [this]

lemma subnormal_round_close (r : IntRounder) [rh : ValidRounder r] (q : ℚ) :
  |q - subnormal_to_q (subnormal_round (C := C) r q)| ≤ 2^C.emin / C.prec := by
  apply le_trans (b := subnormal_to_q (subnormal_round (C := C) roundup q) - subnormal_to_q (subnormal_round (C := C) rounddown q))
  rcases subnormal_round_eq_up_down r q with h | h
  · rw [h]
    rw [abs_of_nonneg]
    · rw [sub_le_sub_iff_right]
      apply le_roundupsub
    rw [sub_nonneg]
    apply rounddownsub_le
  · rw [h, abs_sub_comm, abs_of_nonneg]
    · rw [sub_le_sub_iff_left]
      apply rounddownsub_le
    rw [sub_nonneg]
    apply le_roundupsub
  exact subnormal_up_minus_down q

lemma subnormal_near_close (q : ℚ) :
  |q - subnormal_to_q (subnormal_round (C := C) roundnearest q)| ≤ 2^(C.emin - 1) / C.prec := by
  by_cases h : q = 0
  · rw [h]
    simp [subnormal_round, roundnearest, round_near_int, subnormal_to_q]
    positivity
  wlog h' : 0 < q generalizing q
  · have negq : 0 < -q := by
      apply lt_of_le_of_ne (by linarith)
      exact (neg_ne_zero.mpr h).symm
    replace this := this (q := -q) (by linarith) negq
    rw [<-roundnearest_neg] at this
    rw [subnormal_round_neg (h := h), subnormal_to_q_neg] at this
    rw [neg_sub_neg, abs_sub_comm] at this
    exact this
  rw [subnormal_round, roundnearest]
  have : ¬(q < 0) := by linarith
  simp only [this, decide_false, ge_iff_le, subnormal_to_q, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Int.cast_natAbs]
  rw [abs_of_pos h']
  nth_rw 2 [abs_of_nonneg (by positivity)]
  calc
    |q - (round_near_int (q * 2 ^ (-C.emin) * ↑C.prec)) / ↑C.prec * 2 ^ C.emin| =
      |q * 2^(-C.emin) * C.prec / C.prec * 2^C.emin - (round_near_int (q * 2 ^ (-C.emin) * ↑C.prec)) / ↑C.prec * 2 ^ C.emin| := by
      rw [mul_div_cancel_right₀]
      · rw [mul_assoc (c := 2^_)]
        rw [zpow_neg, inv_mul_cancel₀ (by positivity), mul_one]
      exact_mod_cast ne_of_gt C.prec_pos
    _ = |q * 2^(-C.emin) * C.prec - (round_near_int (q * 2 ^ (-C.emin) * ↑C.prec))| / C.prec * 2^C.emin := by
      rw [<-sub_mul, <-sub_div, abs_mul, abs_div,
        abs_of_pos (a := 2^C.emin) (by positivity),
        abs_of_pos (a := (C.prec : ℚ))]
      exact_mod_cast C.prec_pos
    _ ≤ 1 / 2 / C.prec * 2^C.emin := by
      apply mul_le_mul_of_nonneg_right ?_ (by positivity)
      apply div_le_div_of_nonneg_right
      · rw [abs_sub_comm]
        exact round_near_int_le (q * 2^(-C.emin) * C.prec)
      exact_mod_cast le_of_lt C.prec_pos
    _ = 2^(C.emin - 1) / C.prec := by
      rw [zpow_sub₀ (by linarith)]
      field_simp
