import Flean.FloatCfg
import Flean.Subnorm
import Flean.FloatRep
import Flean.Rounding

variable {C : FloatCfg}

def roundsub [R : Rounding] (q : ℚ) : SubnormRep C :=
  subnormal_round (round_function R) q

def subnormal_roundsub_valid [R : Rounding] :
  ValidSubnormalRounding (roundsub : ℚ → SubnormRep C) := by
  unfold roundsub
  apply subnormal_round_valid

lemma subnormal_roundsub_coe [R : Rounding] (s : SubnormRep C) (h : s.nonzero) :
  roundsub (subnormal_to_q s) = s := by
  unfold roundsub
  apply subnormal_round_coe
  exact h

inductive Flean.Float (C : FloatCfg) where
  | inf : Bool → Float C
  | nan : Float C
  | normal : (f : FloatRep C) → f.valid_e → f.valid_m → Float C
  | subnormal : (sm : SubnormRep C) → sm.m < C.prec → Float C


def to_float [R : Rounding] (q : ℚ) : Flean.Float C :=
  if q_nonneg : q = 0 then
    Flean.Float.subnormal ⟨false, 0⟩ C.prec_pos
  else if h : Int.log 2 |q| < C.emin then
    let sp := roundsub q
    if h_eq_prec : sp.2 = C.prec then by
      refine Flean.Float.normal ⟨q < 0, C.emin, 0⟩ ?_ ?_
      <;> simp only [FloatRep.valid_e, FloatRep.valid_m]
      · refine ⟨by linarith, by linarith [C.emin_lt_emax]⟩
      linarith [C.prec_pos]
    else by
      refine Flean.Float.subnormal ⟨sp.1, sp.2⟩ ?_
      · refine lt_of_le_of_ne ?_ h_eq_prec
        apply subnormal_roundsub_valid q q_nonneg
        exact h
  else match sem_def : round_rep q with
  | (⟨s, e, m⟩ : FloatRep C) => if h': e > C.emax then
      Flean.Float.inf (q < 0)
    else by
      refine Flean.Float.normal ⟨s, e, m⟩ ?_ ?_
      <;> simp only [FloatRep.valid_e, FloatRep.valid_m]
      · refine ⟨?_, by linarith [h', C.emin_lt_emax]⟩
        have := round_min_e (r := round_function R) (C := C) q_nonneg
        rw [<-round_rep] at this
        rw [sem_def] at this
        linarith
      have := round_valid_m (C := C) q q_nonneg
      rw [sem_def] at this
      exact this

def to_rat : Flean.Float C → ℚ
| Flean.Float.inf _ => 0
| Flean.Float.nan => 0
| Flean.Float.normal f _ _ => coe_q f
| Flean.Float.subnormal sm _ => subnormal_to_q sm

def Flean.Float.IsFinite : Flean.Float C → Prop
| Flean.Float.inf _ => false
| Flean.Float.nan => false
| _ => true

def Flean.Float.IsZero : Flean.Float C → Prop
| Flean.Float.subnormal ⟨_, 0⟩ _ => true
| _ => false

lemma subnorm_eq_0_iff_to_q (sm : SubnormRep C) :
  subnormal_to_q sm = 0 ↔ sm.m = 0 := by
  symm
  constructor
  · intro h
    rw [subnormal_to_q, h]
    simp
  contrapose!
  intro h
  have : sm.m > 0 := Nat.zero_lt_of_ne_zero h
  rw [subnormal_to_q]
  by_cases h': sm.s = false
  <;> {
    simp at h'
    rw [h']
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul,
      Nat.cast_eq_zero, not_or]
    have := C.prec_pos
    positivity
  }


lemma is_zero_iff_subnormal_to_q (sm : SubnormRep C) (h : sm.m < C.prec) :
  subnormal_to_q sm = 0 ↔ (Flean.Float.subnormal sm h).IsZero := by
  rw [subnorm_eq_0_iff_to_q]
  constructor
  · intro h'
    simp [Flean.Float.IsZero]
    rcases sm with ⟨s, m⟩
    split
    · simp at *
    simp [C.prec_pos] at *
    contradiction
  intro h'
  rcases sm with ⟨s, m⟩
  simp only [Flean.Float.IsZero] at h'
  split at h'
  next s m h_again sm_def =>
    rw [Flean.Float.subnormal.injEq] at sm_def
    rw [sm_def]
  simp at h'

lemma subnormal_range (f : SubnormRep C) (vm : f.m < C.prec) (ne_zero : f.nonzero) :
  Int.log 2 |subnormal_to_q f| < C.emin := by
  rw [subnormal_to_q]
  rw [SubnormRep.nonzero] at ne_zero
  rcases f with ⟨s, m⟩
  cases s <;> {
    simp only [Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul, abs_neg]
    have man_ge_0 : 0 < (m : ℚ) / C.prec := by
      have := C.prec_pos
      positivity
    have man_lt_1 : (m : ℚ) / C.prec < 1 := by
      rw [div_lt_one (by norm_cast; exact C.prec_pos)]
      norm_cast
    exact log_zero_to_one_lt ((m : ℚ) / C.prec) C.emin man_ge_0 man_lt_1
  }

def max_float (C : FloatCfg) : Flean.Float C := by
  refine Flean.Float.normal (max_float_rep C) ?_ ?_
  · simp [max_float_rep, FloatRep.valid_e, FloatRep.valid_m, le_of_lt C.emin_lt_emax]
  simp [max_float_rep, FloatRep.valid_m, C.prec_pos]

lemma to_rat_max_float :
  to_rat (max_float C) = max_float_q C := by
  simp only [to_rat, max_float, coe_q_max_float_rep]

lemma log_lt_emax_of_max_float {q : ℚ} (q_nonneg : q ≠ 0) (h : |q| ≤ max_float_q C) :
  Int.log 2 |q| ≤ C.emax := by
  suffices Int.log 2 |q| < C.emax + 1 by linarith
  rw [<-Int.lt_zpow_iff_log_lt (by norm_num) (by positivity)]
  unfold max_float_q at h
  apply lt_of_le_of_lt h
  rw [zpow_add₀ (by norm_num)]
  rw [mul_comm]
  apply mul_lt_mul' ?_ ?_ (by linarith [max_mantissa_q C]) (by positivity)
  · rfl
  linarith [max_mantissa_q C]


lemma float_range (f : Flean.Float C) :
  |to_rat f| ≤ max_float_q C := by
  unfold to_rat
  unfold max_float_q
  have : (1 : ℚ) / C.prec ≤ 1 := by
    rw [one_div_le]
    · simp only [ne_eq, one_ne_zero, not_false_eq_true, div_self, Nat.one_le_cast]
      exact C.prec_pos
    · exact Nat.cast_pos'.mpr C.prec_pos
    norm_num
  have : 0 < (2 - (1 : ℚ) / C.prec) := by linarith
  have := C.prec_pos
  rcases f with _ | _ | ⟨f, ve, vm⟩ | ⟨sm, vm⟩
  · simp only [abs_zero]; positivity
  · positivity
  · dsimp
    rw [coe_q]
    cases f.s
    <;> {
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul, ge_iff_le,
      neg_mul, abs_neg
      ]
      apply normal_range'
      · exact vm
      exact ve.2
    }
  dsimp
  apply le_of_lt
  calc
    |subnormal_to_q sm| < (2 : ℚ)^C.emin := by
      by_cases h : 0 < |subnormal_to_q sm|
      · suffices Int.log 2 |subnormal_to_q sm| < C.emin by
          rw [<-Int.lt_zpow_iff_log_lt] at this
          · norm_cast at this
          · norm_num
          exact h
        apply subnormal_range
        · exact vm
        contrapose h
        simp only [abs_pos, ne_eq, Decidable.not_not]
        simp only [SubnormRep.nonzero, ne_eq, Decidable.not_not] at h
        exact (subnorm_eq_0_iff_to_q sm).mpr h
      simp at h
      rw [h]
      positivity
    _ < (2 - 1 / ↑C.prec) * 2 ^ C.emax := by
      rw [<-one_mul (2 ^ _)]
      apply mul_lt_mul' ?_ ?_ (by positivity) (by positivity)
      · linarith
      apply zpow_lt_zpow_right₀ (by norm_num) C.emin_lt_emax


lemma to_floar_to_rat [R : Rounding] (f : Flean.Float C) (finite : f.IsFinite) (nonzero : ¬f.IsZero) :
  to_float (to_rat f) = f := by
  simp [Flean.Float.IsFinite] at finite
  --simp [Flean.Float.IsZero] at nonzero
  rcases f with _ | _ | ⟨f, ve, vm⟩ | ⟨sm, vm⟩
  <;> simp only at finite nonzero
  · have : coe_q f ≠ 0 := by
      rcases f with ⟨s, e, m⟩
      cases s
      · linarith [coe_q_false_pos (C := C) (e := e) (m := m)]
      linarith [coe_q_true_neg (C := C) (e := e) (m := m)]
    simp only [to_rat]
    unfold to_float
    split_ifs
    · contradiction
    · linarith [(normal_range f ve vm).1]
    have : round_rep (coe_q f) = f := round_rep_coe f vm
    dsimp
    split_ifs
    · rw [this] at *
      linarith [ve.2]
    simp [this]
  have sm_nonzero : sm.m ≠ 0 := by
    rw [<-is_zero_iff_subnormal_to_q _ vm] at nonzero
    rw [subnorm_eq_0_iff_to_q] at nonzero
    exact nonzero
  have := subnormal_range sm vm sm_nonzero
  simp only [to_rat]
  unfold to_float
  have snormal_eq := subnormal_roundsub_coe sm sm_nonzero
  if mzero : subnormal_to_q sm = 0 then
    rw [is_zero_iff_subnormal_to_q _ vm] at mzero
    contradiction
  else
    if h_eq_pres : sm.2 = C.prec then
      rw [<-snormal_eq] at h_eq_pres
      simp only [mzero, this, h_eq_pres, ↓reduceDIte, reduceCtorEq]
      rw [snormal_eq] at h_eq_pres
      linarith
    else
      rw [<-snormal_eq] at h_eq_pres
      simp only [mzero, this, h_eq_pres, ↓reduceDIte, Flean.Float.subnormal.injEq]
      rw [snormal_eq]


/-
I would like to prove that rounding preserves order
for finite values
First we split into 4 cases:
- q1 and q2 are both normal
- q1 and q2 are both subnormal
- q1 rounds to a subnormal number and q2 to a normal
- vice versa

We've already proved the first two cases.
For the third case, we can use
the fact that the rounding exactly overlaps
at the subnormal / normal boundary in a
transitive ordering proof.

Of course, this requires it's own case work
to identify that boundary, but it only
depends on the sign of the normal number.

I should also note that we are really splitting
the rational numbers not the floats.
So we need to know how rounding behaves
on different sets. i.e. which sets of ℚ
give us something equivalent to subnormal rounding
or normal rounding (conditioned on rounding giving us finite).

Finally, we need to prove that rounding
preserves the overlapping boundary of those sets.
-/

-- Alternative
-- |q| ≤ 2^C.emin → to_rat (to_float q : Flean.Float C) = subnormal_to_q (roundsub q)
-- 2^C.emin ≤ |q| → to_rat (to_float q : Flean.Float C) = coe_q (round_rep q)
lemma splitIsFinite [R : Rounding] {q : ℚ}
  (h : (to_float q : Flean.Float C).IsFinite) :
  ((|q| ≤ 2^C.emin) ∧
    to_rat (to_float q : Flean.Float C)
  = subnormal_to_q (roundsub (C := C) q))
  ∨ (2^C.emin ≤ |q| ∧ to_rat (to_float q : Flean.Float C) = coe_q (round_rep (C := C) q)) := by
  set f := to_float q with f_def
  unfold to_float at f_def
  split_ifs at f_def with i1 i2
  · left
    constructor
    · rw [i1, abs_zero]
      positivity
    rw [f_def, i1, roundsub, roundsub_zero]
    simp [to_float, to_rat, subnormal_to_q]
  · left
    constructor
    · apply le_of_lt
      exact (Int.lt_zpow_iff_log_lt (b := 2) (by norm_num) (by positivity)).2 i2
    dsimp at f_def
    split_ifs at f_def with h'
    · --simp only [i1, ↓reduceDIte, i2, h']
      rw [f_def, to_rat, coe_q, subnormal_to_q, h']
      rw [roundsub, subnormal_round]
      dsimp
      rw [mul_assoc, mul_assoc]
      congr 1
      rw [div_self]
      · simp
      norm_cast
      exact ne_of_gt C.prec_pos
    rw [f_def, to_rat]
  match sem_def : round_rep q with
  | { s := s, e := e, m := m } => {
    dsimp at f_def
    simp_rw [sem_def] at f_def
    split_ifs at f_def with i3
    · exfalso
      rw [f_def] at h
      simp [Flean.Float.IsFinite] at h
    right
    constructor
    · apply (Int.zpow_le_iff_le_log (b := 2) (by norm_num) (by positivity)).2
      exact not_lt.mp i2
    rw [f_def, to_rat]
  }

lemma subnormal_to_q_emin :
  subnormal_to_q (C := C) ⟨false, C.prec⟩ = 2^C.emin := by
  rw [subnormal_to_q, div_self]
  · simp
  exact_mod_cast ne_of_gt C.prec_pos

lemma subnormal_to_q_neg_emin :
  subnormal_to_q (C := C) ⟨true, C.prec⟩ = -2^C.emin := by
  rw [<-subnormal_to_q_emin]
  simp [subnormal_to_q]

lemma coe_q_emin : coe_q (C := C) ⟨false, C.emin, 0⟩ = 2^C.emin := by
  rw [coe_q]
  simp

lemma coe_q_neg_emin : coe_q (C := C) ⟨true, C.emin, 0⟩ = -2^C.emin := by
  rw [<-coe_q_emin]
  simp [coe_q]

lemma roundsub_emin [R : Rounding] : roundsub (C := C) (2^C.emin) = ⟨false, C.prec⟩ := by
  rw [roundsub, <-subnormal_to_q_emin, subnormal_round_coe]
  simp [SubnormRep.nonzero, ne_of_gt, C.prec_pos]

lemma roundsub_neg_emin [R : Rounding] : roundsub (C := C) (-2^C.emin) = ⟨true, C.prec⟩ := by
  rw [roundsub, <-subnormal_to_q_neg_emin, subnormal_round_coe]
  simp [SubnormRep.nonzero, ne_of_gt, C.prec_pos]

lemma roundrep_emin [R : Rounding] : round_rep (C := C) (2^C.emin) = ⟨false, C.emin, 0⟩ := by
  rw [<-coe_q_emin]
  apply round_rep_coe
  simp [FloatRep.valid_m, C.prec_pos]

lemma roundrep_neg_emin [R : Rounding] : round_rep (C := C) (-2^C.emin) = ⟨true, C.emin, 0⟩ := by
  rw [<-coe_q_neg_emin]
  apply round_rep_coe
  simp [FloatRep.valid_m, C.prec_pos]

lemma float_le_float_of [R : Rounding] (q1 q2 : ℚ)
  (h1 : (to_float (C := C) q1).IsFinite)
  (h2 : (to_float (C := C) q2).IsFinite) (h : q1 ≤ q2) :
  to_rat (to_float (C := C) q1) ≤ to_rat (to_float (C := C) q2) := by
  --let motive (x y : Flean.Float C) := to_rat x ≤ to_rat y
  by_cases h' : q1 = q2
  · rw [h']
  rcases splitIsFinite (h := h1) with ⟨q1_small, h1⟩ | ⟨q1_large, h1⟩
  · rw [h1]
    rcases splitIsFinite (h := h2) with ⟨q2_small, h2⟩ | ⟨q2_large, h2⟩
    · rw [h2]
      apply subnormal_round_le_of_le (C := C) (r := round_function R) q1 q2 h
    · rw [h2]
      have : q2 > 0 := by
        contrapose! h'
        rw [abs_of_nonpos h'] at q2_large
        rw [abs_of_nonpos (le_trans h h')] at q1_small
        apply le_antisymm h
        have := le_trans q1_small q2_large
        linarith
      apply le_trans (b := 2^C.emin)
      · rw [<-subnormal_to_q_emin, <-roundsub_emin]
        apply subnormal_round_le_of_le (C := C) (r := round_function R) q1 (2^C.emin)
        exact (abs_le.mp q1_small).2
      rw [<-abs_of_pos this, <-coe_q_emin, <-roundrep_emin]
      apply le_roundf_of_le
      · positivity
      · positivity
      exact q2_large
  rw [h1]
  rcases splitIsFinite (h := h2) with ⟨q2_small, h2⟩ | ⟨q2_large, h2⟩
  · rw [h2]
    have : q1 < 0 := by
      contrapose! h'
      rw [abs_of_nonneg h'] at q1_large
      apply le_antisymm h
      apply le_trans _ q1_large
      exact (abs_le.mp q2_small).2
    apply le_trans (b := -2^C.emin)
    · rw [<-coe_q_neg_emin, <-roundrep_neg_emin]
      apply le_roundf_of_le
      · exact ne_of_lt this
      · rw [<-neg_ne_zero, neg_neg]
        positivity
      rw [abs_of_neg this] at q1_large
      exact le_neg_of_le_neg q1_large
    rw [<-subnormal_to_q_neg_emin, <-roundsub_neg_emin]
    apply subnormal_round_le_of_le (C := C) (r := round_function R)
    exact (abs_le.mp q2_small).1
  rw [h2]
  apply le_roundf_of_le (C := C) (r := round_function R) q1 q2
  · exact abs_pos.mp (lt_of_lt_of_le (zpow_pos rfl C.emin) q1_large)
  · exact abs_pos.mp (lt_of_lt_of_le (zpow_pos rfl C.emin) q2_large)
  exact h

def to_float_down : ℚ → Flean.Float C := to_float (R := .mk (.down))
def to_float_up : ℚ → Flean.Float C := to_float (R := .mk (.up))

lemma float_down_le (q : ℚ) (h : (to_float_down (C := C) q).IsFinite) :
  to_rat (to_float_down (C := C) q) ≤ q := by
  unfold to_float_down at h ⊢
  rcases splitIsFinite (R := .mk (.down)) (h := h) with ⟨q_small, h⟩ | ⟨q_large, h⟩
  · rw [h]
    apply rounddownsub_le
  rw [h]
  apply roundf_down_le
  apply abs_pos.mp
  linarith [show 0 < (2:ℚ) ^ C.emin by positivity]

lemma le_float_up (q : ℚ) (h : (to_float_up (C := C) q).IsFinite) :
  q ≤ to_rat (to_float_up (C := C) q) := by
  unfold to_float_up at h ⊢
  rcases splitIsFinite (R := .mk (.up)) (h := h) with ⟨q_small, h⟩ | ⟨q_large, h⟩
  · rw [h]
    apply le_roundupsub
  rw [h]
  apply le_roundf_up
  apply abs_pos.mp
  linarith [show 0 < (2:ℚ) ^ C.emin by positivity]

lemma to_float_boundary (R : Rounding) {q : ℚ} (h : |q| = 2^C.emin) :
  to_rat (to_float (C := C) q) = q := by
  rw [abs_eq (by positivity)] at h
  have ne0 : (2 : ℚ)^C.emin ≠ 0 := by positivity
  have logemin : Int.log 2 |(2 : ℚ)^C.emin| = C.emin := by
    rw [abs_of_pos (by positivity)]
    exact Int.log_zpow (b := 2) (by norm_num) C.emin
  rcases h with h | h
  · rw [h, to_float]
    simp_rw [logemin]
    simp only [ne0, ↓reduceDIte, lt_self_iff_false, gt_iff_lt]
    simp_rw [roundrep_emin]
    simp [C.emin_lt_emax.not_lt, to_rat, coe_q]
  rw [h, to_float]
  simp_rw [neg_eq_zero, abs_neg]
  simp_rw [logemin]
  simp_rw [roundrep_neg_emin]
  simp [ne0, C.emin_lt_emax, C.emin_lt_emax.not_lt]
  simp [C.emin_lt_emax.not_lt, to_rat, coe_q]

lemma float_up_minus_down (q : ℚ) (h : (to_float_down (C := C) q).IsFinite)
  (h' : (to_float_up (C := C) q).IsFinite) :
  to_rat (to_float_up (C := C) q) - to_rat (to_float_down (C := C) q)
    ≤ max ((2 : ℚ)^C.emin / (C.prec : ℚ)) (2 ^ (Int.log 2 |q|) / C.prec) := by
  unfold to_float_down to_float_up at *
  by_cases q_is_boundary : |q| = 2^C.emin
  · rw [to_float_boundary (R := .mk (.down)) q_is_boundary]
    rw [to_float_boundary (R := .mk (.up)) q_is_boundary]
    simp only [sub_self]
    positivity
  rcases splitIsFinite (R := .mk (.down)) (h := h) with ⟨q_small, h⟩ | ⟨q_large, h⟩
  <;> rcases splitIsFinite (R := .mk (.up)) (h := h') with ⟨q_small', h'⟩ | ⟨q_large', h'⟩
  · rw [h, h']
    apply le_max_of_le_left
    unfold roundsub
    simp only [round_function]
    apply subnormal_up_minus_down (C := C)
  · exfalso
    apply q_is_boundary
    apply le_antisymm q_small q_large'
  · exfalso
    apply q_is_boundary
    apply le_antisymm q_small' q_large
  rw [h, h']
  apply le_max_of_le_right
  apply roundf_up_minus_down
  apply abs_pos.mp
  linarith [show 0 < (2:ℚ) ^ C.emin by positivity]

lemma float_eq_up_or_down [R : Rounding] (q : ℚ) :
  (to_float (C := C) q) = (to_float_down (C := C) q) ∨
  (to_float (C := C) q) = (to_float_up (C := C) q) := by
  by_cases q_nezero : q = 0
  · left
    rw [q_nezero]
    simp [to_float, to_float_down, subnormal_to_q]
  unfold to_float_down to_float_up to_float roundsub round_rep
  split_ifs with h1
  · simp only
    set x := |q| * 2 ^ (-C.emin) * ↑C.prec with x_def
    have := round_eq_or' (r := round_function R) (b := q < 0)
        (q := x) (h := by positivity)
    simp_rw [subnormal_round]
    rcases this with h' | h'
    · left
      simp_rw [h']
      simp [x_def, round_function]
    right
    simp_rw [h']
    simp [x_def, round_function]
  simp only
  set x := ((|q| * (2 ^ Int.log 2 |q|)⁻¹ - 1) * ↑C.prec) with x_def
  have := by
    refine round_eq_or' (r := round_function R) (b := q < 0)
      (q := x) (h := ?_)
    apply mantissa_nonneg (q_nezero := q_nezero)
  simp_rw [roundf]
  rcases this with h' | h'
  · left
    simp_rw [h']
    simp [x_def, round_function]
  right
  simp_rw [h']
  simp [x_def, round_function]

lemma float_error [R : Rounding] (q : ℚ) (h : (to_float_down (C := C) q).IsFinite) (h' : (to_float_up (C := C) q).IsFinite) :
  |to_rat (to_float (C := C) q) - q| ≤ max ((2 : ℚ)^C.emin / C.prec) (2 ^ (Int.log 2 |q|) / C.prec) := by
  apply le_trans (b := to_rat (to_float_up (C := C) q) - to_rat (to_float_down (C := C) q))
  · rcases float_eq_up_or_down q with h'' | h'' <;> rw [h'']
    · rw [abs_sub_comm, abs_of_nonneg]
      · rw [sub_le_sub_iff_right]
        apply le_float_up (C := C)
        rw [to_float_up]
        exact h'
      rw [sub_nonneg]
      apply float_down_le (C := C) (h := h)
    rw [abs_of_nonneg]
    · rw [sub_le_sub_iff_left]
      apply float_down_le (C := C) (h := h)
    rw [sub_nonneg]
    apply le_float_up (C := C) (h := h')
  apply float_up_minus_down (C := C) q h h'

def Flean.Float.neg : Flean.Float C → Flean.Float C
| Flean.Float.inf s => Flean.Float.inf (¬s)
| Flean.Float.nan => Flean.Float.nan
| Flean.Float.normal f ve vm => Flean.Float.normal f.neg ve vm
| Flean.Float.subnormal sm vm => Flean.Float.subnormal sm.neg vm


lemma to_float_in_range [R : Rounding] {q : ℚ} (h : |q| ≤ max_float_q C) :
  (to_float q : Flean.Float C).IsFinite := by
  by_cases q_nezero : q = 0
  · rw [q_nezero]
    simp [to_float, Flean.Float.IsFinite]
  have := log_lt_emax_of_max_float q_nezero h
  rw [Flean.Float.IsFinite]
  · rw [to_float]
    simp [q_nezero, this.not_lt]
    split_ifs with h1 h2 h3
    · simp
    · simp
    · simp
      have := round_min_e' (C := C) q q_nezero
      exfalso
      suffices (round_rep q).e ≤ C.emax by
        linarith
      exact roundf_in_range _ q_nezero h
    · simp
  simp [to_float]
  split_ifs <;> simp

lemma float_error' [R : Rounding] (q : ℚ) (h : |q| ≤ max_float_q C) :
  |to_rat (to_float (C := C) q) - q| ≤ max ((2 : ℚ)^C.emin / C.prec) (2 ^ (Int.log 2 |q|) / C.prec) := by
  apply float_error
  · apply to_float_in_range (R := .mk (.down)) h
  apply to_float_in_range (R := .mk (.up)) h


def DoubleCfg : FloatCfg := FloatCfg.mk (1 <<< 52) (-1022) 1023 (by norm_num) (
  Nat.zero_lt_succ 4503599627370495
)


def frep : FloatCfg := FloatCfg.mk 256 (-127) 127 (by norm_num) (by norm_num)

def frep64 := FloatRep frep

--#eval ((@round_down frep 3.5) : frep64)
--#check (round_down 3.5 : frep64)
--#check (coe_q (⟨false, 0, 0⟩ : frep64))
--#eval @to_rat C (@to_float C 3.528123042)
--#eval @coe_q C (@round_down C 3.5)
--#eval @round_down C 0
