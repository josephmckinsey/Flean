import Flean.FloatRep
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Int.Log
import Flean.FloatCfg
import Flean.LogRules
import Mathlib.Tactic
import Mathlib.Tactic.Positivity.Core


variable {C : FloatCfg}

abbrev IntRounder := Bool → ℚ → ℕ

def round0 (q : ℚ) := ⌊q⌋.natAbs
def roundinf (q : ℚ) := ⌈q⌉.natAbs
def roundup (s : Bool) := if s then round0 else roundinf
def rounddown (s : Bool) := if s then roundinf else round0
def round_near_int (q : ℚ) :=
  let i1 := ⌊q⌋
  let i2 := ⌈q⌉
  if Int.fract q < 1/2 then
    i1
  else if 1/2 < Int.fract q then
    i2
  else if i1 % 2 = 0 then
    i1
  else
    i2

def roundnearest (q : ℚ) := (round_near_int q).natAbs

lemma round_near_int_of_nonneg {q : ℚ} (h : 0 ≤ q) : 0 ≤ round_near_int q := by
  rw [round_near_int]
  split_ifs <;> (try exact Int.floor_nonneg.mpr h) <;> (try exact Int.ceil_nonneg h)

lemma round_near_int_of_pos {q : ℚ} (h : 0 < q) : 0 ≤ round_near_int q := by
  apply round_near_int_of_nonneg
  exact le_of_lt h

/-
Round nearest preserves order.

Suppose q1 and q2 are far enough away (⌈q1⌉ ≤ ⌊q2⌋), then it is obviously
true in all cases.

If ⌈q1⌉ > ⌊q2⌋, then ⌈q1⌉ = ⌈q2⌉ and ⌊q1⌋ = ⌊q2⌋, then we have
Int.frac q1 ≤ Int.frac q2.

If Int.frac q1 < 1/2, then we round to ⌊q1⌋,
and
-/

lemma round_near_le_round_near {q1 q2 : ℚ} (h : q1 ≤ q2) :
  round_near_int q1 ≤ round_near_int q2 := by
  rw [round_near_int, round_near_int]
  have floor_le_ceil : ⌊q1⌋ ≤ ⌈q2⌉ := by
    qify
    calc
      ⌊q1⌋ ≤ q1 := Int.floor_le q1
      q1 ≤ q2 := h
      q2 ≤ ⌈q2⌉ := Int.le_ceil q2
  by_cases h' : ⌈q1⌉ ≤ ⌊q2⌋
  · split_ifs <;>
      (try exact Int.floor_le_floor h) <;> (try exact Int.ceil_le_ceil h) <;>
      (try exact floor_le_ceil) <;> (try exact h')
  have floorq1_le : ⌊q2⌋ ≤ ⌊q1⌋ := by
    simp at h'
    apply Int.lt_add_one_iff.mp
    apply lt_of_lt_of_le h'
    exact Int.ceil_le_floor_add_one q1
  have : Int.fract q1 ≤ Int.fract q2 := by
    unfold Int.fract
    apply sub_le_sub
    · exact h
    simp only [Int.cast_le, floorq1_le]
  if h1 : Int.fract q1 < 1/2 then
    simp only [h1, reduceIte, ge_iff_le]
    split_ifs <;> (try exact Int.floor_le_floor h) <;>
      (exact floor_le_ceil)
  else if h2 : 1/2 < Int.fract q1 then
    have : 1/2 < Int.fract q2 := lt_of_lt_of_le h2 this
    simp only [h1, ↓reduceIte, h2, this, not_lt_of_gt this]
    exact Int.ceil_le_ceil h
  else
    have fract_eq : Int.fract q1 = 1/2 := le_antisymm (le_of_not_lt h2) (le_of_not_lt h1)
    simp only [fract_eq]
    rcases lt_or_eq_of_le this with h' | h'
    · simp [fract_eq] at *
      simp only [h', not_lt_of_ge (le_of_lt h'), lt_self_iff_false, ↓reduceIte, ge_iff_le]
      split_ifs
      · exact floor_le_ceil
      exact Int.ceil_le_ceil h
    simp only [<-h', fract_eq, ge_iff_le, le_refl, ↓reduceIte, lt_self_iff_false, ↓reduceIte]
    suffices ⌊q1⌋ = ⌊q2⌋ by
      rw [this]
      split_ifs <;> simp [Int.ceil_le_ceil h]
    exact le_antisymm (Int.floor_le_floor h) floorq1_le

lemma round_near_eq_of (q : ℚ) (z : ℤ) :
  z - 1/2 < q ∧ q < z + 1/2 → z = round_near_int q := by
  rintro ⟨h1, h2⟩
  if h3 : z ≤ q then
    have : Int.fract q = q - z := by
      apply Int.fract_eq_iff.mpr
      refine ⟨?_, ?_, ⟨z, ?_⟩⟩
      · simp [h3]
      · linarith
      ring
    rw [round_near_int, this]
    simp_rw [sub_lt_iff_lt_add, add_comm, h2]
    simp only [↓reduceIte]
    symm
    apply Int.floor_eq_iff.mpr ⟨h3, ?_⟩
    apply lt_trans h2
    linarith
  else
    simp at h3
    have floor_eq : ⌊q⌋ = z - 1 := by
      suffices ⌊q⌋ + 1 = z by
        linarith
      rw [<-Int.floor_add_one]
      apply Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      · linarith
      linarith
    have fract_eq : Int.fract q = q - (z - 1) := by
      rw [Int.fract]
      suffices (⌊q⌋ : ℚ) = z - 1 by
        linarith
      norm_cast
    rw [round_near_int, fract_eq]
    have : 1/2 < q - (z - 1) := by
      linarith
    simp_rw [if_neg (not_lt_of_gt this), if_pos this]
    symm
    apply Int.ceil_eq_iff.mpr ⟨?_, le_of_lt h3⟩
    linarith

lemma fract_eq_ceil_of_pos {q : ℚ} (h : 0 < Int.fract q) :
  Int.fract q = q + 1 - ⌈q⌉ := by
  rcases Int.fract_eq_zero_or_add_one_sub_ceil q
  · linarith
  assumption

lemma round_near_int_le (q : ℚ) :
  |round_near_int q - q| ≤ 1/2 := by
  unfold round_near_int
  simp only [Int.cast_ite]
  split_ifs with h1 h2 h3
  · rw [abs_sub_comm, Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg q)]
    exact le_of_lt h1
  · rw [abs_of_nonneg (by linarith [Int.le_ceil q])]
    rw [fract_eq_ceil_of_pos] at h2
    · linarith
    linarith
  · have : Int.fract q = 1/2 := le_antisymm (le_of_not_lt h2) (le_of_not_lt h1)
    rw [abs_sub_comm, Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg q)]
    rw [this]
  have : Int.fract q = 1/2 := le_antisymm (le_of_not_lt h2) (le_of_not_lt h1)
  rw [abs_of_nonneg (by linarith [Int.le_ceil q])]
  rw [fract_eq_ceil_of_pos] at this
  · linarith
  rw [this]
  norm_num

lemma round_near_int_of_int (z : ℤ) :
  round_near_int z = z := by
  rw [round_near_int,Int.fract_intCast]
  simp

lemma round_near_add_half (z : ℤ) (h : z % 2 = 0) :
  round_near_int (z + 1/2) = z := by
  rw [round_near_int]
  have : Int.fract (1 / 2 : ℚ) = 1/2 := by
    exact Int.fract_div_intCast_eq_div_intCast_mod
  rw [one_div] at this
  simp only [one_div, Int.fract_int_add, this, lt_self_iff_false, ↓reduceIte,
    Int.floor_int_add]
  have : ⌊(2⁻¹ : ℚ)⌋ = 0 := by norm_num
  rw [this, <-h]
  simp [h]

lemma round_near_sub_half (z : ℤ) (h : z % 2 = 0) :
  round_near_int (z - 1/2) = z := by
  rw [round_near_int]
  have : Int.fract (1 / 2 : ℚ) = 1/2 := by
    exact Int.fract_div_intCast_eq_div_intCast_mod
  have : Int.fract (-(1 / 2 : ℚ)) = 1/2 := by
    rw [Int.fract_neg, this]
    · norm_num
    rw [this]
    norm_num
  rw [sub_eq_add_neg]
  simp only [Int.fract_int_add, this, lt_self_iff_false, ↓reduceIte]
  rw [add_comm, Int.ceil_add_int]
  have : ⌈(-(1 / 2) : ℚ)⌉ = 0 := by norm_num
  rw [this, zero_add, if_neg]
  rw [add_comm]
  have : ⌊(z : ℚ) + -(1/2)⌋ = z - 1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · qify; linarith
    qify; linarith
  rw [this]
  omega

lemma round_of_add_half (z : ℤ) :
  round_near_int (z + 1/2) % 2 = 0 := by
  rw [round_near_int]
  have : Int.fract (z + 1/2 : ℚ) = 1/2 := by
    rw [Int.fract_int_add]
    norm_num
  rw [this]
  simp only [lt_self_iff_false, ↓reduceIte, Int.floor_int_add]
  rw [add_comm (z : ℚ), Int.ceil_add_int]
  rw [show ⌊(1 : ℚ)/2⌋ = 0 by norm_num, add_zero]
  split_ifs with h
  · assumption
  rw [show ⌈(1 : ℚ) / 2⌉ = 1 by norm_num]
  omega


def round_near_interval (z : ℤ) : Set ℚ :=
  if z % 2 = 0 then
    Set.Icc (z - 1/2) (z + 1/2)
  else
    Set.Ioo (z - 1/2) (z + 1/2)


lemma Icc_of_Ioo {α : Type} [PartialOrder α] {q x y : α} (h : q ∈ Set.Icc x y)
  (not_x : q ≠ x) (not_y : q ≠ y) : q ∈ Set.Ioo x y := by
  simp only [Set.mem_Icc, Set.mem_Ioo] at *
  constructor
  · exact lt_of_le_of_ne h.1 (not_x.symm)
  exact lt_of_le_of_ne h.2 not_y

lemma Ioo_of_Icc {α : Type} [Preorder α] (x y : α):
  Set.Ioo x y ⊆ Set.Icc x y := by
  exact Set.Ioo_subset_Icc_self


lemma round_near_eq_iff (q : ℚ) (z : ℤ) :
  round_near_int q = z ↔ q ∈ round_near_interval z := by
  constructor
  · intro h
    rw [<-h]
    unfold round_near_interval
    have : q ∈ Set.Icc ((round_near_int q) - (1 : ℚ) / 2) ((round_near_int q) + 1 / 2) := by
      suffices |round_near_int q - q| ≤ 1/2 by
        exact Set.mem_Icc_iff_abs_le.mp this
      exact round_near_int_le q
    split_ifs with h'
    · exact this
    · apply Icc_of_Ioo this
      · contrapose! h'
        rw [h']
        convert round_of_add_half (round_near_int q - 1) using 3
        push_cast
        linarith
      contrapose! h'
      rw [h']
      exact round_of_add_half (round_near_int q)
  intro h
  by_cases h' : z % 2 = 0
  · rw [round_near_interval, if_pos h'] at h
    apply le_antisymm
    · rw [<-round_near_add_half z h']
      apply round_near_le_round_near
      linarith [h.2]
    rw [<-round_near_sub_half z h']
    apply round_near_le_round_near
    linarith [h.1]
  rw [round_near_interval, if_neg h'] at h
  symm
  apply round_near_eq_of
  exact h


open Lean Meta Qq Mathlib.Meta.Positivity in
@[positivity round_near_int _]
def evalRoundNearInt : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(round_near_int $a) =>
    let zα : Q(Zero ℚ) := q(inferInstance)
    let pα : Q(PartialOrder ℚ) := q(inferInstance)
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa => pure (.nonnegative q(round_near_int_of_pos $pa))
    | .nonnegative pa => pure (.nonnegative q(round_near_int_of_nonneg $pa))
    | _ => pure .none



class ValidRounder (f : ℚ → ℕ) where
  le_iff_le q1 q2 : (0 ≤ q1) → (q1 ≤ q2) → f q1 ≤ f q2
  leftInverse : Function.LeftInverse f ((↑) : ℕ → ℚ)

instance : ValidRounder round0 where
  le_iff_le q1 q2 q1h q1le := by
    simp only [round0]
    zify
    apply abs_le_abs_of_nonneg
    · positivity
    exact Int.floor_le_floor q1le
  leftInverse := by
    intro n
    simp [round0]

instance : ValidRounder roundinf where
  le_iff_le q1 q2 q1h q1le := by
    simp only [roundinf]
    zify
    apply abs_le_abs_of_nonneg
    · positivity
    exact Int.ceil_le_ceil q1le
  leftInverse := by
    intro n
    simp [roundinf]

instance (s : Bool) : ValidRounder (roundup s) := by
  simp only [roundup]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    infer_instance

instance (s : Bool) : ValidRounder (rounddown s) := by
  simp only [rounddown]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    infer_instance

instance : ValidRounder roundnearest where
  le_iff_le q1 q2 q1h q1le := by
    simp only [roundnearest]
    zify
    apply abs_le_abs_of_nonneg
    · positivity
    exact round_near_le_round_near q1le
  leftInverse := by
    intro n
    rw [roundnearest]
    rw [show round_near_int n = n by exact_mod_cast round_near_int_of_int n]
    simp


def round_down (q : ℚ) : FloatRep C :=
  let exp := Int.log 2 |q|
  let mantissa := ⌊(|q| * 2^(-exp) - 1) * C.prec⌋
  ⟨q < 0, exp, mantissa.natAbs⟩

lemma round_down_neg (q : ℚ) (h : q ≠ 0) :
  round_down (-q) = Flean.neg (round_down q : FloatRep C) := by
  by_cases h' : q ≥ 0
  · have : q > 0 := lt_of_le_of_ne h' (Ne.symm h)
    simp [round_down, Flean.neg, h', this]
  have : q < 0 := not_le.mp h'
  simp [round_down, Flean.neg, this, le_of_lt this]


lemma round_down_coe (f : FloatRep C) (h : f.valid_m) :
  round_down (coe_q f) = f := by
  revert h
  apply floatrep_of_false₁ (f := f)
  · intro f
    rw [coe_q_of_neg, neg_valid_m, round_down_neg (coe_q f) coe_q_nezero, neg_invertible.injective.eq_iff]
    tauto
  intro e m h
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

lemma round_down_of_pos (q : ℚ) (h : 0 < q) :
  0 < coe_q (round_down q : FloatRep C) := by
  simp [coe_q, round_down]
  split
  · linarith
  positivity

lemma round_down_of_pos' (q : ℚ) (h : 0 < q) :
  (round_down q : FloatRep C).s = false := by
  simp [round_down]
  linarith

lemma round_down_of_neg (q : ℚ) (h : q < 0) :
  coe_q (round_down q : FloatRep C) < 0 := by
  suffices 0 < -coe_q (round_down q : FloatRep C) by
    exact Left.neg_pos_iff.mp this
  rw [<-coe_q_of_neg, <-round_down_neg q (by linarith)]
  apply round_down_of_pos
  exact Left.neg_pos_iff.mpr h

lemma round_down_of_neg' (q : ℚ) (h : q < 0) :
  (round_down q : FloatRep C).s = true := by
  simpa [round_down]

lemma casesQPlane (P : ℚ → ℚ → Prop)
  (h1 : ∀q1 > 0, ∀q2 > 0, P q1 q2)
  (h2 : ∀q1 < 0, ∀q2 > 0, P q1 q2)
  (h3 : ∀q1 > 0, ∀q2 < 0, P q1 q2)
  (h4 : ∀q1 < 0, ∀q2 < 0, P (-q1) (-q2) → P q2 q1) (q1 q2 : ℚ)
  (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) : P q1 q2 := by
  have h : ∀q ≠ (0 : ℚ), q > 0 ∨ q < 0 := by
    intro q qnezero
    by_cases h : q > 0
    · exact Or.inl h
    exact lt_or_gt_of_ne (Ne.symm qnezero)
  rcases (h q1 q1_nezero) with h' | h'
  · rcases (h q2 q2_nezero) with h'' | h''
    · exact h1 q1 h' q2 h''
    exact h3 q1 h' q2 h''
  · rcases (h q2 q2_nezero) with h'' | h''
    · exact h2 q1 h' q2 h''
    apply h4 q2 h'' q1 h'
    apply h1
    · exact Left.neg_pos_iff.mpr h''
    exact Left.neg_pos_iff.mpr h'

lemma abs_le_round_down_of_le (q1 q2 : ℚ) (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) :
  |q1| ≤ |q2| → |coe_q (round_down q1 : FloatRep C)| ≤ |coe_q (round_down q2 : FloatRep C)| := by
  intro h
  apply floatrep_le_pos_coe_q (vm1 := le_of_lt (round_down_valid q1 q1_nezero))
  rw [floatrep_pos_equiv]
  unfold floatrep_le_pos'
  constructor
  · simp [round_down]
    apply Int.log_mono_right
    · exact abs_pos.mpr q1_nezero
    exact h
  intro h
  simp only [round_down] at *
  zify
  apply abs_le_abs_of_nonneg
  · have := (mantissa_size_aux q1 q1_nezero).1
    rw [zpow_neg]
    refine Int.floor_nonneg.mpr ?_
    exact mul_nonneg (by linarith) (by linarith)
  apply Int.floor_le_floor
  gcongr
  · norm_num
  exact Int.le_of_eq (h.symm)

lemma le_round_down_of_le (q1 q2 : ℚ) (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) :
  q1 ≤ q2 → coe_q (round_down q1 : FloatRep C) ≤ coe_q (round_down q2 : FloatRep C) := by
  rw [<-floatrep_le_iff_coe_q_le (vm1 := round_down_valid q1 q1_nezero)
    (vm2 := round_down_valid q2 q2_nezero)]
  apply casesQPlane (q1_nezero := q1_nezero) (q2_nezero := q2_nezero)
  · intro q1 q1h q2 q2h h
    simp only [floatrep_le]
    rw [round_down_of_pos' q1 q1h, round_down_of_pos' q2 q2h]
    apply coe_q_le_floatrep_pos
    · exact round_down_valid q2 (by linarith)
    · apply abs_le_round_down_of_le q1 q2 (by linarith) (by linarith)
      rw [abs_of_pos q1h, abs_of_pos q2h]
      exact h
  · intro q1 q1h q2 q2h h
    simp_rw [floatrep_le, round_down_of_neg' q1 q1h, round_down_of_pos' q2 q2h]
  · intro q1 q1h q2 q2h h
    exfalso
    linarith
  · intro q1 q1h q2 q2h h h'
    have : -q1 ≤ -q2 := by
      linarith
    replace h := h this
    rw [floatrep_le, round_down_of_neg' q1 q1h, round_down_of_neg' q2 q2h]
    dsimp
    rw [round_down_neg q1 (by linarith), round_down_neg q2 (by linarith)] at h
    simp [floatrep_le, Flean.neg,
      round_down_of_neg' q1 q1h, round_down_of_neg' q2 q2h] at h
    exact h

lemma round_down_false_of_le_coe_aux (q : ℚ) (e : ℤ) (m : ℕ) (vm : m < C.prec) (q_pos : 0 < q)
  (h : q ≤ coe_q (⟨false, e, m⟩ : FloatRep C)) :
  coe_q (round_down q : FloatRep C) ≤ coe_q (⟨false, e, m⟩ : FloatRep C) := by
  rw [<-round_down_coe ⟨false, e, m⟩ vm]
  apply le_round_down_of_le q _ (ne_of_gt q_pos) coe_q_nezero h


def round_up (q : ℚ) : FloatRep C :=
  let exp := Int.log 2 |q|
  let mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs
  if mantissa = C.prec then
    ⟨q < 0, exp + 1, 0⟩
  else
    ⟨q < 0, exp, mantissa⟩

lemma round_up_def (q : ℚ) :
  let exp := Int.log 2 |q|
  let mantissa := ⌈(|q| * 2^(-exp) - 1) * C.prec⌉.natAbs
  coe_q (round_up q : FloatRep C) = coe_q (⟨(q < 0), exp, mantissa⟩ : FloatRep C) := by
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
  revert h
  apply floatrep_of_false₁ (f := f)
  · intro f
    rw [coe_q_of_neg, neg_valid_m, round_up_neg (coe_q f) coe_q_nezero, neg_invertible.injective.eq_iff]
    tauto
  intro e m h
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

lemma round_up_of_pos (q : ℚ) (h : 0 < q) :
  0 < coe_q (round_up q : FloatRep C) := by
  rw [round_up_def, coe_q]
  split
  · simp at *; linarith
  positivity

lemma round_up_of_pos' (q : ℚ) (h : 0 < q) :
  (round_up q : FloatRep C).s = false := by
  simp only [round_up]
  split <;> (simp; linarith)


lemma round_up_of_neg (q : ℚ) (h : q < 0) :
  coe_q (round_up q : FloatRep C) < 0 := by
  suffices 0 < -coe_q (round_up q : FloatRep C) by
    exact Left.neg_pos_iff.mp this
  rw [<-coe_q_of_neg, <-round_up_neg q (by linarith)]
  apply round_up_of_pos
  exact Left.neg_pos_iff.mpr h

lemma round_up_of_neg' (q : ℚ) (h : q < 0) :
  (round_up q : FloatRep C).s = true := by
  simp [round_up]
  split <;> simpa

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

lemma mantissa_nonneg (C : FloatCfg) (q : ℚ) (q_nezero : q ≠ 0) :
  0 ≤ (|q| * ((2 : ℚ)^Int.log 2 |q|)⁻¹ - 1) * C.prec := by
  apply mul_nonneg
  · linarith [(mantissa_size_aux q q_nezero).1]
  exact_mod_cast le_of_lt C.prec_pos


lemma abs_le_round_up_of_le (q1 q2 : ℚ) (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) :
  |q1| ≤ |q2| → |coe_q (round_up q1 : FloatRep C)| ≤ |coe_q (round_up q2 : FloatRep C)| := by
  intro q_le_than
  rw [round_up_def, round_up_def]
  apply floatrep_le_pos_coe_q
  · simp only [zpow_neg]
    apply small_ceil
    · linarith [(mantissa_size_aux q1 q1_nezero).2]
    · linarith [(mantissa_size_aux q1 q1_nezero).1]
    exact le_of_lt C.prec_pos
  rw [floatrep_pos_equiv]
  unfold floatrep_le_pos'
  constructor
  · dsimp
    apply Int.log_mono_right (abs_pos.mpr q1_nezero) q_le_than
  dsimp
  intro h
  simp only [zpow_neg]
  zify
  rw [abs_of_nonneg (Int.ceil_nonneg (mantissa_nonneg C q1 q1_nezero))]
  rw [abs_of_nonneg (Int.ceil_nonneg (mantissa_nonneg C q2 q2_nezero))]
  rw [h]
  gcongr

lemma le_round_up_of_le (q1 q2 : ℚ) (q1_nezero : q1 ≠ 0) (q2_nezero : q2 ≠ 0) :
  q1 ≤ q2 → coe_q (round_up q1 : FloatRep C) ≤ coe_q (round_up q2 : FloatRep C) := by
  rw [<-floatrep_le_iff_coe_q_le (vm1 := round_up_valid q1 q1_nezero)
    (vm2 := round_up_valid q2 q2_nezero)]
  apply casesQPlane (q1_nezero := q1_nezero) (q2_nezero := q2_nezero)
  · intro q1 q1h q2 q2h h
    simp only [floatrep_le]
    rw [round_up_of_pos' q1 q1h, round_up_of_pos' q2 q2h]
    apply coe_q_le_floatrep_pos
    · exact round_up_valid q2 (by linarith)
    · apply abs_le_round_up_of_le q1 q2 (by linarith) (by linarith)
      rw [abs_of_pos q1h, abs_of_pos q2h]
      exact h
  · intro q1 q1h q2 q2h h
    simp_rw [floatrep_le, round_up_of_neg' q1 q1h, round_up_of_pos' q2 q2h]
  · intro q1 q1h q2 q2h h
    exfalso
    linarith
  · intro q1 q1h q2 q2h h h'
    have : -q1 ≤ -q2 := by
      linarith
    replace h := h this
    rw [floatrep_le, round_up_of_neg' q1 q1h, round_up_of_neg' q2 q2h]
    dsimp
    rw [round_up_neg q1 (by linarith), round_up_neg q2 (by linarith)] at h
    simp [floatrep_le, Flean.neg,
      round_up_of_neg' q1 q1h, round_up_of_neg' q2 q2h] at h
    exact h


-- gross casework
def round_nearest (q : ℚ) : FloatRep C :=
  let f1 : FloatRep C := round_down q -- round towards zero
  let f2 : FloatRep C := round_up q -- round away from zero
  -- Find which one is closest
  if |q| - |coe_q f1| < |coe_q f2| - |q| then
    f1
  else if |coe_q f2| - |q| < |q| - |coe_q f1| then
    f2
  else if f2.m % 2 = 0 then
    f2
  else
    f1


lemma round_nearest_eq_or (q : ℚ) :
  (round_nearest q : FloatRep C) = round_down q ∨ (round_nearest q : FloatRep C) = round_up q := by
  unfold round_nearest
  dsimp
  split_ifs
  repeat (first | split | tauto)


lemma round_nearest_neg (q : ℚ) (q_nezero : q ≠ 0) :
  round_nearest (-q) = Flean.neg (round_nearest q : FloatRep C) := by
  simp only [round_nearest, round_down_neg q q_nezero, round_up_neg q q_nezero]
  simp [coe_q_of_neg]
  split_ifs with h1 h2 h3 h4 h5 <;> (try rfl)
  · exfalso
    apply h4
    simp [Flean.neg] at h3
    exact h3
  · exfalso
    apply h3
    simpa [Flean.neg]


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
