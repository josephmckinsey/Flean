import Batteries.Data.Rat.Float
import Flean.FloatRep
import Flean.Basic

def DoubleCfg : FloatCfg := FloatCfg.mk (1 <<< 52) (-1022) 1023 (by norm_num) (
  Nat.zero_lt_succ 4503599627370495
)

def frep : FloatCfg := FloatCfg.mk 256 (-127) 127 (by norm_num) (by norm_num)

def frep64 := FloatRep DoubleCfg
def f64 := Flean.Float DoubleCfg

example : coe_q (roundf roundnearest (coe_q (roundf roundnearest 0.1 : frep64) + coe_q (roundf roundnearest 0.2 : frep64)) : frep64) == (((0.1 : Float) + (0.2 : Float)).toRat0) := by
  native_decide

instance : Rounding where
  mode := .nearest

-- Could use eval... But native_decide is easier
example : to_rat (to_float (to_rat (to_float 0.1 : f64) + to_rat (to_float 0.2 : f64)) : f64) == (((0.1 : Float) + (0.2 : Float)).toRat0) := by
  native_decide

def test_cases : List (ℚ × ℚ) :=
  [(0.1, 0.2),
   (0.0001, 1000000000.0),
   (2^(-1026 : ℤ), 2^(-1024 : ℤ)),
   (1.2*2^(-1026 : ℤ), 5.3*2^(-1024 : ℤ)),
   (2^30, 2^31)]

def test_cast (x y : ℚ) : Bool :=
  to_rat (to_float (to_rat (to_float x : f64) + to_rat (to_float y : f64)) : f64) == ((x.toFloat + y.toFloat).toRat0)

example : test_cases.all (λ ⟨x, y⟩ => test_cast x y) := by
  native_decide

--#eval ((@round_down frep 3.5) : frep64)
--#check (round_down 3.5 : frep64)
--#check (coe_q (⟨false, 0, 0⟩ : frep64))
--#eval @to_rat C (@to_float C 3.528123042)
--#eval @coe_q C (@round_down C 3.5)
--#eval @round_down C 0
