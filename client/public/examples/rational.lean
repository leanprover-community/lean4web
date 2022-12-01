import Mathlib.Data.Rat.Order -- import the rationals
import Mathlib.Data.Rat.Init -- import notation ℚ for rationals
import Mathlib.Tactic.Linarith -- a linear arithmetic tactic

-- let `x`, `y` and `z` be rationals
variable (x y z : ℚ)

-- let's prove that if `x < y` and `y + 3 < z + 10` then `x + 37 < z + 44`
example (h₁ : x < y) (h₂ : y + 3 < z + 10) : x + 37 < z + 44 := by
  linarith -- the `linarith` tactic can do this automatically

-- let's prove that (x+y)^2=x^2+2*x*y+y^2

example : (x + y)^2 = x^2 + 2 * x * y + y^2 := by
  ring -- the `ring` tactic can do this automatically
