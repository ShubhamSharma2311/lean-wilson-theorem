import Wilson.Basic

namespace Wilson

open Nat

example : 7 ∣ (7 - 1)! + 1 := dvd_factorial_succ (by norm_num)

example : ¬ 6 ∣ (6 - 1)! + 1 := by decide

end Wilson
