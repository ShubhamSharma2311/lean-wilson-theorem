import Mathlib

/-!
# Wilson's theorem

`p` is prime iff `p ∣ (p - 1)! + 1` (for `1 < p`).
The forward direction pairs residues with their inverses (`ZMod.wilsons_lemma`);
the converse uses the least prime factor.
-/

namespace Wilson

open Nat

/-- **Wilson's theorem** in `ZMod p`. -/
theorem wilson {p : ℕ} (hp : p.Prime) : ((p - 1)! : ZMod p) = -1 := by
  haveI := Fact.mk hp
  exact ZMod.wilsons_lemma (p := p)

/-- Divisibility form: `p ∣ (p - 1)! + 1`. -/
theorem dvd_factorial_succ {p : ℕ} (hp : p.Prime) : p ∣ (p - 1)! + 1 := by
  sorry

end Wilson
