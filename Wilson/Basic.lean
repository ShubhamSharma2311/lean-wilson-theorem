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
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [wilson hp]
  ring

/-- Converse: if `n ∣ (n - 1)! + 1` with `1 < n`, then `n` is prime. -/
theorem prime_of_dvd_factorial_succ {n : ℕ} (hn : 1 < n) (h : n ∣ (n - 1)! + 1) : n.Prime := by
  sorry

end Wilson
