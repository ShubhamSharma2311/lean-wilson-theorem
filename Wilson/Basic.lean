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
  by_contra hnp
  have hm := Nat.minFac_prime (show n ≠ 1 by omega)
  have hlt : n.minFac < n := (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp
  have h1 : n.minFac ∣ (n - 1)! := Nat.dvd_factorial hm.pos (by omega)
  have h2 : n.minFac ∣ (n - 1)! + 1 := (Nat.minFac_dvd n).trans h
  have h3 : n.minFac ∣ 1 := (Nat.dvd_add_right h1).mp h2
  exact hm.one_lt.ne' (Nat.dvd_one.mp h3)

/-- Wilson's criterion for primality. -/
theorem prime_iff {n : ℕ} (hn : 1 < n) : n.Prime ↔ n ∣ (n - 1)! + 1 :=
  ⟨dvd_factorial_succ, prime_of_dvd_factorial_succ hn⟩

end Wilson
