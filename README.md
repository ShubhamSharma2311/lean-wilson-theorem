# Wilson's Theorem

`(p - 1)! ≡ -1 (mod p)` for primes, and the converse: it characterises primes.

Formalised in Lean 4 with Mathlib. No `sorry`.

## Proof outline

1. In `ZMod p` every nonzero residue pairs with its inverse; only `±1` are self-inverse, giving `(p - 1)! = -1`.
2. Casting back: `p ∣ (p - 1)! + 1`.
3. Conversely, if `n` is composite its least prime factor `m < n` divides `(n - 1)!`.
4. Then `m ∣ 1`, a contradiction, so `n` is prime.

## Contents

- [`Wilson/Basic.lean`](Wilson/Basic.lean): the main development
- [`Wilson/Examples.lean`](Wilson/Examples.lean): small worked examples

Declarations:

- `Wilson.wilson`
- `Wilson.dvd_factorial_succ`
- `Wilson.prime_of_dvd_factorial_succ`
- `Wilson.prime_iff`

## Build

```
lake exe cache get
lake build
```

Toolchain: `leanprover/lean4:v4.33.0-rc1`.
