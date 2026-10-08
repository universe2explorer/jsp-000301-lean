# JSP-000301 Lean Formalization: Erdős Problem #365

## Problem

**JSP-000301 / Erdős Problem #365**: "Do all pairs of consecutive powerful numbers n and n+1 come from solutions to Pell equations? In other words, must either n or n+1 be a square?"

**Answer**: No. Counterexample by S. W. Golomb.

## Mathematical Solution

**Solver**: Solomon W. Golomb, "Powerful numbers", *American Mathematical Monthly* 77(8), 1970, pp. 848–852. DOI: [10.2307/2317020](https://doi.org/10.2307/2317020).

Golomb observed that:
- `12167 = 23³` is powerful (every prime divisor occurs with exponent ≥ 2)
- `12168 = 2³ · 3² · 13²` is powerful
- Neither `12167` nor `12168` is a perfect square (`110² = 12100 < 12167 < 12168 < 12321 = 111²`)

## Formalization

**File**: `Erdos365.lean` — Main theorem `erdos365` proves `∃ n : Nat, Powerful' n ∧ Powerful' (n+1) ∧ ¬ IsSquare' n ∧ ¬ IsSquare' (n+1)` with witness `n = 12167`.

Definitions are bounded decidable forms equivalent to the standard ones (see file header). Lean core only, no Mathlib.

## Build Instructions

Requirements: Lean 4.34.1 via elan. No dependencies.

```bash
elan toolchain install leanprover/lean4:v4.34.1
lean Erdos365.lean
```

Expected: exit code 0, no errors. `#print axioms` output is at the end of the file.

## Axiom Audit

`'erdos365' depends on axioms: [propext, Quot.sound, divs_12167._native.native_decide.ax_1_1, divs_12168._native.native_decide.ax_1_1, not_isSquare_12167._native.native_decide.ax_1_1, not_isSquare_12168._native.native_decide.ax_1_1]`

No `sorry`, `admit`, or `sorryAx`. The `native_decide` axioms are Lean-generated and disclosed (see Erdos365.lean header).

## Attribution

- Mathematical solver: Solomon W. Golomb (1970)
- Lean formalization author: Yang Liu (GitHub: universe2explorer)

## License

MIT License. See LICENSE.
