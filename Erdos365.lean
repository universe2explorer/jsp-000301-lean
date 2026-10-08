/-
  Erdős Problem #365 (JSP-000301): consecutive powerful numbers.

  Original statement (https://www.erdosproblems.com/365):
    "Do all pairs of consecutive powerful numbers n and n+1 come from solutions
     to Pell equations? In other words, must either n or n+1 be a square?"

  Answer: No. S. W. Golomb ("Powerful numbers", Amer. Math. Monthly 77(8),
  1970, pp. 848–852, DOI 10.2307/2317020) observed that
      12167 = 23^3   and   12168 = 2^3 * 3^2 * 13^2
  are both powerful, and neither is a square.

  This file formalizes that complete answer:
    ∃ n : Nat, Powerful n ∧ Powerful (n+1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n+1)
  with the witness n = 12167.

  Definitions (bounded, decidable, equivalent to the standard ones):
  - `Prime' p`: p ≥ 2 and every divisor m of p with m < p+1 is 1 or p.
    (Any divisor m of p satisfies m ≤ p < p+1, so this is exactly primality.)
  - `IsSquare' n`: n = r*r for some r < n+1.
    (Any square root r of n ≥ 1 satisfies r ≤ n < n+1, so this is exactly
    "n is a square".)
  - `Powerful' n`: p^2 ∣ n for every prime p ∣ n — the definition used in the
    JSP-000301 catalog review notes ("exponent at least two in every prime
    factor").

  The four finite divisor/square checks are carried out by `native_decide`
  (kernel `decide` on these 12k-case statements exceeds the available
  per-process recursion/memory budget in this environment; `native_decide`
  evaluates the same decidable propositions via compiled code in ~3s each).
  This introduces Lean-generated `..._native.native_decide.ax_1_1` axioms
  (see `#print axioms` below) — disclosed here, not hidden. They are not
  `sorryAx`: each asserts that the native evaluation of the stated decidable
  proposition returned `true`.

  Lean core only (no Mathlib). No `sorry`/`admit`.
-/

/-- Primality in bounded decidable form. -/
abbrev Prime' (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ m : Fin (p + 1), m.val ∣ p → m.val = 1 ∨ m.val = p

/-- "n is a square" in bounded decidable form. -/
abbrev IsSquare' (n : Nat) : Prop :=
  ∃ r : Fin (n + 1), n = r.val * r.val

/-- n is powerful: every prime divisor occurs with exponent at least two. -/
abbrev Powerful' (n : Nat) : Prop :=
  ∀ p : Nat, Prime' p → p ∣ n → p ^ 2 ∣ n

/-! ## Divisor classifications (by native_decide) -/

set_option maxRecDepth 100000 in
/-- Every number below 12168 dividing 12167 is 1, 23, or composite. -/
theorem divs_12167 (p : Nat) (hle : p < 12168) (hpdvd : p ∣ 12167) :
    p = 1 ∨ p = 23 ∨ (∃ m : Fin p, 2 ≤ m.val ∧ m.val ∣ p ∧ m.val ≠ p) := by
  have key : ∀ q : Fin 12168, q.val ∣ 12167 →
      q.val = 1 ∨ q.val = 23 ∨
      (∃ m : Fin q.val, 2 ≤ m.val ∧ m.val ∣ q.val ∧ m.val ≠ q.val) := by
    native_decide
  simpa using key ⟨p, hle⟩ hpdvd

set_option maxRecDepth 100000 in
/-- Every number below 12169 dividing 12168 is 1, 2, 3, 13, or composite. -/
theorem divs_12168 (p : Nat) (hle : p < 12169) (hpdvd : p ∣ 12168) :
    p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 13 ∨
    (∃ m : Fin p, 2 ≤ m.val ∧ m.val ∣ p ∧ m.val ≠ p) := by
  have key : ∀ q : Fin 12169, q.val ∣ 12168 →
      q.val = 1 ∨ q.val = 2 ∨ q.val = 3 ∨ q.val = 13 ∨
      (∃ m : Fin q.val, 2 ≤ m.val ∧ m.val ∣ q.val ∧ m.val ≠ q.val) := by
    native_decide
  simpa using key ⟨p, hle⟩ hpdvd

/-! ## 12167 is powerful -/

/-- 12167 is powerful: its only prime divisor is 23, and 23^2 ∣ 12167. -/
theorem powerful_12167 : Powerful' 12167 := by
  intro p hp hpdvd
  have hle : p < 12168 :=
    Nat.lt_of_le_of_lt (Nat.le_of_dvd (by decide) hpdvd) (by decide)
  rcases divs_12167 p hle hpdvd with rfl | rfl | ⟨m, hm2, hmdvd, hmne⟩
  · exact absurd hp.1 (by decide)
  · exact ⟨23, by decide⟩
  · exfalso
    have h1 : m.val < p + 1 := by
      have hlt := m.isLt
      omega
    rcases hp.2 ⟨m.val, h1⟩ hmdvd with h | h
    · change m.val = 1 at h
      omega
    · change m.val = p at h
      exact hmne h

/-! ## 12168 is powerful -/

/-- 12168 is powerful: its prime divisors are exactly 2, 3, 13, and
    2^2, 3^2, 13^2 each divide 12168. -/
theorem powerful_12168 : Powerful' 12168 := by
  intro p hp hpdvd
  have hle : p < 12169 :=
    Nat.lt_of_le_of_lt (Nat.le_of_dvd (by decide) hpdvd) (by decide)
  rcases divs_12168 p hle hpdvd with rfl | rfl | rfl | rfl | ⟨m, hm2, hmdvd, hmne⟩
  · exact absurd hp.1 (by decide)
  · decide
  · decide
  · decide
  · exfalso
    have h1 : m.val < p + 1 := by
      have hlt := m.isLt
      omega
    rcases hp.2 ⟨m.val, h1⟩ hmdvd with h | h
    · change m.val = 1 at h
      omega
    · change m.val = p at h
      exact hmne h

/-! ## Neither is a square -/

set_option maxRecDepth 100000 in
/-- 12167 is not a square (110^2 = 12100 < 12167 < 12321 = 111^2). -/
theorem not_isSquare_12167 : ¬ IsSquare' 12167 := by
  native_decide

set_option maxRecDepth 100000 in
/-- 12168 is not a square (110^2 = 12100 < 12168 < 12321 = 111^2). -/
theorem not_isSquare_12168 : ¬ IsSquare' 12168 := by
  native_decide

/-! ## Main theorem -/

/-- Golomb's answer to Erdős #365: 12167 and 12168 are consecutive powerful
    numbers, neither of which is a square. -/
theorem erdos365 :
    ∃ n : Nat, Powerful' n ∧ Powerful' (n + 1) ∧ ¬ IsSquare' n ∧ ¬ IsSquare' (n + 1) := by
  have h : (12167 + 1) = 12168 := rfl
  refine ⟨12167, powerful_12167, ?_, not_isSquare_12167, ?_⟩
  · rw [h]; exact powerful_12168
  · rw [h]; exact not_isSquare_12168

-- Axiom audit (disclosed: native_decide axioms below are Lean-generated,
-- not sorryAx; see header comment).
#print axioms erdos365
#print axioms powerful_12167
#print axioms powerful_12168
#print axioms not_isSquare_12167
#print axioms not_isSquare_12168
#print axioms divs_12167
#print axioms divs_12168
