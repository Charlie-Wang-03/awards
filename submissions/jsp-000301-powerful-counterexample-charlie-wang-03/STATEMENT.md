# Statement correspondence

## Upstream scoped statement

Repository entry: `JSP-000301` in `problems/catalog-0301-0400.md`.

The recorded question is:

> If two consecutive positive integers are powerful, must at least one be a perfect square?

The upstream review note defines a powerful number by requiring exponent at least two for every prime factor and records the pair `12167, 12168` as a counterexample. It also states that this scoped question is distinct from the separate counting question in Erdős problem #365.

## Lean definitions

```lean
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

def IsSquare (n : ℕ) : Prop :=
  ∃ k : ℕ, k ^ 2 = n
```

These definitions encode the standard prime-divisor characterization of powerful natural numbers and the ordinary notion of a natural-number perfect square.

## Top-level formal statement

```lean
theorem JSP000301.jsp_000301 :
    ¬ ∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) →
      IsSquare n ∨ IsSquare (n + 1)
```

The witness theorem is:

```lean
theorem JSP000301.jsp_000301_counterexample :
    ∃ n : ℕ, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧
      ¬ IsSquare n ∧ ¬ IsSquare (n + 1)
```

## Clause-by-clause audit

| Upstream clause | Lean encoding | Assessment |
| --- | --- | --- |
| positive integer `n` | `n : ℕ` and `0 < n` | exact |
| consecutive integers | `n` and `n + 1` | exact |
| both powerful | `Powerful n` and `Powerful (n + 1)` | exact under the recorded prime-divisor definition |
| at least one is a square | `IsSquare n ∨ IsSquare (n + 1)` | exact |
| yes/no question answered negatively | negation of the universal implication | exact |
| explicit counterexample | existential theorem with witness `12167` | exact |

## Scope result

**Correspondence result: complete negative answer to the scoped JSP-000301 yes/no statement.**

No fixed-cardinality, congruence, coprimality, asymptotic, or other mathematical restriction is added. The positivity condition makes explicit the phrase “positive integers.” The theorem does not claim to formalize or solve the separate counting/asymptotic problem associated with Erdős #365.

The mathematical counterexample is historical and already recorded by upstream. The submitted new work is the Lean formalization and its reproducibility/alignment package, not discovery of the counterexample.
