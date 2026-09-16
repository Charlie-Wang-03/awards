# Formalization map

## Definitions

`JSP000301.Powerful` directly encodes the prime-divisor definition used by the upstream review note:

```text
for every prime p, if p divides n then p^2 divides n.
```

`JSP000301.IsSquare` encodes existence of a natural number whose square is the given number.

## Natural proof to Lean map

| Natural-language step | Lean declaration | Role |
| --- | --- | --- |
| Every `a^2 b^3` is powerful | `powerful_sq_mul_cube` | derives squared prime divisibility from primality and divisibility of powers |
| `12167 = 1^2 * 23^3` | `powerful_12167` | arithmetic normalization plus the general powerful lemma |
| `12168 = 39^2 * 2^3` | `powerful_12168` | arithmetic normalization plus the general powerful lemma |
| no square lies strictly between `110^2` and `111^2` | `not_square_in_gap` | splits `k <= 110` / `111 <= k` and compares squares monotonically |
| `12167` is not a square | `not_square_12167` | instantiates the gap lemma |
| `12168` is not a square | `not_square_12168` | instantiates the gap lemma |
| explicit consecutive counterexample exists | `jsp_000301_counterexample` | assembles positivity, powerfulness, consecutiveness and nonsquareness |
| universal yes-claim is false | `jsp_000301` | applies the universal claim to `12167` and contradicts both square alternatives |

## Strictness and boundary audit

There is no delicate analytic strict inequality. The only strict inequalities are the exact integer facts

```text
110^2 < 12167 < 12168 < 111^2.
```

The square-gap proof covers every `k : ℕ`: linear order gives `k <= 110` or `111 <= k`; multiplication monotonicity then excludes equality with either interior number.

## Dependency audit

The proof uses only Mathlib facts/tactics in the pinned dependency graph, including primality/divisibility facts, `ring`, `norm_num`, and `omega`. No external executable, oracle, generated certificate, or unpinned theorem source is required.

`Audit.lean` prints the two exported result theorems and their axiom dependencies. The verification script fails on any Lean build or audit failure.
