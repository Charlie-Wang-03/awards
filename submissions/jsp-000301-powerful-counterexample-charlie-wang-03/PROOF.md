# Natural-language proof

## The scoped question

Call a positive integer `N` **powerful** if every prime divisor `p` of `N` satisfies `p^2 | N`. JSP-000301 asks whether, whenever `n` and `n+1` are both powerful, at least one of them must be a perfect square.

The answer is **no**.

## Lemma 1 — numbers of the form `a^2 b^3` are powerful

Let `N = a^2 b^3`, and let `p` be a prime divisor of `N`. Since `p` is prime and divides a product, either `p | a^2` or `p | b^3`. A prime dividing a positive power of an integer divides the base, so either `p | a` or `p | b`.

- If `p | a`, then `p^2 | a^2`, hence `p^2 | a^2 b^3 = N`.
- If `p | b`, then `p^2 | b^3`, hence again `p^2 | a^2 b^3 = N`.

Thus every prime divisor of `a^2 b^3` occurs with multiplicity at least two, so `a^2 b^3` is powerful.

## Lemma 2 — `12167` and `12168` are powerful

Direct arithmetic gives

```text
12167 = 23^3 = 1^2 * 23^3,
12168 = 39^2 * 2^3 = 2^3 * 3^2 * 13^2.
```

By Lemma 1, both numbers are powerful.

They are consecutive because

```text
12168 = 12167 + 1.
```

## Lemma 3 — neither number is a square

We have

```text
110^2 = 12100,
111^2 = 12321,
```

and therefore

```text
110^2 < 12167 < 12168 < 111^2.
```

For any natural number `k`, either `k <= 110` or `111 <= k`. In the first case `k^2 <= 110^2`; in the second case `111^2 <= k^2`. Hence no natural-number square lies strictly between `110^2` and `111^2`.

Consequently neither `12167` nor `12168` is a perfect square.

## Conclusion

Taking `n = 12167`, the consecutive positive integers `n` and `n+1` are both powerful, while neither is a perfect square. This is a counterexample to the universal assertion in JSP-000301, so the scoped yes/no question has a complete negative answer.

## Adversarial checks

The argument does not infer powerfulness merely from the displayed decimal values: it proves a general `a^2 b^3` lemma and instantiates it. It does not infer nonsquareness from numerical search: it proves a square-gap lemma. No assumption of coprimality between `a` and `b` is needed. The conclusion is limited to the yes/no statement recorded as JSP-000301 and makes no claim about the separate counting problem associated with Erdős #365.
