# Statement correspondence

## Related entry

- Repository entry: `JSP-000395` — *How do the densities of multiples of a given finite integer set compare across different intervals?*
- Repository catalog: `problems/catalog-0301-0400.md#JSP-000395`
- Related Erdős problem: `https://www.erdosproblems.com/488`

This file records the scope comparison for the submitted restricted theorem. It does not assert equivalence to the unrestricted problem.

## Counting function

For a finite set of positive integers `A`, write

\[
F_A(x)=\#\{1\le t\le x:\exists q\in A,\ q\mid t\}.
\]

In Lean, `countMultiples5 q₁ q₂ q₃ q₄ q₅ x` represents exactly this count for the five-element set `{q₁,...,q₅}`: positive integers `1,...,x` are encoded as `e+1` with `e ∈ Finset.range x`.

## Submitted formal theorem

The top-level theorem is `PC5488.pc5_488`.

Its assumptions are:

```text
0 < m
2 ≤ q₁ < q₂ < q₃ < q₄ < q₅ ≤ n
Nat.Coprime qᵢ qⱼ for every i < j
```

and its conclusion is

```text
n * countMultiples5 q₁ q₂ q₃ q₄ q₅ m
  < 2 * m * countMultiples5 q₁ q₂ q₃ q₄ q₅ n.
```

Equivalently,

\[
nF_A(m)<2mF_A(n).
\]

## Comparison with the unrestricted JSP/Erdős problem

| Dimension | Unrestricted problem | Submitted theorem | Effect |
| --- | --- | --- | --- |
| finite set size | arbitrary finite set | exactly five generators | genuine restriction |
| coprimality | not restricted to pairwise-coprime sets | pairwise coprime | genuine restriction; not WLOG |
| ordering | set notation | `q₁<...<q₅` | normalization of five distinct generators |
| lower generator bound | positive integers | `q₁≥2` | the theorem excludes generator `1`; when `1∈A`, the counting set is all positive integers and the associated inequality is trivial under the original interval ordering |
| `n` condition | `n ≥ max A` in the detailed Erdős formulation used for this comparison | `q₅ ≤ n` | exact match after ordering |
| `m` condition | target case uses `m>n` | theorem proves all `m>0` | strengthening in this variable only |
| inequality | `nF_A(m)<2mF_A(n)` | same | exact match within the restricted class |

## Correspondence result

**Result: restricted implication, not equivalent to the full problem.**

For every instance satisfying the original interval conditions and additionally satisfying `|A|=5`, `min A≥2`, and pairwise coprimality, `PC5488.pc5_488` proves the target inequality. The formal theorem does not remove the fixed-cardinality or pairwise-coprime restrictions and therefore must not be presented as a complete Lean proof of JSP-000395.
