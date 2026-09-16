# Lean formalization map

## Status

The restricted theorem in `STATEMENT.md` has a complete Lean 4 formalization. The package-specific pinned build passed in GitHub Actions run `35127171862`.

## Environment

```text
Lean:    v4.34.0
Mathlib: 5ed2965256430c3649e86755f9576b54eca72435
```

All transitive dependencies are pinned in `lake-manifest.json`.

## Top-level theorem

`PC5488.pc5_488` in `PC5488/Final.lean` assumes:

```lean
0 < m
2 ≤ q₁
q₁ < q₂
q₂ < q₃
q₃ < q₄
q₄ < q₅
q₅ ≤ n
```

and the ten pairwise hypotheses `Nat.Coprime qᵢ qⱼ` for `i < j`. It proves

```lean
n * countMultiples5 q₁ q₂ q₃ q₄ q₅ m <
  2 * m * countMultiples5 q₁ q₂ q₃ q₄ q₅ n
```

`countMultiples5 ... x` encodes positive integers `1,...,x` by `e+1` for `e ∈ Finset.range x`, so it matches the counting function in `STATEMENT.md` and `PROOF.md`.

## Module chain

`PC5488.lean` imports the complete proof chain:

```lean
import PC5488.Basic
import PC5488.Overlap
import PC5488.Aggregate
import PC5488.Bonferroni
import PC5488.Final
```

### `PC5488.Basic`

Defines the counting sets/function, proves the full `q₁ = 2` branch, nested natural division, and the four-reciprocal estimate.

Key declarations:

```text
card_multiplesUpTo
countMultiples5_le
nested_div
half_plus_one_le_count_of_two
count_gt_half_of_two
target_of_two
four_reciprocal_lt_one
```

### `PC5488.Overlap`

Formalizes the row-overlap estimate

\[
\sum_{j\ne i}\left\lfloor\frac{n}{q_iq_j}\right\rfloor
\le
\left\lfloor\frac n{q_i}\right\rfloor-1.
\]

Key declarations:

```text
nat_div_cast_le_div
four_div_sum_le_sub_one
overlap_row_le
```

### `PC5488.Aggregate`

Defines `M` and `D` and proves the subtraction-free aggregate inequality

\[
2D+5\le M.
\]

Key declaration: `two_D_add_five_le_M`.

### `PC5488.Bonferroni`

Formalizes the five-set second-order Bonferroni inequality and coprime pair intersections, obtaining

\[
M\le F_A(n)+D.
\]

Key declaration: `M_le_count_add_D`.

### `PC5488.Final`

Combines

\[
M+5\le2F_A(n),\qquad nS<M+5,\qquad F_A(m)\le mS
\]

and performs the outer `q₁=2` / `q₁≥3` split.

Key declarations:

```text
div_lt_natDiv_add_one
n_mul_S_lt_M_add_five
M_add_five_le_two_count
n_mul_S_lt_two_count
count_le_M
count_cast_le_mul_S
target_of_ge_three
pc5_488
```

## Axiom audit

`Audit.lean` contains

```lean
#check PC5488.pc5_488
#print axioms PC5488.pc5_488
```

The pinned package run reports:

```text
'PC5488.pc5_488' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorryAx` in the reported dependency set.

## Natural-language alignment

| Mathematical proof step | Lean module |
| --- | --- |
| `a=2` density branch | `Basic` |
| reciprocal / row overlap | `Basic`, `Overlap` |
| double-counted pair overlap | `Aggregate` |
| second-order Bonferroni | `Bonferroni` |
| density sandwich and final case split | `Final` |

The formal theorem is intentionally only the restricted five-generator pairwise-coprime result documented in `STATEMENT.md`.
