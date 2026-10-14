# PC5-488 Lean formalization

> Status: **complete and kernel-checked**. The full theorem `PC5488.pc5_488` builds successfully in the pinned Lean 4.34.0 / Mathlib v4.34.0 environment and matches the theorem stated in `README.md`.

## 1. Environment

The isolated proof project lives in:

```text
proofs/pc5-488/lean/
```

It pins:

```text
Lean:    v4.34.0
Mathlib: v4.34.0
```

through `lean-toolchain` and `lakefile.lean`.

The build path used by CI is:

```bash
lake update
lake exe cache get
lake build
```

The dedicated workflow is:

```text
.github/workflows/pc5-488-lean.yml
```

## 2. Formal theorem

The final theorem is `PC5488.pc5_488` in `PC5488/Final.lean`.

It assumes:

```lean
0 < m
2 ≤ q₁
q₁ < q₂
q₂ < q₃
q₃ < q₄
q₄ < q₅
q₅ ≤ n
```

plus the ten explicit hypotheses

```lean
Nat.Coprime qᵢ qⱼ
```

for every `i < j`.

It proves

```lean
n * countMultiples5 q₁ q₂ q₃ q₄ q₅ m <
  2 * m * countMultiples5 q₁ q₂ q₃ q₄ q₅ n
```

Thus the checked theorem requires only `m > 0`; the originally frozen condition `m > n` is stronger than necessary for this restricted result.

`countMultiples5 ... x` encodes the positive integers `1, ..., x` by `e ∈ Finset.range x` and tests divisibility of `e + 1`, so it is exactly the counting function used in the natural-language statement.

## 3. Module structure

### `PC5488.Basic`

Defines the finite sets and counting function and proves the complete `q₁ = 2` branch.

Load-bearing results:

```lean
card_multiplesUpTo
countMultiples5_le
nested_div
half_plus_one_le_count_of_two
count_gt_half_of_two
target_of_two
four_reciprocal_lt_one
```

### `PC5488.Overlap`

Formalizes the arithmetic overlap estimate:

```lean
nat_div_cast_le_div
four_div_sum_le_sub_one
overlap_row_le
```

The central result corresponds to

\[
\sum_{j\ne i}\left\lfloor\frac{n}{q_iq_j}\right\rfloor
\le
\left\lfloor\frac n{q_i}\right\rfloor-1.
\]

### `PC5488.Aggregate`

Defines

```lean
M
D
```

and proves

```lean
two_D_add_five_le_M
```

corresponding to the subtraction-free natural-number inequality

\[
2D+5\le M.
\]

### `PC5488.Bonferroni`

Formalizes the five-set second-order Bonferroni step and coprime pair intersections. Its specialized result

```lean
M_le_count_add_D
```

is the natural-number form

\[
M\le F_A(n)+D.
\]

### `PC5488.Final`

Contains the density sandwich and final theorem.

Key results:

```lean
div_lt_natDiv_add_one
n_mul_S_lt_M_add_five
M_add_five_le_two_count
n_mul_S_lt_two_count
count_le_M
count_cast_le_mul_S
target_of_ge_three
pc5_488
```

The nontrivial branch implements

\[
M+5\le2F_A(n),
\qquad
nS<M+5,
\qquad
F_A(m)\le mS,
\]

and therefore

\[
nF_A(m)<2mF_A(n).
\]

The final theorem performs the outer split `q₁ = 2` versus `q₁ ≥ 3`.

## 4. Top-level build coverage

`PC5488.lean` imports the complete chain:

```lean
import PC5488.Basic
import PC5488.Overlap
import PC5488.Aggregate
import PC5488.Bonferroni
import PC5488.Final
```

Therefore `lake build` checks the final theorem rather than only intermediate lemmas.

## 5. Natural-language / formal alignment

The final theorem in `README.md` states:

- five strictly increasing generators, all at least `2`;
- pairwise coprimality;
- `n ≥` the largest generator;
- `m > 0`;
- conclusion `nF_A(m) < 2mF_A(n)`.

These are exactly the hypotheses and conclusion of `PC5488.pc5_488` after identifying

```text
a,b,c,d,e  ↔  q₁,q₂,q₃,q₄,q₅.
```

The proof structure also matches module-by-module:

| Natural-language proof | Formal module |
| --- | --- |
| `a = 2` density branch | `Basic` |
| reciprocal / row overlap estimate | `Basic`, `Overlap` |
| five-row double count | `Aggregate` |
| second-order Bonferroni | `Bonferroni` |
| final density sandwich and case split | `Final` |

No alternate unrecorded mathematical argument is used by the Lean proof.

## 6. Kernel-verification record

GitHub Actions workflow `PC5-488 Lean`, run **#22**, succeeded on proof commit:

```text
57e29558224e95854957380442c4b7e7fbb672de
```

The log explicitly reports:

```text
Built PC5488.Basic
Built PC5488.Overlap
Built PC5488.Aggregate
Built PC5488.Bonferroni
Built PC5488.Final
Built PC5488
Build completed successfully (8930 jobs).
```

The repository's existing `Build data`, `Validate`, and `Data consistency` workflows also succeeded on that proof commit.

Later documentation-only commits do not change the verified proof code.

## 7. Formalization debugging record

The main pre-green failures were implementation-level:

1. reversed products such as `qᵢ*qⱼ` and `qⱼ*qᵢ` needed explicit normalization before `omega`;
2. natural-number truncated subtraction required explicit lower bounds `n/qᵢ ≥ 1`;
3. Bonferroni helper sets needed explicit `Finset.card_union_le` chaining rather than relying on arithmetic normalization of differently written unions;
4. two final lemma calls required explicit `(n := n)` arguments.

No mathematical lemma was weakened, removed, or replaced in order to obtain the green build.

## 8. Proof-completion status

For the stated restricted theorem, the formalization task is complete:

- statement encoded;
- counting function matched to the natural-language definition;
- both proof branches formalized;
- all load-bearing lemmas compiled;
- final theorem compiled through the top-level library;
- dedicated CI passed.

Questions about the unrestricted problem or repository award/candidate status are outside the scope of this proof artifact.
