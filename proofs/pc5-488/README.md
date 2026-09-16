# PC5-488 formal proof

> Status: **proof-complete**. This directory contains a complete natural-language proof and a matching Lean formalization of the frozen five-generator pairwise-coprime subproblem. The final theorem is kernel-checked in the pinned Lean 4.34.0 / Mathlib v4.34.0 environment. This artifact makes no claim to solve JSP-000395 / Erdős #488 in full and does not change any candidate/award status.

## Scope

`PC5-488` is the internal label for the following restricted theorem associated with Erdős Problem #488 / JSP-000395.

Let

\[
A=\{a<b<c<d<e\}\subset \mathbb N_{\ge 2}
\]

consist of five pairwise coprime integers. For a positive integer \(x\), define

\[
F_A(x)=\#\{1\le t\le x:\exists q\in A,\ q\mid t\}.
\]

### Theorem

If \(n\ge e\), then for every positive integer \(m\),

\[
\boxed{nF_A(m)<2mF_A(n)}.
\]

In particular, the originally frozen target follows whenever \(m>n\ge e\).

The pairwise-coprime and five-generator assumptions are part of this restricted theorem; this document does not assert that they are without loss of generality for the full Erdős/JSP problem.

## Proof

We split according to whether the least generator is \(2\).

### Case 1: \(a=2\)

Because the generators are pairwise coprime, \(b,c,d,e\) are all odd. Since \(n\ge e\ge b\), the integer \(b\) lies in \([1,n]\), is divisible by \(b\), and is not divisible by \(2\). Therefore the union of multiples counted by \(F_A(n)\) contains all multiples of \(2\) in \([1,n]\) together with at least one additional integer. Hence

\[
F_A(n)
\ge
\left\lfloor\frac n2\right\rfloor+1
>
\frac n2.
\]

Thus

\[
\frac{2F_A(n)}n>1.
\tag{1}
\]

For every positive integer \(m\), trivially \(F_A(m)\le m\), so

\[
\frac{F_A(m)}m\le1<\frac{2F_A(n)}n.
\]

Multiplying by \(mn>0\) gives

\[
nF_A(m)<2mF_A(n).
\]

This closes the case \(a=2\).

### Case 2: \(a\ge3\)

Write

\[
A=\{q_1,q_2,q_3,q_4,q_5\},
\]

so every \(q_i\ge3\). Set

\[
k_i=\left\lfloor \frac n{q_i}\right\rfloor,
\qquad
M=\sum_{i=1}^5 k_i,
\qquad
S=\sum_{i=1}^5\frac1{q_i},
\]

and

\[
D=\sum_{1\le i<j\le5}
\left\lfloor\frac{n}{q_iq_j}\right\rfloor.
\]

Because the \(q_i\) are pairwise coprime,

\[
\operatorname{lcm}(q_i,q_j)=q_iq_j.
\]

Thus \(D\) is the sum of the cardinalities of all pairwise intersections among the five sets of multiples of the \(q_i\) in \([1,n]\).

#### Step 2.1: second-order Bonferroni

For \(1\le i\le5\), let

\[
E_i=\{1\le t\le n:q_i\mid t\}.
\]

Then

\[
|E_i|=k_i,
\qquad
|E_i\cap E_j|=
\left\lfloor\frac{n}{q_iq_j}\right\rfloor.
\]

The second Bonferroni inequality gives

\[
F_A(n)=\left|\bigcup_{i=1}^5E_i\right|
\ge
\sum_i|E_i|-\sum_{i<j}|E_i\cap E_j|
=M-D.
\tag{2}
\]

#### Step 2.2: bound the total pair-overlap term

Fix \(i\). Since

\[
k_i=\left\lfloor\frac n{q_i}\right\rfloor,
\]

natural-number division associativity gives, for every \(j\ne i\),

\[
\left\lfloor\frac{n}{q_iq_j}\right\rfloor
=
\left\lfloor\frac{k_i}{q_j}\right\rfloor.
\tag{3}
\]

The four integers \(q_j\) with \(j\ne i\) are distinct and at least \(3\). Arrange them increasingly as

\[
r_1<r_2<r_3<r_4.
\]

Then

\[
r_1\ge3,\qquad r_2\ge4,\qquad r_3\ge5,\qquad r_4\ge6,
\]

so

\[
\sum_{j\ne i}\frac1{q_j}
\le
\frac13+\frac14+\frac15+\frac16
=
\frac{19}{20}<1.
\tag{4}
\]

Using (3) and \(\lfloor y\rfloor\le y\),

\[
\sum_{j\ne i}
\left\lfloor\frac{n}{q_iq_j}\right\rfloor
=
\sum_{j\ne i}
\left\lfloor\frac{k_i}{q_j}\right\rfloor
\le
k_i\sum_{j\ne i}\frac1{q_j}
<k_i.
\]

The left side is an integer. Also \(k_i\ge1\) because \(n\ge e\ge q_i\). Therefore

\[
\sum_{j\ne i}
\left\lfloor\frac{n}{q_iq_j}\right\rfloor
\le k_i-1.
\tag{5}
\]

Summing (5) over \(i=1,\dots,5\), every unordered pair \(\{i,j\}\) is counted twice. Hence

\[
2D\le\sum_{i=1}^5(k_i-1)=M-5.
\tag{6}
\]

Combining (2) and (6),

\[
2F_A(n)
\ge2M-2D
\ge M+5.
\tag{7}
\]

#### Step 2.3: the density sandwich

For every \(i\),

\[
\frac n{q_i}
<
\left\lfloor\frac n{q_i}\right\rfloor+1
=k_i+1.
\]

Summing gives

\[
nS
=
\sum_{i=1}^5\frac n{q_i}
<
\sum_{i=1}^5(k_i+1)
=M+5.
\tag{8}
\]

Together with (7),

\[
S<\frac{2F_A(n)}n.
\tag{9}
\]

For every positive integer \(m\), the union bound gives

\[
F_A(m)
\le
\sum_{i=1}^5\left\lfloor\frac m{q_i}\right\rfloor
\le
m\sum_{i=1}^5\frac1{q_i}
=mS.
\tag{10}
\]

Therefore

\[
\frac{F_A(m)}m
\le S
<\frac{2F_A(n)}n.
\]

Since \(m,n>0\), multiplying by \(mn\) yields

\[
\boxed{nF_A(m)<2mF_A(n)}.
\]

This closes the case \(a\ge3\) and proves the theorem. \(\square\)

## Natural-language / Lean correspondence

The Lean formalization follows the proof above rather than a different argument.

| Natural-language step | Lean module / theorem |
| --- | --- |
| Counting positive multiples and the \(a=2\) branch | `PC5488.Basic`; `target_of_two` |
| Nested division and the four-reciprocal estimate | `PC5488.Basic`; `nested_div`, `four_reciprocal_lt_one` |
| Per-generator overlap estimate | `PC5488.Overlap`; `overlap_row_le` |
| Double counting to \(2D+5\le M\) | `PC5488.Aggregate`; `two_D_add_five_le_M` |
| Five-set Bonferroni and coprime pair intersections | `PC5488.Bonferroni`; `M_le_count_add_D` |
| \(M+5\le2F_A(n)\), \(nS<M+5\), union bound, final sandwich | `PC5488.Final`; `target_of_ge_three` |
| Outer split \(q_1=2\) / \(q_1\ge3\) | `PC5488.Final`; `pc5_488` |

## Formal theorem alignment

The final Lean theorem `PC5488.pc5_488` assumes exactly:

- `0 < m`;
- `2 ≤ q₁`;
- `q₁ < q₂ < q₃ < q₄ < q₅`;
- `q₅ ≤ n`;
- all ten pairwise coprimality hypotheses.

It concludes

```lean
n * countMultiples5 q₁ q₂ q₃ q₄ q₅ m <
  2 * m * countMultiples5 q₁ q₂ q₃ q₄ q₅ n
```

where `countMultiples5 ... x` is exactly the cardinality of the positive integers `1, ..., x` divisible by at least one of the five generators. Thus the natural-language theorem and the formal theorem have matching hypotheses and conclusion.

## Kernel-verification record

The isolated proof project is in `proofs/pc5-488/lean/` and pins:

- Lean `v4.34.0`;
- Mathlib `v4.34.0`.

GitHub Actions workflow `PC5-488 Lean`, run **#22**, succeeded on proof commit

```text
57e29558224e95854957380442c4b7e7fbb672de
```

and explicitly built:

```text
PC5488.Basic
PC5488.Overlap
PC5488.Aggregate
PC5488.Bonferroni
PC5488.Final
PC5488
```

ending with

```text
Build completed successfully (8930 jobs).
```

The final theorem is therefore kernel-checked in the pinned environment.

## Completion boundary

This artifact is complete for its stated purpose:

1. the restricted theorem is stated precisely;
2. a complete natural-language proof is recorded;
3. the Lean theorem matches that statement;
4. the complete Lean module chain is kernel-checked;
5. no step of the final proof depends on the earlier PT1/PT2/PT3 margin route.

Questions about the unrestricted problem or repository award/candidate status are outside the scope of this proof artifact.
