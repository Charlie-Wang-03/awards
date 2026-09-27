import JSP000404Research.WeightedHanselEquality
import Mathlib.Tactic

/-!
# Coordinate slices of an exact weighted-Hansel tiling

When the completed partial cubes tile the whole Boolean cube bijectively, fix
one coordinate c and intersect every cube with the half-cube

  word c = false.

For a vertex v:

* if c is specified at v, the whole local cube lies in one half, so the
  intersection has either full size or zero size;
* if c is free at v, exactly half of the local completions lie in each half.

This module packages the exact finite-cardinality statement.  It is the
parity interface used by the six-point two-exception equality terminal.
-/

namespace JSP000404Research

open scoped BigOperators

def FalseCompletionAt
    {V : Type*} {k : ℕ}
    (bit : V → Fin k → Bool)
    (specified : V → Finset (Fin k))
    (c : Fin k) (v : V) :=
  {f : FreeCoordinates (specified v) //
    completeWord bit specified v f c = false}

def FalseWordAt (k : ℕ) (c : Fin k) :=
  {w : Fin k → Bool // w c = false}

/-- If c is free in S, fixing that free Boolean value to false is equivalent
to deleting c from the free-coordinate domain, i.e. inserting c into S. -/
noncomputable def falseFreeEquivInserted
    {k : ℕ}
    (S : Finset (Fin k))
    (c : Fin k)
    (hc : c ∉ S) :
    {f : FreeCoordinates S // f ⟨c, hc⟩ = false}
      ≃
    FreeCoordinates (insert c S) where
  toFun f := fun i =>
    f.1 ⟨i.1, by
      intro hiS
      exact i.2 (Finset.mem_insert_of_mem hiS)⟩
  invFun g :=
    ⟨fun i =>
      if h : i.1 = c then false
      else
        g ⟨i.1, by
          simp only [Finset.mem_insert]
          push_neg
          exact ⟨h, i.2⟩⟩,
      by simp⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    by_cases h : i.1 = c
    · subst c
      simpa using f.2
    · simp [h]
  right_inv g := by
    funext i
    have hic : i.1 ≠ c := by
      intro h
      subst c
      exact i.2 (by simp)
    simp [hic]

theorem card_false_free
    {k : ℕ}
    (S : Finset (Fin k))
    (c : Fin k)
    (hc : c ∉ S) :
    Fintype.card
      {f : FreeCoordinates S // f ⟨c, hc⟩ = false}
      =
    2 ^ (k - (insert c S).card) := by
  classical
  rw [Fintype.card_congr
    (falseFreeEquivInserted S c hc)]
  exact card_freeCoordinates (insert c S)

/-- Exact local half-slice cardinality. -/
theorem card_falseCompletionAt
    {V : Type*} {k : ℕ}
    (bit : V → Fin k → Bool)
    (specified : V → Finset (Fin k))
    (c : Fin k) (v : V) :
    Fintype.card (FalseCompletionAt bit specified c v)
      =
    if hc : c ∈ specified v then
      if bit v c = false then
        2 ^ (k - (specified v).card)
      else 0
    else
      2 ^ (k - (insert c (specified v)).card) := by
  classical
  by_cases hc : c ∈ specified v
  · rw [dif_pos hc]
    by_cases hb : bit v c = false
    · rw [if_pos hb]
      have hpred :
          ∀ f : FreeCoordinates (specified v),
            completeWord bit specified v f c = false := by
        intro f
        simp [completeWord, hc, hb]
      let e :
          FalseCompletionAt bit specified c v
            ≃ FreeCoordinates (specified v) :=
        {
          toFun := fun f => f.1
          invFun := fun f => ⟨f, hpred f⟩
          left_inv := by intro f; rfl
          right_inv := by intro f; rfl
        }
      rw [Fintype.card_congr e]
      exact card_freeCoordinates (specified v)
    · rw [if_neg hb]
      have hempty :
          IsEmpty (FalseCompletionAt bit specified c v) := by
        refine ⟨fun f => ?_⟩
        have hf := f.2
        simp [completeWord, hc] at hf
        exact hb hf
      letI := hempty
      simp
  · rw [dif_neg hc]
    let cfree : {i : Fin k // i ∉ specified v} := ⟨c, hc⟩
    let e :
        FalseCompletionAt bit specified c v
          ≃
        {f : FreeCoordinates (specified v) //
          f cfree = false} :=
      {
        toFun := fun f => ⟨f.1, by
          have hf := f.2
          simpa [completeWord, hc, cfree] using hf⟩
        invFun := fun f => ⟨f.1, by
          simpa [completeWord, hc, cfree] using f.2⟩
        left_inv := by intro f; rfl
        right_inv := by intro f; rfl
      }
    rw [Fintype.card_congr e]
    simpa [cfree] using
      card_false_free (specified v) c hc

/-- False words are exactly free assignments off the single fixed coordinate. -/
noncomputable def falseWordEquivFreeSingleton
    {k : ℕ}
    (c : Fin k) :
    FalseWordAt k c ≃ FreeCoordinates ({c} : Finset (Fin k)) where
  toFun w := fun i => w.1 i.1
  invFun f :=
    ⟨fun i =>
      if h : i = c then false
      else f ⟨i, by simp [h]⟩,
      by simp⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    by_cases h : i = c
    · subst i
      simpa using w.2
    · simp [h]
  right_inv f := by
    funext i
    have hic : i.1 ≠ c := by
      intro h
      subst c
      exact i.2 (by simp)
    simp [hic]

theorem card_falseWordAt
    {k : ℕ}
    (c : Fin k) :
    Fintype.card (FalseWordAt k c) = 2 ^ (k - 1) := by
  classical
  rw [Fintype.card_congr
    (falseWordEquivFreeSingleton c)]
  simpa using
    card_freeCoordinates ({c} : Finset (Fin k))

def falseCompletionSigmaMap
    {V : Type*} {k : ℕ}
    (bit : V → Fin k → Bool)
    (specified : V → Finset (Fin k))
    (c : Fin k) :
    (Σ v, FalseCompletionAt bit specified c v) →
      FalseWordAt k c :=
  fun x =>
    ⟨completeWord bit specified x.1 x.2.1, x.2.2⟩

theorem falseCompletionSigmaMap_bijective
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool)
    (specified : V → Finset (Fin k))
    (c : Fin k)
    (hbij :
      Function.Bijective
        (fun x : Σ v, FreeCoordinates (specified v) =>
          completeWord bit specified x.1 x.2)) :
    Function.Bijective
      (falseCompletionSigmaMap bit specified c) := by
  constructor
  · intro x y hxy
    have hword :
        completeWord bit specified x.1 x.2.1 =
          completeWord bit specified y.1 y.2.1 := by
      exact congrArg Subtype.val hxy
    have hbase :
        (⟨x.1, x.2.1⟩ :
          Σ v, FreeCoordinates (specified v))
          =
        ⟨y.1, y.2.1⟩ :=
      hbij.1 hword
    cases x with
    | mk vx fx =>
      cases y with
      | mk vy fy =>
        cases hbase
        rfl
  · intro w
    obtain ⟨x, hx⟩ := hbij.2 w.1
    cases x with
    | mk v f =>
      have hfc :
          completeWord bit specified v f c = false := by
        have hc := congrFun hx c
        rw [w.2] at hc
        exact hc
      refine ⟨⟨v, ⟨f, hfc⟩⟩, ?_⟩
      apply Subtype.ext
      exact hx

/-- Exact half-slice count obtained by summing the local intersections. -/
theorem false_slice_card_sum_eq
    {V : Type*} [Fintype V] {k : ℕ}
    (bit : V → Fin k → Bool)
    (specified : V → Finset (Fin k))
    (c : Fin k)
    (hbij :
      Function.Bijective
        (fun x : Σ v, FreeCoordinates (specified v) =>
          completeWord bit specified x.1 x.2)) :
    (∑ v : V,
      Fintype.card (FalseCompletionAt bit specified c v))
      =
    2 ^ (k - 1) := by
  classical
  have hcard :
      Fintype.card
          (Σ v, FalseCompletionAt bit specified c v)
        =
      Fintype.card (FalseWordAt k c) := by
    exact Fintype.card_congr
      (Equiv.ofBijective
        (falseCompletionSigmaMap bit specified c)
        (falseCompletionSigmaMap_bijective
          bit specified c hbij))
  rw [Fintype.card_sigma, card_falseWordAt] at hcard
  exact hcard

#print axioms card_falseCompletionAt
#print axioms card_falseWordAt
#print axioms falseCompletionSigmaMap_bijective
#print axioms false_slice_card_sum_eq

end JSP000404Research
