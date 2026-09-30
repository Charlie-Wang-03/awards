import JSP000404Research.CanonicalRankMiddleTerminal
import JSP000404Research.SupportThreeMiddleHiddenSeparatedPattern
import Mathlib.Tactic

/-!
# From middle-hidden signs to the canonical-rank terminal

For a six-point middle-hidden centre i, suppose the canonical ray signs have
the pattern

  top, c, d : one sign
  r, b      : the opposite sign.

The four vertices r,b,c,d are exactly all vertices other than top and i.

Since sign=true is the global canonical order i < v, there are only two
possibilities:

* sign(top)=true: exactly r,b lie below i, hence rank(i)=2 and i<top;
* sign(top)=false: exactly top,c,d lie below i, hence rank(i)=3 and top<i.

This is the missing order bridge between the middle-hidden certificate and
the purely rank-theoretic contradiction.
-/

namespace JSP000404Research

theorem raySign_false_iff_reverse_canonicalPointLt
    {V : Type*} {p : V → Plane}
    (hp : Function.Injective p)
    {i j : V}
    (hij : i ≠ j) :
    raySignAt hp i (⟨j, hij.symm⟩ : OtherVertex i) = false
      ↔
    CanonicalPointLt p j i := by
  rw [← raySign_true_iff_canonicalPointLt hp hij.symm]
  rw [raySignAt_reverse_eq_not hp hij]
  cases h :
      raySignAt hp i (⟨j, hij.symm⟩ : OtherVertex i) <;>
    simp

theorem middleHidden_rankSignature_of_sign_groups
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : V → Plane}
    (hp : Function.Injective p)
    {top i : V} {delta lam : ℝ}
    (M : MiddleHiddenSeparatedPatternAwayFromTop
      p top i delta lam)
    (hcard : Fintype.card V = 6)
    (hit : i ≠ top)
    (hRB :
      raySignAt hp i M.r =
        raySignAt hp i M.b)
    (hCD :
      raySignAt hp i M.c =
        raySignAt hp i M.d)
    (hTopC :
      raySignAt hp i
          (⟨top, hit.symm⟩ : OtherVertex i) =
        raySignAt hp i M.c)
    (hTopR :
      raySignAt hp i
          (⟨top, hit.symm⟩ : OtherVertex i) ≠
        raySignAt hp i M.r) :
    MiddleHiddenRankSignature p top i := by
  classical
  let topRay : OtherVertex i := ⟨top, hit.symm⟩
  by_cases hTopTrue :
      raySignAt hp i topRay = true
  · left
    have hiTop :
        CanonicalPointLt p i top := by
      exact
        (raySign_true_iff_canonicalPointLt hp hit).1
          (by simpa [topRay] using hTopTrue)

    have hrFalse :
        raySignAt hp i M.r = false := by
      have hne :
          raySignAt hp i topRay ≠ raySignAt hp i M.r := by
        simpa [topRay] using hTopR
      rw [hTopTrue] at hne
      cases hr : raySignAt hp i M.r <;> simp_all

    have hbFalse :
        raySignAt hp i M.b = false := by
      rw [← hRB]
      exact hrFalse

    have hcTrue :
        raySignAt hp i M.c = true := by
      rw [← hTopC]
      simpa [topRay] using hTopTrue

    have hdTrue :
        raySignAt hp i M.d = true := by
      rw [← hCD]
      exact hcTrue

    have hrBelow :
        CanonicalPointLt p M.r.1 i :=
      (raySign_false_iff_reverse_canonicalPointLt
        hp M.r.2.symm).1 hrFalse
    have hbBelow :
        CanonicalPointLt p M.b.1 i :=
      (raySign_false_iff_reverse_canonicalPointLt
        hp M.b.2.symm).1 hbFalse
    have hiC :
        CanonicalPointLt p i M.c.1 :=
      (raySign_true_iff_canonicalPointLt
        hp M.c.2.symm).1 hcTrue
    have hiD :
        CanonicalPointLt p i M.d.1 :=
      (raySign_true_iff_canonicalPointLt
        hp M.d.2.symm).1 hdTrue

    have hpred :
        (Finset.univ.filter
          (fun v => CanonicalPointLt p v i)) =
        {M.r.1, M.b.1} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hv
        have hvi : v ≠ i := by
          intro h
          subst v
          exact canonicalPointLt_irrefl (p := p) i hv
        have hvt : v ≠ top := by
          intro h
          subst v
          exact (canonicalPointLt_asymm hiTop) hv
        rcases M.covers_every_other_nonTop
            hcard hit hvt hvi with
          hvr | hvb | hvc | hvd
        · exact Or.inl hvr
        · exact Or.inr hvb
        · exfalso
          subst v
          exact (canonicalPointLt_asymm hiC) hv
        · exfalso
          subst v
          exact (canonicalPointLt_asymm hiD) hv
      · intro hv
        rcases hv with rfl | rfl
        · exact hrBelow
        · exact hbBelow

    constructor
    · exact hiTop
    · unfold canonicalRank
      rw [hpred]
      have hrb :
          M.r.1 ≠ M.b.1 := by
        intro h
        exact M.r_ne_b (Subtype.ext h)
      simp [hrb]

  · have hTopFalse :
        raySignAt hp i topRay = false := by
      cases h : raySignAt hp i topRay <;> simp_all

    right
    have hTopI :
        CanonicalPointLt p top i := by
      exact
        (raySign_false_iff_reverse_canonicalPointLt
          hp hit).1
          (by simpa [topRay] using hTopFalse)

    have hrTrue :
        raySignAt hp i M.r = true := by
      have hne :
          raySignAt hp i topRay ≠ raySignAt hp i M.r := by
        simpa [topRay] using hTopR
      rw [hTopFalse] at hne
      cases hr : raySignAt hp i M.r <;> simp_all

    have hbTrue :
        raySignAt hp i M.b = true := by
      rw [← hRB]
      exact hrTrue

    have hcFalse :
        raySignAt hp i M.c = false := by
      rw [← hTopC]
      simpa [topRay] using hTopFalse

    have hdFalse :
        raySignAt hp i M.d = false := by
      rw [← hCD]
      exact hcFalse

    have hiR :
        CanonicalPointLt p i M.r.1 :=
      (raySign_true_iff_canonicalPointLt
        hp M.r.2.symm).1 hrTrue
    have hiB :
        CanonicalPointLt p i M.b.1 :=
      (raySign_true_iff_canonicalPointLt
        hp M.b.2.symm).1 hbTrue
    have hcBelow :
        CanonicalPointLt p M.c.1 i :=
      (raySign_false_iff_reverse_canonicalPointLt
        hp M.c.2.symm).1 hcFalse
    have hdBelow :
        CanonicalPointLt p M.d.1 i :=
      (raySign_false_iff_reverse_canonicalPointLt
        hp M.d.2.symm).1 hdFalse

    have hpred :
        (Finset.univ.filter
          (fun v => CanonicalPointLt p v i)) =
        {top, M.c.1, M.d.1} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hv
        by_cases hvt : v = top
        · exact Or.inl hvt
        · have hvi : v ≠ i := by
            intro h
            subst v
            exact canonicalPointLt_irrefl (p := p) i hv
          rcases M.covers_every_other_nonTop
              hcard hit hvt hvi with
            hvr | hvb | hvc | hvd
          · exfalso
            subst v
            exact (canonicalPointLt_asymm hiR) hv
          · exfalso
            subst v
            exact (canonicalPointLt_asymm hiB) hv
          · exact Or.inr (Or.inl hvc)
          · exact Or.inr (Or.inr hvd)
      · intro hv
        rcases hv with rfl | hvc | hvd
        · exact hTopI
        · subst v
          exact hcBelow
        · subst v
          exact hdBelow

    constructor
    · exact hTopI
    · unfold canonicalRank
      rw [hpred]
      have htc : top ≠ M.c.1 := by
        intro h
        exact M.c_ne_top h.symm
      have htd : top ≠ M.d.1 := by
        intro h
        exact M.d_ne_top h.symm
      have hcd :
          M.c.1 ≠ M.d.1 := by
        intro h
        exact M.c_ne_d (Subtype.ext h)
      simp [htc, htd, hcd]

#print axioms raySign_false_iff_reverse_canonicalPointLt
#print axioms middleHidden_rankSignature_of_sign_groups

end JSP000404Research
