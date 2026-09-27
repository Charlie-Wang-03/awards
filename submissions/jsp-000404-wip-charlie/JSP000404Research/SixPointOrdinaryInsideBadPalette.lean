import JSP000404Research.SixPointMergedTwoBadActiveSet
import JSP000404Research.WeightedHanselSlice
import JSP000404Research.SixPointMergedEqualityRoot
import Mathlib.Tactic

/-!
# An ordinary minimum supported inside the common bad palette

In the exact two-bad Hansel equality profile, remove the unique top root
coordinate.  The two bad minima have the same three remaining active colours.

This file proves a further equality rigidity statement: among the three
ordinary minima, at least one has both of its remaining active colours inside
that common three-colour set.

The key slice fact is local.  If a colour c is outside the bad active palette
but is used by one ordinary minimum, then exact half-cube counting at c forces
exactly two of the three ordinary minima to use c.  This turns outside colours
into pairs.  If all three ordinary minima had an outside colour, one such pair
would use up one of the two non-root coordinates at each endpoint; each
endpoint must also use a common bad colour in order to connect to a bad
minimum.  The third ordinary minimum then has another outside colour which
would need a second partner, impossible.

This is the combinatorial bridge needed to convert the two-bad equality
terminal into cross-centre band geometry.
-/

namespace JSP000404Research

open scoped BigOperators
open BinaryEdgePartition

theorem finset_sum_split_predicate
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p]
    (f : α → ℕ) :
    (∑ x ∈ s, f x) =
      (∑ x ∈ s.filter p, f x) +
      (∑ x ∈ s.filter (fun x => ¬ p x), f x) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      by_cases hpa : p a
      · simp [ha, hpa, ih, add_assoc, add_left_comm, add_comm]
      · simp [ha, hpa, ih, add_assoc, add_left_comm, add_comm]

theorem finset_card_split_predicate
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card +
      (s.filter (fun x => ¬ p x)).card =
    s.card := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      by_cases hpa : p a
      · simp [ha, hpa, ih]
      · simp [ha, hpa, ih]

/-- At exact two-exception equality, an outside-bad colour that appears at an
ordinary minimum appears at exactly two ordinary minima. -/
theorem outside_bad_colour_used_by_exactly_two_ordinary
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (hn5 : 5 ≤ n)
    (P : BinaryEdgePartition V n)
    (top bad₁ bad₂ v : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hTop : (active P top).card ≤ 1)
    (hBad₁ : (active P bad₁).card ≤ 4)
    (hBad₂ : (active P bad₂).card ≤ 4)
    (hOther :
      ∀ w : V,
        w ≠ top → w ≠ bad₁ → w ≠ bad₂ →
        (active P w).card ≤ 3)
    (hvt : v ≠ top)
    (hvb₁ : v ≠ bad₁)
    (hvb₂ : v ≠ bad₂)
    (c : Fin n)
    (hcBad : c ∉ active P bad₁)
    (hcV : c ∈ active P v) :
    let O : Finset V :=
      ((Finset.univ.erase top).erase bad₁).erase bad₂
    (O.filter (fun w => c ∈ active P w)).card = 2 := by
  classical
  let O : Finset V :=
    ((Finset.univ.erase top).erase bad₁).erase bad₂

  have hexact :=
    six_point_two_min_exceptions_active_exact
      (by omega : 4 ≤ n) P top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther
  have hbadEq :=
    six_point_two_min_exceptions_active_eq
      hn5 P top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther

  obtain ⟨root, hrootTop, hrootAll, _hrootEdges,
      _hrootBad₁, _hrootBad₂, _hrootOther⟩ :=
    six_point_two_exception_root_factorization
      (by omega : 4 ≤ n) P top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther

  have hcBad₂ : c ∉ active P bad₂ := by
    rw [← hbadEq]
    exact hcBad
  have hcRoot : c ≠ root := by
    intro h
    subst c
    exact hcBad ((hrootAll bad₁ htb₁).1)
  have hcTop : c ∉ active P top := by
    rw [hrootTop]
    simp [hcRoot]

  have hOcard : O.card = 3 := by
    dsimp [O]
    have hb₁Mem :
        bad₁ ∈ (Finset.univ.erase top : Finset V) := by
      simp [htb₁]
    have hb₂Mem :
        bad₂ ∈ ((Finset.univ.erase top).erase bad₁ : Finset V) := by
      simp [htb₂, hb₁₂]
    rw [Finset.card_erase_of_mem hb₂Mem,
        Finset.card_erase_of_mem hb₁Mem,
        Finset.card_erase_of_mem (Finset.mem_univ top)]
    simp [hcard]

  have hvO : v ∈ O := by
    dsimp [O]
    simp [hvt, hvb₁, hvb₂]

  have hbij :=
    six_point_two_min_exceptions_completeWord_bijective
      (by omega : 4 ≤ n) P top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther

  let F : V → ℕ :=
    fun w =>
      Fintype.card
        (FalseCompletionAt P.bit (active P) c w)
  let B : ℕ := 2 ^ (n - 5)

  have hBpos : 0 < B := by
    dsimp [B]
    positivity

  have hpow4 :
      2 ^ (n - 4) = 2 * B := by
    have he : n - 4 = (n - 5) + 1 := by omega
    rw [he, pow_add]
    simp [B, Nat.mul_comm]
  have hpow3 :
      2 ^ (n - 3) = 4 * B := by
    have he : n - 3 = (n - 5) + 2 := by omega
    rw [he, pow_add]
    norm_num
    ring
  have hpow2 :
      2 ^ (n - 2) = 8 * B := by
    have he : n - 2 = (n - 5) + 3 := by omega
    rw [he, pow_add]
    norm_num
    ring
  have hpow1 :
      2 ^ (n - 1) = 16 * B := by
    have he : n - 1 = (n - 5) + 4 := by omega
    rw [he, pow_add]
    norm_num
    ring

  have hFtop : F top = 8 * B := by
    dsimp [F]
    rw [card_falseCompletionAt,
      dif_neg hcTop,
      Finset.card_insert_of_not_mem hcTop,
      hexact.1,
      hpow2]

  have hFb1 : F bad₁ = B := by
    dsimp [F]
    rw [card_falseCompletionAt,
      dif_neg hcBad,
      Finset.card_insert_of_not_mem hcBad,
      hexact.2.1]
    have he : n - (4 + 1) = n - 5 := by omega
    rw [he]

  have hFb2 : F bad₂ = B := by
    dsimp [F]
    rw [card_falseCompletionAt,
      dif_neg hcBad₂,
      Finset.card_insert_of_not_mem hcBad₂,
      hexact.2.2.1]
    have he : n - (4 + 1) = n - 5 := by omega
    rw [he]

  have hOrdCard :
      ∀ w ∈ O, (active P w).card = 3 := by
    intro w hw
    have hw' : w ≠ top ∧ w ≠ bad₁ ∧ w ≠ bad₂ := by
      dsimp [O] at hw
      simp at hw
      exact ⟨hw.2.2, hw.2.1, hw.1⟩
    exact hexact.2.2.2 w hw'.1 hw'.2.1 hw'.2.2

  let A := O.filter (fun w => c ∈ active P w)
  let U := O.filter (fun w => c ∉ active P w)

  have hAplusU : A.card + U.card = 3 := by
    have h :=
      finset_card_split_predicate O
        (fun w => c ∈ active P w)
    dsimp [A, U]
    rw [hOcard] at h
    simpa using h

  have hvA : v ∈ A := by
    dsimp [A]
    simp [hvO, hcV]
  have hApos : 1 ≤ A.card :=
    Finset.card_pos.mpr ⟨v, hvA⟩
  have hUle : U.card ≤ 2 := by omega

  have hFfree :
      ∀ w ∈ U, F w = 2 * B := by
    intro w hw
    have hwO : w ∈ O := (Finset.mem_filter.mp hw).1
    have hcw : c ∉ active P w := (Finset.mem_filter.mp hw).2
    have hwCard := hOrdCard w hwO
    dsimp [F]
    rw [card_falseCompletionAt,
      dif_neg hcw,
      Finset.card_insert_of_not_mem hcw,
      hwCard, hpow4]

  have hFactive :
      ∀ w ∈ A, ∃ q : ℕ, F w = (4 * B) * q := by
    intro w hw
    have hwO : w ∈ O := (Finset.mem_filter.mp hw).1
    have hcw : c ∈ active P w := (Finset.mem_filter.mp hw).2
    have hwCard := hOrdCard w hwO
    dsimp [F]
    rw [card_falseCompletionAt, dif_pos hcw]
    by_cases hb : P.bit w c = false
    · rw [if_pos hb, hwCard, hpow3]
      exact ⟨1, by ring⟩
    · rw [if_neg hb]
      exact ⟨0, by simp⟩

  let q : V → ℕ :=
    fun w =>
      if h : w ∈ A then
        Classical.choose (hFactive w h)
      else 0
  let Q : ℕ := ∑ w ∈ A, q w

  have hFA :
      (∑ w ∈ A, F w) = (4 * B) * Q := by
    calc
      (∑ w ∈ A, F w)
          =
        ∑ w ∈ A, (4 * B) * q w := by
          apply Finset.sum_congr rfl
          intro w hw
          dsimp [q]
          rw [dif_pos hw]
          exact Classical.choose_spec (hFactive w hw)
      _ = (4 * B) * (∑ w ∈ A, q w) := by
          rw [Finset.mul_sum]
      _ = (4 * B) * Q := rfl

  have hFU :
      (∑ w ∈ U, F w) = (2 * B) * U.card := by
    calc
      (∑ w ∈ U, F w)
          = ∑ _w ∈ U, 2 * B := by
              apply Finset.sum_congr rfl
              intro w hw
              exact hFfree w hw
      _ = U.card * (2 * B) := by simp
      _ = (2 * B) * U.card := by omega

  have hFO :
      (∑ w ∈ O, F w) =
        (4 * B) * Q + (2 * B) * U.card := by
    rw [finset_sum_split_predicate O
      (fun w => c ∈ active P w) F]
    simpa [A, U, hFA, hFU] using congrArg id (show
      (∑ w ∈ A, F w) + (∑ w ∈ U, F w) =
        (4 * B) * Q + (2 * B) * U.card by
          rw [hFA, hFU])

  have hslice :=
    false_slice_card_sum_eq
      P.bit (active P) c hbij

  have hsumDecomp :
      (∑ w : V, F w) =
        F top + F bad₁ + F bad₂ +
          ∑ w ∈ O, F w := by
    dsimp [O]
    rw [← Finset.sum_erase_add F (Finset.mem_univ top)]
    have hb1mem :
        bad₁ ∈ (Finset.univ.erase top : Finset V) := by
      simp [htb₁]
    rw [← Finset.sum_erase_add F hb1mem]
    have hb2mem :
        bad₂ ∈ ((Finset.univ.erase top).erase bad₁ : Finset V) := by
      simp [htb₂, hb₁₂]
    rw [← Finset.sum_erase_add F hb2mem]
    omega

  have hmain :
      8 * B + B + B +
          ((4 * B) * Q + (2 * B) * U.card)
        =
      16 * B := by
    rw [← hFtop, ← hFb1, ← hFb2,
        ← hFO, ← hsumDecomp,
        hslice, hpow1]

  have hfactor :
      (10 + 4 * Q + 2 * U.card) * B =
        16 * B := by
    calc
      (10 + 4 * Q + 2 * U.card) * B
          =
        8 * B + B + B +
          ((4 * B) * Q + (2 * B) * U.card) := by ring
      _ = 16 * B := hmain

  have hcoef :
      10 + 4 * Q + 2 * U.card = 16 :=
    Nat.eq_of_mul_eq_mul_right hBpos hfactor

  have hUcard : U.card = 1 := by
    omega
  omega

/-- In exact two-bad equality, at least one ordinary minimum has all of its
two non-root colours inside the common reduced bad palette. -/
theorem exists_ordinary_reduced_active_subset_bad
    {V : Type*} [LinearOrder V] [Fintype V]
    {n : ℕ}
    (hn5 : 5 ≤ n)
    (P : BinaryEdgePartition V n)
    (top bad₁ bad₂ : V)
    (htb₁ : top ≠ bad₁)
    (htb₂ : top ≠ bad₂)
    (hb₁₂ : bad₁ ≠ bad₂)
    (hcard : Fintype.card V = 6)
    (hTop : (active P top).card ≤ 1)
    (hBad₁ : (active P bad₁).card ≤ 4)
    (hBad₂ : (active P bad₂).card ≤ 4)
    (hOther :
      ∀ w : V,
        w ≠ top → w ≠ bad₁ → w ≠ bad₂ →
        (active P w).card ≤ 3) :
    ∃ root : Fin n, ∃ v : V,
      v ≠ top ∧ v ≠ bad₁ ∧ v ≠ bad₂ ∧
      ((active P v).erase root) ⊆
        ((active P bad₁).erase root) := by
  classical
  obtain ⟨root, hrootTop, hrootAll, _hrootEdges,
      hrootBad₁, hrootBad₂, hrootOther⟩ :=
    six_point_two_exception_root_factorization
      (by omega : 4 ≤ n) P top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther

  have hbadEq :=
    six_point_two_min_exceptions_active_eq
      hn5 P top bad₁ bad₂
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther

  let S := (active P bad₁).erase root
  let O : Finset V :=
    ((Finset.univ.erase top).erase bad₁).erase bad₂

  have hOcard : O.card = 3 := by
    dsimp [O]
    have hb₁Mem :
        bad₁ ∈ (Finset.univ.erase top : Finset V) := by
      simp [htb₁]
    have hb₂Mem :
        bad₂ ∈ ((Finset.univ.erase top).erase bad₁ : Finset V) := by
      simp [htb₂, hb₁₂]
    rw [Finset.card_erase_of_mem hb₂Mem,
        Finset.card_erase_of_mem hb₁Mem,
        Finset.card_erase_of_mem (Finset.mem_univ top)]
    simp [hcard]

  by_contra hnone
  push_neg at hnone
  have hout :
      ∀ v ∈ O,
        ∃ c : Fin n,
          c ∈ (active P v).erase root ∧ c ∉ S := by
    intro v hv
    have hvne : v ≠ top ∧ v ≠ bad₁ ∧ v ≠ bad₂ := by
      dsimp [O] at hv
      simp at hv
      exact ⟨hv.2.2, hv.2.1, hv.1⟩
    have hnsub :
        ¬ ((active P v).erase root ⊆ S) := by
      intro hsub
      exact hnone root v hvne.1 hvne.2.1 hvne.2.2 hsub
    simpa [Finset.not_subset] using hnsub

  obtain ⟨v, hvO⟩ : ∃ v, v ∈ O := by
    have : O.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      rw [h] at hOcard
      simp at hOcard
    exact this

  obtain ⟨c, hcVErase, hcOut⟩ := hout v hvO
  have hcV : c ∈ active P v :=
    Finset.mem_of_mem_erase hcVErase
  have hcBad : c ∉ active P bad₁ := by
    intro hc
    have hcRoot : c ≠ root :=
      (Finset.mem_erase.mp hcVErase).1
    exact hcOut (Finset.mem_erase.mpr ⟨hcRoot, hc⟩)

  have hvne : v ≠ top ∧ v ≠ bad₁ ∧ v ≠ bad₂ := by
    dsimp [O] at hvO
    simp at hvO
    exact ⟨hvO.2.2, hvO.2.1, hvO.1⟩

  have hused2 :=
    outside_bad_colour_used_by_exactly_two_ordinary
      hn5 P top bad₁ bad₂ v
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther
      hvne.1 hvne.2.1 hvne.2.2
      c hcBad hcV

  let A := O.filter (fun w => c ∈ active P w)
  have hvA : v ∈ A := by
    dsimp [A]
    simp [hvO, hcV]
  have hAcard : A.card = 2 := by
    simpa [A, O] using hused2
  obtain ⟨w, hwA, hwne⟩ :
      ∃ w ∈ A, w ≠ v := by
    have htwo : 1 < A.card := by rw [hAcard]
    have hex :=
      Finset.exists_ne_of_one_lt_card htwo v
    obtain ⟨w, hw, hwv⟩ := hex
    exact ⟨w, hw, hwv⟩

  have hwO : w ∈ O := (Finset.mem_filter.mp hwA).1
  have hcW : c ∈ active P w := (Finset.mem_filter.mp hwA).2
  have hwne3 : w ≠ top ∧ w ≠ bad₁ ∧ w ≠ bad₂ := by
    dsimp [O] at hwO
    simp at hwO
    exact ⟨hwO.2.2, hwO.2.1, hwO.1⟩

  -- The third ordinary minimum exists uniquely outside the two-element A.
  obtain ⟨u, huO, huA⟩ :
      ∃ u ∈ O, u ∉ A := by
    have hlt : A.card < O.card := by
      rw [hAcard, hOcard]
    obtain ⟨u, huO, huA⟩ :=
      Finset.exists_mem_not_mem_of_card_lt_card hlt
    exact ⟨u, huO, huA⟩

  have huNe : u ≠ top ∧ u ≠ bad₁ ∧ u ≠ bad₂ := by
    dsimp [O] at huO
    simp at huO
    exact ⟨huO.2.2, huO.2.1, huO.1⟩
  have hcU : c ∉ active P u := by
    intro hcu
    exact huA (by simp [A, huO, hcu])

  obtain ⟨d, hdUErase, hdOut⟩ := hout u huO
  have hdU : d ∈ active P u :=
    Finset.mem_of_mem_erase hdUErase
  have hdBad : d ∉ active P bad₁ := by
    intro hd
    have hdRoot : d ≠ root :=
      (Finset.mem_erase.mp hdUErase).1
    exact hdOut (Finset.mem_erase.mpr ⟨hdRoot, hd⟩)

  have hduse2 :=
    outside_bad_colour_used_by_exactly_two_ordinary
      hn5 P top bad₁ bad₂ u
      htb₁ htb₂ hb₁₂ hcard
      hTop hBad₁ hBad₂ hOther
      huNe.1 huNe.2.1 huNe.2.2
      d hdBad hdU

  let D := O.filter (fun x => d ∈ active P x)
  have hDcard : D.card = 2 := by
    simpa [D, O] using hduse2
  have huD : u ∈ D := by
    simp [D, huO, hdU]

  -- At least one of v,w also uses d.
  have hotherD :
      v ∈ D ∨ w ∈ D := by
    by_contra hnoneVW
    push_neg at hnoneVW
    have hsubset : D ⊆ {u} := by
      intro x hxD
      have hxO := (Finset.mem_filter.mp hxD).1
      have hxCases : x = v ∨ x = w ∨ x = u := by
        have hOeq : O = {v,w,u} := by
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            by_contra hxCases
            have hxv : x ≠ v := by tauto
            have hxw : x ≠ w := by tauto
            have hxu : x ≠ u := by tauto
            have hfour :
                4 ≤ O.card := by
              have hset :
                  {v,w,u,x} ⊆ O := by
                intro y hy
                simp only [Finset.mem_insert, Finset.mem_singleton] at hy
                rcases hy with rfl | rfl | rfl | rfl
                · exact hvO
                · exact hwO
                · exact huO
                · exact hxO
              have hcard4 :
                  ({v,w,u,x} : Finset V).card = 4 := by
                simp [hwne, hxv, hxw, hxu,
                  show u ≠ v by
                    intro h; subst u; exact huA hvA,
                  show u ≠ w by
                    intro h; subst u; exact huA hwA]
              rw [← hcard4]
              exact Finset.card_le_card hset
            omega
          · simp [hOcard]
        rw [hOeq] at hxO
        simpa using hxO
      rcases hxCases with rfl | rfl | rfl
      · exact False.elim (hnoneVW.1 hxD)
      · exact False.elim (hnoneVW.2 hxD)
      · simp
    have hcardLe : D.card ≤ 1 := by
      calc
        D.card ≤ ({u} : Finset V).card :=
          Finset.card_le_card hsubset
        _ = 1 := by simp
    rw [hDcard] at hcardLe
    omega

  rcases hotherD with hvD | hwD
  · have hdV : d ∈ active P v :=
      (Finset.mem_filter.mp hvD).2
    -- v has reduced active cardinality two and already uses outside c;
    -- because it must also meet the bad palette to colour edge v--bad₁,
    -- there is no room for a second outside colour d.
    have hcvRoot : c ≠ root :=
      (Finset.mem_erase.mp hcVErase).1
    have hdRoot : d ≠ root :=
      (Finset.mem_erase.mp hdUErase).1
    have hcd : c ≠ d := by
      intro h
      subst d
      exact hcU hdU
    have hredCard :
        ((active P v).erase root).card = 2 :=
      hrootOther v hvne.1 hvne.2.1 hvne.2.2
    have hcRed :
        c ∈ (active P v).erase root :=
      Finset.mem_erase.mpr ⟨hcvRoot, hcV⟩
    have hdRed :
        d ∈ (active P v).erase root :=
      Finset.mem_erase.mpr ⟨hdRoot, hdV⟩
    have hsubsetCD :
        (active P v).erase root = {c,d} := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        have htwo :
            ({c,d} : Finset (Fin n)).card = 2 := by
          simp [hcd]
        by_contra hxCD
        have h3 :
            3 ≤ ((active P v).erase root).card := by
          have hs :
              ({c,d,x} : Finset (Fin n)) ⊆
                (active P v).erase root := by
            intro y hy
            simp only [Finset.mem_insert, Finset.mem_singleton] at hy
            rcases hy with rfl | rfl | rfl
            · exact hcRed
            · exact hdRed
            · exact hx
          have hc3 :
              ({c,d,x} : Finset (Fin n)).card = 3 := by
            simp [hcd]
            push_neg at hxCD
            tauto
          rw [← hc3]
          exact Finset.card_le_card hs
        rw [hredCard] at h3
        omega
      · simp [hredCard]
    -- But edge v--bad₁ needs a non-root colour in both active sets.
    rcases lt_or_gt_of_ne hvne.2.1 with hvb | hbv
    · let e := P.edgeColor v bad₁
      have heV := edgeColor_mem_active_lower P hvb
      have heB := edgeColor_mem_active_upper P hvb
      have heRoot :
          e ≠ root :=
        nonTop_edgeColor_ne_root P hrootAll
          hvb hvne.1 htb₁.symm
      have heRed :
          e ∈ (active P v).erase root :=
        Finset.mem_erase.mpr ⟨heRoot, heV⟩
      rw [hsubsetCD] at heRed
      simp only [Finset.mem_insert, Finset.mem_singleton] at heRed
      rcases heRed with hec | hed
      · subst e
        exact hcBad heB
      · subst e
        exact hdBad heB
    · let e := P.edgeColor bad₁ v
      have heB := edgeColor_mem_active_lower P hbv
      have heV := edgeColor_mem_active_upper P hbv
      have heRoot :
          e ≠ root :=
        nonTop_edgeColor_ne_root P hrootAll
          hbv htb₁.symm hvne.1
      have heRed :
          e ∈ (active P v).erase root :=
        Finset.mem_erase.mpr ⟨heRoot, heV⟩
      rw [hsubsetCD] at heRed
      simp only [Finset.mem_insert, Finset.mem_singleton] at heRed
      rcases heRed with hec | hed
      · subst e
        exact hcBad heB
      · subst e
        exact hdBad heB
  · have hdW : d ∈ active P w :=
      (Finset.mem_filter.mp hwD).2
    have hcWRoot : c ≠ root := by
      intro h
      subst c
      exact hcBad ((hrootAll bad₁ htb₁).1)
    have hdRoot : d ≠ root :=
      (Finset.mem_erase.mp hdUErase).1
    have hcd : c ≠ d := by
      intro h
      subst d
      exact hcU hdU
    have hredCard :
        ((active P w).erase root).card = 2 :=
      hrootOther w hwne3.1 hwne3.2.1 hwne3.2.2
    have hcRed :
        c ∈ (active P w).erase root :=
      Finset.mem_erase.mpr ⟨hcWRoot, hcW⟩
    have hdRed :
        d ∈ (active P w).erase root :=
      Finset.mem_erase.mpr ⟨hdRoot, hdW⟩
    have hsubsetCD :
        (active P w).erase root = {c,d} := by
      have hcardCD :
          ({c,d} : Finset (Fin n)).card = 2 := by
        simp [hcd]
      apply Finset.Subset.antisymm
      · intro x hx
        by_contra hxCD
        have hs :
            ({c,d,x} : Finset (Fin n)) ⊆
              (active P w).erase root := by
          intro y hy
          simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl | rfl
          · exact hcRed
          · exact hdRed
          · exact hx
        have hc3 :
            ({c,d,x} : Finset (Fin n)).card = 3 := by
          simp [hcd]
          push_neg at hxCD
          tauto
        have h3 := Finset.card_le_card hs
        rw [hc3, hredCard] at h3
        omega
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hcRed
        · exact hdRed
    rcases lt_or_gt_of_ne hwne3.2.1 with hwb | hbw
    · let e := P.edgeColor w bad₁
      have heW := edgeColor_mem_active_lower P hwb
      have heB := edgeColor_mem_active_upper P hwb
      have heRoot :
          e ≠ root :=
        nonTop_edgeColor_ne_root P hrootAll
          hwb hwne3.1 htb₁.symm
      have heRed :
          e ∈ (active P w).erase root :=
        Finset.mem_erase.mpr ⟨heRoot, heW⟩
      rw [hsubsetCD] at heRed
      simp only [Finset.mem_insert, Finset.mem_singleton] at heRed
      rcases heRed with hec | hed
      · subst e
        exact hcBad heB
      · subst e
        exact hdBad heB
    · let e := P.edgeColor bad₁ w
      have heB := edgeColor_mem_active_lower P hbw
      have heW := edgeColor_mem_active_upper P hbw
      have heRoot :
          e ≠ root :=
        nonTop_edgeColor_ne_root P hrootAll
          hbw htb₁.symm hwne3.1
      have heRed :
          e ∈ (active P w).erase root :=
        Finset.mem_erase.mpr ⟨heRoot, heW⟩
      rw [hsubsetCD] at heRed
      simp only [Finset.mem_insert, Finset.mem_singleton] at heRed
      rcases heRed with hec | hed
      · subst e
        exact hcBad heB
      · subst e
        exact hdBad heB

#print axioms outside_bad_colour_used_by_exactly_two_ordinary
#print axioms exists_ordinary_reduced_active_subset_bad

end JSP000404Research
