import JSP000404Research.NinePhaseData
import JSP000404Research.NinePhaseBooleanCertificate

/-!
# Semantic interpretation of the nine-phase matching certificate

Full coverage by separated catalog rows forces one of two specified five-row cores.
Each numerical premise of the generated Boolean proof is discharged against the
explicit row and slot definitions by ordinary kernel reduction.
-/

namespace JSP000404Research.NinePhase

private theorem positive_clause (selected : Fin 78 → Bool) (slot : Fin 42)
    (indices : List (Fin 78)) (hindices : ∀ i, covers i slot = true → i ∈ indices)
    (hcover : ∀ slot, ∃ i, covers i slot = true ∧ selected i = true) :
    indices.any selected = true := by
  obtain ⟨i, hic, his⟩ := hcover slot
  exact List.any_eq_true.mpr ⟨i, hindices i hic, his⟩

private theorem negative_clause (selected : Fin 78 → Bool) (i j : Fin 78)
    (hne : i ≠ j) (hbad : ¬Separated i j)
    (hsep : ∀ i j, i ≠ j → selected i = true → selected j = true → Separated i j) :
    selected i = false ∨ selected j = false := by
  cases hi : selected i with
  | false => exact Or.inl rfl
  | true =>
    cases hj : selected j with
    | false => exact Or.inr rfl
    | true => exact (hbad (hsep i j hne hi hj)).elim

private theorem five_clause (a b c d e : Bool)
    (h : ¬(a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true)) :
    a = false ∨ b = false ∨ c = false ∨ d = false ∨ e = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp_all

theorem no_full_cover_avoiding_cores (selected : Fin 78 → Bool)
    (hcover : ∀ slot, ∃ i, covers i slot = true ∧ selected i = true)
    (hsep : ∀ i j, i ≠ j → selected i = true → selected j = true → Separated i j)
    (hcore : ¬(selected 25 = true ∧ selected 54 = true ∧ selected 70 = true ∧
      selected 11 = true ∧ selected 44 = true))
    (hflip : ¬(selected 24 = true ∧ selected 55 = true ∧ selected 71 = true ∧
      selected 10 = true ∧ selected 45 = true)) : False := by
  apply BooleanCertificate.clauses_impossible
    (selected 10) (selected 11) (selected 14) (selected 15) (selected 16) (selected 17)
    (selected 18) (selected 19) (selected 22) (selected 23) (selected 24) (selected 25)
    (selected 26) (selected 27) (selected 28) (selected 29) (selected 30) (selected 31)
    (selected 32) (selected 33) (selected 36) (selected 37) (selected 38) (selected 39)
    (selected 40) (selected 41) (selected 42) (selected 43) (selected 44) (selected 45)
    (selected 46) (selected 47) (selected 48) (selected 49) (selected 50) (selected 51)
    (selected 52) (selected 53) (selected 54) (selected 55) (selected 58) (selected 59)
    (selected 60) (selected 61) (selected 62) (selected 63) (selected 64) (selected 65)
    (selected 66) (selected 67) (selected 68) (selected 69) (selected 70) (selected 71)
    (selected 72) (selected 73) (selected 74) (selected 75) (selected 76) (selected 77)
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 0 [44, 46, 50, 52, 60, 62, 64, 66] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 1 [36, 38, 40, 58] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 3 [54, 68, 74, 76] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 4 [48, 50, 64, 70] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 5 [14, 16, 22, 24, 67, 69, 73, 75] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 7 [18, 26, 30, 32] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 9 [10, 59, 61, 63] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 14 [10, 14, 16, 18] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 16 [28, 42, 48, 77] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 17 [32, 46, 52, 54] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 19 [22, 36, 71, 73] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 20 [24, 26, 28, 30, 38, 40, 42, 44] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 21 [25, 27, 29, 31, 39, 41, 43, 45] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 22 [23, 37, 70, 72] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 24 [33, 47, 53, 55] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 25 [29, 43, 49, 76] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 27 [11, 15, 17, 19] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 32 [11, 58, 60, 62] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 34 [19, 27, 31, 33] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 36 [15, 17, 23, 25, 66, 68, 72, 74] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 37 [49, 51, 65, 71] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 38 [55, 69, 75, 77] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 40 [37, 39, 41, 59] (by decide) hcover
  · simpa only [List.any_cons, List.any_nil, Bool.or_eq_true,
      Bool.false_eq_true, or_false] using
      positive_clause selected 41 [45, 47, 51, 53, 61, 63, 65, 67] (by decide) hcover
  · exact negative_clause selected 10 14 (by decide) (by decide) hsep
  · exact negative_clause selected 10 16 (by decide) (by decide) hsep
  · exact negative_clause selected 10 18 (by decide) (by decide) hsep
  · exact negative_clause selected 10 59 (by decide) (by decide) hsep
  · exact negative_clause selected 10 61 (by decide) (by decide) hsep
  · exact negative_clause selected 10 63 (by decide) (by decide) hsep
  · exact negative_clause selected 10 65 (by decide) (by decide) hsep
  · exact negative_clause selected 10 67 (by decide) (by decide) hsep
  · exact negative_clause selected 10 69 (by decide) (by decide) hsep
  · exact negative_clause selected 11 15 (by decide) (by decide) hsep
  · exact negative_clause selected 11 17 (by decide) (by decide) hsep
  · exact negative_clause selected 11 19 (by decide) (by decide) hsep
  · exact negative_clause selected 11 58 (by decide) (by decide) hsep
  · exact negative_clause selected 11 60 (by decide) (by decide) hsep
  · exact negative_clause selected 11 62 (by decide) (by decide) hsep
  · exact negative_clause selected 11 64 (by decide) (by decide) hsep
  · exact negative_clause selected 11 66 (by decide) (by decide) hsep
  · exact negative_clause selected 11 68 (by decide) (by decide) hsep
  · exact negative_clause selected 14 16 (by decide) (by decide) hsep
  · exact negative_clause selected 14 18 (by decide) (by decide) hsep
  · exact negative_clause selected 14 22 (by decide) (by decide) hsep
  · exact negative_clause selected 14 24 (by decide) (by decide) hsep
  · exact negative_clause selected 14 26 (by decide) (by decide) hsep
  · exact negative_clause selected 14 61 (by decide) (by decide) hsep
  · exact negative_clause selected 14 63 (by decide) (by decide) hsep
  · exact negative_clause selected 14 65 (by decide) (by decide) hsep
  · exact negative_clause selected 14 67 (by decide) (by decide) hsep
  · exact negative_clause selected 14 69 (by decide) (by decide) hsep
  · exact negative_clause selected 14 71 (by decide) (by decide) hsep
  · exact negative_clause selected 14 73 (by decide) (by decide) hsep
  · exact negative_clause selected 14 75 (by decide) (by decide) hsep
  · exact negative_clause selected 15 17 (by decide) (by decide) hsep
  · exact negative_clause selected 15 19 (by decide) (by decide) hsep
  · exact negative_clause selected 15 23 (by decide) (by decide) hsep
  · exact negative_clause selected 15 25 (by decide) (by decide) hsep
  · exact negative_clause selected 15 27 (by decide) (by decide) hsep
  · exact negative_clause selected 15 60 (by decide) (by decide) hsep
  · exact negative_clause selected 15 62 (by decide) (by decide) hsep
  · exact negative_clause selected 15 64 (by decide) (by decide) hsep
  · exact negative_clause selected 15 66 (by decide) (by decide) hsep
  · exact negative_clause selected 15 68 (by decide) (by decide) hsep
  · exact negative_clause selected 15 70 (by decide) (by decide) hsep
  · exact negative_clause selected 15 72 (by decide) (by decide) hsep
  · exact negative_clause selected 15 74 (by decide) (by decide) hsep
  · exact negative_clause selected 16 18 (by decide) (by decide) hsep
  · exact negative_clause selected 16 22 (by decide) (by decide) hsep
  · exact negative_clause selected 16 24 (by decide) (by decide) hsep
  · exact negative_clause selected 16 26 (by decide) (by decide) hsep
  · exact negative_clause selected 16 28 (by decide) (by decide) hsep
  · exact negative_clause selected 16 30 (by decide) (by decide) hsep
  · exact negative_clause selected 16 63 (by decide) (by decide) hsep
  · exact negative_clause selected 16 67 (by decide) (by decide) hsep
  · exact negative_clause selected 16 69 (by decide) (by decide) hsep
  · exact negative_clause selected 16 73 (by decide) (by decide) hsep
  · exact negative_clause selected 16 75 (by decide) (by decide) hsep
  · exact negative_clause selected 16 77 (by decide) (by decide) hsep
  · exact negative_clause selected 17 19 (by decide) (by decide) hsep
  · exact negative_clause selected 17 23 (by decide) (by decide) hsep
  · exact negative_clause selected 17 25 (by decide) (by decide) hsep
  · exact negative_clause selected 17 27 (by decide) (by decide) hsep
  · exact negative_clause selected 17 29 (by decide) (by decide) hsep
  · exact negative_clause selected 17 31 (by decide) (by decide) hsep
  · exact negative_clause selected 17 62 (by decide) (by decide) hsep
  · exact negative_clause selected 17 66 (by decide) (by decide) hsep
  · exact negative_clause selected 17 68 (by decide) (by decide) hsep
  · exact negative_clause selected 17 72 (by decide) (by decide) hsep
  · exact negative_clause selected 17 74 (by decide) (by decide) hsep
  · exact negative_clause selected 17 76 (by decide) (by decide) hsep
  · exact negative_clause selected 18 22 (by decide) (by decide) hsep
  · exact negative_clause selected 18 24 (by decide) (by decide) hsep
  · exact negative_clause selected 18 26 (by decide) (by decide) hsep
  · exact negative_clause selected 18 28 (by decide) (by decide) hsep
  · exact negative_clause selected 18 30 (by decide) (by decide) hsep
  · exact negative_clause selected 18 32 (by decide) (by decide) hsep
  · exact negative_clause selected 19 23 (by decide) (by decide) hsep
  · exact negative_clause selected 19 25 (by decide) (by decide) hsep
  · exact negative_clause selected 19 27 (by decide) (by decide) hsep
  · exact negative_clause selected 19 29 (by decide) (by decide) hsep
  · exact negative_clause selected 19 31 (by decide) (by decide) hsep
  · exact negative_clause selected 19 33 (by decide) (by decide) hsep
  · exact negative_clause selected 22 24 (by decide) (by decide) hsep
  · exact negative_clause selected 22 26 (by decide) (by decide) hsep
  · exact negative_clause selected 22 36 (by decide) (by decide) hsep
  · exact negative_clause selected 22 38 (by decide) (by decide) hsep
  · exact negative_clause selected 22 71 (by decide) (by decide) hsep
  · exact negative_clause selected 23 25 (by decide) (by decide) hsep
  · exact negative_clause selected 23 27 (by decide) (by decide) hsep
  · exact negative_clause selected 23 37 (by decide) (by decide) hsep
  · exact negative_clause selected 23 39 (by decide) (by decide) hsep
  · exact negative_clause selected 23 64 (by decide) (by decide) hsep
  · exact negative_clause selected 23 70 (by decide) (by decide) hsep
  · exact negative_clause selected 24 26 (by decide) (by decide) hsep
  · exact negative_clause selected 24 28 (by decide) (by decide) hsep
  · exact negative_clause selected 24 30 (by decide) (by decide) hsep
  · exact negative_clause selected 24 36 (by decide) (by decide) hsep
  · exact negative_clause selected 24 38 (by decide) (by decide) hsep
  · exact negative_clause selected 24 40 (by decide) (by decide) hsep
  · exact negative_clause selected 24 42 (by decide) (by decide) hsep
  · exact negative_clause selected 24 44 (by decide) (by decide) hsep
  · exact negative_clause selected 24 73 (by decide) (by decide) hsep
  · exact negative_clause selected 24 75 (by decide) (by decide) hsep
  · exact negative_clause selected 24 77 (by decide) (by decide) hsep
  · exact negative_clause selected 25 27 (by decide) (by decide) hsep
  · exact negative_clause selected 25 29 (by decide) (by decide) hsep
  · exact negative_clause selected 25 31 (by decide) (by decide) hsep
  · exact negative_clause selected 25 37 (by decide) (by decide) hsep
  · exact negative_clause selected 25 39 (by decide) (by decide) hsep
  · exact negative_clause selected 25 41 (by decide) (by decide) hsep
  · exact negative_clause selected 25 43 (by decide) (by decide) hsep
  · exact negative_clause selected 25 45 (by decide) (by decide) hsep
  · exact negative_clause selected 25 72 (by decide) (by decide) hsep
  · exact negative_clause selected 25 74 (by decide) (by decide) hsep
  · exact negative_clause selected 25 76 (by decide) (by decide) hsep
  · exact negative_clause selected 26 28 (by decide) (by decide) hsep
  · exact negative_clause selected 26 30 (by decide) (by decide) hsep
  · exact negative_clause selected 26 32 (by decide) (by decide) hsep
  · exact negative_clause selected 26 36 (by decide) (by decide) hsep
  · exact negative_clause selected 26 38 (by decide) (by decide) hsep
  · exact negative_clause selected 26 40 (by decide) (by decide) hsep
  · exact negative_clause selected 26 42 (by decide) (by decide) hsep
  · exact negative_clause selected 26 44 (by decide) (by decide) hsep
  · exact negative_clause selected 26 46 (by decide) (by decide) hsep
  · exact negative_clause selected 27 29 (by decide) (by decide) hsep
  · exact negative_clause selected 27 31 (by decide) (by decide) hsep
  · exact negative_clause selected 27 33 (by decide) (by decide) hsep
  · exact negative_clause selected 27 37 (by decide) (by decide) hsep
  · exact negative_clause selected 27 39 (by decide) (by decide) hsep
  · exact negative_clause selected 27 41 (by decide) (by decide) hsep
  · exact negative_clause selected 27 43 (by decide) (by decide) hsep
  · exact negative_clause selected 27 45 (by decide) (by decide) hsep
  · exact negative_clause selected 27 47 (by decide) (by decide) hsep
  · exact negative_clause selected 28 30 (by decide) (by decide) hsep
  · exact negative_clause selected 28 38 (by decide) (by decide) hsep
  · exact negative_clause selected 28 42 (by decide) (by decide) hsep
  · exact negative_clause selected 28 48 (by decide) (by decide) hsep
  · exact negative_clause selected 28 50 (by decide) (by decide) hsep
  · exact negative_clause selected 28 75 (by decide) (by decide) hsep
  · exact negative_clause selected 28 77 (by decide) (by decide) hsep
  · exact negative_clause selected 29 31 (by decide) (by decide) hsep
  · exact negative_clause selected 29 39 (by decide) (by decide) hsep
  · exact negative_clause selected 29 49 (by decide) (by decide) hsep
  · exact negative_clause selected 29 51 (by decide) (by decide) hsep
  · exact negative_clause selected 29 74 (by decide) (by decide) hsep
  · exact negative_clause selected 29 76 (by decide) (by decide) hsep
  · exact negative_clause selected 30 32 (by decide) (by decide) hsep
  · exact negative_clause selected 30 38 (by decide) (by decide) hsep
  · exact negative_clause selected 30 40 (by decide) (by decide) hsep
  · exact negative_clause selected 30 42 (by decide) (by decide) hsep
  · exact negative_clause selected 30 44 (by decide) (by decide) hsep
  · exact negative_clause selected 30 46 (by decide) (by decide) hsep
  · exact negative_clause selected 30 48 (by decide) (by decide) hsep
  · exact negative_clause selected 30 50 (by decide) (by decide) hsep
  · exact negative_clause selected 30 52 (by decide) (by decide) hsep
  · exact negative_clause selected 31 33 (by decide) (by decide) hsep
  · exact negative_clause selected 31 39 (by decide) (by decide) hsep
  · exact negative_clause selected 31 41 (by decide) (by decide) hsep
  · exact negative_clause selected 31 43 (by decide) (by decide) hsep
  · exact negative_clause selected 31 45 (by decide) (by decide) hsep
  · exact negative_clause selected 31 47 (by decide) (by decide) hsep
  · exact negative_clause selected 31 49 (by decide) (by decide) hsep
  · exact negative_clause selected 31 51 (by decide) (by decide) hsep
  · exact negative_clause selected 31 53 (by decide) (by decide) hsep
  · exact negative_clause selected 32 40 (by decide) (by decide) hsep
  · exact negative_clause selected 32 44 (by decide) (by decide) hsep
  · exact negative_clause selected 32 46 (by decide) (by decide) hsep
  · exact negative_clause selected 32 50 (by decide) (by decide) hsep
  · exact negative_clause selected 32 52 (by decide) (by decide) hsep
  · exact negative_clause selected 32 54 (by decide) (by decide) hsep
  · exact negative_clause selected 33 41 (by decide) (by decide) hsep
  · exact negative_clause selected 33 45 (by decide) (by decide) hsep
  · exact negative_clause selected 33 47 (by decide) (by decide) hsep
  · exact negative_clause selected 33 51 (by decide) (by decide) hsep
  · exact negative_clause selected 33 53 (by decide) (by decide) hsep
  · exact negative_clause selected 33 55 (by decide) (by decide) hsep
  · exact negative_clause selected 36 38 (by decide) (by decide) hsep
  · exact negative_clause selected 36 40 (by decide) (by decide) hsep
  · exact negative_clause selected 36 58 (by decide) (by decide) hsep
  · exact negative_clause selected 36 71 (by decide) (by decide) hsep
  · exact negative_clause selected 36 73 (by decide) (by decide) hsep
  · exact negative_clause selected 36 75 (by decide) (by decide) hsep
  · exact negative_clause selected 37 39 (by decide) (by decide) hsep
  · exact negative_clause selected 37 41 (by decide) (by decide) hsep
  · exact negative_clause selected 37 59 (by decide) (by decide) hsep
  · exact negative_clause selected 37 70 (by decide) (by decide) hsep
  · exact negative_clause selected 37 72 (by decide) (by decide) hsep
  · exact negative_clause selected 37 74 (by decide) (by decide) hsep
  · exact negative_clause selected 38 40 (by decide) (by decide) hsep
  · exact negative_clause selected 38 42 (by decide) (by decide) hsep
  · exact negative_clause selected 38 44 (by decide) (by decide) hsep
  · exact negative_clause selected 38 58 (by decide) (by decide) hsep
  · exact negative_clause selected 38 60 (by decide) (by decide) hsep
  · exact negative_clause selected 38 73 (by decide) (by decide) hsep
  · exact negative_clause selected 38 75 (by decide) (by decide) hsep
  · exact negative_clause selected 38 77 (by decide) (by decide) hsep
  · exact negative_clause selected 39 43 (by decide) (by decide) hsep
  · exact negative_clause selected 39 45 (by decide) (by decide) hsep
  · exact negative_clause selected 39 59 (by decide) (by decide) hsep
  · exact negative_clause selected 39 61 (by decide) (by decide) hsep
  · exact negative_clause selected 39 72 (by decide) (by decide) hsep
  · exact negative_clause selected 39 74 (by decide) (by decide) hsep
  · exact negative_clause selected 39 76 (by decide) (by decide) hsep
  · exact negative_clause selected 40 42 (by decide) (by decide) hsep
  · exact negative_clause selected 40 44 (by decide) (by decide) hsep
  · exact negative_clause selected 40 46 (by decide) (by decide) hsep
  · exact negative_clause selected 40 58 (by decide) (by decide) hsep
  · exact negative_clause selected 40 60 (by decide) (by decide) hsep
  · exact negative_clause selected 40 62 (by decide) (by decide) hsep
  · exact negative_clause selected 41 43 (by decide) (by decide) hsep
  · exact negative_clause selected 41 45 (by decide) (by decide) hsep
  · exact negative_clause selected 41 47 (by decide) (by decide) hsep
  · exact negative_clause selected 41 59 (by decide) (by decide) hsep
  · exact negative_clause selected 41 61 (by decide) (by decide) hsep
  · exact negative_clause selected 42 44 (by decide) (by decide) hsep
  · exact negative_clause selected 42 48 (by decide) (by decide) hsep
  · exact negative_clause selected 42 50 (by decide) (by decide) hsep
  · exact negative_clause selected 42 58 (by decide) (by decide) hsep
  · exact negative_clause selected 42 60 (by decide) (by decide) hsep
  · exact negative_clause selected 42 64 (by decide) (by decide) hsep
  · exact negative_clause selected 42 75 (by decide) (by decide) hsep
  · exact negative_clause selected 42 77 (by decide) (by decide) hsep
  · exact negative_clause selected 43 45 (by decide) (by decide) hsep
  · exact negative_clause selected 43 49 (by decide) (by decide) hsep
  · exact negative_clause selected 43 51 (by decide) (by decide) hsep
  · exact negative_clause selected 43 59 (by decide) (by decide) hsep
  · exact negative_clause selected 43 61 (by decide) (by decide) hsep
  · exact negative_clause selected 43 65 (by decide) (by decide) hsep
  · exact negative_clause selected 43 76 (by decide) (by decide) hsep
  · exact negative_clause selected 44 46 (by decide) (by decide) hsep
  · exact negative_clause selected 44 48 (by decide) (by decide) hsep
  · exact negative_clause selected 44 50 (by decide) (by decide) hsep
  · exact negative_clause selected 44 52 (by decide) (by decide) hsep
  · exact negative_clause selected 44 58 (by decide) (by decide) hsep
  · exact negative_clause selected 45 47 (by decide) (by decide) hsep
  · exact negative_clause selected 45 49 (by decide) (by decide) hsep
  · exact negative_clause selected 45 59 (by decide) (by decide) hsep
  · exact negative_clause selected 45 61 (by decide) (by decide) hsep
  · exact negative_clause selected 45 67 (by decide) (by decide) hsep
  · exact negative_clause selected 46 54 (by decide) (by decide) hsep
  · exact negative_clause selected 46 58 (by decide) (by decide) hsep
  · exact negative_clause selected 46 62 (by decide) (by decide) hsep
  · exact negative_clause selected 47 55 (by decide) (by decide) hsep
  · exact negative_clause selected 47 59 (by decide) (by decide) hsep
  · exact negative_clause selected 47 67 (by decide) (by decide) hsep
  · exact negative_clause selected 47 69 (by decide) (by decide) hsep
  · exact negative_clause selected 48 50 (by decide) (by decide) hsep
  · exact negative_clause selected 48 60 (by decide) (by decide) hsep
  · exact negative_clause selected 48 64 (by decide) (by decide) hsep
  · exact negative_clause selected 48 70 (by decide) (by decide) hsep
  · exact negative_clause selected 48 77 (by decide) (by decide) hsep
  · exact negative_clause selected 49 51 (by decide) (by decide) hsep
  · exact negative_clause selected 49 61 (by decide) (by decide) hsep
  · exact negative_clause selected 49 65 (by decide) (by decide) hsep
  · exact negative_clause selected 49 71 (by decide) (by decide) hsep
  · exact negative_clause selected 49 76 (by decide) (by decide) hsep
  · exact negative_clause selected 50 52 (by decide) (by decide) hsep
  · exact negative_clause selected 50 70 (by decide) (by decide) hsep
  · exact negative_clause selected 50 72 (by decide) (by decide) hsep
  · exact negative_clause selected 51 53 (by decide) (by decide) hsep
  · exact negative_clause selected 51 61 (by decide) (by decide) hsep
  · exact negative_clause selected 51 67 (by decide) (by decide) hsep
  · exact negative_clause selected 51 71 (by decide) (by decide) hsep
  · exact negative_clause selected 51 73 (by decide) (by decide) hsep
  · exact negative_clause selected 52 54 (by decide) (by decide) hsep
  · exact negative_clause selected 52 62 (by decide) (by decide) hsep
  · exact negative_clause selected 52 66 (by decide) (by decide) hsep
  · exact negative_clause selected 52 68 (by decide) (by decide) hsep
  · exact negative_clause selected 52 70 (by decide) (by decide) hsep
  · exact negative_clause selected 52 72 (by decide) (by decide) hsep
  · exact negative_clause selected 52 74 (by decide) (by decide) hsep
  · exact negative_clause selected 53 55 (by decide) (by decide) hsep
  · exact negative_clause selected 53 67 (by decide) (by decide) hsep
  · exact negative_clause selected 53 69 (by decide) (by decide) hsep
  · exact negative_clause selected 53 71 (by decide) (by decide) hsep
  · exact negative_clause selected 53 73 (by decide) (by decide) hsep
  · exact negative_clause selected 54 62 (by decide) (by decide) hsep
  · exact negative_clause selected 54 66 (by decide) (by decide) hsep
  · exact negative_clause selected 54 68 (by decide) (by decide) hsep
  · exact negative_clause selected 54 72 (by decide) (by decide) hsep
  · exact negative_clause selected 54 74 (by decide) (by decide) hsep
  · exact negative_clause selected 54 76 (by decide) (by decide) hsep
  · exact negative_clause selected 55 63 (by decide) (by decide) hsep
  · exact negative_clause selected 55 67 (by decide) (by decide) hsep
  · exact negative_clause selected 55 69 (by decide) (by decide) hsep
  · exact negative_clause selected 55 73 (by decide) (by decide) hsep
  · exact negative_clause selected 55 75 (by decide) (by decide) hsep
  · exact negative_clause selected 55 77 (by decide) (by decide) hsep
  · exact negative_clause selected 58 60 (by decide) (by decide) hsep
  · exact negative_clause selected 58 62 (by decide) (by decide) hsep
  · exact negative_clause selected 59 61 (by decide) (by decide) hsep
  · exact negative_clause selected 59 63 (by decide) (by decide) hsep
  · exact negative_clause selected 60 64 (by decide) (by decide) hsep
  · exact negative_clause selected 61 65 (by decide) (by decide) hsep
  · exact negative_clause selected 63 67 (by decide) (by decide) hsep
  · exact negative_clause selected 63 69 (by decide) (by decide) hsep
  · exact negative_clause selected 64 66 (by decide) (by decide) hsep
  · exact negative_clause selected 64 70 (by decide) (by decide) hsep
  · exact negative_clause selected 64 72 (by decide) (by decide) hsep
  · exact negative_clause selected 65 67 (by decide) (by decide) hsep
  · exact negative_clause selected 65 71 (by decide) (by decide) hsep
  · exact negative_clause selected 65 73 (by decide) (by decide) hsep
  · exact negative_clause selected 66 68 (by decide) (by decide) hsep
  · exact negative_clause selected 66 70 (by decide) (by decide) hsep
  · exact negative_clause selected 67 69 (by decide) (by decide) hsep
  · exact negative_clause selected 67 71 (by decide) (by decide) hsep
  · exact negative_clause selected 68 76 (by decide) (by decide) hsep
  · exact negative_clause selected 69 77 (by decide) (by decide) hsep
  · exact negative_clause selected 70 72 (by decide) (by decide) hsep
  · exact negative_clause selected 71 73 (by decide) (by decide) hsep
  · exact negative_clause selected 74 76 (by decide) (by decide) hsep
  · exact negative_clause selected 75 77 (by decide) (by decide) hsep
  · exact five_clause (selected 25) (selected 54) (selected 70) (selected 11) (selected 44)
      hcore
  · exact five_clause (selected 24) (selected 55) (selected 71) (selected 10) (selected 45)
      hflip

#print axioms no_full_cover_avoiding_cores

end JSP000404Research.NinePhase
