import JSP000404Research.SameSignUnitGapSlot
import JSP000404Research.TransitionUnitGapSlot
import JSP000404Research.CentreAdjacentTransitionOccurrence
import JSP000404Research.TransitionGapRayAlignment
import Mathlib.Tactic

/-!
# Same-sign and ordinary-transition unit-slot certificates are disjoint

The two positional slot certificates refer to the same dependent q=1
coordinate.

* CentreUnitGapSameSign says that, at the slot index m, the aligned lifted sign
  path has the same sign immediately before and after the quotient step.
* CentreUnitGapOrdinaryTransition says that the same index m is an ordinary
  adjacent ray pair with opposite signs.

The two descriptions are incompatible.  This discharges the natural
"same-sign slots are unusable" hypothesis whenever critical obstructions are
defined only on ordinary transition slots.
-/

namespace JSP000404Research

theorem not_centreUnitGapSameSign_and_ordinaryTransition
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p} {i : V}
    (C : CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : CentreUnitGap C t)
    (hsame : CentreUnitGapSameSign C t u)
    (htrans : CentreUnitGapOrdinaryTransition C t u) :
    False := by
  rcases hsame with
    ⟨first, rest, signPre, signPost,
      qPre, qPost, b,
      hrays, hsigns, _hqs, hlen,
      hqIdx, hlast⟩
  rcases htrans with
    ⟨m, hm, huIdx, _hfloor, hne⟩
  have hmEq : m = qPre.length := by
    omega
  subst m
  have hmRest : qPre.length < rest.length := by
    rw [hrays] at hm
    simp at hm
    omega
  let signs :=
    liftedCentreSignPath hp i first rest
  have hsignLen :
      qPre.length < signs.length := by
    dsimp [signs, liftedCentreSignPath]
    simp
    omega
  have hstd :
      signs =
        signs.take qPre.length ++
          signs[qPre.length] ::
            signs.drop (qPre.length + 1) := by
    have htake :
        signs.take qPre.length ++ [signs[qPre.length]] =
          signs.take (qPre.length + 1) :=
      List.take_concat_get' signs qPre.length hsignLen
    have hfull :
        signs.take (qPre.length + 1) ++
          signs.drop (qPre.length + 1) = signs :=
      List.take_append_drop (qPre.length + 1) signs
    calc
      signs = signs.take (qPre.length + 1) ++
          signs.drop (qPre.length + 1) := hfull.symm
      _ = (signs.take qPre.length ++ [signs[qPre.length]]) ++
          signs.drop (qPre.length + 1) :=
        congrArg (fun xs => xs ++ signs.drop (qPre.length + 1)) htake.symm
      _ = signs.take qPre.length ++ signs[qPre.length] ::
          signs.drop (qPre.length + 1) := by simp [List.append_assoc]
  have hsigns' :
      signs = signPre ++ b :: signPost := by
    simpa [signs] using hsigns
  have hblocks :=
    blocks_eq_of_decompositions
      hsigns' hstd (by
        simpa [hlen, List.length_take, Nat.min_eq_left hsignLen.le])
  have hpreEq :
      signPre = signs.take qPre.length :=
    hblocks.1
  have hbEq :
      b = signs[qPre.length] :=
    hblocks.2.1
  have hpreTake :
      signs.take qPre.length =
        (rest.take qPre.length).map
          (raySignAt hp i) := by
    dsimp [signs, liftedCentreSignPath]
    have hle : qPre.length ≤ rest.length := hmRest.le
    rw [List.take_append_of_le_length]
    · simp
    · simpa using hle
  have hidxLeft : qPre.length < (first :: rest).length := by
    simp only [List.length_cons]
    omega
  have hidxRight : qPre.length + 1 < (first :: rest).length := by
    simp only [List.length_cons]
    omega
  have hmRay : qPre.length + 1 < C.rays.length := by omega
  have hleft :
      boolLastFrom (raySignAt hp i first) signPre =
        raySignAt hp i
          ((first :: rest)[qPre.length]'hidxLeft) := by
    rw [hpreEq, hpreTake]
    exact boolLastFrom_map_take_eq_ray_getElem
      (raySignAt hp i) first rest qPre.length
      (by simp; omega)
  have hright :
      b =
        raySignAt hp i
          ((first :: rest)[qPre.length + 1]'hidxRight) := by
    have hsignMap :
        signs[qPre.length] =
          (rest.map (raySignAt hp i))[qPre.length]'(by
            simpa using hmRest) := by
      have hopt :
          signs[qPre.length]? =
            (rest.map (raySignAt hp i))[qPre.length]? := by
        change
          (rest.map (raySignAt hp i) ++ [!raySignAt hp i first])[qPre.length]? =
            (rest.map (raySignAt hp i))[qPre.length]?
        exact List.getElem?_append_left (by simpa using hmRest)
      rw [List.getElem?_eq_getElem hsignLen,
        List.getElem?_eq_getElem (by simpa using hmRest)] at hopt
      exact Option.some_inj.mp hopt
    calc
      b = signs[qPre.length] := hbEq
      _ = (rest.map (raySignAt hp i))[qPre.length]'(by
            simpa using hmRest) := hsignMap
      _ = raySignAt hp i (rest[qPre.length]'hmRest) := by simp
      _ = raySignAt hp i
            ((first :: rest)[qPre.length + 1]'hidxRight) := by simp
  have hmLeft : qPre.length < C.rays.length := by omega
  have hraysLeft :
      (C.rays.get ⟨qPre.length, hmLeft⟩) =
        (first :: rest)[qPre.length]'hidxLeft := by
    have hopt := congrArg
      (fun rays : List (OtherVertex i) => rays[qPre.length]?) hrays
    rw [List.getElem?_eq_getElem hmLeft,
      List.getElem?_eq_getElem hidxLeft] at hopt
    exact Option.some_inj.mp hopt
  have hraysRight :
      (C.rays.get ⟨qPre.length + 1, hmRay⟩) =
        (first :: rest)[qPre.length + 1]'hidxRight := by
    have hopt := congrArg
      (fun rays : List (OtherVertex i) => rays[qPre.length + 1]?) hrays
    rw [List.getElem?_eq_getElem hmRay,
      List.getElem?_eq_getElem hidxRight] at hopt
    exact Option.some_inj.mp hopt
  have hsamePair :
      raySignAt hp i
          (C.rays.get ⟨qPre.length, by omega⟩)
        =
      raySignAt hp i
          (C.rays.get ⟨qPre.length + 1, hmRay⟩) := by
    rw [hraysLeft, hraysRight]
    rw [← hleft, ← hright]
    exact hlast
  have hne' :
      raySignAt hp i
          (C.rays.get ⟨qPre.length, by omega⟩) ≠
        raySignAt hp i
          (C.rays.get ⟨qPre.length + 1, hmRay⟩) := by
    simpa only [← hmEq] using hne
  exact hne' hsamePair

theorem globalUnitGapSameSign_not_ordinaryTransition
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane} {hp : Function.Injective p}
    (C : ∀ i : V, CentreProjectiveCycle hp i)
    (t : ℝ)
    (u : GlobalUnitGapSlot C t)
    (hsame : GlobalUnitGapSameSign C t u) :
    ¬ GlobalUnitGapOrdinaryTransition C t u := by
  intro htrans
  exact not_centreUnitGapSameSign_and_ordinaryTransition
    (C u.1) t u.2 hsame htrans

#print axioms not_centreUnitGapSameSign_and_ordinaryTransition
#print axioms globalUnitGapSameSign_not_ordinaryTransition

end JSP000404Research
