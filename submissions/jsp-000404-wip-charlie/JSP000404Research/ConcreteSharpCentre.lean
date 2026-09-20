import JSP000404Research.ConcreteOneSupportInterval
import JSP000404Research.SharpCentre
import Mathlib.Tactic

/-!
# Concrete unit-deficit centres are Sendov-sharp

For an actual centre cycle at fixed Sendov scale

  t = n + delta,   lambda = pi / t,

the unit-deficit condition k=n-1 forces quotient support one and the unique
positive quotient equals n.  The concrete one-support interval certificate
therefore has transition gap ge with

  n <= t*ge.

Its common-signed complementary interval has width

  pi*(1-ge) <= delta*lambda.

Hence every pair of rays at the centre makes genuine Euclidean angle at most
delta*lambda: the centre satisfies SharpAt.

This is the missing concrete bridge needed to reuse the closed sharp-centre
geometry in the s=3 terminal case.
-/

namespace JSP000404Research

open Real
open scoped BigOperators

/-- Two rays represented in one same-sign interval have angle at most the
interval width. -/
theorem angle_le_width_of_common_signed_interval
    {V : Type*} {p : V → Plane}
    {i j k : V}
    {a width : ℝ} {sigma : Bool}
    (hwidth0 : 0 ≤ width)
    (hwidthpi : width < Real.pi)
    (hji : j ≠ i) (hki : k ≠ i)
    (hrepr : ∀ x, x ≠ i →
      ∃ rho : ℝ, ∃ theta : ℝ,
        0 < rho ∧
        a ≤ theta ∧ theta ≤ a + width ∧
        p x - p i =
          rho • signedRayDirection sigma theta) :
    EuclideanGeometry.angle (p j) (p i) (p k) ≤ width := by
  obtain ⟨rhoj, thetaj, hrhoj, hjlo, hjhi, hjrepr⟩ :=
    hrepr j hji
  obtain ⟨rhok, thetak, hrhok, hklo, hkhi, hkrepr⟩ :=
    hrepr k hki
  have hdiff : |thetaj - thetak| ≤ width := by
    rw [abs_le]
    constructor <;> linarith
  have hdiffpi : |thetaj - thetak| ≤ Real.pi :=
    hdiff.trans hwidthpi.le
  change
    InnerProductGeometry.angle
        (p j - p i) (p k - p i) ≤ width
  rw [hjrepr, hkrepr,
      angle_positive_smul_signedRay hrhoj hrhok]
  rw [angle_signedRayDirection_eq_of_sign_eq
      (theta := thetaj) (phi := thetak) rfl hdiffpi]
  exact hdiff

/-- A concrete exponent n-1 centre is geometrically sharp in the lower
Sendov normalization. -/
theorem concrete_unit_deficit_is_sharp
    {V : Type*} [LinearOrder V] [Fintype V]
    {p : V → Plane}
    (hp : Function.Injective p)
    (hcap : AngleCap p lam)
    {lam t delta : ℝ} {n : ℕ}
    (hn : 2 ≤ n)
    (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta < 1)
    (ht : t = (n : ℝ) + delta)
    (hlam : lam = Real.pi / t)
    (i : V)
    (C : CentreProjectiveCycle hp i)
    (hexp : centreExponent C t = n - 1) :
    SharpAt p delta lam i := by
  have hsum :=
    centreQuotient_function_sum_le_n
      C n delta t (by omega) hdelta0 hdelta1 ht
  have hdef :
      n - floorExcess (centreQuotient C t) = 1 := by
    rw [← show centreExponent C t =
      floorExcess (centreQuotient C t) by rfl, hexp]
    omega
  have hsupport :
      positiveSupport (centreQuotient C t) = 1 :=
    (unit_deficit_structure
      (centreQuotient C t) n hn hsum hdef).1
  let cert :=
    Classical.choice
      (exists_oneSupportIntervalCertificate
        hp hcap (by omega : 1 ≤ n) hdelta0
        ht hlam i C hsupport)
  have hqeN : cert.qe = n := by
    rw [cert.qe_eq, hexp]
    omega
  have htpos : 0 < t :=
    sendov_scale_pos (by omega : 1 ≤ n) hdelta0 ht
  have hge :
      (n : ℝ) / t ≤ cert.ge := by
    rw [div_le_iff₀ htpos]
    rw [← hqeN]
    exact cert.qe_le
  have hwidth :
      cert.width ≤ delta * lam := by
    rw [cert.width_eq, hlam]
    have hnt : (n : ℝ) / t ≤ cert.ge := hge
    have htEq : (n : ℝ) = t - delta := by
      rw [ht]
      ring
    rw [htEq] at hnt
    have hpi := Real.pi_pos
    have hinvt : 0 < 1 / t := one_div_pos.mpr htpos
    calc
      cert.width
          = Real.pi * (1 - cert.ge) := cert.width_eq
      _ ≤ Real.pi * (delta / t) := by
        apply mul_le_mul_of_nonneg_left _ hpi.le
        rw [div_eq_mul_inv] at hnt ⊢
        have hone :
            1 - (t - delta) * (1 / t) =
              delta * (1 / t) := by
          field_simp
          ring
        rw [← hone]
        linarith
      _ = delta * (Real.pi / t) := by ring
  intro j k hji hki hjk
  exact (angle_le_width_of_common_signed_interval
    cert.width_nonneg cert.width_lt_pi hji hki cert.repr).trans hwidth

#print axioms angle_le_width_of_common_signed_interval
#print axioms concrete_unit_deficit_is_sharp

end JSP000404Research
