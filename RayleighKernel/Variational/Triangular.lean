import RayleighKernel.Variational
import RayleighKernel.Analysis.HalfLineSobolevConverse
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

namespace RayleighKernel

open Set
open MeasureTheory
open scoped Topology

def triangularProfile (L : ℝ) (x : ℝ) : ℝ :=
  6 * max x 0 * max (2 * L - x) 0 / (2 * L) ^ 3

@[simp] theorem triangularProfile_apply (L x : ℝ) :
    triangularProfile L x = 6 * max x 0 * max (2 * L - x) 0 / (2 * L) ^ 3 := rfl

theorem triangularProfile_nonnegative {L x : ℝ} (hL : 0 ≤ L) :
    0 ≤ triangularProfile L x := by
  unfold triangularProfile
  positivity

theorem triangularProfile_eq_zero_of_ge {L x : ℝ} (_hL : 0 < L) (hx : 2 * L ≤ x) :
    triangularProfile L x = 0 := by
  simp [triangularProfile, max_eq_right (sub_nonpos.mpr hx)]

theorem triangularProfile_continuous {L : ℝ} :
    Continuous (triangularProfile L) := by
  unfold triangularProfile
  fun_prop

theorem triangularProfile_support_subset {L : ℝ} (hL : 0 < L) :
    Function.support (triangularProfile L) ⊆ Ioo 0 (2 * L) := by
  intro x hx
  constructor
  · by_contra h
    exact hx (by
      rcases le_or_gt x 0 with hle | hgt
      · simp [triangularProfile, max_eq_right hle]
      · exact False.elim (h hgt))
  · by_contra h
    exact hx (triangularProfile_eq_zero_of_ge hL (le_of_not_gt h))

theorem triangularProfile_integrable {L : ℝ} (hL : 0 < L) :
    Integrable (triangularProfile L) volume := by
  apply triangularProfile_continuous.integrable_of_hasCompactSupport
  refine HasCompactSupport.intro (K := Icc 0 (2 * L)) isCompact_Icc ?_
  intro x hx
  by_cases hx0 : x ≤ 0
  · simp [triangularProfile, max_eq_right hx0]
  · by_cases hxL : 2 * L ≤ x
    · exact triangularProfile_eq_zero_of_ge hL hxL
    · exfalso
      exact hx ⟨le_of_not_ge hx0, le_of_not_ge hxL⟩

theorem triangularProfile_integrableOn {L : ℝ} (hL : 0 < L) :
    IntegrableOn (triangularProfile L) (Ici 0) :=
  triangularProfile_integrable hL |>.integrableOn

theorem triangularProfile_eq_poly {L x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 2 * L) :
    triangularProfile L x = 6 * x * (2 * L - x) / (2 * L) ^ 3 := by
  simp [triangularProfile, max_eq_left hx0, max_eq_left (sub_nonneg.mpr hx2)]

theorem triangularProfile_eq_zero_of_nonpos {L x : ℝ} (hx : x ≤ 0) :
    triangularProfile L x = 0 := by
  simp [triangularProfile, max_eq_right hx]

theorem triangularProfile_deriv_eq {L x : ℝ} (_hL : 0 < L)
    (hx0 : 0 < x) (hx2 : x < 2 * L) :
    deriv (triangularProfile L) x = 6 * (2 * L - 2 * x) / (2 * L) ^ 3 := by
  have hp : HasDerivAt (fun y : ℝ => 6 * y * (2 * L - y) / (2 * L) ^ 3)
      (6 * (2 * L - 2 * x) / (2 * L) ^ 3) x := by
    convert ((((hasDerivAt_id x).const_mul 6).mul
      ((hasDerivAt_const x (2 * L)).sub (hasDerivAt_id x))).div_const ((2 * L) ^ 3)) using 1 <;>
      simp
    ring
  have heq : (fun y : ℝ => 6 * y * (2 * L - y) / (2 * L) ^ 3) =ᶠ[𝓝 x]
      triangularProfile L := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hx0, hx2⟩] with y hy
    exact (triangularProfile_eq_poly (le_of_lt hy.1) (le_of_lt hy.2)).symm
  exact (heq.deriv_eq).symm.trans hp.deriv

theorem triangularProfile_deriv_ae_eq {L : ℝ} (hL : 0 < L) :
    deriv (triangularProfile L) =ᵐ[volume]
      fun x ↦ if 0 < x ∧ x < 2 * L then
        6 * (2 * L - 2 * x) / (2 * L) ^ 3 else 0 := by
  have hbad : ∀ᵐ x : ℝ ∂volume, x ∉ ({0} ∪ {2 * L} : Set ℝ) := by
    rw [ae_iff]
    have hs : {x : ℝ | ¬ x ∉ ({0} ∪ {2 * L} : Set ℝ)} = ({0} ∪ {2 * L} : Set ℝ) := by
      ext x
      by_cases h : x = 2 * L <;> simp [h]
    rw [hs]
    exact (finite_singleton 0).union (finite_singleton (2 * L)) |>.measure_zero volume
  filter_upwards [hbad] with x hx
  have hx0ne : x ≠ 0 := by intro h; apply hx; simp [h]
  have hx2ne : x ≠ 2 * L := by intro h; apply hx; simp [h]
  by_cases hx0 : x ≤ 0
  · have hxlt : x < 0 := lt_of_le_of_ne hx0 (by intro he; exact hx0ne he)
    have hconst : triangularProfile L =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
      filter_upwards [Iic_mem_nhds hxlt] with y hy
      exact triangularProfile_eq_zero_of_nonpos hy
    rw [hconst.deriv_eq]
    simp [hx0]
  by_cases hx2 : 2 * L ≤ x
  · have hxgt : 2 * L < x := lt_of_le_of_ne hx2 (by intro he; exact hx2ne he.symm)
    have hconst : triangularProfile L =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
      filter_upwards [Ici_mem_nhds hxgt] with y hy
      exact triangularProfile_eq_zero_of_ge hL hy
    rw [hconst.deriv_eq]
    simp [hx2]
  · have hx0' : 0 < x := lt_of_not_ge hx0
    have hx2' : x < 2 * L := lt_of_not_ge hx2
    rw [triangularProfile_deriv_eq hL hx0' hx2']
    simp [hx0', hx2']

private theorem triangular_weak_local {L : ℝ} (hL : 0 < L)
    (hvalue : MemLp (triangularProfile L) 2 volume)
    (hderiv : MemLp (deriv (triangularProfile L)) 2 volume)
    (hac : AbsolutelyContinuousOnInterval (triangularProfile L) 0 (2 * L)) :
    ∀ φ : SchwartzMap ℝ ℝ,
      Analysis.l2Pairing (hvalue.toLp (triangularProfile L))
          (Analysis.schwartzDeriv φ) =
        -Analysis.l2Pairing (hderiv.toLp (deriv (triangularProfile L)))
          (Analysis.schwartzValue φ) := by
  intro φ
  have hφac : AbsolutelyContinuousOnInterval (φ : ℝ → ℝ) 0 (2 * L) := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    intro x hx
    exact (φ.contDiffAt 1).contDiffWithinAt
  have hparts := hac.integral_mul_deriv_eq_deriv_mul hφac
  rw [triangularProfile_eq_zero_of_nonpos (le_refl 0),
    triangularProfile_eq_zero_of_ge hL (le_refl (2 * L))] at hparts
  have hφ_memLp : MemLp (φ : ℝ → ℝ) 2 volume := φ.memLp 2 volume
  have hφd_memLp : MemLp (deriv (φ : ℝ → ℝ)) 2 volume :=
    (SchwartzMap.derivCLM ℝ ℝ φ).memLp 2 volume
  have hleftInt : Integrable (fun x => triangularProfile L x * deriv (φ : ℝ → ℝ) x) :=
    hvalue.integrable_mul hφd_memLp
  have hrightInt : Integrable (fun x => deriv (triangularProfile L) x * φ x) :=
    hderiv.integrable_mul hφ_memLp
  have h0L : 0 ≤ 2 * L := by linarith
  have hleft : Analysis.l2Pairing (hvalue.toLp (triangularProfile L))
      (Analysis.schwartzDeriv φ) = ∫ x in (0 : ℝ)..(2 * L), triangularProfile L x * deriv φ x := by
    rw [Analysis.l2Pairing, ContinuousLinearMap.lpPairing_eq_integral]
    have hnorm : (∫ x : ℝ, ((ContinuousLinearMap.mul ℝ ℝ)
        (((hvalue.toLp (triangularProfile L) : Analysis.RealL2) : ℝ → ℝ) x)
        (((Analysis.schwartzDeriv φ : Analysis.RealL2) : ℝ → ℝ) x)) ∂volume) =
        ∫ x : ℝ, triangularProfile L x * deriv (φ : ℝ → ℝ) x ∂volume := by
      apply integral_congr_ae
      filter_upwards [hvalue.coeFn_toLp,
        (SchwartzMap.derivCLM ℝ ℝ φ).coeFn_toLp 2 volume] with x hx hφx
      simp [Analysis.schwartzDeriv, Analysis.schwartzValue, hx, hφx]
    rw [hnorm]
    have hcomp : (∫ x in (Ioc (0 : ℝ) (2 * L))ᶜ,
        triangularProfile L x * deriv (φ : ℝ → ℝ) x) = 0 := by
      apply integral_eq_zero_of_ae
      refine (ae_restrict_iff' measurableSet_Ioc.compl).2 ?_
      filter_upwards with x hx
      change ¬ (0 < x ∧ x ≤ 2 * L) at hx
      rcases le_or_gt x 0 with hx0 | hx0
      · rw [triangularProfile_eq_zero_of_nonpos hx0]; simp
      · have hx2' : 2 * L < x := lt_of_not_ge (fun hx2 ↦ hx ⟨hx0, hx2⟩)
        rw [triangularProfile_eq_zero_of_ge hL hx2'.le]; simp
    have hdecomp := integral_add_compl (s := Ioc (0 : ℝ) (2 * L)) measurableSet_Ioc hleftInt
    rw [hcomp] at hdecomp
    have hz : ∫ x : ℝ, triangularProfile L x * deriv (φ : ℝ → ℝ) x =
        ∫ x in Ioc 0 (2 * L), triangularProfile L x * deriv (φ : ℝ → ℝ) x := by linarith
    rw [hz, ← intervalIntegral.integral_of_le h0L]
  have hright : Analysis.l2Pairing (hderiv.toLp (deriv (triangularProfile L)))
      (Analysis.schwartzValue φ) = ∫ x in (0 : ℝ)..(2 * L), deriv (triangularProfile L) x * φ x := by
    rw [Analysis.l2Pairing, ContinuousLinearMap.lpPairing_eq_integral]
    have hnorm : (∫ x : ℝ, ((ContinuousLinearMap.mul ℝ ℝ)
        (((hderiv.toLp (deriv (triangularProfile L)) : Analysis.RealL2) : ℝ → ℝ) x)
        (((Analysis.schwartzValue φ : Analysis.RealL2) : ℝ → ℝ) x)) ∂volume) =
        ∫ x : ℝ, deriv (triangularProfile L) x * φ x ∂volume := by
      apply integral_congr_ae
      filter_upwards [hderiv.coeFn_toLp, φ.coeFn_toLp 2 volume] with x hx hφx
      simp [Analysis.schwartzValue, hx, hφx]
    rw [hnorm]
    have hcomp : (∫ x in (Ioc (0 : ℝ) (2 * L))ᶜ,
        deriv (triangularProfile L) x * φ x) = 0 := by
      apply integral_eq_zero_of_ae
      refine (ae_restrict_iff' measurableSet_Ioc.compl).2 ?_
      filter_upwards [triangularProfile_deriv_ae_eq hL] with x hdx
      intro hx
      change ¬ (0 < x ∧ x ≤ 2 * L) at hx
      rcases le_or_gt x 0 with hx0 | hx0
      · rw [hdx]; simp [hx0]
      · have hx2' : 2 * L < x := lt_of_not_ge (fun hx2 ↦ hx ⟨hx0, hx2⟩)
        rw [hdx]
        simp [show ¬ (0 < x ∧ x < 2 * L) by intro h; exact (not_lt_of_ge hx2'.le) h.2]
    have hdecomp := integral_add_compl (s := Ioc (0 : ℝ) (2 * L)) measurableSet_Ioc hrightInt
    rw [hcomp] at hdecomp
    have hz : ∫ x : ℝ, deriv (triangularProfile L) x * φ x =
        ∫ x in Ioc 0 (2 * L), deriv (triangularProfile L) x * φ x := by linarith
    rw [hz, ← intervalIntegral.integral_of_le h0L]
  have hparts' : (∫ x in (0 : ℝ)..(2 * L), triangularProfile L x * deriv φ x) =
      -(∫ x in (0 : ℝ)..(2 * L), deriv (triangularProfile L) x * φ x) := by
    simpa using hparts
  rw [hleft, hright, hparts']

theorem triangularProfile_representativeData {L : ℝ} (hL : 0 < L) :
    Analysis.HalfLineRepresentativeData (triangularProfile L) := by
  let dL : ℝ → ℝ := fun x ↦
    if 0 < x ∧ x < 2 * L then 6 * (2 * L - 2 * x) / (2 * L) ^ 3 else 0
  have hvalue : MemLp (triangularProfile L) 2 volume := by
    apply (triangularProfile_continuous.memLp_of_hasCompactSupport ?_)
    refine HasCompactSupport.intro (K := Icc 0 (2 * L)) isCompact_Icc ?_
    intro x hx
    by_cases hx0 : x ≤ 0
    · exact triangularProfile_eq_zero_of_nonpos hx0
    · by_cases hx2 : 2 * L ≤ x
      · exact triangularProfile_eq_zero_of_ge hL hx2
      · exact False.elim (hx ⟨le_of_not_ge hx0, le_of_not_ge hx2⟩)
  have hdL_support : HasCompactSupport dL := by
    refine HasCompactSupport.intro (K := Icc 0 (2 * L)) isCompact_Icc ?_
    intro x hx
    simp only [dL]
    by_cases hx0 : x ≤ 0
    · simp [hx0]
    · by_cases hx2 : 2 * L ≤ x
      · simp [hx2]
      · exact False.elim (hx ⟨le_of_not_ge hx0, le_of_not_ge hx2⟩)
  have hdL_meas : AEStronglyMeasurable dL volume := by
    apply Measurable.aestronglyMeasurable
    dsimp [dL]
    apply Measurable.ite (measurableSet_Ioi.inter measurableSet_Iio)
    · fun_prop
    · exact measurable_const
  have hdL_bound : ∀ᵐ x : ℝ ∂volume, ‖dL x‖ ≤ 6 / (2 * L) ^ 2 + 1 := by
    filter_upwards with x
    simp only [dL]
    by_cases hx : 0 < x ∧ x < 2 * L
    · simp [hx]
      rw [abs_of_pos hL] at *
      have hden : 0 < (2 * L) ^ 3 := by positivity
      have hnum : |6 * (2 * L - 2 * x)| ≤ 12 * L := by
        rw [abs_mul]
        have : |2 * L - 2 * x| ≤ 2 * L := by
          rw [abs_le]
          constructor <;> linarith [hL]
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
        nlinarith
      calc
        6 * |2 * L - 2 * x| / (2 * L) ^ 3 ≤ 12 * L / (2 * L) ^ 3 := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)] at hnum
          exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
        _ = 6 / (2 * L) ^ 2 := by field_simp; ring
        _ ≤ 6 / (2 * L) ^ 2 + 1 := by linarith
    · simp [hx, norm_zero]
      positivity
  have hdL_memLp : MemLp dL 2 volume :=
    hdL_support.memLp_of_bound hdL_meas (6 / (2 * L) ^ 2 + 1) hdL_bound
  have hderiv : MemLp (deriv (triangularProfile L)) 2 volume := by
    apply hdL_memLp.ae_eq
    exact (triangularProfile_deriv_ae_eq hL).symm
  have hac_of_R (R : ℝ) (hR : 0 < R) :
      AbsolutelyContinuousOnInterval (triangularProfile L) 0 R := by
    have hp : AbsolutelyContinuousOnInterval (fun x : ℝ ↦ max x 0) 0 R := by
      exact (LipschitzWith.id.max_const 0).lipschitzOnWith.absolutelyContinuousOnInterval
    have hq : AbsolutelyContinuousOnInterval
        (fun x : ℝ ↦ max (2 * L - x) 0) 0 R := by
      have hbase := (LipschitzWith.const (2 * L)).sub LipschitzWith.id
      exact hbase.max_const 0 |>.lipschitzOnWith.absolutelyContinuousOnInterval
    have hmul := hp.mul hq
    have hac' := hmul.const_mul (6 / (2 * L) ^ 3)
    have heq : (fun x : ℝ => 6 * max x 0 * max (2 * L - x) 0 / (2 * L) ^ 3) =
        (fun x => 6 / (2 * L) ^ 3 * (max x 0 * max (2 * L - x) 0)) := by
      funext x
      ring
    rw [show triangularProfile L = fun x =>
      6 * max x 0 * max (2 * L - x) 0 / (2 * L) ^ 3 by rfl, heq]
    exact hac'
  have hweak : ∀ φ : SchwartzMap ℝ ℝ,
      Analysis.l2Pairing (hvalue.toLp (triangularProfile L)) (Analysis.schwartzDeriv φ) =
        -Analysis.l2Pairing (hderiv.toLp (deriv (triangularProfile L)))
          (Analysis.schwartzValue φ) := by
    intro φ
    exact triangular_weak_local hL hvalue hderiv (hac_of_R (2 * L) (by linarith)) φ
  refine {
    trace_zero := ?_,
    locally_absolutelyContinuous := hac_of_R,
    value_memLp := hvalue,
    deriv_memLp := hderiv,
    value_ae_eq_zero_on_nonpositive := ?_,
    deriv_ae_eq_zero_on_nonpositive := ?_,
    weakDerivative_identity := hweak }
  · exact triangularProfile_eq_zero_of_nonpos (L := L) (x := 0) (le_refl 0)
  · filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [triangularProfile_eq_zero_of_nonpos hx]
    rfl
  · have hdx' : deriv (triangularProfile L) =ᵐ[volume.restrict (Iic 0)]
        (fun x => if 0 < x ∧ x < 2 * L then
          6 * (2 * L - 2 * x) / (2 * L) ^ 3 else 0) := by
      exact (triangularProfile_deriv_ae_eq hL).filter_mono ae_restrict_le
    filter_upwards [hdx', ae_restrict_mem measurableSet_Iic] with x hdx hx
    change x ≤ 0 at hx
    rw [hdx]
    simp [hx]

def Analysis.HalfLineH1.triangular (L : ℝ) (hL : 0 < L) : Analysis.HalfLineH1 :=
  Analysis.HalfLineH1.ofRepresentative (triangularProfile L)
    (triangularProfile_representativeData hL)

theorem Analysis.HalfLineH1.continuousRep_triangular {L : ℝ} (hL : 0 < L)
    {x : ℝ} (hx : x ∈ Ici 0) :
    Analysis.HalfLineH1.continuousRep (Analysis.HalfLineH1.triangular L hL) x =
      triangularProfile L x := by
  apply Analysis.HalfLineH1.continuousRep_ofRepresentative
    (triangularProfile L) (triangularProfile_representativeData hL) hx

private theorem triangular_poly_integral {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..(2 * L), 6 * x * (2 * L - x) / (2 * L) ^ 3) = 1 := by
  let F : ℝ → ℝ := fun x ↦ (6 * L * x ^ 2 - 2 * x ^ 3) / (2 * L) ^ 3
  have h0L : 0 ≤ 2 * L := by linarith
  have hcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hint : IntervalIntegrable (fun x : ℝ ↦ 6 * x * (2 * L - x) / (2 * L) ^ 3)
      volume 0 (2 * L) := by
    have hc : Continuous (fun x : ℝ ↦ 6 * x * (2 * L - x) / (2 * L) ^ 3) := by fun_prop
    exact hc.intervalIntegrable 0 (2 * L)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (2 * L),
      HasDerivAt F (6 * x * (2 * L - x) / (2 * L) ^ 3) x := by
    intro x hx
    dsimp [F]
    convert (((hasDerivAt_const x (6 * L)).mul ((hasDerivAt_id x).pow 2)).sub
      ((hasDerivAt_const x 2).mul ((hasDerivAt_id x).pow 3))).div_const ((2 * L) ^ 3) using 1 <;>
      (dsimp <;> ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0L hcont.continuousOn hderiv hint]
  dsimp [F]
  have hden : (2 * L) ^ 3 ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) hL.ne')
  field_simp [hden]
  ring

private theorem triangular_weighted_poly_integral {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..(2 * L), x * (6 * x * (2 * L - x) / (2 * L) ^ 3)) = L := by
  let G : ℝ → ℝ := fun x ↦ (8 * L * x ^ 3 - 3 * x ^ 4) / (2 * (2 * L) ^ 3)
  have h0L : 0 ≤ 2 * L := by linarith
  have hcont : Continuous G := by
    dsimp [G]
    fun_prop
  have hint : IntervalIntegrable (fun x : ℝ ↦ x * (6 * x * (2 * L - x) / (2 * L) ^ 3))
      volume 0 (2 * L) := by
    have hc : Continuous (fun x : ℝ ↦ x * (6 * x * (2 * L - x) / (2 * L) ^ 3)) := by fun_prop
    exact hc.intervalIntegrable 0 (2 * L)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (2 * L),
      HasDerivAt G (x * (6 * x * (2 * L - x) / (2 * L) ^ 3)) x := by
    intro x hx
    dsimp [G]
    convert (((hasDerivAt_const x (8 * L)).mul ((hasDerivAt_id x).pow 3)).sub
      ((hasDerivAt_const x 3).mul ((hasDerivAt_id x).pow 4))).div_const (2 * (2 * L) ^ 3) using 1 <;>
      (dsimp <;> ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0L hcont.continuousOn hderiv hint]
  dsimp [G]
  have hden : (2 * (2 * L) ^ 3) ≠ 0 := by positivity
  field_simp [hden]
  ring

private theorem triangular_square_poly_integral {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..(2 * L), (6 * x * (2 * L - x) / (2 * L) ^ 3) ^ 2) =
      3 / (5 * L) := by
  let F : ℝ → ℝ := fun x ↦
    (48 * L ^ 2 * x ^ 3 - 36 * L * x ^ 4 + (36 / 5) * x ^ 5) / (2 * L) ^ 6
  have h0L : 0 ≤ 2 * L := by linarith
  have hcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hint : IntervalIntegrable
      (fun x : ℝ => (6 * x * (2 * L - x) / (2 * L) ^ 3) ^ 2)
      volume 0 (2 * L) := by
    have hc : Continuous
        (fun x : ℝ => (6 * x * (2 * L - x) / (2 * L) ^ 3) ^ 2) := by fun_prop
    exact hc.intervalIntegrable 0 (2 * L)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (2 * L),
      HasDerivAt F ((6 * x * (2 * L - x) / (2 * L) ^ 3) ^ 2) x := by
    intro x hx
    dsimp [F]
    convert (((hasDerivAt_const x (48 * L ^ 2)).mul ((hasDerivAt_id x).pow 3)).sub
      (((hasDerivAt_const x 36).mul (hasDerivAt_const x L)).mul
        ((hasDerivAt_id x).pow 4))).add
      ((hasDerivAt_const x (36 / 5)).mul ((hasDerivAt_id x).pow 5)) |>.div_const
      ((2 * L) ^ 6) using 1 <;> (dsimp <;> field_simp [hL.ne'] <;> ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0L hcont.continuousOn
    hderiv hint]
  dsimp [F]
  have hden : (2 * L) ^ 6 ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) hL.ne')
  field_simp [hden]
  ring

private theorem triangular_derivative_square_poly_integral {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..(2 * L), (6 * (2 * L - 2 * x) / (2 * L) ^ 3) ^ 2) =
      3 / (2 * L ^ 3) := by
  let F : ℝ → ℝ := fun x ↦
    (144 * L ^ 2 * x - 144 * L * x ^ 2 + 48 * x ^ 3) / (2 * L) ^ 6
  have h0L : 0 ≤ 2 * L := by linarith
  have hcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hint : IntervalIntegrable
      (fun x : ℝ => (6 * (2 * L - 2 * x) / (2 * L) ^ 3) ^ 2)
      volume 0 (2 * L) := by
    have hc : Continuous
        (fun x : ℝ => (6 * (2 * L - 2 * x) / (2 * L) ^ 3) ^ 2) := by fun_prop
    exact hc.intervalIntegrable 0 (2 * L)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) (2 * L),
      HasDerivAt F ((6 * (2 * L - 2 * x) / (2 * L) ^ 3) ^ 2) x := by
    intro x hx
    dsimp [F]
    convert ((((hasDerivAt_const x (144 * L ^ 2)).mul (hasDerivAt_id x)).sub
      ((hasDerivAt_const x (144 * L)).mul ((hasDerivAt_id x).pow 2))).add
      ((hasDerivAt_const x 48).mul ((hasDerivAt_id x).pow 3))).div_const
        ((2 * L) ^ 6) using 1 <;> (dsimp [id] <;> field_simp [hL.ne'] <;> ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0L hcont.continuousOn
    hderiv hint]
  dsimp [F]
  have hden : (2 * L) ^ 6 ≠ 0 := pow_ne_zero _ (mul_ne_zero (by norm_num) hL.ne')
  field_simp [hden]
  ring

private theorem triangularProfile_square_integrableOn {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun x => triangularProfile L x ^ 2) halfLine := by
  exact (triangularProfile_representativeData hL).value_memLp.integrable_sq.integrableOn

private theorem triangularProfile_derivative_square_integrableOn {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun x => deriv (triangularProfile L) x ^ 2) halfLine := by
  exact (triangularProfile_representativeData hL).deriv_memLp.integrable_sq.integrableOn

theorem triangularProfile_squareEnergy {L : ℝ} (hL : 0 < L) :
    squareEnergy (triangularProfile L) = 3 / (5 * L) := by
  have h0L : 0 ≤ 2 * L := by linarith
  have hfull := triangularProfile_square_integrableOn hL
  have htail := hfull.mono_set (Ici_subset_Ici.2 (by linarith : 0 ≤ 2 * L))
  have hz : (∫ x in Ici (2 * L), triangularProfile L x ^ 2) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ici (2 * L)) measurableSet_Ici] with x hx
    rw [triangularProfile_eq_zero_of_ge hL hx]
    simp
  have hsplit := intervalIntegral.integral_Ici_sub_Ici' hfull htail
  have hpoly : (∫ x in (0 : ℝ)..(2 * L), triangularProfile L x ^ 2) =
      ∫ x in (0 : ℝ)..(2 * L), (6 * x * (2 * L - x) / (2 * L) ^ 3) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    have hx' : x ∈ Ioc 0 (2 * L) := by simpa [uIoc_of_le h0L] using hx
    rw [triangularProfile_eq_poly hx'.1.le hx'.2]
  rw [squareEnergy, halfLine]
  linarith [hsplit, hpoly, triangular_square_poly_integral hL]

theorem triangularProfile_dirichletEnergy {L : ℝ} (hL : 0 < L) :
    dirichletEnergy (triangularProfile L) = 3 / (2 * L ^ 3) := by
  have h0L : 0 ≤ 2 * L := by linarith
  have hfull := triangularProfile_derivative_square_integrableOn hL
  have htail := hfull.mono_set (Ici_subset_Ici.2 (by linarith : 0 ≤ 2 * L))
  have hz : (∫ x in Ici (2 * L), deriv (triangularProfile L) x ^ 2) = 0 := by
    apply integral_eq_zero_of_ae
    refine (ae_restrict_iff' (μ := volume) measurableSet_Ici).2 ?_
    filter_upwards [triangularProfile_deriv_ae_eq hL] with x hdx hx
    rw [hdx]
    have hnot : ¬ (0 < x ∧ x < 2 * L) := by
      intro h
      exact (not_lt_of_ge hx) h.2
    simp [hnot]
  have hsplit := intervalIntegral.integral_Ici_sub_Ici' hfull htail
  have hpoly : (∫ x in (0 : ℝ)..(2 * L), deriv (triangularProfile L) x ^ 2) =
      ∫ x in (0 : ℝ)..(2 * L), (6 * (2 * L - 2 * x) / (2 * L) ^ 3) ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    have hbad : ∀ᵐ x : ℝ ∂volume, x ≠ 0 ∧ x ≠ 2 * L := by
      rw [ae_iff]
      have hs : {x : ℝ | ¬ (x ≠ 0 ∧ x ≠ 2 * L)} = ({0} ∪ {2 * L} : Set ℝ) := by
        ext x
        simp only [not_and_or, not_ne_iff, mem_ofPred_eq, mem_union, mem_singleton_iff]
      rw [hs]
      exact (finite_singleton 0).union (finite_singleton (2 * L)) |>.measure_zero volume
    filter_upwards [hbad, triangularProfile_deriv_ae_eq hL] with x hne hx
    intro hxI
    have hx' : x ∈ Ioc (0 : ℝ) (2 * L) := by
      simpa [uIoc_of_le h0L] using hxI
    rw [hx]
    have hinside : 0 < x ∧ x < 2 * L :=
      ⟨hx'.1, lt_of_le_of_ne hx'.2 hne.2⟩
    simp [hinside]
  rw [dirichletEnergy, halfLine]
  linarith [hsplit, hpoly, triangular_derivative_square_poly_integral hL]

theorem triangularProfile_rayleighQuotient {L : ℝ} (hL : 0 < L) :
    rayleighQuotient (triangularProfile L) = 5 / (2 * L ^ 2) := by
  rw [rayleighQuotient, triangularProfile_dirichletEnergy hL,
    triangularProfile_squareEnergy hL]
  field_simp

theorem Analysis.HalfLineH1.squareEnergy_triangular {L : ℝ} (hL : 0 < L) :
    (Analysis.HalfLineH1.triangular L hL).squareEnergy = 3 / (5 * L) := by
  rw [← (Analysis.HalfLineH1.triangular L hL).squareEnergy_continuousRep]
  rw [← triangularProfile_squareEnergy hL]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  rw [Analysis.HalfLineH1.continuousRep_triangular hL hx]

theorem Analysis.HalfLineH1.dirichletEnergy_triangular {L : ℝ} (hL : 0 < L) :
    (Analysis.HalfLineH1.triangular L hL).dirichletEnergy = 3 / (2 * L ^ 3) := by
  rw [← (Analysis.HalfLineH1.triangular L hL).dirichletEnergy_continuousRep]
  rw [← triangularProfile_dirichletEnergy hL]
  apply integral_congr_ae
  have hweak := Analysis.HalfLineH1.weakDeriv_ofRepresentative_ae_eq
      (triangularProfile L) (triangularProfile_representativeData hL)
  have hderiv := Analysis.HalfLineH1.deriv_continuousRep_ae
      (Analysis.HalfLineH1.triangular L hL)
  filter_upwards [hderiv.filter_mono ae_restrict_le,
    hweak.filter_mono ae_restrict_le] with x hx1 hx2
  exact congrArg (fun z => z ^ 2) (hx1.trans hx2)

theorem Analysis.HalfLineH1.rayleighQuotient_triangular {L : ℝ} (hL : 0 < L) :
    (Analysis.HalfLineH1.triangular L hL).rayleighQuotient = 5 / (2 * L ^ 2) := by
  rw [rayleighQuotient, Analysis.HalfLineH1.dirichletEnergy_triangular hL,
    Analysis.HalfLineH1.squareEnergy_triangular hL]
  field_simp

theorem triangularProfile_firstMoment_integrableOn {L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun x ↦ x * triangularProfile L x) halfLine := by
  have hc : Continuous (fun x : ℝ ↦ x * triangularProfile L x) :=
    continuous_id.mul triangularProfile_continuous
  have hs : HasCompactSupport (fun x : ℝ ↦ x * triangularProfile L x) := by
    refine HasCompactSupport.intro (K := Icc 0 (2 * L)) isCompact_Icc ?_
    intro x hx
    by_cases hx0 : x ≤ 0
    · rw [triangularProfile_eq_zero_of_nonpos hx0, mul_zero]
    · by_cases hx2 : 2 * L ≤ x
      · rw [triangularProfile_eq_zero_of_ge hL hx2, mul_zero]
      · exact False.elim (hx ⟨le_of_not_ge hx0, le_of_not_ge hx2⟩)
  exact (hc.integrable_of_hasCompactSupport hs).integrableOn

theorem triangularProfile_mass {L : ℝ} (hL : 0 < L) :
    mass (triangularProfile L) = 1 := by
  have h0L : 0 ≤ 2 * L := by linarith
  have hfull := triangularProfile_integrableOn hL
  have htail : IntegrableOn (triangularProfile L) (Ici (2 * L)) :=
    hfull.mono_set (Ici_subset_Ici.2 (by linarith))
  have hz : (∫ x in Ici (2 * L), triangularProfile L x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ici (2 * L)) measurableSet_Ici] with x hx
    simpa [zero_apply] using triangularProfile_eq_zero_of_ge hL hx
  have hsplit := intervalIntegral.integral_Ici_sub_Ici' hfull htail
  rw [hz] at hsplit
  have hpoly : (∫ x in (0 : ℝ)..(2 * L), triangularProfile L x) =
      ∫ x in (0 : ℝ)..(2 * L), 6 * x * (2 * L - x) / (2 * L) ^ 3 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    apply triangularProfile_eq_poly
    · have hx' : x ∈ Ioc 0 (2 * L) := by simpa [uIoc_of_le h0L] using hx
      exact hx'.1.le
    · have hx' : x ∈ Ioc 0 (2 * L) := by simpa [uIoc_of_le h0L] using hx
      exact hx'.2
  rw [mass, halfLine]
  linarith [hsplit, hpoly, triangular_poly_integral hL]

theorem triangularProfile_firstMoment {L : ℝ} (hL : 0 < L) :
    firstMoment (triangularProfile L) = L := by
  have h0L : 0 ≤ 2 * L := by linarith
  have hfull := triangularProfile_firstMoment_integrableOn hL
  have htail : IntegrableOn (fun x => x * triangularProfile L x) (Ici (2 * L)) :=
    hfull.mono_set (Ici_subset_Ici.2 (by linarith))
  have hz : (∫ x in Ici (2 * L), x * triangularProfile L x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ici (2 * L)) measurableSet_Ici] with x hx
    simpa [zero_apply] using congrArg (fun y => x * y) (triangularProfile_eq_zero_of_ge hL hx)
  have hsplit := intervalIntegral.integral_Ici_sub_Ici' hfull htail
  rw [hz] at hsplit
  have hpoly : (∫ x in (0 : ℝ)..(2 * L), x * triangularProfile L x) =
      ∫ x in (0 : ℝ)..(2 * L), x * (6 * x * (2 * L - x) / (2 * L) ^ 3) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    have hx' : x ∈ Ioc 0 (2 * L) := by simpa [uIoc_of_le h0L] using hx
    rw [triangularProfile_eq_poly hx'.1.le hx'.2]
  rw [firstMoment, halfLine]
  linarith [hsplit, hpoly, triangular_weighted_poly_integral hL]

theorem Analysis.HalfLineH1.triangular_isAdmissible {L : ℝ} (hL : 0 < L) :
    (Analysis.HalfLineH1.triangular L hL).IsAdmissible L := by
  let u := Analysis.HalfLineH1.triangular L hL
  have hrep : u.continuousRep =ᵐ[volume.restrict halfLine] triangularProfile L := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    exact Analysis.HalfLineH1.continuousRep_triangular hL hx
  have hi : IntegrableOn u.continuousRep halfLine := by
    apply (triangularProfile_integrableOn hL).congr
    exact hrep.symm
  have hm : IntegrableOn (fun x => x * u.continuousRep x) halfLine := by
    have hmul : (fun x => x * u.continuousRep x) =ᵐ[volume.restrict halfLine]
        (fun x => x * triangularProfile L x) := by
      filter_upwards [hrep] with x hx
      rw [hx]
    apply (triangularProfile_firstMoment_integrableOn hL).congr
    exact hmul.symm
  refine {
    nonnegative := ?_,
    integrable := hi,
    firstMoment_integrable := hm,
    mass_eq := ?_,
    firstMoment_eq := ?_ }
  · intro x hx
    change x ∈ Ici 0 at hx
    rw [Analysis.HalfLineH1.continuousRep_triangular hL hx]
    exact triangularProfile_nonnegative hL.le
  · change (∫ x in halfLine, u.continuousRep x) = 1
    rw [integral_congr_ae hrep]
    change RayleighKernel.mass (triangularProfile L) = 1
    exact triangularProfile_mass hL
  · change (∫ x in halfLine, x * u.continuousRep x) = L
    have hmul : (fun x => x * u.continuousRep x) =ᵐ[volume.restrict halfLine]
        (fun x => x * triangularProfile L x) := by
      filter_upwards [hrep] with x hx
      rw [hx]
    rw [integral_congr_ae hmul]
    change RayleighKernel.firstMoment (triangularProfile L) = L
    exact triangularProfile_firstMoment hL

theorem Analysis.admissibleQuotients_nonempty_of_pos {L : ℝ} (hL : 0 < L) :
    (Analysis.admissibleQuotients L).Nonempty := by
  exact Analysis.admissibleQuotients_nonempty
    (Analysis.HalfLineH1.triangular_isAdmissible hL)

end RayleighKernel
