import RayleighKernel.Probability.Kurtosis
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Finite weighted triangular-array sums

This module records the characteristic-function factorization used by the
weighted triangular-array CLT.  It also records a uniform cubic remainder
bound for the scalar characteristic-function integrand and the resulting
normalized diffuse weighted triangular-array convergence in distribution.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open Filter
open scoped BigOperators
open scoped Topology

namespace RayleighKernel.Probability

def weightedFinsetSum {Ω ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ i ∈ s, a i * X i ω

/-- Exact characteristic-function product formula for a finite weighted row.

The independence hypothesis is stated for the already weighted coordinates;
this is the form directly consumed by the characteristic-function API and is
also convenient for triangular-array rows whose coefficients vary with the
row. -/
theorem charFun_weightedFinsetSum_eq_prod
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {s : Finset ι} {a : ι → ℝ} {X : ι → Ω → ℝ}
    (mX : ∀ i ∈ s, AEMeasurable (X i) P)
    (hX : iIndepFun (s.restrict (fun i => a i • X i)) P) :
    charFun (P.map (weightedFinsetSum s a X)) =
      ∏ i ∈ s, charFun (P.map (a i • X i)) := by
  rw [show weightedFinsetSum s a X =
      fun ω => ∑ i ∈ s, (a i • X i) ω by
    funext ω
    simp [weightedFinsetSum, smul_eq_mul]]
  exact hX.charFun_map_fun_finsetSum_eq_prod
    (fun i hi => (mX i hi).const_mul (a i))

private lemma cubic_exp_remainder (x : ℝ) :
    ‖Complex.exp (Complex.I * x) -
        (1 + Complex.I * x - (x : ℂ)^2 / 2)‖ ≤
      (4 + Real.exp 1) * |x| ^ 3 := by
  have hpoly : (∑ m ∈ Finset.range 3, (Complex.I * x) ^ m / m.factorial) =
      1 + Complex.I * x - (x : ℂ)^2 / 2 := by
    norm_num [Finset.sum_range_succ]
    rw [show (Complex.I * (x : ℂ)) ^ 2 = -(x : ℂ)^2 by
      rw [mul_pow, Complex.I_sq, neg_mul, one_mul]]
    ring
  by_cases hx : |x| ≤ 1
  · have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (Complex.I * x) 3
    rw [hpoly] at h
    calc
      _ ≤ |x| ^ 3 * Real.exp |x| := by simpa using h
      _ ≤ Real.exp 1 * |x| ^ 3 := by
        calc
          _ = Real.exp |x| * |x| ^ 3 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx)
            (pow_nonneg (abs_nonneg x) 3)
      _ ≤ (4 + Real.exp 1) * |x| ^ 3 := by
        exact mul_le_mul_of_nonneg_right (by nlinarith [Real.exp_pos 1])
          (pow_nonneg (abs_nonneg x) 3)
  · have hx' : 1 ≤ |x| := le_of_not_ge hx
    calc
      _ ≤ ‖Complex.exp (Complex.I * x)‖ +
          ‖1 + Complex.I * x - (x : ℂ)^2 / 2‖ := norm_sub_le _ _
      _ ≤ 1 + (1 + |x| + |x| ^ 2 / 2) := by
        have he : ‖Complex.exp (Complex.I * x)‖ = 1 := by
          rw [Complex.norm_exp]
          simp
        rw [he]
        gcongr
        calc
          ‖1 + Complex.I * x - (x : ℂ)^2 / 2‖ ≤
              ‖(1 : ℂ)‖ + ‖Complex.I * x‖ + ‖(x : ℂ)^2 / 2‖ := by
            rw [show (1 : ℂ) + Complex.I * x - (x : ℂ)^2 / 2 =
                1 + (Complex.I * x) + -((x : ℂ)^2 / 2) by ring]
            calc
              _ ≤ ‖1 + Complex.I * x‖ + ‖-((x : ℂ)^2 / 2)‖ := norm_add_le _ _
              _ ≤ (‖(1 : ℂ)‖ + ‖Complex.I * x‖) +
                  ‖(x : ℂ)^2 / 2‖ := by
                calc
                  _ ≤ ‖1 + Complex.I * x‖ + ‖(x : ℂ)^2 / 2‖ := by rw [norm_neg]
                  _ ≤ _ := by
                    have h := add_le_add_right (norm_add_le (1 : ℂ) (Complex.I * x))
                      ‖(x : ℂ)^2 / 2‖
                    simpa [add_assoc, add_left_comm, add_comm] using h
          _ = 1 + |x| + |x| ^ 2 / 2 := by simp
      _ ≤ (4 + Real.exp 1) * |x| ^ 3 := by
        have h4 : 2 + |x| + |x| ^ 2 / 2 ≤ 4 * |x| ^ 3 := by
          nlinarith [sq_nonneg (|x| - 1), sq_nonneg |x|]
        nlinarith [Real.exp_pos 1]

/-- Integrated cubic characteristic-function remainder estimate.

The hypotheses are deliberately expressed as integrability of the two
complex-valued terms and of the third absolute moment, so the lemma can be
used for arbitrary finite rows without introducing an auxiliary `MemLp`
package. -/
theorem integral_charFun_cubic_remainder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} (t : ℝ)
    (_hX : AEMeasurable X P)
    (h0 : Integrable (fun ω => Complex.exp (Complex.I * (t * X ω))) P)
    (h1 : Integrable (fun ω => 1 + Complex.I * (t * X ω) -
      (t * X ω : ℂ)^2 / 2) P)
    (h3 : Integrable (fun ω => |X ω| ^ 3) P) :
    ‖(∫ ω, Complex.exp (Complex.I * (t * X ω)) ∂P) -
        ∫ ω, (1 + Complex.I * (t * X ω) - (t * X ω : ℂ)^2 / 2) ∂P‖ ≤
      (4 + Real.exp 1) * |t| ^ 3 * (∫ ω, |X ω| ^ 3 ∂P) := by
  rw [← integral_sub h0 h1]
  calc
    ‖∫ ω, (Complex.exp (Complex.I * (t * X ω)) -
        (1 + Complex.I * (t * X ω) - (t * X ω : ℂ)^2 / 2)) ∂P‖ ≤
        ∫ ω, ‖Complex.exp (Complex.I * (t * X ω)) -
          (1 + Complex.I * (t * X ω) - (t * X ω : ℂ)^2 / 2)‖ ∂P :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ((4 + Real.exp 1) * |t * X ω| ^ 3) ∂P := by
      rw [show (fun ω => (4 + Real.exp 1) * |t * X ω| ^ 3) =
          (fun ω => ((4 + Real.exp 1) * |t| ^ 3) * |X ω| ^ 3) by
        funext ω
        rw [abs_mul, mul_pow]
        ring]
      apply integral_mono_ae (h0.sub h1).norm
        (h3.const_mul ((4 + Real.exp 1) * |t| ^ 3))
      filter_upwards [] with ω
      simpa [abs_mul, mul_pow, mul_assoc, mul_left_comm, mul_comm] using
        (cubic_exp_remainder (t * X ω))
    _ = (4 + Real.exp 1) * |t| ^ 3 * (∫ ω, |X ω| ^ 3 ∂P) := by
      rw [show (fun ω => (4 + Real.exp 1) * |t * X ω| ^ 3) =
          (fun ω => ((4 + Real.exp 1) * |t| ^ 3) * |X ω| ^ 3) by
        funext ω
        rw [abs_mul, mul_pow]
        ring]
      rw [integral_const_mul]

private lemma quadratic_char_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ}
    (h1 : Integrable X P)
    (h2i : Integrable (fun ω => X ω ^ 2) P)
    (h0 : P[X] = 0)
    (h2 : P[X ^ 2] = 1)
    (u : ℝ) :
    (∫ ω, (1 : ℂ) + Complex.I * (u * X ω) -
        (u * X ω : ℂ)^2 / 2 ∂P) = 1 - (u : ℂ)^2 / 2 := by
  have hconst : Integrable (fun _ : Ω => (1 : ℂ)) P :=
    integrable_const (μ := P) (1 : ℂ)
  have hXc : Integrable (fun ω => (X ω : ℂ)) P :=
    (h1.ofReal : Integrable (fun ω => (X ω : ℂ)) P)
  have hX2c : Integrable (fun ω => ((X ω ^ 2 : ℝ) : ℂ)) P :=
    (h2i.ofReal : Integrable (fun ω => ((X ω ^ 2 : ℝ) : ℂ)) P)
  have hlin : Integrable (fun ω => Complex.I * ((u : ℂ) * (X ω : ℂ))) P :=
    (hXc.const_mul (u : ℂ)).const_mul Complex.I
  have hsq : Integrable (fun ω => ((u : ℂ)^2 / 2) *
      ((X ω ^ 2 : ℝ) : ℂ)) P :=
    hX2c.const_mul ((u : ℂ)^2 / 2)
  have hquad_eq :
      (fun ω => (1 : ℂ) + Complex.I * (u * X ω) -
        (u * X ω : ℂ)^2 / 2) =
      (fun ω => (1 : ℂ) + Complex.I * ((u : ℂ) * (X ω : ℂ)) -
        ((u : ℂ)^2 / 2) * ((X ω ^ 2 : ℝ) : ℂ)) := by
    funext ω
    push_cast
    ring
  have hlin_int :
      (∫ ω, Complex.I * ((u : ℂ) * (X ω : ℂ)) ∂P) = 0 := by
    rw [integral_const_mul, integral_const_mul, integral_complex_ofReal, h0]
    simp
  have h2' : (∫ ω, X ω ^ 2 ∂P) = 1 := by
    simpa only [Pi.pow_apply] using h2
  have hsq_int :
      (∫ ω, ((u : ℂ)^2 / 2) * ((X ω ^ 2 : ℝ) : ℂ) ∂P) =
        (u : ℂ)^2 / 2 := by
    rw [integral_const_mul, integral_complex_ofReal, h2']
    norm_num
  rw [hquad_eq]
  calc
    _ = (∫ ω, (1 : ℂ) + Complex.I * ((u : ℂ) * (X ω : ℂ)) ∂P) -
        ∫ ω, ((u : ℂ)^2 / 2) * ((X ω ^ 2 : ℝ) : ℂ) ∂P := by
      exact integral_sub (hconst.add hlin) hsq
    _ = ((∫ ω, (1 : ℂ) ∂P) +
        ∫ ω, Complex.I * ((u : ℂ) * (X ω : ℂ)) ∂P) -
        ∫ ω, ((u : ℂ)^2 / 2) * ((X ω ^ 2 : ℝ) : ℂ) ∂P := by
      rw [integral_add hconst hlin]
    _ = 1 - (u : ℂ)^2 / 2 := by
      rw [integral_const, hlin_int, hsq_int]
      norm_num

theorem charFun_centered_unit_cubic_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : AEMeasurable X P)
    (h1 : Integrable X P)
    (h2i : Integrable (fun ω => X ω ^ 2) P)
    (h3 : Integrable (fun ω => |X ω| ^ 3) P)
    (h0 : P[X] = 0) (h2 : P[X ^ 2] = 1) (u : ℝ) :
    ‖charFun (P.map X) u - (1 - (u : ℂ)^2 / 2)‖ ≤
      (4 + Real.exp 1) * |u|^3 * (∫ ω, |X ω|^3 ∂P) := by
  have hexp : Integrable (fun ω => Complex.exp (Complex.I * (u * X ω))) P := by
    apply (integrable_const (μ := P) (1 : ℝ)).mono
    · fun_prop
    filter_upwards [] with ω
    rw [Complex.norm_exp]
    simp
  have hquad : Integrable (fun ω =>
      1 + Complex.I * (u * X ω) - (u * X ω : ℂ)^2 / 2) P := by
    have hXc : Integrable (fun ω => (X ω : ℂ)) P :=
      (h1.ofReal : Integrable (fun ω => (X ω : ℂ)) P)
    have hX2c : Integrable (fun ω => ((X ω ^ 2 : ℝ) : ℂ)) P :=
      (h2i.ofReal : Integrable (fun ω => ((X ω ^ 2 : ℝ) : ℂ)) P)
    have hlin : Integrable (fun ω => Complex.I * ((u : ℂ) * (X ω : ℂ))) P :=
      (hXc.const_mul (u : ℂ)).const_mul Complex.I
    have hsq : Integrable (fun ω => ((u : ℂ)^2 / 2) *
        ((X ω ^ 2 : ℝ) : ℂ)) P :=
      hX2c.const_mul ((u : ℂ)^2 / 2)
    have hquad_eq :
        (fun ω => 1 + Complex.I * (u * X ω) - (u * X ω : ℂ)^2 / 2) =
        (fun ω => (1 : ℂ) + Complex.I * ((u : ℂ) * (X ω : ℂ)) -
          ((u : ℂ)^2 / 2) * ((X ω ^ 2 : ℝ) : ℂ)) := by
      funext ω
      push_cast
      ring
    rw [hquad_eq]
    exact ((integrable_const (μ := P) (1 : ℂ)).add hlin).sub hsq
  have hi := integral_charFun_cubic_remainder u hX hexp hquad h3
  have hchar : charFun (P.map X) u =
      ∫ ω, Complex.exp (Complex.I * (u * X ω)) ∂P := by
    rw [charFun_apply_real, integral_map hX (by fun_prop)]
    congr with ω
    ring_nf
  have hpoly := quadratic_char_integral h1 h2i h0 h2 u
  calc
    ‖charFun (P.map X) u - (1 - (u : ℂ)^2 / 2)‖ =
        ‖(∫ ω, Complex.exp (Complex.I * (u * X ω)) ∂P) -
          (∫ ω, (1 + Complex.I * (u * X ω) -
            (u * X ω : ℂ)^2 / 2) ∂P)‖ := by rw [hchar, ← hpoly]
      _ ≤ (4 + Real.exp 1) * |u| ^ 3 * (∫ ω, |X ω| ^ 3 ∂P) := hi

private lemma norm_prod_sub_prod_le_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      simp only [Finset.sum_insert hi]
      have hfi := hf i (Finset.mem_insert_self i s)
      have hgi := hg i (Finset.mem_insert_self i s)
      have hfs : ∀ j ∈ s, ‖f j‖ ≤ 1 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      have hgs : ∀ j ∈ s, ‖g j‖ ≤ 1 := fun j hj => hg j (Finset.mem_insert_of_mem hj)
      calc
        ‖f i * (∏ j ∈ s, f j) - g i * ∏ j ∈ s, g j‖ =
            ‖f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) +
              (f i - g i) * ∏ j ∈ s, g j‖ := by ring_nf
        _ ≤ ‖f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j)‖ +
              ‖(f i - g i) * ∏ j ∈ s, g j‖ := norm_add_le _ _
        _ = ‖f i‖ * ‖(∏ j ∈ s, f j) - ∏ j ∈ s, g j‖ +
              ‖f i - g i‖ * ‖∏ j ∈ s, g j‖ := by rw [norm_mul, norm_mul]
        _ ≤ 1 * (∑ j ∈ s, ‖f j - g j‖) + ‖f i - g i‖ * 1 := by
          gcongr
          · exact ih hfs hgs
          · simpa only [norm_prod] using
              (Finset.prod_le_one₀ (fun j hj => norm_nonneg (g j)) hgs)
        _ = ‖f i - g i‖ + ∑ j ∈ s, ‖f j - g j‖ := by ring

theorem product_centered_unit_cubic_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : AEMeasurable X P) (h1 : Integrable X P)
    (h2i : Integrable (fun ω => X ω ^ 2) P)
    (h3 : Integrable (fun ω => |X ω| ^ 3) P)
    (h0 : P[X] = 0) (h2 : P[X ^ 2] = 1)
    (s : Finset ι) (b : ι → ℝ) (t : ℝ)
    (hsmall : ∀ i ∈ s, (b i * t)^2 / 2 ≤ 1) :
    ‖(∏ i ∈ s, charFun (P.map X) (b i * t)) -
      ∏ i ∈ s, (1 - (((b i * t)^2 / 2 : ℝ) : ℂ))‖ ≤
      (4 + Real.exp 1) * |t|^3 * (∫ ω, |X ω| ^ 3 ∂P) * ∑ i ∈ s, |b i|^3 := by
  let _ : IsProbabilityMeasure (P.map X) :=
    (Measure.isProbabilityMeasure_map_iff hX).2 inferInstance
  have htel := norm_prod_sub_prod_le_sum s
      (fun i => charFun (P.map X) (b i * t))
      (fun i => 1 - (((b i * t)^2 / 2 : ℝ) : ℂ))
  calc
    _ ≤ ∑ i ∈ s, ‖charFun (P.map X) (b i * t) -
          (1 - (((b i * t)^2 / 2 : ℝ) : ℂ))‖ := by
      apply htel
      · intro i hi
        exact norm_charFun_le_one _
      · intro i hi
        have hq : 0 ≤ (b i * t)^2 / 2 := by positivity
        have hnonneg : 0 ≤ 1 - (b i * t)^2 / 2 := sub_nonneg.mpr (hsmall i hi)
        have hle : 1 - (b i * t)^2 / 2 ≤ 1 := by linarith
        rw [show (1 : ℂ) - (((b i * t)^2 / 2 : ℝ) : ℂ) =
            ((1 - (b i * t)^2 / 2 : ℝ) : ℂ) by norm_num]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact hle
    _ ≤ _ := by
      calc
        _ ≤ ∑ i ∈ s, ((4 + Real.exp 1) * |t| ^ 3 *
            (∫ ω, |X ω| ^ 3 ∂P)) * |b i| ^ 3 := by
          apply Finset.sum_le_sum
          intro i hi
          have hpoint := charFun_centered_unit_cubic_bound hX h1 h2i h3 h0 h2
            (b i * t)
          simpa [abs_mul, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hpoint
        _ = (4 + Real.exp 1) * |t| ^ 3 * (∫ ω, |X ω| ^ 3 ∂P) *
            ∑ i ∈ s, |b i| ^ 3 := by
           rw [Finset.mul_sum]

theorem charFun_weightedFinsetSum_cubic_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} {Z : Ω → ℝ}
    (s : Finset ι) (b : ι → ℝ) (t : ℝ)
    (hZ : AEMeasurable Z P) (hZ1 : Integrable Z P)
    (hZ2i : Integrable (fun ω => Z ω ^ 2) P)
    (hZ3 : Integrable (fun ω => |Z ω| ^ 3) P)
    (hZ0 : P[Z] = 0) (hZ2 : P[Z ^ 2] = 1)
    (hident : ∀ i ∈ s, IdentDistrib (X i) Z P P)
    (hindep : iIndepFun X P)
    (hsmall : ∀ i ∈ s, (b i * t)^2 / 2 ≤ 1) :
    ‖charFun (P.map (weightedFinsetSum s b X)) t -
       ∏ i ∈ s, (1 - ((((b i * t)^2 / 2 : ℝ)) : ℂ))‖ ≤
       (4 + Real.exp 1) * |t|^3 * (∫ ω, |Z ω|^3 ∂P) * ∑ i∈s, |b i|^3 := by
  have hm : ∀ i ∈ s, AEMeasurable (X i) P := fun i hi =>
    (hident i hi).aemeasurable_fst
  have hc : iIndepFun (fun i ω => b i * X i ω) P :=
    hindep.comp (fun i x => b i * x) (fun i => measurable_const_mul (b i))
  have hiw : iIndepFun (s.restrict (fun i => b i • X i)) P := by
    convert hc.restrict s using 1
  have hfactor := charFun_weightedFinsetSum_eq_prod hm hiw
  have hprod :
      (∏ i ∈ s, charFun (P.map (b i • X i)) t) =
        ∏ i ∈ s, charFun (P.map Z) (b i * t) := by
    apply Finset.prod_congr rfl
    intro i hi
    calc
      charFun (P.map (b i • X i)) t =
          charFun (P.map (X i)) (b i * t) := by
        rw [show b i • X i = (fun ω => b i * X i ω) by
          ext ω; simp [smul_eq_mul]]
        exact charFun_map_mul_comp (hm i hi) (b i) t
      _ = charFun (P.map Z) (b i * t) := by rw [(hident i hi).map_eq]
  have hfactorT : charFun (P.map (weightedFinsetSum s b X)) t =
      ∏ i ∈ s, charFun (P.map (b i • X i)) t := by
    simpa using congrFun hfactor t
  rw [hfactorT, hprod]
  apply product_centered_unit_cubic_bound hZ hZ1 hZ2i hZ3 hZ0 hZ2 s b t hsmall

private lemma norm_one_sub_product_sub_exp_neg_sum_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (q : ι → ℝ)
    (hq0 : ∀ i ∈ s, 0 ≤ q i) (hq1 : ∀ i ∈ s, q i ≤ 1) :
    ‖(∏ i ∈ s, (1 - (q i : ℂ))) -
       ((Real.exp (-(∑ i ∈ s, q i)) : ℝ) : ℂ)‖ ≤ ∑ i ∈ s, q i^2 := by
  have hprod := norm_prod_sub_prod_le_sum s
    (fun i => 1 - (q i : ℂ))
    (fun i => ((Real.exp (-(q i)) : ℝ) : ℂ))
  have hscalar : ∀ i ∈ s, ‖(1 - (q i : ℂ)) -
      ((Real.exp (-(q i)) : ℝ) : ℂ)‖ ≤ q i^2 := by
    intro i hi
    rw [show (1 - (q i : ℂ)) - ((Real.exp (-(q i)) : ℝ) : ℂ) =
      (((1 - q i) - Real.exp (-(q i)) : ℝ) : ℂ) by norm_num]
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hr := Real.norm_exp_sub_one_sub_id_le (x := -(q i)) (by
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (hq0 i hi)]
      exact hq1 i hi)
    calc
      |1 - q i - Real.exp (-(q i))| =
          |-(Real.exp (-(q i)) - 1 - (-(q i)))| := by congr 1; ring
      _ = |Real.exp (-(q i)) - 1 - (-(q i))| := abs_neg _
      _ ≤ ‖-(q i)‖ ^ 2 := hr
      _ = q i ^ 2 := by rw [Real.norm_eq_abs, abs_neg, sq_abs]
  have hmain : ‖(∏ i ∈ s, (1 - (q i : ℂ))) -
      ∏ i ∈ s, ((Real.exp (-(q i)) : ℝ) : ℂ)‖ ≤ ∑ i ∈ s, q i^2 := by
    calc
      _ ≤ ∑ i ∈ s, ‖(1 - (q i : ℂ)) -
          ((Real.exp (-(q i)) : ℝ) : ℂ)‖ := hprod
          (fun i hi => by
            rw [show (1 : ℂ) - (q i : ℂ) = ((1 - q i : ℝ) : ℂ) by norm_num,
              Complex.norm_real, Real.norm_eq_abs]
            rw [abs_of_nonneg (sub_nonneg.mpr (hq1 i hi))]
            exact sub_le_self 1 (hq0 i hi))
          (fun i hi => by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
            exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hq0 i hi)))
      _ ≤ _ := Finset.sum_le_sum (fun i hi => hscalar i hi)
  calc
    _ = ‖(∏ i ∈ s, (1 - (q i : ℂ))) -
        ∏ i ∈ s, ((Real.exp (-(q i)) : ℝ) : ℂ)‖ := by
      congr 1
      rw [← Complex.ofReal_prod]
      norm_num [← Real.exp_sum, Finset.sum_neg_distrib]
    _ ≤ _ := hmain

theorem quadraticProduct_gaussian_bound
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℝ) (t : ℝ)
    (hsum : ∑ i∈s, (b i)^2 = 1)
    (hsmall : ∀ i∈s, (b i*t)^2 / 2 ≤ 1) :
    ‖(∏ i∈s, (1 - ((((b i*t)^2/2 : ℝ)) : ℂ))) -
       ((Real.exp (-(t^2 / 2)) : ℝ) : ℂ)‖ ≤
      (t^4 / 4) * ∑ i∈s, (b i)^4 := by
  let q : ι → ℝ := fun i => (b i * t)^2 / 2
  have hq0 : ∀ i ∈ s, 0 ≤ q i := fun i hi => by dsimp [q]; positivity
  have hq1 : ∀ i ∈ s, q i ≤ 1 := fun i hi => hsmall i hi
  have hsumq : ∑ i ∈ s, q i = t^2 / 2 := by
    dsimp [q]
    calc
      _ = ∑ i ∈ s, (t^2 / 2) * b i^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (t^2 / 2) * ∑ i ∈ s, b i^2 := by rw [Finset.mul_sum]
    rw [hsum, mul_one]
  have hsq : ∑ i ∈ s, q i^2 = (t^4 / 4) * ∑ i ∈ s, b i^4 := by
    dsimp [q]
    simp_rw [mul_pow]
    rw [Finset.mul_sum]
    congr 1
    funext i
    ring
  have hmain := norm_one_sub_product_sub_exp_neg_sum_le s q hq0 hq1
  rw [hsumq] at hmain
  rw [hsq] at hmain
  simpa [q] using hmain

theorem charFun_weightedFinsetSum_gaussian_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} {Z : Ω → ℝ}
    (s : Finset ι) (b : ι → ℝ) (t : ℝ)
    (hZ : AEMeasurable Z P) (hZ1 : Integrable Z P)
    (hZ2i : Integrable (fun ω => Z ω ^ 2) P)
    (hZ3 : Integrable (fun ω => |Z ω| ^ 3) P)
    (hZ0 : P[Z] = 0) (hZ2 : P[Z ^ 2] = 1)
    (hident : ∀ i ∈ s, IdentDistrib (X i) Z P P)
    (hindep : iIndepFun X P)
    (hsum : ∑ i ∈ s, (b i)^2 = 1)
    (hsmall : ∀ i ∈ s, (b i * t)^2 / 2 ≤ 1) :
    ‖charFun (P.map (weightedFinsetSum s b X)) t -
       ((Real.exp (-(t^2 / 2)) : ℝ) : ℂ)‖ ≤
      (4 + Real.exp 1) * |t|^3 * (∫ ω, |Z ω|^3 ∂P) * ∑ i∈s, |b i|^3 +
      (t^4 / 4) * ∑ i∈s, (b i)^4 := by
  have hc := charFun_weightedFinsetSum_cubic_bound s b t hZ hZ1 hZ2i hZ3
    hZ0 hZ2 hident hindep hsmall
  have hq := quadraticProduct_gaussian_bound s b t hsum hsmall
  calc
    ‖charFun (P.map (weightedFinsetSum s b X)) t -
        ((Real.exp (-(t^2 / 2)) : ℝ) : ℂ)‖ =
        ‖(charFun (P.map (weightedFinsetSum s b X)) t -
          ∏ i ∈ s, (1 - (((b i * t)^2 / 2 : ℝ) : ℂ))) +
          (∏ i ∈ s, (1 - (((b i * t)^2 / 2 : ℝ) : ℂ)) -
            ((Real.exp (-(t^2 / 2)) : ℝ) : ℂ))‖ := by
      congr 1
      ring
    _ ≤ ‖charFun (P.map (weightedFinsetSum s b X)) t -
          ∏ i ∈ s, (1 - (((b i * t)^2 / 2 : ℝ) : ℂ))‖ +
        ‖∏ i ∈ s, (1 - (((b i * t)^2 / 2 : ℝ) : ℂ)) -
          ((Real.exp (-(t^2 / 2)) : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ (4 + Real.exp 1) * |t|^3 * (∫ ω, |Z ω|^3 ∂P) * ∑ i∈s, |b i|^3 +
        (t^4 / 4) * ∑ i∈s, (b i)^4 := add_le_add hc hq

theorem tendsto_charFun_weightedFinsetSum
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} {Z : Ω → ℝ}
    (s : ℕ → Finset ι) (b : ℕ → ι → ℝ)
    (hZ : AEMeasurable Z P) (hZ1 : Integrable Z P)
    (hZ2i : Integrable (fun ω => Z ω ^ 2) P)
    (hZ3 : Integrable (fun ω => |Z ω| ^ 3) P)
    (hZ0 : P[Z] = 0) (hZ2 : P[Z ^ 2] = 1)
    (hident : ∀ i, IdentDistrib (X i) Z P P)
    (hindep : iIndepFun X P)
    (hsum : ∀ n, ∑ i ∈ s n, (b n i)^2 = 1)
    (hthree : Tendsto (fun n => ∑ i ∈ s n, |b n i|^3) atTop (𝓝 0))
    (hfour : Tendsto (fun n => ∑ i ∈ s n, (b n i)^4) atTop (𝓝 0))
    (hsmall : ∀ t : ℝ, ∀ᶠ n in atTop,
       ∀ i ∈ s n, (b n i * t)^2 / 2 ≤ 1) :
    ∀ t : ℝ,
      Tendsto
        (fun n => charFun (P.map (weightedFinsetSum (s n) (b n) X)) t)
        atTop (𝓝 (((Real.exp (-(t^2 / 2)) : ℝ) : ℂ))) := by
  intro t
  let C₃ : ℝ := (4 + Real.exp 1) * |t| ^ 3 * (∫ ω, |Z ω| ^ 3 ∂P)
  let C₄ : ℝ := t ^ 4 / 4
  have hC₃ : Tendsto (fun n => C₃ * ∑ i ∈ s n, |b n i| ^ 3)
      atTop (𝓝 0) := by
    simpa [C₃] using (tendsto_const_nhds.mul hthree)
  have hC₄ : Tendsto (fun n => C₄ * ∑ i ∈ s n, (b n i) ^ 4)
      atTop (𝓝 0) := by
    simpa [C₄] using (tendsto_const_nhds.mul hfour)
  have hbound : ∀ᶠ n in atTop,
      ‖charFun (P.map (weightedFinsetSum (s n) (b n) X)) t -
          ((Real.exp (-(t^2 / 2)) : ℝ) : ℂ)‖ ≤
        C₃ * ∑ i ∈ s n, |b n i| ^ 3 + C₄ * ∑ i ∈ s n, (b n i) ^ 4 := by
    filter_upwards [hsmall t] with n hn
    have h := charFun_weightedFinsetSum_gaussian_bound (s n) (b n) t
      hZ hZ1 hZ2i hZ3 hZ0 hZ2 (fun i hi => hident i) hindep (hsum n) hn
    simpa [C₃, C₄, mul_assoc] using h
  have hrhs : Tendsto
      (fun n => C₃ * ∑ i ∈ s n, |b n i| ^ 3 +
        C₄ * ∑ i ∈ s n, (b n i) ^ 4) atTop (𝓝 0) := by
    simpa using hC₃.add hC₄
  have hnonneg : ∀ n,
      0 ≤ C₃ * ∑ i ∈ s n, |b n i| ^ 3 + C₄ * ∑ i ∈ s n, (b n i) ^ 4 := by
    intro n
    dsimp [C₃, C₄]
    positivity
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _))
     hbound hrhs

lemma cubic_sum_le_of_diffuse
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℝ) (ε : ℝ)
    (_hε : 0 ≤ ε) (hb : ∀ i ∈ s, |b i| ≤ ε)
    (hsum : ∑ i ∈ s, (b i)^2 = 1) :
    ∑ i ∈ s, |b i|^3 ≤ ε := by
  calc
    ∑ i ∈ s, |b i|^3 ≤ ∑ i ∈ s, ε * (b i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        |b i| ^ 3 = |b i| * (b i)^2 := by rw [← sq_abs]; ring
        _ ≤ ε * (b i)^2 := mul_le_mul_of_nonneg_right (hb i hi) (sq_nonneg _)
    _ = ε := by
      rw [← Finset.mul_sum, hsum, mul_one]

lemma fourth_sum_le_of_diffuse
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (b : ι → ℝ) (ε : ℝ)
    (_hε : 0 ≤ ε) (hb : ∀ i ∈ s, |b i| ≤ ε)
    (hsum : ∑ i ∈ s, (b i)^2 = 1) :
    ∑ i ∈ s, (b i)^4 ≤ ε^2 := by
  calc
    ∑ i ∈ s, (b i)^4 ≤ ∑ i ∈ s, ε^2 * (b i)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have habs : |b i| ^ 2 ≤ ε ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self (abs_nonneg _) (hb i hi)
      calc
        (b i)^4 = |b i|^2 * (b i)^2 := by rw [sq_abs]; ring
        _ ≤ ε^2 * (b i)^2 := mul_le_mul_of_nonneg_right habs (sq_nonneg _)
    _ = ε^2 := by
      rw [← Finset.mul_sum, hsum, mul_one]

theorem tendsto_cubic_sum_of_diffuse
    {ι : Type*} [DecidableEq ι] (s : ℕ → Finset ι) (b : ℕ → ι → ℝ)
    (hsum : ∀ n, ∑ i ∈ s n, (b n i)^2 = 1)
    (hdiffuse : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i ∈ s n, |b n i| ≤ ε) :
    Tendsto (fun n => ∑ i ∈ s n, |b n i|^3) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hdiffuse (ε / 2) (by linarith))
  refine ⟨N, fun n hnN => ?_⟩
  have hn := hN n hnN
  rw [Real.dist_eq, abs_of_nonneg]
  · have h := cubic_sum_le_of_diffuse (s n) (b n) (ε / 2) (by linarith) hn (hsum n)
    linarith
  · simpa using (Finset.sum_nonneg (fun i hi => pow_nonneg (abs_nonneg _) 3))

theorem tendsto_fourth_sum_of_diffuse
    {ι : Type*} [DecidableEq ι] (s : ℕ → Finset ι) (b : ℕ → ι → ℝ)
    (hsum : ∀ n, ∑ i ∈ s n, (b n i)^2 = 1)
    (hdiffuse : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i ∈ s n, |b n i| ≤ ε) :
    Tendsto (fun n => ∑ i ∈ s n, (b n i)^4) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hdiffuse (Real.sqrt ε / 2)
    (by positivity))
  refine ⟨N, fun n hnN => ?_⟩
  have hn := hN n hnN
  rw [Real.dist_eq, abs_of_nonneg]
  · have h := fourth_sum_le_of_diffuse (s n) (b n) (Real.sqrt ε / 2)
      (by positivity) hn (hsum n)
    have hs : (Real.sqrt ε)^2 = ε := (Real.sq_sqrt (le_of_lt hε))
    nlinarith
  · have hnonneg : 0 ≤ ∑ i ∈ s n, (b n i)^4 := by
      apply Finset.sum_nonneg
      intro i hi
      positivity
    simpa using hnonneg

theorem eventually_weighted_square_le_one_of_diffuse
    {ι : Type*} [DecidableEq ι] (s : ℕ → Finset ι) (b : ℕ → ι → ℝ)
    (hdiffuse : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i ∈ s n, |b n i| ≤ ε) (t : ℝ) :
    ∀ᶠ n in atTop, ∀ i ∈ s n, (b n i * t)^2 / 2 ≤ 1 := by
  let ε : ℝ := 1 / (1 + |t|)
  have hε : 0 < ε := by dsimp [ε]; positivity
  filter_upwards [hdiffuse ε hε] with n hn i hi
  have ht : |b n i * t| ≤ 1 := by
    rw [abs_mul]
    have hden : 0 < 1 + |t| := by positivity
    apply le_trans (mul_le_mul_of_nonneg_right (hn i hi) (abs_nonneg t))
    rw [div_mul_eq_mul_div]
    simp only [one_mul]
    apply (div_le_iff₀ hden).2
    nlinarith [abs_nonneg t]
  have hs : (b n i * t)^2 ≤ 1 := by
    have habs : |b n i * t| ^ 2 ≤ 1 := by
      nlinarith [mul_self_le_mul_self (abs_nonneg (b n i * t)) ht]
    simpa [sq_abs] using habs
  nlinarith

theorem tendsto_charFun_weightedFinsetSum_of_diffuse
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} {Z : Ω → ℝ}
    (s : ℕ → Finset ι) (b : ℕ → ι → ℝ)
    (hZ : AEMeasurable Z P) (hZ1 : Integrable Z P)
    (hZ2i : Integrable (fun ω => Z ω ^ 2) P)
    (hZ3 : Integrable (fun ω => |Z ω| ^ 3) P)
    (hZ0 : P[Z] = 0) (hZ2 : P[Z ^ 2] = 1)
    (hident : ∀ i, IdentDistrib (X i) Z P P)
    (hindep : iIndepFun X P)
    (hsum : ∀ n, ∑ i ∈ s n, (b n i)^2 = 1)
    (hdiffuse : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ i ∈ s n, |b n i| ≤ ε) :
    ∀ t, Tendsto (fun n => charFun (P.map (weightedFinsetSum (s n) (b n) X)) t)
      atTop (𝓝 (((Real.exp (-(t^2 / 2)) : ℝ) : ℂ))) := by
  apply tendsto_charFun_weightedFinsetSum s b hZ hZ1 hZ2i hZ3 hZ0 hZ2 hident hindep hsum
    (tendsto_cubic_sum_of_diffuse s b hsum hdiffuse)
    (tendsto_fourth_sum_of_diffuse s b hsum hdiffuse)
    (eventually_weighted_square_le_one_of_diffuse s b hdiffuse)

theorem tendstoInDistribution_weightedFinsetSum_of_diffuse
    {Ω Ω' ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : ι → Ω → ℝ} {Z : Ω → ℝ} {Y : Ω' → ℝ}
    (s : ℕ → Finset ι) (b : ℕ → ι → ℝ)
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hZ : AEMeasurable Z P) (hZ1 : Integrable Z P)
    (hZ2i : Integrable (fun ω => Z ω ^ 2) P)
    (hZ3 : Integrable (fun ω => |Z ω| ^ 3) P)
    (hZ0 : P[Z] = 0) (hZ2 : P[Z ^ 2] = 1)
    (hident : ∀ i, IdentDistrib (X i) Z P P)
    (hindep : iIndepFun X P)
    (hsum : ∀ n, ∑ i ∈ s n, (b n i)^2 = 1)
    (hdiffuse : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
       ∀ i ∈ s n, |b n i| ≤ ε) :
    TendstoInDistribution
      (fun n => weightedFinsetSum (s n) (b n) X)
      atTop Y (fun _ => P) P' := by
  apply TendstoInDistribution.of_tendsto_charFun
  · intro n
    unfold weightedFinsetSum
    exact Finset.aemeasurable_fun_sum _ (fun i _ =>
      (hident i).aemeasurable_fst.const_mul (b n i))
  · exact hY.aemeasurable
  · intro t
    have hlim := tendsto_charFun_weightedFinsetSum_of_diffuse s b hZ hZ1 hZ2i hZ3
      hZ0 hZ2 hident hindep hsum hdiffuse t
    rw [hY.map_eq, charFun_gaussianReal]
    simpa [charFun_gaussianReal, neg_div] using hlim

end RayleighKernel.Probability
