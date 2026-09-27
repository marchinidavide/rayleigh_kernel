import RayleighKernel.Probability.TriangularArrayCLT
import RayleighKernel.Probability.GaussianTurnover
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Uniform integrability from a common L² bound

This module provides the generic L²-to-L¹ uniform-integrability bridge used by
the weighted triangular-array arguments.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace RayleighKernel.Probability

theorem uniformIntegrable_of_eLpNorm_two_le
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : ι → Ω → ℝ} {C : ENNReal}
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (hCtop : C ≠ ⊤)
    (hC : ∀ i, eLpNorm (f i) 2 P ≤ C) :
    UniformIntegrable f 1 P := by
  refine ⟨?_, ?_⟩
  · rw [unifIntegrable_iff']
    intro ε hε
    by_cases hεtop : ε = ⊤
    · subst ε
      exact ⟨1, zero_lt_one, fun i s hs hμs => le_top⟩
    let δ : ENNReal := (ε / (C + 1)) ^ (2 : ℝ)
    have hδ : 0 < δ := by
      dsimp [δ]
      apply ENNReal.rpow_pos
      · exact ENNReal.div_pos hε.ne' (by finiteness)
      · exact ENNReal.div_ne_top (by exact hεtop) (by finiteness)
    refine ⟨δ, hδ, fun i s hs hμs => ?_⟩
    have hrestrict : eLpNorm (f i) 2 (P.restrict s) ≤ C := by
      exact (eLpNorm_restrict_le (f i) 2 P s).trans (hC i)
    have hmeasure : P.restrict s Set.univ = P s := by
      exact Measure.restrict_apply_univ s
    have hholder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (μ := P.restrict s) (p := (1 : ENNReal)) (q := (2 : ENNReal)) (by norm_num)
      ((hf i).restrict)
    rw [hmeasure] at hholder
    have hexp : 1 / ENNReal.toReal (1 : ENNReal) -
        1 / ENNReal.toReal (2 : ENNReal) = (1 / 2 : ℝ) := by norm_num
    rw [hexp] at hholder
    have hbound : eLpNorm (f i) 1 (P.restrict s) ≤
        C * (P s) ^ (1 / 2 : ℝ) := by
      calc
        eLpNorm (f i) 1 (P.restrict s) ≤
            eLpNorm (f i) 2 (P.restrict s) * (P s) ^ (1 / 2 : ℝ) := hholder
        _ ≤ C * (P s) ^ (1 / 2 : ℝ) := by
          exact mul_le_mul_left hrestrict _
    have hpow : (P s) ^ (1 / 2 : ℝ) ≤ ε / (C + 1) := by
      have hPs : P s ≤ δ := hμs
      dsimp [δ] at hPs ⊢
      calc
        P s ^ (1 / 2 : ℝ) ≤ ((ε / (C + 1)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hPs (by norm_num)
        _ = ε / (C + 1) := by
          rw [← ENNReal.rpow_mul]
          norm_num
    calc
      eLpNorm (f i) 1 (P.restrict s) ≤ C * (P s) ^ (1 / 2 : ℝ) := hbound
      _ ≤ C * (ε / (C + 1)) := by
        simpa [mul_comm] using mul_le_mul_left hpow C
      _ ≤ ε := by
        calc
          C * (ε / (C + 1)) ≤ (C + 1) * (ε / (C + 1)) := by
            simpa [mul_comm] using
              mul_le_mul_left (show C ≤ C + 1 from le_add_right (le_refl C))
                (ε / (C + 1))
          _ = ε := ENNReal.mul_div_cancel (by positivity) (by finiteness)
  · refine ⟨C.toNNReal, fun i => ?_⟩
    have hCeq : (C.toNNReal : ENNReal) = C := ENNReal.coe_toNNReal hCtop
    rw [hCeq]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (p := (1 : ENNReal))
      (q := (2 : ENNReal)) (by norm_num)).trans (hC i)

private def trunc_bcf (R : ℝ) (hR : 0 ≤ R) : BoundedContinuousFunction ℝ ℝ := by
  let g : C(ℝ, ℝ) := ⟨fun x => min |x| R, continuous_abs.min continuous_const⟩
  apply BoundedContinuousFunction.mkOfBound g R
  intro x y
  rw [Real.dist_eq]
  have hxR : min |x| R ≤ R := min_le_right _ _
  have hyR : min |y| R ≤ R := min_le_right _ _
  have hx0 : 0 ≤ min |x| R := le_min (abs_nonneg x) hR
  have hy0 : 0 ≤ min |y| R := le_min (abs_nonneg y) hR
  change |min |x| R - min |y| R| ≤ R
  by_cases hxy : min |x| R ≤ min |y| R
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy))]
    linarith

private lemma trunc_tail_bound (R : ℝ) (hR : 0 < R) (x : ℝ) :
    0 ≤ |x| - min |x| R ∧ |x| - min |x| R ≤ x ^ 2 / R := by
  constructor
  · exact sub_nonneg.mpr (min_le_left _ _)
  · by_cases hx : |x| ≤ R
    · rw [min_eq_left hx]
      simp only [sub_self]
      exact div_nonneg (sq_nonneg x) hR.le
    · rw [min_eq_right (le_of_not_ge hx)]
      have hx' : R < |x| := lt_of_not_ge hx
      have hnonneg : 0 ≤ |x| - R := sub_nonneg.mpr hx'.le
      apply (le_div_iff₀ hR).2
      have hsq : (|x| - R) * R ≤ (|x| - R) * |x| :=
        mul_le_mul_of_nonneg_left hx'.le hnonneg
      have habs_sq : |x| ^ 2 = x ^ 2 := sq_abs x
      nlinarith [habs_sq, hsq]

private lemma integrable_min_abs_const
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Integrable (fun x => |f x|) μ) (R : ℝ) :
    Integrable (fun x => min |f x| R) μ := by
  change Integrable ((fun x => |f x|) ⊓ (fun _ => R)) μ
  exact hf.inf (integrable_const R)

theorem fixed_radius_truncation_tendsto
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (hconv : TendstoInDistribution X atTop Y (fun _ => P) P')
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun n => ∫ ω, min |X n ω| R ∂P) atTop
      (𝓝 (∫ ω, min |Y ω| R ∂P')) := by
  let g := trunc_bcf R hR.le
  have hc := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hconv.forall_aemeasurable hconv.aemeasurable_limit).1 hconv g
  change Tendsto (fun n => ∫ ω, (g : ℝ → ℝ) (X n ω) ∂P) atTop
    (𝓝 (∫ ω, (g : ℝ → ℝ) (Y ω) ∂P')) at hc
  simpa [g, trunc_bcf] using hc

theorem tendsto_integral_abs_of_tendstoInDistribution_of_integral_sq_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ} {C : ℝ}
    (hconv : TendstoInDistribution X atTop Y (fun _ => P) P')
    (hX2 : ∀ n, Integrable (fun ω => (X n ω)^2) P)
    (hX2le : ∀ n, (∫ ω, (X n ω)^2 ∂P) ≤ C)
    (hY2 : Integrable (fun ω => (Y ω)^2) P') :
    Tendsto (fun n => ∫ ω, |X n ω| ∂P) atTop
      (𝓝 (∫ ω, |Y ω| ∂P')) := by
  have hXaemeas : ∀ n, AEStronglyMeasurable (X n) P := fun n =>
    (hconv.forall_aemeasurable n).aestronglyMeasurable
  have hYaemeas : AEStronglyMeasurable Y P' := hconv.aemeasurable_limit.aestronglyMeasurable
  have hXmem : ∀ n, MemLp (X n) 2 P := fun n => by
    rw [memLp_two_iff_integrable_sq (hXaemeas n)]
    exact hX2 n
  have hYmem : MemLp Y 2 P' := by
    rw [memLp_two_iff_integrable_sq hYaemeas]
    exact hY2
  have hX1 : ∀ n, Integrable (X n) P := fun n =>
    memLp_one_iff_integrable.mp ((hXmem n).mono_exponent (by norm_num))
  have hY1 : Integrable Y P' :=
    memLp_one_iff_integrable.mp (hYmem.mono_exponent (by norm_num))
  have hXabs : ∀ n, Integrable (fun ω => |X n ω|) P := fun n => (hX1 n).norm
  have hYabs : Integrable (fun ω => |Y ω|) P' := hY1.norm
  let MY : ℝ := ∫ ω, (Y ω)^2 ∂P'
  have hMY : 0 ≤ MY := by
    dsimp [MY]
    exact integral_nonneg (fun ω => sq_nonneg _)
  have hC : 0 ≤ C := by
    have hn := hX2le 0
    have hn0 : 0 ≤ (∫ ω, (X 0 ω)^2 ∂P) :=
      integral_nonneg (fun ω => sq_nonneg _)
    linarith
  apply Metric.tendsto_atTop.2
  intro ε hε
  let R : ℝ := 1 + 3 * (C + MY + 1) / ε
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hRX : C / R < ε / 3 := by
    dsimp [R]
    have : C ≤ C + MY + 1 := by linarith
    rw [div_lt_iff₀ hR]
    dsimp [R]
    field_simp
    nlinarith
  have hRY : MY / R < ε / 3 := by
    dsimp [R]
    have : MY ≤ C + MY + 1 := by linarith
    rw [div_lt_iff₀ hR]
    dsimp [R]
    field_simp
    nlinarith
  have htailX : ∀ n,
      0 ≤ (∫ ω, |X n ω| ∂P) - ∫ ω, min |X n ω| R ∂P ∧
      (∫ ω, |X n ω| ∂P) - ∫ ω, min |X n ω| R ∂P ≤ C / R := by
    intro n
    have htruncX : Integrable (fun ω => min |X n ω| R) P :=
      integrable_min_abs_const (X n) (hXabs n) R
    have hi : Integrable (fun ω => |X n ω| - min |X n ω| R) P :=
      (hXabs n).sub htruncX
    have hi2 : Integrable (fun ω => (X n ω)^2 / R) P := by
      simpa [div_eq_mul_inv, mul_comm] using (hX2 n).const_mul R⁻¹
    have hp := fun ω => trunc_tail_bound R hR (X n ω)
    constructor
    · rw [← integral_sub (hXabs n) htruncX]
      exact integral_nonneg (fun ω => (hp ω).1)
    · rw [← integral_sub (hXabs n) htruncX]
      calc
        _ ≤ ∫ ω, (X n ω)^2 / R ∂P :=
          integral_mono_ae hi hi2 (Filter.Eventually.of_forall fun ω => (hp ω).2)
        _ = (∫ ω, (X n ω)^2 ∂P) / R := by
          rw [show (fun ω => (X n ω)^2 / R) = fun ω => R⁻¹ * (X n ω)^2 by
            funext ω; field_simp]
          rw [integral_const_mul]
          field_simp
        _ ≤ C / R := by
          gcongr
          exact hX2le n
  have htailY :
      0 ≤ (∫ ω, |Y ω| ∂P') - ∫ ω, min |Y ω| R ∂P' ∧
      (∫ ω, |Y ω| ∂P') - ∫ ω, min |Y ω| R ∂P' ≤ MY / R := by
    have htruncY : Integrable (fun ω => min |Y ω| R) P' :=
      integrable_min_abs_const Y hYabs R
    have hi : Integrable (fun ω => |Y ω| - min |Y ω| R) P' :=
      hYabs.sub htruncY
    have hi2 : Integrable (fun ω => (Y ω)^2 / R) P' := by
      simpa [div_eq_mul_inv, mul_comm] using hY2.const_mul R⁻¹
    have hp := fun ω => trunc_tail_bound R hR (Y ω)
    constructor
    · rw [← integral_sub hYabs htruncY]
      exact integral_nonneg (fun ω => (hp ω).1)
    · rw [← integral_sub hYabs htruncY]
      calc
        _ ≤ ∫ ω, (Y ω)^2 / R ∂P' :=
          integral_mono_ae hi hi2 (Filter.Eventually.of_forall fun ω => (hp ω).2)
        _ = MY / R := by
          dsimp [MY]
          rw [show (fun ω => (Y ω)^2 / R) = fun ω => R⁻¹ * (Y ω)^2 by
            funext ω; field_simp]
          rw [integral_const_mul]
          field_simp
  have htrunc := fixed_radius_truncation_tendsto hconv R hR
  have hev : ∀ᶠ n in atTop,
      |(∫ ω, min |X n ω| R ∂P) - ∫ ω, min |Y ω| R ∂P'| < ε / 3 := by
    have := (Metric.tendsto_atTop.1 htrunc) (ε / 3) (by linarith)
    filter_upwards [eventually_atTop.2 this] with n hn
    simpa [Real.dist_eq] using hn
  have hfinal : ∀ᶠ n in atTop,
      dist (∫ ω, |X n ω| ∂P) (∫ ω, |Y ω| ∂P') < ε := by
    filter_upwards [hev] with n hn
    have htx := htailX n
    have hty := htailY
    have hdiff :
      (∫ ω, |X n ω| ∂P) - ∫ ω, |Y ω| ∂P' =
        ((∫ ω, |X n ω| ∂P) - ∫ ω, min |X n ω| R ∂P) +
        ((∫ ω, min |X n ω| R ∂P) - ∫ ω, min |Y ω| R ∂P') -
        ((∫ ω, |Y ω| ∂P') - ∫ ω, min |Y ω| R ∂P') := by ring
    rw [Real.dist_eq, hdiff]
    let a : ℝ := (∫ ω, |X n ω| ∂P) - ∫ ω, min |X n ω| R ∂P
    let b : ℝ := (∫ ω, min |X n ω| R ∂P) - ∫ ω, min |Y ω| R ∂P'
    let c : ℝ := (∫ ω, |Y ω| ∂P') - ∫ ω, min |Y ω| R ∂P'
    have habs : |a + b - c| ≤ |a| + |b| + |c| := by
      calc
        _ ≤ |a + b| + |c| := by
          simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le (a + b) 0 c)
        _ ≤ _ := by
          have h := add_le_add_right (abs_add_le a b) |c|
          simpa [a, b, c, abs_neg, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
    rw [show ((∫ ω, |X n ω| ∂P) - ∫ ω, min |X n ω| R ∂P) = a by rfl,
      show ((∫ ω, min |X n ω| R ∂P) - ∫ ω, min |Y ω| R ∂P') = b by rfl,
      show ((∫ ω, |Y ω| ∂P') - ∫ ω, min |Y ω| R ∂P') = c by rfl]
    calc
      _ ≤ _ := habs
      _ < ε := by
        have hxnon : 0 ≤ (∫ ω, |X n ω| ∂P) - ∫ ω, min |X n ω| R ∂P := htx.1
        have hynon : 0 ≤ (∫ ω, |Y ω| ∂P') - ∫ ω, min |Y ω| R ∂P' := hty.1
        rw [abs_of_nonneg hxnon, abs_of_nonneg hynon]
        nlinarith [htx.2, hty.2, hRX, hRY]
  exact Filter.eventually_atTop.1 hfinal

theorem weightedFinsetSum_memLp_two
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {s : Finset ι} {b : ι → ℝ} {X : ι → Ω → ℝ} {Z : Ω → ℝ}
    (hZ : MemLp Z 2 P) (hident : ∀ i, IdentDistrib (X i) Z P P) :
    MemLp (weightedFinsetSum s b X) 2 P := by
  unfold weightedFinsetSum
  apply memLp_finsetSum s
  intro i hi
  simpa [smul_eq_mul] using ((hident i).const_mul (b i)).memLp_iff.mpr (hZ.const_mul (b i))

theorem weightedFinsetSum_integral_eq_zero
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {s : Finset ι} {b : ι → ℝ} {X : ι → Ω → ℝ} {Z : Ω → ℝ}
    (hZ1 : Integrable Z P) (hZ0 : P[Z] = 0)
    (hident : ∀ i, IdentDistrib (X i) Z P P) :
    P[weightedFinsetSum s b X] = 0 := by
  unfold weightedFinsetSum
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    calc
      _ = ∑ x ∈ s, b x * P[X x] := by
        congr 1
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [(hident i).integral_eq, hZ0, mul_zero]
  · intro i hi
    exact ((hident i).const_mul (b i)).integrable_iff.mpr (hZ1.const_mul (b i))

theorem weightedFinsetSum_integral_sq
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {s : Finset ι} {b : ι → ℝ} {X : ι → Ω → ℝ} {Z : Ω → ℝ}
    (hZ2 : MemLp Z 2 P) (hZ0 : P[Z] = 0) (hZsq : P[Z ^ 2] = 1)
    (hident : ∀ i, IdentDistrib (X i) Z P P) (hindep : iIndepFun X P)
    (hsum : ∑ i ∈ s, (b i)^2 = 1) :
    ∫ ω, (weightedFinsetSum s b X ω)^2 ∂P = 1 := by
  let F : ι → Ω → ℝ := fun i ω => b i * X i ω
  have hFm : ∀ i ∈ s, MemLp (F i) 2 P := by
    intro i hi
    exact ((hident i).const_mul (b i)).memLp_iff.mpr (hZ2.const_mul (b i))
  have hFi : ∀ i ∈ s, Integrable (F i) P := fun i hi =>
    (hFm i hi).integrable one_le_two
  have hp : Set.Pairwise (↑s) (fun i j => F i ⟂ᵢ[P] F j) := by
    intro i hi j hj hij
    exact (hindep.indepFun hij).comp (measurable_const_mul (b i))
      (measurable_const_mul (b j))
  have hvar : variance (∑ i ∈ s, F i) P = ∑ i ∈ s, variance (F i) P :=
    IndepFun.variance_sum (fun i hi => hFm i hi) hp
  have hzvar : variance Z P = 1 := by
    rw [variance_of_integral_eq_zero hZ2.aemeasurable hZ0]
    simpa [pow_two] using hZsq
  have hFvar : ∀ i ∈ s, variance (F i) P = (b i)^2 := by
    intro i hi
    rw [variance_const_mul]
    rw [show variance (X i) P = variance Z P from (hident i).variance_eq, hzvar]
    ring
  have hsumvar : variance (∑ i ∈ s, F i) P = 1 := by
    rw [hvar]
    calc
      _ = ∑ i ∈ s, b i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hFvar i hi
      _ = 1 := hsum
  have hzero : P[∑ i ∈ s, F i] = 0 := by
    convert weightedFinsetSum_integral_eq_zero
      (s := s) (b := b) (X := X) (Z := Z) (hZ2.integrable one_le_two) hZ0 hident using 1;
      simp [F, weightedFinsetSum]
  have hzero' : P[fun ω => ∑ i ∈ s, F i ω] = 0 := by
    simpa only [Finset.sum_apply] using hzero
  have hsumvar' : variance (fun ω => ∑ i ∈ s, F i ω) P = 1 := by
    convert hsumvar using 1
    congr 1
    funext ω
    simp
  rw [variance_of_integral_eq_zero (memLp_finsetSum s hFm).aemeasurable hzero'] at hsumvar'
  simpa [F, weightedFinsetSum] using hsumvar'

theorem uniformIntegrable_weightedFinsetSum_of_square_sum_one
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} {Z : Ω → ℝ} (s : ℕ → Finset ι) (b : ℕ → ι → ℝ)
    (hZ2 : MemLp Z 2 P) (hZ0 : P[Z] = 0) (hZsq : P[Z ^ 2] = 1)
    (hident : ∀ i, IdentDistrib (X i) Z P P) (hindep : iIndepFun X P)
    (hsum : ∀ n, ∑ i ∈ s n, (b n i)^2 = 1) :
    UniformIntegrable (fun n => weightedFinsetSum (s n) (b n) X) 1 P := by
  apply uniformIntegrable_of_eLpNorm_two_le (C := (1 : ENNReal))
  · intro n
    exact (weightedFinsetSum_memLp_two hZ2 hident).aestronglyMeasurable
  · norm_num
  · intro n
    have hm := weightedFinsetSum_memLp_two (s := s n) (b := b n) hZ2 hident
    rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    have hi := weightedFinsetSum_integral_sq (s := s n) (b := b n)
      hZ2 hZ0 hZsq hident hindep (hsum n)
    simp only [Real.norm_eq_abs]
    norm_num [Real.norm_eq_abs, sq_abs] at hi ⊢
    rw [hi]
    norm_num

theorem tendsto_integral_abs_weightedFinsetSum_of_diffuse
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : ι → Ω → ℝ} {Z : Ω → ℝ} {Y : Ω' → ℝ}
    (s : ℕ → Finset ι) (b : ℕ → ι → ℝ)
    (hY : HasLaw Y (gaussianReal 0 1) P') (hZ : AEMeasurable Z P)
    (hZ1 : Integrable Z P) (hZ2i : Integrable (fun ω => Z ω ^ 2) P)
    (hZ3 : Integrable (fun ω => |Z ω| ^ 3) P) (hZ0 : P[Z] = 0) (hZ2 : P[Z ^ 2] = 1)
    (hident : ∀ i, IdentDistrib (X i) Z P P) (hindep : iIndepFun X P)
    (hsum : ∀ n, ∑ i ∈ s n, (b n i)^2 = 1)
    (hdiffuse : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ i ∈ s n, |b n i| ≤ ε) :
    Tendsto (fun n => ∫ ω, |weightedFinsetSum (s n) (b n) X ω| ∂P) atTop
      (𝓝 (Real.sqrt (2 / Real.pi))) := by
  have hconv := tendstoInDistribution_weightedFinsetSum_of_diffuse s b hY hZ hZ1 hZ2i hZ3
    hZ0 hZ2 hident hindep hsum hdiffuse
  have ht := tendsto_integral_abs_of_tendstoInDistribution_of_integral_sq_le
    (C := (1 : ℝ)) hconv (by
      intro n
      exact (weightedFinsetSum_memLp_two (s := s n) (b := b n)
        (memLp_two_iff_integrable_sq hZ.aestronglyMeasurable |>.2 hZ2i) hident).integrable_sq)
    (by
      intro n
      have hi := weightedFinsetSum_integral_sq (s := s n) (b := b n)
        (memLp_two_iff_integrable_sq hZ.aestronglyMeasurable |>.2 hZ2i) hZ0 hZ2
        hident hindep (hsum n)
      simpa using hi.le)
    (hY.memLp (memLp_id_gaussianReal' 2 (by norm_num)) |>.integrable_sq)
  have hend : (∫ ω, |Y ω| ∂P') = Real.sqrt (2 / Real.pi) := by
    calc
      _ = ∫ x, |x| ∂gaussianReal 0 1 := by
        simpa [Function.comp_def] using
          hY.integral_comp (continuous_abs.aemeasurable.aestronglyMeasurable)
      _ = _ := integral_abs_standardGaussian
  rw [hend] at ht
  exact ht

end RayleighKernel.Probability
