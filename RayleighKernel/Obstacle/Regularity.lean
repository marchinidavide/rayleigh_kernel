import RayleighKernel.Obstacle.KKT
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

noncomputable section
namespace RayleighKernel
namespace Analysis

open MeasureTheory Set Filter
open scoped SchwartzMap
open scoped Topology
open scoped ENNReal
open scoped NNReal

/-- The cumulative distribution function of a finite measure on the real line. -/
def measureCDF (μ : Measure ℝ) (x : ℝ) : ℝ := μ.real (Iic x)

/-- The cumulative distribution function is monotone. -/
theorem measureCDF_monotone {μ : Measure ℝ} [IsFiniteMeasure μ] :
    Monotone (measureCDF μ) := by
  intro x y hxy
  exact ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono ((Iic_subset_Iic).mpr hxy))

theorem measureCDF_continuousWithinAt_Ici
    {μ : Measure ℝ} [IsFiniteMeasure μ] (x : ℝ) :
    ContinuousWithinAt (measureCDF μ) (Ici x) x := by
  let s : ℕ → Set ℝ := fun n => Iic (x + 1 / (n + 1 : ℝ))
  have hs : ∀ n, MeasurableSet (s n) := fun n => measurableSet_Iic
  have hanti : Antitone s := by
    intro m n hmn
    apply Iic_subset_Iic.mpr
    gcongr
  have hinter : ⋂ n, s n = Iic x := by
    ext y
    constructor
    · intro hy
      have hle : ∀ n : ℕ, y ≤ x + 1 / (n + 1 : ℝ) := by
        intro n
        exact (mem_iInter.1 hy n)
      by_contra hxy
      have hpos : 0 < y - x := sub_pos.mpr (lt_of_not_ge hxy)
      obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / (y - x) < n :=
        exists_nat_gt (1 / (y - x))
      have hsmall : 1 / (n + 1 : ℝ) < y - x := by
        calc
          1 / (n + 1 : ℝ) < 1 / n := by
            apply one_div_lt_one_div_of_lt
            · exact lt_trans (by positivity) hn
            · exact_mod_cast Nat.lt_add_one n
          _ < y - x := by
            have hn0 : (0 : ℝ) < n := lt_trans (by positivity) hn
            apply (div_lt_iff₀ hn0).2
            have hdn : 1 < (n : ℝ) * (y - x) := (div_lt_iff₀ hpos).mp hn
            nlinarith
      linarith [hle n]
    · intro hy
      have hyx : y ≤ x := hy
      rw [mem_iInter]
      intro n
      have hnonneg : 0 ≤ (1 / ((n : ℝ) + 1)) := by positivity
      exact le_trans hyx (le_add_of_nonneg_right hnonneg)
  have hlimE : Tendsto (fun n => μ (s n)) atTop (𝓝 (μ (Iic x))) := by
    rw [← hinter]
    exact tendsto_measure_iInter_atTop (fun n => (hs n).nullMeasurableSet)
      hanti ⟨0, by exact measure_ne_top μ (s 0)⟩
  have hlim : Tendsto (fun n : ℕ => measureCDF μ (x + 1 / (n + 1 : ℝ))) atTop
      (𝓝 (measureCDF μ x)) := by
    change Tendsto (fun n => (μ (s n)).toReal) atTop (𝓝 (μ (Iic x)).toReal)
    exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp hlimE
  change Tendsto (measureCDF μ) (𝓝[≥] x) (𝓝 (measureCDF μ x))
  apply tendsto_order.2
  constructor
  · intro z hz
    filter_upwards [self_mem_nhdsWithin] with y hy
    change x ≤ y at hy
    exact hz.trans_le (measureCDF_monotone (μ := μ) hy)
  · intro z hz
    have hev : ∀ᶠ n : ℕ in atTop, measureCDF μ (x + 1 / (n + 1 : ℝ)) < z :=
      (tendsto_order.1 hlim).2 z hz
    obtain ⟨n, hn⟩ := (eventually_atTop.1 hev)
    have hxn : x < x + 1 / (n + 1 : ℝ) := by
      have hp : 0 < (n : ℝ) + 1 := by positivity
      linarith [one_div_pos.mpr hp]
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hxn)] with y hy
    exact lt_of_le_of_lt (measureCDF_monotone (μ := μ) hy) (hn n le_rfl)

def cdfStieltjes (μ : Measure ℝ) [IsFiniteMeasure μ] : StieltjesFunction ℝ :=
  { toFun := measureCDF μ
    mono' := measureCDF_monotone
    right_continuous' := measureCDF_continuousWithinAt_Ici }

theorem cdfStieltjes_measure_eq (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (cdfStieltjes μ).measure = μ := by
  apply Measure.ext_of_Ioc
  intro x y hxy
  have hdiff : Iic y \ Iic x = Ioc x y := by
    ext z
    simp only [Set.mem_sdiff, mem_Iic, mem_Ioc]
    constructor
    · intro h
      exact ⟨lt_of_not_ge h.2, h.1⟩
    · intro h
      exact ⟨h.2, not_le_of_gt h.1⟩
  have hsub : Iic x ⊆ Iic y := Iic_subset_Iic.mpr hxy.le
  have hμ := measureReal_sdiff (μ := μ) hsub measurableSet_Iic
  have hμtop : μ (Iic y) ≠ ∞ := measure_ne_top μ _
  have hμx_top : μ (Iic x) ≠ ∞ := measure_ne_top μ _
  have hμE : μ (Iic y \ Iic x) = μ (Iic y) - μ (Iic x) :=
    measure_sdiff hsub measurableSet_Iic.nullMeasurableSet hμx_top
  rw [hdiff] at hμ
  rw [StieltjesFunction.measure_Ioc, cdfStieltjes]
  simp only [measureCDF, MeasureTheory.measureReal_def]
  rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg]
  rw [ENNReal.ofReal_toReal hμtop, ENNReal.ofReal_toReal hμx_top]
  rw [← hμE, hdiff]

theorem clipped_cdf_lipschitz
    {μ : Measure ℝ} [IsFiniteMeasure μ] {p q : ℝ} (hpq : p ≤ q)
    {C : ℝ≥0} (hC : LipschitzOnWith C (measureCDF μ) (Icc p q)) :
    LipschitzWith C (fun x : ℝ =>
      measureCDF μ ((Set.projIcc p q hpq x : Icc p q) : ℝ)) := by
  let f : Icc p q → ℝ := fun z => measureCDF μ (z : ℝ)
  have hf : LipschitzWith C f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hC.dist_le_mul (x : ℝ) x.2 (y : ℝ) y.2
    change |measureCDF μ (x : ℝ) - measureCDF μ (y : ℝ)| ≤
      (C : ℝ) * |(x : ℝ) - (y : ℝ)|
    exact h
  have hcomp := hf.comp (LipschitzWith.projIcc hpq)
  simpa [f, Function.comp_def] using hcomp

theorem clipped_ioc_inter
    {p q x y : ℝ} (hpq : p ≤ q) :
    Ioc x y ∩ Ioc p q =
      Ioc ((Set.projIcc p q hpq x : Icc p q) : ℝ)
        ((Set.projIcc p q hpq y : Icc p q) : ℝ) := by
  ext z
  simp only [mem_inter_iff, mem_Ioc, Set.coe_projIcc]
  constructor <;> intro h
  · rcases h with ⟨⟨hx, hy⟩, ⟨hp, hq⟩⟩
    constructor <;> grind
  · rcases h with ⟨hx, hy⟩
    constructor
    · constructor <;> grind
    · constructor <;> grind

theorem cdf_increment
    {μ : Measure ℝ} [IsFiniteMeasure μ] {x y : ℝ} (hxy : x < y) :
    measureCDF μ y - measureCDF μ x = μ.real (Ioc x y) := by
  have hsub : Iic x ⊆ Iic y := Iic_subset_Iic.mpr hxy.le
  have hμ := measureReal_sdiff (μ := μ) hsub measurableSet_Iic
  have hμE : μ (Iic y \ Iic x) = μ (Iic y) - μ (Iic x) :=
    measure_sdiff hsub measurableSet_Iic.nullMeasurableSet (measure_ne_top μ _)
  have hdiff : Iic y \ Iic x = Ioc x y := by
    ext z
    simp only [Set.mem_sdiff, mem_Iic, mem_Ioc]
    constructor
    · intro h
      exact ⟨lt_of_not_ge h.2, h.1⟩
    · intro h
      exact ⟨h.2, not_le_of_gt h.1⟩
  dsimp [measureCDF]
  rw [← hμ, hdiff]

def clippedCdf (μ : Measure ℝ) [IsFiniteMeasure μ] (p q : ℝ) (hpq : p ≤ q) :
    ℝ → ℝ := fun x => measureCDF μ ((Set.projIcc p q hpq x : Icc p q) : ℝ)

def clippedCdfStieltjes (μ : Measure ℝ) [IsFiniteMeasure μ] (p q : ℝ) (hpq : p ≤ q)
    {C : ℝ≥0}
    (hC : LipschitzOnWith C (measureCDF μ) (Icc p q)) : StieltjesFunction ℝ :=
  { toFun := clippedCdf μ p q hpq
    mono' := (measureCDF_monotone (μ := μ)).comp (Set.monotone_projIcc hpq)
    right_continuous' := fun _x =>
      (clipped_cdf_lipschitz hpq hC).continuous.continuousAt.continuousWithinAt }

theorem clipped_cdf_stieltjes_measure_eq
    {μ : Measure ℝ} [IsFiniteMeasure μ] {p q : ℝ} (hpq : p ≤ q)
    {C : ℝ≥0} (hC : LipschitzOnWith C (measureCDF μ) (Icc p q)) :
    (clippedCdfStieltjes μ p q hpq hC).measure = μ.restrict (Ioc p q) := by
  apply Measure.ext_of_Ioc
  intro x y hxy
  rw [StieltjesFunction.measure_Ioc, Measure.restrict_apply measurableSet_Ioc]
  simp only [clippedCdfStieltjes, clippedCdf]
  have hproj : (Set.projIcc p q hpq x : ℝ) ≤ (Set.projIcc p q hpq y : ℝ) :=
    (Set.monotone_projIcc hpq) hxy.le
  by_cases hstrict : (Set.projIcc p q hpq x : ℝ) <
      (Set.projIcc p q hpq y : ℝ)
  · rw [cdf_increment hstrict]
    rw [clipped_ioc_inter hpq]
    simp [MeasureTheory.measureReal_def]
  · have heq : (Set.projIcc p q hpq x : ℝ) =
        (Set.projIcc p q hpq y : ℝ) := le_antisymm hproj (le_of_not_gt hstrict)
    rw [heq]
    have hz : Ioc x y ∩ Ioc p q = ∅ := by
      rw [clipped_ioc_inter hpq, heq, Ioc_self]
    rw [hz, measure_empty]
    simp

def clippedRemainder (C : ℝ≥0) (G : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (C : ℝ) * x - G x

theorem clippedRemainder_monotone
    {C : ℝ≥0} {G : ℝ → ℝ} (hG : Monotone G)
    (hLip : LipschitzWith C G) : Monotone (clippedRemainder C G) := by
  intro x y hxy
  dsimp [clippedRemainder]
  have hd := hLip.dist_le_mul x y
  rw [Real.dist_eq] at hd
  have hdist : |G y - G x| ≤ (C : ℝ) * (y - x) := by
    rw [abs_sub_comm]
    have hxy' : dist x y = y - x := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)]
      linarith
    rw [hxy'] at hd
    exact hd
  have hle : G y - G x ≤ (C : ℝ) * (y - x) := (abs_le.mp hdist).2
  have hGxy := hG hxy
  linarith

theorem clipped_measure_le_smul_volume
    {μ : Measure ℝ} [IsFiniteMeasure μ] {p q : ℝ} (hpq : p ≤ q)
    {C : ℝ≥0} (hC : LipschitzOnWith C (measureCDF μ) (Icc p q)) :
    μ.restrict (Ioc p q) ≤ (C : ℝ≥0∞) • volume := by
  let G : ℝ → ℝ := clippedCdf μ p q hpq
  let R : ℝ → ℝ := clippedRemainder C G
  let Rst : StieltjesFunction ℝ :=
    { toFun := R
      mono' := clippedRemainder_monotone
        ((measureCDF_monotone (μ := μ)).comp (Set.monotone_projIcc hpq))
        (clipped_cdf_lipschitz hpq hC)
      right_continuous' := fun x => by
        change ContinuousWithinAt R (Ici x) x
        exact ((continuous_const.mul continuous_id).sub
          (clipped_cdf_lipschitz hpq hC).continuous).continuousWithinAt }
  have hsum : clippedCdfStieltjes μ p q hpq hC + Rst =
      (C : ℝ≥0) • StieltjesFunction.id := by
    apply StieltjesFunction.ext
    intro x
    change measureCDF μ ((Set.projIcc p q hpq x : Icc p q) : ℝ) +
      ((C : ℝ) * x - measureCDF μ ((Set.projIcc p q hpq x : Icc p q) : ℝ)) =
      (C : ℝ) * x
    ring
  have hmeasure :
      (clippedCdfStieltjes μ p q hpq hC).measure + Rst.measure =
        (C : ℝ≥0∞) • volume := by
    calc
      _ = (clippedCdfStieltjes μ p q hpq hC + Rst).measure :=
        (StieltjesFunction.measure_add _ _).symm
      _ = ((C : ℝ≥0) • StieltjesFunction.id).measure :=
        congrArg (fun f : StieltjesFunction ℝ => f.measure) hsum
      _ = (C : ℝ≥0∞) • volume := by
        rw [StieltjesFunction.measure_smul, ← Real.volume_eq_stieltjes_id]
        rfl
  have hle : (clippedCdfStieltjes μ p q hpq hC).measure ≤
      (C : ℝ≥0∞) • volume := by
    rw [← hmeasure]
    exact Measure.le_add_right le_rfl
  simpa [clipped_cdf_stieltjes_measure_eq hpq hC] using hle

theorem clipped_measure_le_smul_volume_restrict
    {μ : Measure ℝ} [IsFiniteMeasure μ] {p q : ℝ} (hpq : p ≤ q)
    {C : ℝ≥0} (hC : LipschitzOnWith C (measureCDF μ) (Icc p q)) :
    μ.restrict (Ioc p q) ≤ (C : ℝ≥0∞) • volume.restrict (Ioc p q) := by
  have h := clipped_measure_le_smul_volume hpq hC
  have h' := Measure.restrict_mono_measure h (Ioc p q)
  simpa [Measure.restrict_smul] using h'

theorem clipped_measure_le_smul_volume_Icc
    {μ : Measure ℝ} [IsFiniteMeasure μ] {r p q : ℝ} (hrp : r < p) (hpq : p ≤ q)
    {C : ℝ≥0} (hC : LipschitzOnWith C (measureCDF μ) (Icc r q)) :
    μ.restrict (Icc p q) ≤ (C : ℝ≥0∞) • volume.restrict (Icc p q) := by
  have hdom : μ.restrict (Ioc r q) ≤ (C : ℝ≥0∞) • volume := by
    exact clipped_measure_le_smul_volume (p := r) (q := q)
      (le_trans hrp.le hpq) hC
  have hset : Icc p q ⊆ Ioc r q := by
    intro x hx
    exact ⟨lt_of_lt_of_le hrp hx.1, hx.2⟩
  have hres := Measure.restrict_mono_measure hdom (Icc p q)
  rw [Measure.restrict_restrict_of_subset hset, Measure.restrict_smul] at hres
  simpa using hres

/-- The RN density of a measure bounded by a finite scalar multiple is bounded. -/
theorem rnDeriv_memLp_top_of_le_smul
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [SigmaFinite μ] [SigmaFinite ν]
    {C : NNReal} (h : μ ≤ (C : ℝ≥0∞) • ν) :
    MemLp (fun x => (μ.rnDeriv ν x).toReal) ∞ ν := by
  have hae : μ.rnDeriv ν ≤ᵐ[ν] (fun _ => (C : ℝ≥0∞)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (Measure.measurable_rnDeriv μ ν)
    intro s hs hst
    calc
      ∫⁻ x in s, μ.rnDeriv ν x ∂ν ≤ μ s := Measure.setLIntegral_rnDeriv_le s
      _ ≤ ((C : ℝ≥0∞) • ν) s := h s
      _ = ∫⁻ x in s, (C : ℝ≥0∞) ∂ν := by
        simp [Measure.smul_apply]
  have htop : ∀ᵐ x ∂ν, μ.rnDeriv ν x < ∞ := by
    exact Measure.rnDeriv_lt_top μ ν
  have hbound : ∀ᵐ x ∂ν, ‖(μ.rnDeriv ν x).toReal‖ ≤ (C : ℝ) := by
    filter_upwards [hae, htop] with x hx hxtop
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_le_toReal hxtop.ne (by simp)).2 hx
  have hmeas : AEStronglyMeasurable (fun x => (μ.rnDeriv ν x).toReal) ν :=
    (Measure.measurable_rnDeriv μ ν).ennreal_toReal.aestronglyMeasurable
  apply memLp_top_of_bound hmeas (C : ℝ)
  exact hbound

/-- The cumulative distribution function is bounded by the total mass. -/
theorem measureCDF_bounded {μ : Measure ℝ} [IsFiniteMeasure μ] (K : Set ℝ) :
    ∀ x ∈ K, |measureCDF μ x| ≤ (μ Set.univ).toReal := by
  intro x hx
  change |(μ (Iic x)).toReal| ≤ (μ Set.univ).toReal
  rw [abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (measure_ne_top μ _)
    (measure_mono (Set.subset_univ _))

/-- The cumulative distribution function is integrable on every compact interval. -/
theorem measureCDF_integrableOn_Icc {μ : Measure ℝ} [IsFiniteMeasure μ] (a b : ℝ) :
    IntegrableOn (measureCDF μ) (Icc a b) volume := by
  apply Measure.integrableOn_of_bounded (measure_Icc_lt_top.ne)
    (measureCDF_monotone (μ := μ)).measurable.aestronglyMeasurable
    (M := (μ Set.univ).toReal)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact measureCDF_bounded (μ := μ) (Icc a b) x hx

theorem measureCDF_eq_const_sub_deriv_of_sub_eq_intervalIntegral
    {μ : Measure ℝ} [IsFiniteMeasure μ] {a b c : ℝ} {v : ℝ → ℝ}
    (hdiff : DifferentiableOn ℝ v (Ioo a b))
    (hsub : ∀ ⦃x y⦄, x ∈ Ioo a b → y ∈ Ioo a b →
      v y - v x = ∫ t in x..y, (c - measureCDF μ t)) :
    ∀ x ∈ Ioo a b, measureCDF μ x = c - deriv v x := by
  intro x hx
  let w : ℝ → ℝ := fun t => c - measureCDF μ t
  let F : ℝ → ℝ := fun y => ∫ t in x..y, w t
  have hI : IntervalIntegrable w volume x x := by
    apply intervalIntegrable_const.sub
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le le_rfl).2
    exact (measureCDF_integrableOn_Icc (μ := μ) x x).mono_set (by intro y hy; exact hy)
  have hwmeas : Measurable w := by
    exact measurable_const.sub (measureCDF_monotone (μ := μ)).measurable
  have hwstrong : StronglyMeasurableAtFilter w (𝓝[>] x) :=
    hwmeas.stronglyMeasurable.stronglyMeasurableAtFilter
  have hwcont : ContinuousWithinAt w (Ioi x) x := by
    exact (continuousWithinAt_const.sub (measureCDF_continuousWithinAt_Ici x)).mono_left
      (nhdsWithin_mono x Ioi_subset_Ici_self)
  have hFderiv : HasDerivWithinAt F (w x) (Ici x) x := by
    exact intervalIntegral.integral_hasDerivWithinAt_right (a := x) (b := x)
      (s := Ici x) (t := Ioi x) hI hwstrong hwcont
  have hv : HasDerivAt v (deriv v x) x :=
    (hdiff x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2) |>.hasDerivAt
  have hVderiv : HasDerivWithinAt (fun y => v y - v x) (deriv v x) (Ici x) x :=
    hv.sub_const (v x) |>.hasDerivWithinAt
  have hEq : (fun y => F y) =ᶠ[𝓝[Ici x] x] (fun y => v y - v x) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hx.1 hx.2)] with y hy
    dsimp [F, w]
    exact (hsub hx hy).symm
  have hFderiv' : HasDerivWithinAt (fun y => v y - v x) (w x) (Ici x) x :=
    hFderiv.congr_of_eventuallyEq hEq.symm (by simp [F])
  have heq' :=
    (uniqueDiffWithinAt_Ici x).eq hFderiv'.hasFDerivWithinAt hVderiv.hasFDerivWithinAt
  have heq : w x = deriv v x := by simpa using congrArg (fun L => L 1) heq'
  dsimp [w] at heq
  linarith

/-- The tail integral of the derivative of a compactly supported Schwartz function. -/
theorem integral_Ioi_deriv_schwartz
    (φ : SchwartzMap ℝ ℝ) (hφ : HasCompactSupport φ) (t : ℝ) :
    ∫ x in Ioi t, deriv φ x = -φ t := by
  exact hφ.integral_Ioi_deriv_eq (φ.smooth 1) t

/-- The corresponding left-tail integral of the derivative. -/
theorem integral_Iic_deriv_schwartz
    (φ : SchwartzMap ℝ ℝ) (hφ : HasCompactSupport φ) (t : ℝ) :
    ∫ x in Iic t, deriv φ x = φ t := by
  exact hφ.integral_Iic_deriv_eq (φ.smooth 1) t

/-- The kernel appearing in the CDF/Fubini identity is integrable. -/
theorem measureCDF_kernel_integrable
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (φ : SchwartzMap ℝ ℝ) (hφ : HasCompactSupport φ) :
    Integrable
      (Set.indicator {z : ℝ × ℝ | z.1 ≤ z.2}
        (fun z ↦ deriv φ z.2)) (μ.prod volume) := by
  let s : Set (ℝ × ℝ) := {z | z.1 ≤ z.2}
  have hs : MeasurableSet s := measurableSet_le measurable_fst measurable_snd
  have hd : Integrable (deriv φ) volume :=
    (φ.smooth 1).continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hφ.deriv
  have hone : Integrable (fun _ : ℝ ↦ (1 : ℝ)) μ := by
    exact integrable_const_iff.mpr (Or.inr inferInstance)
  have hprod : Integrable (fun z : ℝ × ℝ ↦ deriv φ z.2) (μ.prod volume) :=
    by simpa using hone.mul_prod hd
  exact hprod.indicator hs

/-- Fubini rewrites the CDF pairing as a pairing with its upper-tail kernel. -/
theorem measureCDF_kernel_fubini
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (φ : SchwartzMap ℝ ℝ) (hφ : HasCompactSupport φ) :
    ∫ x : ℝ, measureCDF μ x * deriv φ x =
      ∫ t : ℝ, ∫ x : ℝ,
        (if t ≤ x then (1 : ℝ) else 0) * deriv φ x ∂volume ∂μ := by
  have hi := measureCDF_kernel_integrable (μ := μ) φ hφ
  calc
    ∫ x : ℝ, measureCDF μ x * deriv φ x =
        ∫ x : ℝ, (∫ t : ℝ, (if t ≤ x then (1 : ℝ) else 0) ∂μ) * deriv φ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show (fun t : ℝ ↦ if t ≤ x then (1 : ℝ) else 0) =
          (Iic x).indicator 1 by
            funext t
            by_cases h : t ≤ x <;> simp [indicator_of_mem, h]]
      rw [integral_indicator_one measurableSet_Iic, measureCDF]
    _ = ∫ t : ℝ, ∫ x : ℝ,
        (if t ≤ x then (1 : ℝ) else 0) * deriv φ x ∂volume ∂μ := by
      let k : ℝ × ℝ → ℝ := fun z ↦
        (if z.1 ≤ z.2 then (1 : ℝ) else 0) * deriv φ z.2
      have hk : Integrable k (μ.prod volume) := by
        apply hi.congr
        filter_upwards [] with z
        by_cases hz : z.1 ≤ z.2 <;> simp [k, hz]
      have hprod := integral_prod k hk
      have hswap := integral_prod_symm k hk
      calc
        _ = ∫ x : ℝ, ∫ t : ℝ, k (t, x) ∂μ ∂volume := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp_rw [k]
          rw [MeasureTheory.integral_mul_const]
        _ = ∫ z : ℝ × ℝ, k z ∂μ.prod volume := hswap.symm
        _ = ∫ t : ℝ, ∫ x : ℝ, k (t, x) ∂volume ∂μ := hprod

/-- A finite measure is the negative distributional derivative of its cumulative function. -/
theorem measureCDF_distributional_derivative
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (φ : SchwartzMap ℝ ℝ) (hφ : HasCompactSupport φ) :
    ∫ x, measureCDF μ x * deriv φ x = -∫ x, φ x ∂μ := by
  rw [measureCDF_kernel_fubini (μ := μ) φ hφ]
  have hinner : ∀ t : ℝ,
      ∫ x : ℝ, (if t ≤ x then (1 : ℝ) else 0) * deriv φ x ∂volume = -φ t := by
    intro t
    calc
      ∫ x : ℝ, (if t ≤ x then (1 : ℝ) else 0) * deriv φ x ∂volume =
          ∫ x in Ici t, deriv φ x := by
        rw [← integral_indicator measurableSet_Ici]
        apply integral_congr_ae
        filter_upwards [] with x
        by_cases hx : t ≤ x <;> simp [hx]
      _ = ∫ x in Ioi t, deriv φ x := integral_Ici_eq_integral_Ioi
      _ = -φ t := integral_Ioi_deriv_schwartz φ hφ t
  simp_rw [hinner]
  rw [integral_neg]

/-- Compactly supported smooth scalar tests separate locally integrable functions on an interval.

This wrapper asserts vanishing of the function itself, not a derivative-zero-implies-constant
statement. -/
theorem locallyIntegrableOn_ae_eq_zero_of_compactSmooth_pairings_eq_zero
    {w : ℝ → ℝ} {a b : ℝ} (_hab : a < b)
    (hw : LocallyIntegrableOn w (Ioo a b) volume)
    (hweak : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b → ∫ x, g x * w x ∂volume = 0) :
    ∀ᵐ x ∂volume, x ∈ Ioo a b → w x = 0 := by
  apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo hw
  intro g hg hcompact hsupport
  simpa [smul_eq_mul] using hweak g hg hcompact hsupport

/-- The weak-derivative pairing with a positive-half-line Schwartz test is a whole-line integral. -/
theorem inner_weakDeriv_toHalfLineH1_eq_integral
    (f : HalfLineH1) (φ : PositiveTestFunction) :
    inner ℝ f.weakDeriv (PositiveTestFunction.toHalfLineH1 φ).weakDeriv =
      ∫ x : ℝ, (f.weakDeriv : ℝ → ℝ) x * deriv φ.1 x := by
  rw [← l2Pairing_eq_inner, l2Pairing,
    ContinuousLinearMap.lpPairing_eq_integral]
  rw [PositiveTestFunction.weakDeriv_toHalfLineH1]
  apply integral_congr_ae
  filter_upwards [(Lp.memLp f.weakDeriv).coeFn_toLp,
    (SchwartzMap.derivCLM ℝ ℝ φ.1).coeFn_toLp 2 volume] with x hx hφ
  simp [hφ]

/-- The value pairing with a positive-half-line Schwartz test is a whole-line integral. -/
theorem inner_value_toHalfLineH1_eq_integral
    (f : HalfLineH1) (φ : PositiveTestFunction) :
    inner ℝ f.value (PositiveTestFunction.toHalfLineH1 φ).value =
      ∫ x : ℝ, f.continuousRep x * φ.1 x := by
  rw [← l2Pairing_eq_inner, l2Pairing,
    ContinuousLinearMap.lpPairing_eq_integral]
  rw [PositiveTestFunction.value_toHalfLineH1]
  apply integral_congr_ae
  filter_upwards [(Lp.memLp f.value).coeFn_toLp,
    φ.1.coeFn_toLp 2 volume, f.continuousRep_ae_eq_value] with x hx hφ hrep
  simp [hφ, hrep]

/-- The integral of an affine forcing term against a Schwartz test splits into its
    zeroth and first moments. -/
lemma integral_affine_forcing_mul_schwartz
    {F : ℝ → ℝ} {a b : ℝ} (φ : SchwartzMap ℝ ℝ)
    (hFφ : Integrable (fun x : ℝ => F x * φ x) volume)
    (hφ : Integrable (fun x : ℝ => φ x) volume)
    (hφx : Integrable (fun x : ℝ => x * φ x) volume) :
    (∫ x : ℝ, (F x - a - b * x) * φ x) =
      (∫ x : ℝ, F x * φ x) - a * (∫ x : ℝ, φ x) -
        b * (∫ x : ℝ, x * φ x) := by
  have hbody : (fun x : ℝ => (F x - a - b * x) * φ x) =
      (fun x : ℝ => F x * φ x - a * φ x - b * (x * φ x)) := by
    funext x
    ring
  rw [hbody]
  calc
    (∫ x : ℝ, F x * φ x - a * φ x - b * (x * φ x)) =
        (∫ x : ℝ, F x * φ x - a * φ x) - ∫ x : ℝ, b * (x * φ x) := by
      simpa only [Pi.sub_apply] using
        integral_sub (hFφ.sub (hφ.const_mul a)) (hφx.const_mul b)
    _ = ((∫ x : ℝ, F x * φ x) - ∫ x : ℝ, a * φ x) -
        ∫ x : ℝ, b * (x * φ x) := by
      congr 1
      simpa only [Pi.sub_apply] using integral_sub hFφ (hφ.const_mul a)
    _ = _ := by
      rw [integral_const_mul, integral_const_mul]

/-- The O3 weak KKT equation written against a whole-line Schwartz test. -/
theorem HalfLineH1.CorrectionBumps.weak_KKT_equation_schwartz
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (φ : SchwartzMap ℝ ℝ)
    (hcompact : HasCompactSupport φ)
    (hsupport : tsupport φ ⊆ Ioi 0) :
    ∫ x : Ioi (0 : ℝ), φ x ∂B.reactionMeasure hfmin =
      (∫ x : ℝ, (f.weakDeriv : ℝ → ℝ) x * deriv φ x)
      - (f.rayleighQuotient * (∫ x : ℝ, f.continuousRep x * φ x))
      + (B.massMultiplier * (∫ x : ℝ, φ x))
      + (B.momentMultiplier * (∫ x : ℝ, x * φ x)) := by
  let ψ : PositiveTestFunction := ⟨φ, hsupport⟩
  have h := B.weak_KKT_equation hfmin ψ hcompact
  rw [inner_weakDeriv_toHalfLineH1_eq_integral f ψ,
    inner_value_toHalfLineH1_eq_integral f ψ] at h
  simpa only [ψ, PositiveTestFunction.testMass, PositiveTestFunction.testFirstMoment,
    add_assoc] using h

/-- The Schwartz-test KKT equation solved for the weak derivative pairing. -/
theorem HalfLineH1.CorrectionBumps.weak_KKT_equation_schwartz_deriv
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (φ : SchwartzMap ℝ ℝ)
    (hcompact : HasCompactSupport φ)
    (hsupport : tsupport φ ⊆ Ioi 0) :
    (∫ x : ℝ, (f.weakDeriv : ℝ → ℝ) x * deriv φ x) =
      ∫ x : Ioi (0 : ℝ), φ x ∂B.reactionMeasure hfmin +
      (∫ x : ℝ, (f.rayleighQuotient * f.continuousRep x
        - B.massMultiplier - B.momentMultiplier * x) * φ x) := by
  have h := B.weak_KKT_equation_schwartz hfmin φ hcompact hsupport
  have hmass : Integrable (φ : ℝ → ℝ) volume := φ.integrable
  have hmoment : Integrable (fun x : ℝ => x * φ x) volume :=
    (φ.integrable_pow_mul volume 1).mono
      (continuous_id.mul φ.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp [norm_mul, Real.norm_eq_abs])
  have hvalue : Integrable (fun x : ℝ => f.continuousRep x * φ x) volume :=
    f.continuousRep_memLp.integrable_mul (φ.memLp 2 volume)
  have hright :
      (∫ x : ℝ, (f.rayleighQuotient * f.continuousRep x
        - B.massMultiplier - B.momentMultiplier * x) * φ x) =
        f.rayleighQuotient * (∫ x : ℝ, f.continuousRep x * φ x) -
           B.massMultiplier * (∫ x : ℝ, φ x) -
           B.momentMultiplier * (∫ x : ℝ, x * φ x) := by
    rw [← integral_const_mul]
    simpa only [mul_assoc] using integral_affine_forcing_mul_schwartz φ
      (F := fun x => f.rayleighQuotient * f.continuousRep x)
      (a := B.massMultiplier) (b := B.momentMultiplier)
      (by simpa only [mul_assoc] using hvalue.const_mul f.rayleighQuotient)
      hmass hmoment
  have h' := h
  linarith [h', hright]

/-- The compact part of the positive half-line lying in a real interval. -/
def localReactionSet (a b : ℝ) : Set (Ioi (0 : ℝ)) :=
  {x | (x : ℝ) ∈ Icc a b}

/-- The reaction measure restricted to `[a,b]`, transported to the real line. -/
  def HalfLineH1.CorrectionBumps.localReactionMeasure
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (a b : ℝ) : Measure ℝ :=
  Measure.map (Subtype.val : Ioi (0 : ℝ) → ℝ)
    ((B.reactionMeasure hfmin).restrict (localReactionSet a b))

/-- The localized reaction set is compact when its interval is nonempty and positive. -/
theorem HalfLineH1.CorrectionBumps.localReactionSet_isCompact
    {a b : ℝ} (ha : 0 < a) :
    IsCompact (localReactionSet a b) := by
  rw [show localReactionSet a b =
      (Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Icc a b by rfl]
  rw [Subtype.isCompact_iff]
  have himage :
      (Subtype.val : Ioi (0 : ℝ) → ℝ) ''
          ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Icc a b) = Icc a b := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨⟨x, lt_of_lt_of_le ha hx.1⟩, hx, rfl⟩
  rw [himage]
  exact isCompact_Icc

/-- The localized reaction measure is finite. -/
theorem HalfLineH1.CorrectionBumps.localReactionMeasure_isFinite
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) :
    IsFiniteMeasure (B.localReactionMeasure hfmin a b) := by
  apply IsFiniteMeasure.mk
  rw [HalfLineH1.CorrectionBumps.localReactionMeasure,
    Measure.map_apply continuous_subtype_val.measurable MeasurableSet.univ]
  simp only [preimage_univ]
  rw [Measure.restrict_apply MeasurableSet.univ]
  let _ : IsFiniteMeasureOnCompacts (B.reactionMeasure hfmin) :=
    B.reactionMeasure_isFiniteMeasureOnCompacts hfmin
  have hfin : (B.reactionMeasure hfmin)
      (univ ∩ localReactionSet a b) < ⊤ := by
    rw [univ_inter]
    exact localReactionSet_isCompact ha |>.measure_lt_top
  exact hfin

/-- Integrals against the localized real-line measure pull back to the restricted measure. -/
theorem HalfLineH1.CorrectionBumps.integral_localReactionMeasure
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (_ha : 0 < a)
    (φ : ℝ → ℝ)
    (hφ : AEStronglyMeasurable φ (B.localReactionMeasure hfmin a b)) :
    ∫ x : ℝ, φ x ∂B.localReactionMeasure hfmin a b =
      ∫ x : Ioi (0 : ℝ), φ (x : ℝ) ∂
        (B.reactionMeasure hfmin).restrict (localReactionSet a b) := by
  exact MeasureTheory.integral_map continuous_subtype_val.measurable.aemeasurable hφ

/-- Compactly supported Schwartz tests supported in `(a,b)` see the full localized measure. -/
theorem HalfLineH1.CorrectionBumps.integral_localReactionMeasure_schwartz
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a)
    (φ : SchwartzMap ℝ ℝ) (_hφ : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ Ioo a b) :
    ∫ x : ℝ, φ x ∂B.localReactionMeasure hfmin a b =
      ∫ x : Ioi (0 : ℝ), φ x ∂B.reactionMeasure hfmin := by
  have hmeas : AEStronglyMeasurable φ (B.localReactionMeasure hfmin a b) :=
    φ.continuous.aestronglyMeasurable
  rw [B.integral_localReactionMeasure hfmin ha φ hmeas]
  change ∫ x : Ioi (0 : ℝ), φ (x : ℝ) ∂
      ((B.reactionMeasure hfmin).restrict (localReactionSet a b)) = _
  have hzero : ∀ x ∈ (localReactionSet a b)ᶜ, φ (x : ℝ) = 0 := by
    intro x hx
    by_contra hne
    have hts : (x : ℝ) ∈ tsupport φ := by
      exact not_not.mp (fun h' => hne (image_eq_zero_of_notMem_tsupport h'))
    have hI := hsupp hts
    exact hx ⟨le_of_lt hI.1, hI.2.le⟩
  rw [← integral_union_eq_left_of_forall (s := localReactionSet a b)
    (t := (localReactionSet a b)ᶜ)
    ((measurableSet_Icc.preimage continuous_subtype_val.measurable).compl) hzero]
  rw [union_compl_self]
  simp only [Measure.restrict_univ]

/-- A primitive of a continuous forcing, normalized to vanish at a chosen point. -/
def forcingPrimitive (F : ℝ → ℝ) (c x : ℝ) : ℝ := ∫ t in c..x, F t

/-- The forcing primitive of a continuous function is continuous. -/
theorem forcingPrimitive_continuous
    {F : ℝ → ℝ} (hF : Continuous F) (c : ℝ) :
    Continuous (forcingPrimitive F c) := by
  exact intervalIntegral.continuous_primitive (f := F) (μ := volume)
    (fun a b => hF.intervalIntegrable a b) c

/-- The derivative of the forcing primitive is the forcing function. -/
theorem forcingPrimitive_hasDerivAt
    {F : ℝ → ℝ} (hF : Continuous F) (c x : ℝ) :
    HasDerivAt (forcingPrimitive F c) (F x) x := by
  change HasDerivAt (fun y => ∫ t in c..y, F t) (F x) x
  exact (hF.integral_hasStrictDerivAt c x).hasDerivAt

theorem forcingPrimitive_lipschitzOn
    {F : ℝ → ℝ} {a p q : ℝ} (hF : Continuous F) (hpq : p ≤ q) :
    ∃ C : NNReal, LipschitzOnWith C (forcingPrimitive F a) (Icc p q) := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn
  let C : NNReal := Real.toNNReal K
  refine ⟨C, ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (s := Icc p q)
    (f := forcingPrimitive F a) (f' := F) (convex_Icc p q)
  · intro x hx
    exact (forcingPrimitive_hasDerivAt hF a x).hasDerivWithinAt
  · intro x hx
    have hnorm : ‖F x‖ ≤ K := hK x hx
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.coe_toNNReal]
    · exact hnorm
    · exact le_trans (norm_nonneg _) (hK p (mem_Icc.2 ⟨le_rfl, hpq⟩))

/-- A second primitive of a continuous forcing, normalized at a chosen point. -/
def forcingPotential (F : ℝ → ℝ) (c x : ℝ) : ℝ :=
  forcingPrimitive (forcingPrimitive F c) c x

/-- The second primitive of a continuous function is continuous. -/
theorem forcingPotential_continuous
    {F : ℝ → ℝ} (hF : Continuous F) (c : ℝ) :
    Continuous (forcingPotential F c) := by
  exact forcingPrimitive_continuous (forcingPrimitive_continuous hF c) c

/-- The derivative of the second primitive is the first primitive. -/
theorem forcingPotential_hasDerivAt
    {F : ℝ → ℝ} (hF : Continuous F) (c x : ℝ) :
    HasDerivAt (forcingPotential F c) (forcingPrimitive F c x) x := by
  exact forcingPrimitive_hasDerivAt (forcingPrimitive_continuous hF c) c x

theorem forcingPotential_sub_eq_integral_forcingPrimitive
    {F : ℝ → ℝ} (hF : Continuous F) (c x y : ℝ) :
    forcingPotential F c y - forcingPotential F c x =
      ∫ t in x..y, forcingPrimitive F c t := by
  have hcy := (forcingPrimitive_continuous hF c).intervalIntegrable c y (μ := volume)
  have hcx := (forcingPrimitive_continuous hF c).intervalIntegrable c x (μ := volume)
  have h := intervalIntegral.integral_interval_sub_left hcy hcx
  change (∫ t in c..y, forcingPrimitive F c t) -
    (∫ t in c..x, forcingPrimitive F c t) = _
  exact h

/-- A continuous function times a compactly supported Schwartz function is integrable. -/
theorem continuous_mul_schwartz_integrable
    {g : ℝ → ℝ} (hg : Continuous g)
    (φ : SchwartzMap ℝ ℝ) (hφ : HasCompactSupport φ) :
    Integrable (fun x => g x * φ x) volume := by
  have hsupp : Function.support (fun x => g x * φ x) ⊆ tsupport φ := by
    intro x hx
    by_contra hxt
    have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hxt
    exact hx (by simp [hφx])
  have hcompact : HasCompactSupport (fun x => g x * φ x) := by
    exact HasCompactSupport.of_support_subset_isCompact hφ.isCompact hsupp
  exact (hg.mul φ.continuous).integrable_of_hasCompactSupport hcompact

theorem LocallyIntegrableOn.integrable_mul_of_continuous_hasCompactSupport
    {w g : ℝ → ℝ} {U : Set ℝ}
    (hw : LocallyIntegrableOn w U volume)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ U) :
    Integrable (fun x => g x * w x) volume := by
  let K := tsupport g
  have hK : IsCompact K := hgc.isCompact
  have hwK : IntegrableOn w K volume :=
    (hw.mono_set hgs).integrableOn_isCompact hK
  have hmulK : IntegrableOn (fun x => w x * g x) K volume :=
    hwK.mul_continuousOn hg.continuousOn hK
  have hmul : Integrable (K.indicator (fun x => w x * g x)) volume :=
    hmulK.integrable_indicator hK.measurableSet
  apply hmul.congr
  filter_upwards [] with x
  by_cases hx : x ∈ K
  · simp [hx, mul_comm]
  · have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hx, hgx]

theorem IsCompact.exists_Icc_subset_Ioo_of_subset
    {K : Set ℝ} {a b : ℝ} (hK : IsCompact K) (hKU : K ⊆ Ioo a b) (hab : a < b) :
    ∃ A B, a < A ∧ A < B ∧ B < b ∧ K ⊆ Icc A B := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hxK, hx⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨y, hyK, hy⟩ := hK.exists_isMaxOn hne continuous_id.continuousOn
    let A := (a + x) / 2
    let B := (y + b) / 2
    refine ⟨A, B, ?_, ?_, ?_, ?_⟩
    · dsimp [A]
      linarith [(hKU hxK).1]
    · dsimp [A, B]
      have hxy : x ≤ y := hx.isGLB hxK |>.1 ⟨y, hyK, rfl⟩
      linarith [hab, (hKU hxK).1, (hKU hyK).2, hxy]
    · dsimp [B]
      linarith [(hKU hyK).2]
    · intro z hz
      constructor
      · dsimp [A]
        have hmin : x ≤ z := by
          exact hx hz
        linarith [(hKU hxK).1]
      · dsimp [B]
        have hmax : z ≤ y := by
          exact hy hz
        linarith [(hKU hyK).2]
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    let A := (2 * a + b) / 3
    let B := (a + 2 * b) / 3
    refine ⟨A, B, ?_, ?_, ?_, ?_⟩
    · dsimp [A]
      linarith
    · dsimp [A, B]
      linarith
    · dsimp [B]
      linarith
    · rw [hKempty]
      exact empty_subset _

theorem exists_normalized_schwartz_bump_Ioo
    {a b : ℝ} (hab : a < b) :
    ∃ η : SchwartzMap ℝ ℝ, HasCompactSupport η ∧ tsupport η ⊆ Ioo a b ∧
      (∀ x, 0 ≤ η x) ∧ (∫ x, η x) = 1 := by
  let m := (a + b) / 2
  have hm : m ∈ Ioo a b := by
    dsimp [m]
    constructor <;> linarith
  obtain ⟨g, hgs, hgc, hgdiff, hgrange, hgm⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (isOpen_Ioo.mem_nhds hm)
  let η₀ : SchwartzMap ℝ ℝ := hgc.toSchwartzMap hgdiff
  have hnonneg : ∀ x, 0 ≤ η₀ x := by
    intro x
    exact hgrange ⟨x, rfl⟩ |>.1
  have hpos : 0 < ∫ x, η₀ x := by
    exact hgdiff.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hgc
      hnonneg (by simpa [η₀] using (show g m ≠ 0 by linarith [hgm]))
  let η : SchwartzMap ℝ ℝ := (∫ x, η₀ x)⁻¹ • η₀
  have hηcomp : HasCompactSupport η := by
    refine HasCompactSupport.of_support_subset_isCompact hgc.isCompact ?_
    intro x hx
    have hη0 : η₀ x ≠ 0 := by
      intro hzero
      apply hx
      simp [η, hzero]
    have hsupp : x ∈ Function.support (g : ℝ → ℝ) := by
      simpa [η₀] using hη0
    exact subset_closure hsupp
  refine ⟨η, hηcomp, ?_, ?_, ?_⟩
  · intro x hx
    apply hgs
    change x ∈ closure (Function.support (η : ℝ → ℝ)) at hx
    exact closure_mono (by
      intro y hy
      have hη0 : η₀ y ≠ 0 := by
        intro hzero
        apply hy
        simp [η, hzero]
      simpa [η₀] using hη0) hx
  · intro x
    simp only [η, smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hpos)) (hnonneg x)
  · simp only [η, smul_apply, smul_eq_mul, integral_const_mul]
    field_simp

theorem exists_schwartz_primitive_of_integral_eq_zero
    {g : ℝ → ℝ} {A B C D : ℝ} (hCA : C < A) (hBD : B < D)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgt : tsupport g ⊆ Icc A B) (hzero : ∫ x, g x = 0) :
    ∃ φ : SchwartzMap ℝ ℝ,
      HasCompactSupport φ ∧ tsupport φ ⊆ Icc C D ∧
      (∀ x, deriv φ x = g x) := by
  let q : ℝ → ℝ := fun x => ∫ t in C..x, g t
  have hgc : Continuous g := hg.continuous
  have hderiv : ∀ x, deriv q x = g x := by
    intro x
    exact Continuous.deriv_integral g hgc C x
  have hzero_interval : ∀ {u v : ℝ}, u ≤ v →
      (∀ t ∈ Ioc u v, g t = 0) → (∫ t in u..v, g t) = 0 := by
    intro u v huv hvan
    rw [intervalIntegral.integral_of_le huv]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hvan t ht
  have hsupport : Function.support q ⊆ Icc C D := by
    intro x hx
    rcases lt_or_ge x C with hxleft | hxmid
    · exfalso
      apply hx
      change (∫ t in C..x, g t) = 0
      rw [intervalIntegral.integral_symm]
      have hvan : ∀ t ∈ Ioc x C, g t = 0 := by
        intro t ht
        by_contra hne
        have hts : t ∈ tsupport g := by
          exact not_not.mp (fun h => hne (image_eq_zero_of_notMem_tsupport h))
        exact (not_lt_of_ge (hgt hts).1) (ht.2.trans_lt hCA)
      rw [hzero_interval hxleft.le hvan]
      simp
    · rcases lt_or_ge x D with hxright | hright
      · exact ⟨hxmid, hxright.le⟩
      · exfalso
        apply hx
        change (∫ t in C..x, g t) = 0
        have hsub : Function.support g ⊆ Ioc C x := by
          intro t ht
          have hts : t ∈ tsupport g := subset_closure ht
          exact ⟨lt_of_lt_of_le hCA (hgt hts).1,
            (hgt hts).2.trans_lt (hBD.trans_le hright) |>.le⟩
        rw [intervalIntegral.integral_eq_integral_of_support_subset hsub, hzero]
  have hqcompact : HasCompactSupport q :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport
  have hqdiff : ContDiff ℝ (⊤ : ℕ∞) q := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨?_, ?_⟩
    · exact fun x => (hgc.integral_hasStrictDerivAt C x).hasDerivAt.differentiableAt
    · rw [show deriv q = g by funext x; exact hderiv x]
      exact hg
  exact ⟨hqcompact.toSchwartzMap hqdiff, hqcompact,
    closure_minimal hsupport isClosed_Icc, hderiv⟩

theorem support_sub_const_mul_subset
    (g η : ℝ → ℝ) (k : ℝ) :
    Function.support (fun x => g x - k * η x) ⊆
      Function.support g ∪ Function.support η := by
  intro x hx
  by_cases hgx : g x = 0
  · by_cases hηx : η x = 0
    · exact False.elim (hx (by simp [hgx, hηx]))
    · exact Or.inr hηx
  · exact Or.inl hgx

theorem tsupport_sub_const_mul_subset
    (g η : ℝ → ℝ) (k : ℝ) :
    tsupport (fun x => g x - k * η x) ⊆ tsupport g ∪ tsupport η := by
  have hsupport : Function.support (fun x => g x - k * η x) ⊆
      tsupport g ∪ tsupport η :=
    (support_sub_const_mul_subset g η k).trans (fun x hx => by
      rcases hx with hgx | hηx
      · exact Or.inl (subset_closure hgx)
      · exact Or.inr (subset_closure hηx))
  have hclosed : IsClosed (tsupport g ∪ tsupport η) :=
    isClosed_closure.union isClosed_closure
  exact closure_minimal hsupport hclosed

/-- A continuous function times the derivative of a compactly supported Schwartz function is integrable. -/
theorem continuous_mul_schwartz_deriv_integrable
    {g : ℝ → ℝ} (hg : Continuous g)
    (φ : SchwartzMap ℝ ℝ) (hφ : HasCompactSupport φ) :
    Integrable (fun x => g x * deriv φ x) volume := by
  have hD : HasCompactSupport (deriv φ) := hφ.deriv
  have hsupp : Function.support (fun x => g x * deriv φ x) ⊆ tsupport (deriv φ) := by
    intro x hx
    by_contra hxt
    have hDx : deriv φ x = 0 := image_eq_zero_of_notMem_tsupport hxt
    exact hx (by simp [hDx])
  have hcompact : HasCompactSupport (fun x => g x * deriv φ x) := by
    exact HasCompactSupport.of_support_subset_isCompact hD.isCompact hsupp
  exact (hg.mul ((φ.smooth 1).continuous_deriv le_rfl)).integrable_of_hasCompactSupport
    hcompact

/-- Integration by parts for a continuous forcing primitive and a compactly supported Schwartz test. -/
theorem integral_forcingPrimitive_mul_deriv_schwartz
    (F : ℝ → ℝ) (hF : Continuous F) (c : ℝ)
    (φ : SchwartzMap ℝ ℝ) (hφ : HasCompactSupport φ) :
    ∫ x, forcingPrimitive F c x * deriv φ x =
      - ∫ x, F x * φ x := by
  apply integral_mul_deriv_eq_deriv_mul_of_integrable
  · intro x hx
    exact forcingPrimitive_hasDerivAt hF c x
  · intro x hx
    exact φ.differentiableAt.hasDerivAt
  · exact continuous_mul_schwartz_deriv_integrable
      (forcingPrimitive_continuous hF c) φ hφ
  · exact continuous_mul_schwartz_integrable hF φ hφ
  · exact continuous_mul_schwartz_integrable (forcingPrimitive_continuous hF c) φ hφ

/-- The localized adjusted weak derivative has zero pairing with interior Schwartz derivatives. -/
theorem HalfLineH1.CorrectionBumps.local_adjustedWeakDeriv_pairing_deriv_eq_zero
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (_hab : a < b)
    (φ : SchwartzMap ℝ ℝ) (hφ : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ Ioo a b) :
    ∫ x, ((f.weakDeriv : ℝ → ℝ) x +
      measureCDF (B.localReactionMeasure hfmin a b) x +
      forcingPrimitive
        (fun x => f.rayleighQuotient * f.continuousRep x -
          B.massMultiplier - B.momentMultiplier * x) a x) * deriv φ x = 0 := by
  let μloc := B.localReactionMeasure hfmin a b
  let F : ℝ → ℝ := fun x => f.rayleighQuotient * f.continuousRep x -
    B.massMultiplier - B.momentMultiplier * x
  let P : ℝ → ℝ := forcingPrimitive F a
  let w0 : ℝ → ℝ := fun x => (f.weakDeriv : ℝ → ℝ) x * deriv φ x
  let h0 : ℝ → ℝ := fun x => measureCDF μloc x * deriv φ x
  let p0 : ℝ → ℝ := fun x => P x * deriv φ x
  let W : ℝ → ℝ := fun x =>
    ((f.weakDeriv : ℝ → ℝ) x + measureCDF μloc x + P x) * deriv φ x
  let Iw := ∫ x, w0 x
  let IH := ∫ x, h0 x
  let IP := ∫ x, p0 x
  let Iμ := ∫ x, φ x ∂μloc
  let IF := ∫ x, F x * φ x
  let _ : IsFiniteMeasure μloc := B.localReactionMeasure_isFinite hfmin ha
  have hsupport_pos : tsupport φ ⊆ Ioi (0 : ℝ) := by
    intro x hx
    exact lt_trans ha (hsupp hx).1
  have hk := B.weak_KKT_equation_schwartz_deriv hfmin φ hφ hsupport_pos
  have hreaction := B.integral_localReactionMeasure_schwartz hfmin ha φ hφ hsupp
  have hF : Continuous F := by
    dsimp [F]
    exact (((continuous_const.mul f.continuous_continuousRep).sub continuous_const).sub
      (continuous_const.mul continuous_id))
  have hcdf := measureCDF_distributional_derivative (μ := μloc) φ hφ
  have hprim := integral_forcingPrimitive_mul_deriv_schwartz F hF a φ hφ
  have hW : W = w0 + h0 + p0 := by
    funext x
    dsimp [W, w0, h0, p0]
    ring
  have hweak : Integrable w0 volume := by
    exact (Lp.memLp f.weakDeriv).integrable_mul
      ((SchwartzMap.derivCLM ℝ ℝ φ).memLp 2 volume)
  have hcdf_int : Integrable h0 volume := by
    have hd : Integrable (deriv φ) volume := by
      exact (φ.smooth 1).continuous_deriv le_rfl |>.integrable_of_hasCompactSupport hφ.deriv
    let M : ℝ := (μloc Set.univ).toReal
    have hM : 0 ≤ M := ENNReal.toReal_nonneg
    have hc : Integrable (fun x => M * deriv φ x) volume := by
      simpa [M] using hd.const_mul (μloc Set.univ).toReal
    apply hc.mono
    · exact (measureCDF_monotone (μ := μloc)).measurable.aestronglyMeasurable.mul
        ((φ.smooth 1).continuous_deriv le_rfl).aestronglyMeasurable
    · filter_upwards [] with x
      change ‖measureCDF μloc x * deriv φ x‖ ≤ ‖M * deriv φ x‖
      calc
        ‖measureCDF μloc x * deriv φ x‖ =
            |measureCDF μloc x| * |deriv φ x| := by
              simp [Real.norm_eq_abs]
        _ ≤ M * |deriv φ x| := by
          exact mul_le_mul_of_nonneg_right
            (measureCDF_bounded (μ := μloc) Set.univ x (Set.mem_univ x))
            (abs_nonneg _)
        _ = ‖M * deriv φ x‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM]
  have hp_int : Integrable p0 volume := by
    exact continuous_mul_schwartz_deriv_integrable
      (forcingPrimitive_continuous hF a) φ hφ
  have hKKT : Iw = Iμ + IF := by
    calc
      Iw = (∫ x : Ioi (0 : ℝ), φ x ∂B.reactionMeasure hfmin) + IF := by
        simpa [Iw, w0, F] using hk
      _ = Iμ + IF := by
        rw [show (∫ x : Ioi (0 : ℝ), φ x ∂B.reactionMeasure hfmin) = Iμ by
          simpa [Iμ, μloc] using hreaction.symm]
  have hCDF : IH = -Iμ := by
    simpa [IH, h0] using hcdf
  have hP : IP = -IF := by
    simpa [IP, p0, P] using hprim
  change (∫ x, W x) = 0
  rw [hW]
  change (∫ x, w0 x + h0 x + p0 x) = 0
  have hsplit : (∫ x, w0 x + h0 x + p0 x) = Iw + IH + IP := by
    calc
      (∫ x, w0 x + h0 x + p0 x) =
          (∫ x, (w0 + h0) x) + ∫ x, p0 x := by
            simpa only [Pi.add_apply, add_assoc] using
              integral_add (hweak.add hcdf_int) hp_int
      _ = Iw + IH + IP := by
        have hadd : (w0 + h0) = (fun x => w0 x + h0 x) := by
          funext x
          rfl
        rw [hadd, integral_add hweak hcdf_int]
  rw [hsplit]
  change Iw + IH + IP = 0
  rw [hKKT, hCDF, hP]
  ring

theorem locallyIntegrableOn_ae_eq_const_of_compactSmooth_deriv_pairings_eq_zero
    {w : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hw : LocallyIntegrableOn w (Ioo a b) volume)
    (hweak : ∀ φ : SchwartzMap ℝ ℝ, HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ x, w x * deriv φ x = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂volume, x ∈ Ioo a b → w x = c := by
  obtain ⟨η, hηc, hηs, _, hηint⟩ := exists_normalized_schwartz_bump_Ioo hab
  let c := ∫ x, η x * w x
  have hηw : Integrable (fun x => η x * w x) volume :=
    LocallyIntegrableOn.integrable_mul_of_continuous_hasCompactSupport hw
      η.continuous hηc hηs
  have hpair : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b → (∫ x, g x * w x) = c * ∫ x, g x := by
    intro g hg hgc hgs
    let K := tsupport g ∪ tsupport (η : ℝ → ℝ)
    have hKc : IsCompact K := hgc.isCompact.union hηc.isCompact
    have hKs : K ⊆ Ioo a b := union_subset hgs hηs
    obtain ⟨A, B, hA, hAB, hB, hKAB⟩ :=
      IsCompact.exists_Icc_subset_Ioo_of_subset hKc hKs hab
    let g0 : ℝ → ℝ := fun x => g x - (∫ y, g y) * η x
    have hηdiff : ContDiff ℝ (⊤ : ℕ∞) (η : ℝ → ℝ) := η.smooth ⊤
    have hg0 : ContDiff ℝ (⊤ : ℕ∞) g0 := hg.sub (contDiff_const.mul hηdiff)
    have hg0sK : tsupport g0 ⊆ K :=
      tsupport_sub_const_mul_subset g η (∫ y, g y)
    have hg0c : HasCompactSupport g0 := by
      refine HasCompactSupport.of_support_subset_isCompact hKc ?_
      exact (subset_closure.trans hg0sK)
    have hg0sAB : tsupport g0 ⊆ Icc A B := hg0sK.trans hKAB
    have hgint : Integrable g volume := hg.continuous.integrable_of_hasCompactSupport hgc
    have hηint' : Integrable (η : ℝ → ℝ) volume :=
      η.continuous.integrable_of_hasCompactSupport hηc
    have hg0int : (∫ x, g0 x) = 0 := by
      calc
        (∫ x, g0 x) = (∫ x, g x) - ∫ x, (∫ y, g y) * η x :=
          integral_sub hgint (hηint'.const_mul (∫ y, g y))
        _ = (∫ x, g x) - (∫ y, g y) * ∫ x, η x := by
          rw [integral_const_mul]
        _ = 0 := by rw [hηint]; ring
    let C := (a + A) / 2
    let D := (B + b) / 2
    obtain ⟨φ, hφc, hφs, hφd⟩ := exists_schwartz_primitive_of_integral_eq_zero
      (A := A) (B := B) (C := C) (D := D)
      (by dsimp [C]; linarith) (by dsimp [D]; linarith) hg0 hg0sAB hg0int
    have hφI : Icc C D ⊆ Ioo a b := by
      intro x hx
      constructor
      · have hC : a < C := by dsimp [C]; linarith
        exact lt_of_lt_of_le hC hx.1
      · have hD : D < b := by dsimp [D]; linarith
        exact lt_of_le_of_lt hx.2 hD
    have hφpair := hweak φ hφc (hφs.trans hφI)
    have hgw : Integrable (fun x => g x * w x) volume :=
      LocallyIntegrableOn.integrable_mul_of_continuous_hasCompactSupport hw
        hg.continuous hgc hgs
    have hg0w : Integrable (fun x => g0 x * w x) volume :=
      LocallyIntegrableOn.integrable_mul_of_continuous_hasCompactSupport hw
        hg0.continuous hg0c (hg0sK.trans hKs)
    have hweak0 : (∫ x, w x * g0 x) = 0 := by
      rw [← hφpair]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hφd]
    have hsplit : (∫ x, w x * g0 x) =
        (∫ x, g x * w x) - (∫ y, g y) * c := by
      calc
        (∫ x, w x * g0 x) = ∫ x, (g x * w x) - ((∫ y, g y) * (η x * w x)) := by
          apply integral_congr_ae
          filter_upwards [] with x
          dsimp [g0]
          ring
        _ = (∫ x, g x * w x) - ∫ x, (∫ y, g y) * (η x * w x) :=
          integral_sub hgw (hηw.const_mul (∫ y, g y))
        _ = (∫ x, g x * w x) - (∫ y, g y) * c := by
          rw [integral_const_mul]
    have hgw_eq : (∫ x, g x * w x) = c * ∫ x, g x := by
      dsimp [c]
      linarith [hsplit, hweak0]
    exact hgw_eq
  have hzero : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ Ioo a b → ∫ x, g x * (w x - c) = 0 := by
    intro g hg hgc hgs
    have hgw := LocallyIntegrableOn.integrable_mul_of_continuous_hasCompactSupport hw
      hg.continuous hgc hgs
    have hgcint : Integrable (fun x => g x * c) volume :=
      hg.continuous.integrable_of_hasCompactSupport hgc |>.mul_const c
    have hconst : (∫ x, g x * c) = c * ∫ x, g x := by
      calc
        (∫ x, g x * c) = (∫ x, g x) * c := integral_mul_const c g
        _ = c * ∫ x, g x := mul_comm _ _
    calc
      ∫ x, g x * (w x - c) = ∫ x, (g x * w x) - (g x * c) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (∫ x, g x * w x) - ∫ x, g x * c := integral_sub hgw hgcint
      _ = (c * ∫ x, g x) - ∫ x, g x * c := by
        rw [hpair g hg hgc hgs]
      _ = (c * ∫ x, g x) - (c * ∫ x, g x) := by rw [hconst]
      _ = 0 := sub_self _
  have hz := locallyIntegrableOn_ae_eq_zero_of_compactSmooth_pairings_eq_zero hab
    (hw.sub (locallyIntegrableOn_const c)) (by
      intro g hg hgc hgs
      exact hzero g hg hgc hgs)
  refine ⟨c, ?_⟩
  filter_upwards [hz] with x hx
  intro hxI
  exact sub_eq_zero.mp (hx hxI)

theorem HalfLineH1.CorrectionBumps.local_adjustedWeakDeriv_locallyIntegrableOn
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    LocallyIntegrableOn
      (fun x => (f.weakDeriv : ℝ → ℝ) x +
        measureCDF (B.localReactionMeasure hfmin a b) x +
        forcingPrimitive
          (fun x => f.rayleighQuotient * f.continuousRep x -
            B.massMultiplier - B.momentMultiplier * x) a x)
      (Ioo a b) volume := by
  let μloc := B.localReactionMeasure hfmin a b
  let F : ℝ → ℝ := fun x => f.rayleighQuotient * f.continuousRep x -
    B.massMultiplier - B.momentMultiplier * x
  let P : ℝ → ℝ := forcingPrimitive F a
  let _ : IsFiniteMeasure μloc := B.localReactionMeasure_isFinite hfmin ha
  have hw : LocallyIntegrable ((f.weakDeriv : ℝ → ℝ)) volume :=
    (Lp.memLp f.weakDeriv).locallyIntegrable fact_one_le_two_ennreal.out
  have hW : LocallyIntegrableOn (f.weakDeriv : ℝ → ℝ) (Ioo a b) volume :=
    hw.locallyIntegrableOn _
  have hcdf : LocallyIntegrableOn (measureCDF μloc) (Ioo a b) volume := by
    rw [locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed]
    intro K hK hKc
    obtain ⟨A, B', hA, hAB, hB', hsub⟩ :=
      IsCompact.exists_Icc_subset_Ioo_of_subset hKc hK hab
    exact (measureCDF_integrableOn_Icc (μ := μloc) A B').mono_set hsub
  have hF : Continuous F := by
    dsimp [F]
    exact (((continuous_const.mul f.continuous_continuousRep).sub continuous_const).sub
      (continuous_const.mul continuous_id))
  have hP : LocallyIntegrableOn P (Ioo a b) volume :=
    (forcingPrimitive_continuous hF a).locallyIntegrable.locallyIntegrableOn _
  change LocallyIntegrableOn ((f.weakDeriv : ℝ → ℝ) + measureCDF μloc + P)
    (Ioo a b) volume
  exact (hW.add hcdf).add hP

theorem HalfLineH1.CorrectionBumps.exists_ae_weakDeriv_eq_local_cdf_forcing
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ c : ℝ, ∀ᵐ x ∂volume, x ∈ Ioo a b →
      (f.weakDeriv : ℝ → ℝ) x = c -
        measureCDF (B.localReactionMeasure hfmin a b) x -
        forcingPrimitive
          (fun x => f.rayleighQuotient * f.continuousRep x -
            B.massMultiplier - B.momentMultiplier * x) a x := by
  let μloc := B.localReactionMeasure hfmin a b
  let F : ℝ → ℝ := fun x => f.rayleighQuotient * f.continuousRep x -
    B.massMultiplier - B.momentMultiplier * x
  let P : ℝ → ℝ := forcingPrimitive F a
  let W : ℝ → ℝ := fun x => (f.weakDeriv : ℝ → ℝ) x +
    measureCDF μloc x + P x
  have hloc : LocallyIntegrableOn W (Ioo a b) volume := by
    dsimp [W, μloc, F, P]
    exact B.local_adjustedWeakDeriv_locallyIntegrableOn hfmin ha hab
  have hpair : ∀ φ : SchwartzMap ℝ ℝ, HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ x, W x * deriv φ x = 0 := by
    intro φ hφ hsupp
    exact B.local_adjustedWeakDeriv_pairing_deriv_eq_zero hfmin ha hab φ hφ hsupp
  obtain ⟨c, hc⟩ := locallyIntegrableOn_ae_eq_const_of_compactSmooth_deriv_pairings_eq_zero
    hab hloc hpair
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx hxI
  have hx := hx hxI
  dsimp [W, μloc, F, P] at hx ⊢
  linarith

theorem HalfLineH1.CorrectionBumps.exists_local_continuousRep_sub_eq_integral_cdf_forcing
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ c : ℝ, ∀ ⦃x y : ℝ⦄, x ∈ Ioo a b → y ∈ Ioo a b →
      f.continuousRep y - f.continuousRep x =
        ∫ t in x..y,
          (c - measureCDF (B.localReactionMeasure hfmin a b) t -
            forcingPrimitive
              (fun z => f.rayleighQuotient * f.continuousRep z -
                B.massMultiplier - B.momentMultiplier * z) a t) := by
  obtain ⟨c, hc⟩ := B.exists_ae_weakDeriv_eq_local_cdf_forcing hfmin ha hab
  refine ⟨c, ?_⟩
  intro x y hx hy
  rw [f.continuousRep_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hc] with t ht htu
  have htu' : t ∈ uIcc x y := uIoc_subset_uIcc htu
  have hxy : ∀ {t : ℝ}, t ∈ uIcc x y → t ∈ Ioo a b := by
    intro t ht
    rcases le_total x y with hxy' | hyx'
    · rw [uIcc_of_le hxy'] at ht
      constructor
      · exact lt_of_lt_of_le hx.1 ht.1
      · exact lt_of_le_of_lt ht.2 hy.2
    · rw [uIcc_of_ge hyx'] at ht
      constructor
      · exact lt_of_lt_of_le hy.1 ht.1
      · exact lt_of_le_of_lt ht.2 hx.2
  have htI := ht (hxy htu')
  linarith

theorem concaveOn_of_sub_eq_intervalIntegral_antitone
    {v g : ℝ → ℝ} {a b : ℝ} (_hab : a < b)
    (hgint : LocallyIntegrableOn g (Ioo a b) volume)
    (hganti : AntitoneOn g (Ioo a b))
    (hsub : ∀ ⦃x y : ℝ⦄, x ∈ Ioo a b → y ∈ Ioo a b →
      v y - v x = ∫ t in x..y, g t) :
    ConcaveOn ℝ (Ioo a b) v := by
  apply concaveOn_of_slope_anti_adjacent (convex_Ioo a b)
  intro x y z hx hz hxy hyz
  have hy : y ∈ Ioo a b := ⟨lt_of_lt_of_le hx.1 hxy.le, lt_of_le_of_lt hyz.le hz.2⟩
  have hxyIcc : Icc x y ⊆ Ioo a b := by
    intro t ht
    exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
  have hyzIcc : Icc y z ⊆ Ioo a b := by
    intro t ht
    exact ⟨lt_of_lt_of_le hy.1 ht.1, lt_of_le_of_lt ht.2 hz.2⟩
  have hgxy : IntervalIntegrable g volume x y :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hxy.le).mpr
      (hgint.integrableOn_compact_subset hxyIcc isCompact_Icc)
  have hgyz : IntervalIntegrable g volume y z :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hyz.le).mpr
      (hgint.integrableOn_compact_subset hyzIcc isCompact_Icc)
  have hleft : (y - x) * g y ≤ ∫ t in x..y, g t := by
    calc
      (y - x) * g y = ∫ t in x..y, g y := by rw [intervalIntegral.integral_const]; ring
      _ ≤ ∫ t in x..y, g t := by
        apply intervalIntegral.integral_mono_on hxy.le
          (continuous_const.intervalIntegrable x y) hgxy
        intro t ht
        exact hganti (hxyIcc ht) hy ht.2
  have hright : ∫ t in y..z, g t ≤ (z - y) * g y := by
    calc
      ∫ t in y..z, g t ≤ ∫ t in y..z, g y := by
        apply intervalIntegral.integral_mono_on hyz.le hgyz
          (continuous_const.intervalIntegrable y z)
        intro t ht
        exact hganti hy (hyzIcc ht) ht.1
      _ = (z - y) * g y := by rw [intervalIntegral.integral_const]; ring
  have hxypos : 0 < y - x := sub_pos.mpr hxy
  have hyzpos : 0 < z - y := sub_pos.mpr hyz
  rw [hsub hx hy, hsub hy hz]
  calc
    (∫ t in y..z, g t) / (z - y) ≤ g y :=
      (div_le_iff₀ hyzpos).mpr (by simpa [mul_comm] using hright)
    _ ≤ (∫ t in x..y, g t) / (y - x) :=
      (le_div_iff₀ hxypos).mpr (by simpa [mul_comm] using hleft)

def HalfLineH1.CorrectionBumps.localReducedProfile
    (f : HalfLineH1) (B : f.CorrectionBumps)
    (a x : ℝ) : ℝ :=
  f.continuousRep x + forcingPotential
    (fun z => f.rayleighQuotient * f.continuousRep z -
      B.massMultiplier - B.momentMultiplier * z) a x

theorem HalfLineH1.CorrectionBumps.localReactionMeasure_measure_Ioc_eq_zero_of_mem_freeInterval
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (hfree : Ioo a b ⊆ f.positivitySet)
    {p q : ℝ} (hp : p ∈ Ioo a b) (hq : q ∈ Ioo a b) :
    (B.localReactionMeasure hfmin a b) (Ioc p q) = 0 := by
  let μ := B.reactionMeasure hfmin
  let U : Set (Ioi (0 : ℝ)) := {z | (z : ℝ) ∈ f.positivitySet}
  have hUz : μ U = 0 := B.reactionMeasure_positivitySet_eq_zero hfmin
  by_cases hpq : p ≤ q
  · have hsub : (Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Ioc p q ∩
        localReactionSet a b ⊆ U := by
      intro z hz
      have hzpq : p < (z : ℝ) ∧ (z : ℝ) ≤ q := hz.1
      exact hfree ⟨lt_of_lt_of_le hp.1 hzpq.1.le,
        lt_of_le_of_lt hzpq.2 hq.2⟩
    rw [HalfLineH1.CorrectionBumps.localReactionMeasure,
      Measure.map_apply continuous_subtype_val.measurable measurableSet_Ioc,
      Measure.restrict_apply (measurableSet_Ioc.preimage continuous_subtype_val.measurable)]
    exact measure_mono_null hsub hUz
  · rw [Ioc_eq_empty (not_lt_of_ge (le_of_not_ge hpq)), measure_empty]

theorem HalfLineH1.CorrectionBumps.localReactionMeasure_measure_Ioc_eq_zero_of_local_freeInterval
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b p q x y : ℝ}
    (hfree : Ioo p q ⊆ f.positivitySet)
    (hx : x ∈ Ioo p q) (hy : y ∈ Ioo p q) :
    (B.localReactionMeasure hfmin a b) (Ioc x y) = 0 := by
  let μ := B.reactionMeasure hfmin
  let U : Set (Ioi (0 : ℝ)) := {z | (z : ℝ) ∈ f.positivitySet}
  have hUz : μ U = 0 := B.reactionMeasure_positivitySet_eq_zero hfmin
  by_cases hxy : x ≤ y
  · have hsub : (Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Ioc x y ∩
        localReactionSet a b ⊆ U := by
      intro z hz
      have hzxy : x < (z : ℝ) ∧ (z : ℝ) ≤ y := hz.1
      exact hfree ⟨lt_trans hx.1 hzxy.1, lt_of_le_of_lt hzxy.2 hy.2⟩
    rw [HalfLineH1.CorrectionBumps.localReactionMeasure,
      Measure.map_apply continuous_subtype_val.measurable measurableSet_Ioc,
      Measure.restrict_apply (measurableSet_Ioc.preimage continuous_subtype_val.measurable)]
    exact measure_mono_null hsub hUz
  · rw [Ioc_eq_empty (not_lt_of_ge (le_of_not_ge hxy)), measure_empty]

theorem HalfLineH1.CorrectionBumps.measureCDF_localReactionMeasure_eq_of_local_freeInterval
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b p q x y : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hfree : Ioo p q ⊆ f.positivitySet)
    (hx : x ∈ Ioo p q) (hy : y ∈ Ioo p q) :
    measureCDF (B.localReactionMeasure hfmin a b) x =
      measureCDF (B.localReactionMeasure hfmin a b) y := by
  have _ := ha
  have _ := hab
  rcases le_total x y with hxy | hyx
  · have hdecomp : Iic y = Iic x ∪ Ioc x y := by
      ext z
      constructor
      · intro hz
        by_cases hzx : z ≤ x
        · exact Or.inl hzx
        · exact Or.inr ⟨lt_of_not_ge hzx, hz⟩
      · rintro (hz | hz)
        · exact hz.trans hxy
        · exact hz.2
    have hadd := measure_union (μ := B.localReactionMeasure hfmin a b)
      (show Disjoint (Iic x) (Ioc x y) by
        rw [Set.disjoint_left]
        intro z hz1 hz2
        exact (not_lt_of_ge hz1) hz2.1) measurableSet_Ioc
    have hz := B.localReactionMeasure_measure_Ioc_eq_zero_of_local_freeInterval
      (a := a) (b := b) hfmin hfree hx hy
    have hr : (B.localReactionMeasure hfmin a b) (Iic y) =
        (B.localReactionMeasure hfmin a b) (Iic x) := by
      rw [hdecomp, hadd, hz, add_zero]
    simpa [measureCDF, MeasureTheory.measureReal_def] using
      congrArg ENNReal.toReal hr.symm
  · have hdecomp : Iic x = Iic y ∪ Ioc y x := by
      ext z
      constructor
      · intro hz
        by_cases hzy : z ≤ y
        · exact Or.inl hzy
        · exact Or.inr ⟨lt_of_not_ge hzy, hz⟩
      · rintro (hz | hz)
        · exact hz.trans hyx
        · exact hz.2
    have hadd := measure_union (μ := B.localReactionMeasure hfmin a b)
      (show Disjoint (Iic y) (Ioc y x) by
        rw [Set.disjoint_left]
        intro z hz1 hz2
        exact (not_lt_of_ge hz1) hz2.1) measurableSet_Ioc
    have hz := B.localReactionMeasure_measure_Ioc_eq_zero_of_local_freeInterval
      (a := a) (b := b) hfmin hfree hy hx
    have hr : (B.localReactionMeasure hfmin a b) (Iic x) =
        (B.localReactionMeasure hfmin a b) (Iic y) := by
      rw [hdecomp, hadd, hz, add_zero]
    simpa [measureCDF, MeasureTheory.measureReal_def] using
      congrArg ENNReal.toReal hr

theorem HalfLineH1.CorrectionBumps.measureCDF_localReactionMeasure_eq_of_mem_freeInterval
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hfree : Ioo a b ⊆ f.positivitySet)
    {x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    measureCDF (B.localReactionMeasure hfmin a b) x =
      measureCDF (B.localReactionMeasure hfmin a b) y := by
  have _ := ha
  have _ := hab
  rcases le_total x y with hxy | hyx
  · have hdecomp : Iic y = Iic x ∪ Ioc x y := by
      ext z
      constructor
      · intro hz
        by_cases hzx : z ≤ x
        · exact Or.inl hzx
        · exact Or.inr ⟨lt_of_not_ge hzx, hz⟩
      · rintro (hz | hz)
        · exact hz.trans hxy
        · exact hz.2
    have hadd := measure_union (μ := B.localReactionMeasure hfmin a b)
      (show Disjoint (Iic x) (Ioc x y) by
        rw [Set.disjoint_left]
        intro z hz1 hz2
        exact (not_lt_of_ge hz1) hz2.1) measurableSet_Ioc
    have hz := B.localReactionMeasure_measure_Ioc_eq_zero_of_mem_freeInterval
      hfmin hfree hx hy
    have hr : (B.localReactionMeasure hfmin a b) (Iic y) =
        (B.localReactionMeasure hfmin a b) (Iic x) := by
      rw [hdecomp, hadd, hz, add_zero]
    simpa [measureCDF, MeasureTheory.measureReal_def] using
      congrArg ENNReal.toReal hr.symm
  · have hdecomp : Iic x = Iic y ∪ Ioc y x := by
      ext z
      constructor
      · intro hz
        by_cases hzy : z ≤ y
        · exact Or.inl hzy
        · exact Or.inr ⟨lt_of_not_ge hzy, hz⟩
      · rintro (hz | hz)
        · exact hz.trans hyx
        · exact hz.2
    have hadd := measure_union (μ := B.localReactionMeasure hfmin a b)
      (show Disjoint (Iic y) (Ioc y x) by
        rw [Set.disjoint_left]
        intro z hz1 hz2
        exact (not_lt_of_ge hz1) hz2.1) measurableSet_Ioc
    have hz := B.localReactionMeasure_measure_Ioc_eq_zero_of_mem_freeInterval
      hfmin hfree hy hx
    have hr : (B.localReactionMeasure hfmin a b) (Iic x) =
        (B.localReactionMeasure hfmin a b) (Iic y) := by
      rw [hdecomp, hadd, hz, add_zero]
    simpa [measureCDF, MeasureTheory.measureReal_def] using
      congrArg ENNReal.toReal hr

theorem HalfLineH1.CorrectionBumps.exists_localReducedProfile_sub_eq_integral_const_sub_cdf
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ c, ∀ ⦃x y : ℝ⦄, x ∈ Ioo a b → y ∈ Ioo a b →
      B.localReducedProfile f a y - B.localReducedProfile f a x =
        ∫ t in x..y, (c - measureCDF (B.localReactionMeasure hfmin a b) t) := by
  let F : ℝ → ℝ := fun z => f.rayleighQuotient * f.continuousRep z -
    B.massMultiplier - B.momentMultiplier * z
  have hF : Continuous F := by
    dsimp [F]
    exact (((continuous_const.mul f.continuous_continuousRep).sub continuous_const).sub
      (continuous_const.mul continuous_id))
  obtain ⟨c, hc⟩ := B.exists_local_continuousRep_sub_eq_integral_cdf_forcing
    hfmin ha hab
  refine ⟨c, ?_⟩
  intro x y hx hy
  have hH := forcingPotential_sub_eq_integral_forcingPrimitive hF a x y
  rw [show B.localReducedProfile f a y - B.localReducedProfile f a x =
      (f.continuousRep y - f.continuousRep x) +
        (forcingPotential F a y - forcingPotential F a x) by
      simp [HalfLineH1.CorrectionBumps.localReducedProfile, F]; ring]
  rw [hc hx hy, hH]
  have hcdf : LocallyIntegrableOn
      (measureCDF (B.localReactionMeasure hfmin a b)) (Ioo a b) volume := by
    let μloc := B.localReactionMeasure hfmin a b
    let _ : IsFiniteMeasure μloc := B.localReactionMeasure_isFinite hfmin ha
    rw [locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed]
    intro K hK hKc
    obtain ⟨A, B', hA, hAB, hB', hsub⟩ :=
      IsCompact.exists_Icc_subset_Ioo_of_subset hKc hK hab
    exact (measureCDF_integrableOn_Icc (μ := μloc) A B').mono_set hsub
  have hxyIcc : uIcc x y ⊆ Ioo a b := by
    intro t ht
    rcases le_total x y with hxy' | hyx'
    · rw [uIcc_of_le hxy'] at ht
      exact ⟨lt_of_lt_of_le hx.1 ht.1, lt_of_le_of_lt ht.2 hy.2⟩
    · rw [uIcc_of_ge hyx'] at ht
      exact ⟨lt_of_lt_of_le hy.1 ht.1, lt_of_le_of_lt ht.2 hx.2⟩
  have hcdfxy : IntervalIntegrable (measureCDF
      (B.localReactionMeasure hfmin a b)) volume x y := by
    rcases le_total x y with hxy' | hyx'
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hxy').mpr
        (hcdf.integrableOn_compact_subset (by simpa [uIcc_of_le hxy'] using hxyIcc)
          isCompact_Icc)
    · have hrev : IntervalIntegrable (measureCDF
          (B.localReactionMeasure hfmin a b)) volume y x :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le hyx').mpr
          (hcdf.integrableOn_compact_subset (by simpa [uIcc_of_ge hyx'] using hxyIcc)
            isCompact_Icc)
      exact hrev.symm
  have hconst : IntervalIntegrable (fun _ : ℝ => c) volume x y :=
    continuous_const.intervalIntegrable x y
  have hPxy : IntervalIntegrable (forcingPrimitive F a) volume x y :=
    (forcingPrimitive_continuous hF a).intervalIntegrable x y
  calc
    (∫ t in x..y, c - measureCDF (B.localReactionMeasure hfmin a b) t -
        forcingPrimitive F a t) + ∫ t in x..y, forcingPrimitive F a t =
      (∫ t in x..y, c - measureCDF (B.localReactionMeasure hfmin a b) t) := by
        rw [intervalIntegral.integral_sub
          (hconst.sub hcdfxy) hPxy, intervalIntegral.integral_sub hconst hcdfxy]
        ring
    _ = ∫ t in x..y, c - measureCDF (B.localReactionMeasure hfmin a b) t := rfl

theorem HalfLineH1.CorrectionBumps.localReducedProfile_concaveOn
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ConcaveOn ℝ (Ioo a b) (B.localReducedProfile f a) := by
  let μloc := B.localReactionMeasure hfmin a b
  obtain ⟨c, hc⟩ := B.exists_localReducedProfile_sub_eq_integral_const_sub_cdf hfmin ha hab
  let g : ℝ → ℝ := fun x => c - measureCDF μloc x
  let _ : IsFiniteMeasure μloc := B.localReactionMeasure_isFinite hfmin ha
  have hcdf : LocallyIntegrableOn (measureCDF μloc) (Ioo a b) := by
    rw [locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed]
    intro K hK hKc
    obtain ⟨A, B', hA, hAB, hB', hsub⟩ :=
      IsCompact.exists_Icc_subset_Ioo_of_subset hKc hK hab
    exact (measureCDF_integrableOn_Icc (μ := μloc) A B').mono_set hsub
  have hgint : LocallyIntegrableOn g (Ioo a b) volume := by
    exact (locallyIntegrableOn_const _).sub hcdf
  have hganti : AntitoneOn g (Ioo a b) := by
    intro x hx y hy hxy
    dsimp [g]
    linarith [measureCDF_monotone (μ := μloc) hxy]
  apply concaveOn_of_sub_eq_intervalIntegral_antitone hab hgint hganti
  intro x y hx hy
  dsimp [g, μloc]
  simpa using hc hx hy

theorem ConcaveOn.hasDerivAt_eq_of_le_of_eq
    {v ψ : ℝ → ℝ} {a b x ψ' : ℝ}
    (hv : ConcaveOn ℝ (Ioo a b) v) (hx : x ∈ Ioo a b)
    (hψ : HasDerivAt ψ ψ' x)
    (hle : ∀ y ∈ Ioo a b, ψ y ≤ v y)
    (heq : v x = ψ x) :
    HasDerivAt v ψ' x := by
  have hneg : ConvexOn ℝ (Ioo a b) (-v) := hv.neg
  have hxi : x ∈ interior (Ioo a b) := by simpa [interior_Ioo] using hx
  let l : ℝ := derivWithin (-v) (Iio x) x
  let r : ℝ := derivWithin (-v) (Ioi x) x
  have hl : HasDerivWithinAt (-v) l (Iio x) x :=
    (hneg.differentiableWithinAt_Iio_of_mem_interior hxi).hasDerivWithinAt
  have hr : HasDerivWithinAt (-v) r (Ioi x) x :=
    (hneg.differentiableWithinAt_Ioi_of_mem_interior hxi).hasDerivWithinAt
  have hvl : HasDerivWithinAt v (-l) (Iio x) x := by simpa using hl.neg
  have hvr : HasDerivWithinAt v (-r) (Ioi x) x := by simpa using hr.neg
  have horder : l ≤ r := hneg.leftDeriv_le_rightDeriv_of_mem_interior hxi
  have hleft : -l ≤ ψ' := by
    apply le_of_tendsto_of_tendsto
      ((hasDerivWithinAt_iff_tendsto_slope' (f := v) (f' := -l) (s := Iio x)
        (x := x) self_notMem_Iio).mp hvl)
      ((hasDerivWithinAt_iff_tendsto_slope' (f := ψ) (f' := ψ') (s := Iio x)
        (x := x) self_notMem_Iio).mp hψ.hasDerivWithinAt)
    filter_upwards [eventually_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hx.1 hx.2)] with y hy hyI
    rw [slope_def_field, slope_def_field]
    exact (div_le_iff_of_neg (sub_neg.mpr hy)).mpr (by
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hy.ne)]
      linarith [hle y hyI, heq])
  have hright : ψ' ≤ -r := by
    apply le_of_tendsto_of_tendsto
      ((hasDerivWithinAt_iff_tendsto_slope' (f := ψ) (f' := ψ') (s := Ioi x)
        (x := x) self_notMem_Ioi).mp hψ.hasDerivWithinAt)
      ((hasDerivWithinAt_iff_tendsto_slope' (f := v) (f' := -r) (s := Ioi x)
        (x := x) self_notMem_Ioi).mp hvr)
    filter_upwards [eventually_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hx.1 hx.2)] with y hy hyI
    rw [slope_def_field, slope_def_field]
    apply (div_le_iff₀ (sub_pos.mpr hy)).mpr
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hy.ne')]
    linarith [hle y hyI, heq]
  have heq' : -l = ψ' := by linarith [horder, hleft, hright]
  have heq'' : -r = ψ' := by linarith [horder, hleft, hright]
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  exact ⟨by simpa [heq'] using
      ((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp hvl),
    by simpa [heq''] using
      ((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hvr)⟩

theorem HalfLineH1.CorrectionBumps.localReducedProfile_hasDerivAt_of_contact
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b x : ℝ} (ha : 0 < a) (hab : a < b)
    (hx : x ∈ Ioo a b) (hcontact : f.continuousRep x = 0) :
    HasDerivAt (B.localReducedProfile f a)
      (forcingPrimitive
        (fun z => f.rayleighQuotient*f.continuousRep z -
          B.massMultiplier - B.momentMultiplier*z) a x) x := by
  let F : ℝ → ℝ := fun z => f.rayleighQuotient * f.continuousRep z -
    B.massMultiplier - B.momentMultiplier * z
  have hF : Continuous F := by
    dsimp [F]
    exact (((continuous_const.mul f.continuous_continuousRep).sub continuous_const).sub
      (continuous_const.mul continuous_id))
  have hv := B.localReducedProfile_concaveOn hfmin ha hab
  have hpot := forcingPotential_hasDerivAt hF a x
  have hle : ∀ y ∈ Ioo a b, forcingPotential F a y ≤
      B.localReducedProfile f a y := by
    intro y hy
    have hn := hfmin.1.nonnegative y (le_trans (le_of_lt ha) hy.1.le)
    dsimp [HalfLineH1.CorrectionBumps.localReducedProfile, F]
    linarith
  have heq : B.localReducedProfile f a x = forcingPotential F a x := by
    dsimp [HalfLineH1.CorrectionBumps.localReducedProfile, F]
    rw [hcontact]
    ring
  simpa [F] using
    (ConcaveOn.hasDerivAt_eq_of_le_of_eq hv hx hpot hle heq)

theorem HalfLineH1.CorrectionBumps.continuousRep_hasDerivAt_zero_of_contact
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b x : ℝ} (ha : 0 < a) (hab : a < b)
    (hx : x ∈ Ioo a b) (hcontact : f.continuousRep x = 0) :
    HasDerivAt f.continuousRep 0 x := by
  let F : ℝ → ℝ := fun z => f.rayleighQuotient * f.continuousRep z -
    B.massMultiplier - B.momentMultiplier * z
  have hF : Continuous F := by
    dsimp [F]
    exact (((continuous_const.mul f.continuous_continuousRep).sub continuous_const).sub
      (continuous_const.mul continuous_id))
  have hprof := B.localReducedProfile_hasDerivAt_of_contact hfmin ha hab hx hcontact
  have hpot := forcingPotential_hasDerivAt hF a x
  have hsub : HasDerivAt (fun y =>
      B.localReducedProfile f a y - forcingPotential F a y)
      (forcingPrimitive F a x - forcingPrimitive F a x) x :=
    hprof.sub hpot
  simpa [HalfLineH1.CorrectionBumps.localReducedProfile, F] using hsub

theorem HalfLineH1.CorrectionBumps.localReducedProfile_differentiableOn
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    DifferentiableOn ℝ (B.localReducedProfile f a) (Ioo a b) := by
  obtain ⟨c, hc⟩ := B.exists_localReducedProfile_sub_eq_integral_const_sub_cdf
    hfmin ha hab
  intro x hx
  by_cases hcontact : f.continuousRep x = 0
  · exact (B.localReducedProfile_hasDerivAt_of_contact hfmin ha hab hx hcontact).differentiableAt.differentiableWithinAt
  · have hnonneg := hfmin.1.nonnegative x (le_trans (le_of_lt ha) hx.1.le)
    have hpos : x ∈ f.positivitySet := lt_of_le_of_ne hnonneg (Ne.symm hcontact)
    have hopen : IsOpen (f.positivitySet ∩ Ioo a b) :=
      f.isOpen_positivitySet.inter isOpen_Ioo
    obtain ⟨p, q, hxpq, hpq⟩ :=
      mem_nhds_iff_exists_Ioo_subset.1 (hopen.mem_nhds ⟨hpos, hx⟩)
    have hfree : Ioo p q ⊆ f.positivitySet := fun y hy => (hpq hy).1
    let μ := B.localReactionMeasure hfmin a b
    let k := measureCDF μ x
    let m := c - k
    let d := B.localReducedProfile f a x - m * x
    have heq : ∀ y ∈ Ioo p q, B.localReducedProfile f a y = m * y + d := by
      intro y hy
      have hsub := hc hx (hpq hy).2
      have hint : (∫ t in x..y, (c - measureCDF μ t)) = (y - x) * m := by
        calc
          _ = ∫ t in x..y, m := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards [] with t ht
            have ht' : t ∈ uIcc x y := uIoc_subset_uIcc ht
            have htI : t ∈ Ioo p q := by
              rcases le_total x y with hxy | hyx
              · rw [uIcc_of_le hxy] at ht'
                exact ⟨lt_of_lt_of_le hxpq.1 ht'.1,
                  lt_of_le_of_lt ht'.2 hy.2⟩
              · rw [uIcc_of_ge hyx] at ht'
                exact ⟨lt_of_lt_of_le hy.1 ht'.1,
                  lt_of_le_of_lt ht'.2 hxpq.2⟩
            have hcdf := B.measureCDF_localReactionMeasure_eq_of_local_freeInterval
              (a := a) (b := b) hfmin ha hab hfree hxpq htI
            dsimp [m, k]
            rw [hcdf]
          _ = _ := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
      dsimp [d]
      linarith [hsub, hint]
    have hneigh : ∀ᶠ y in nhds x, B.localReducedProfile f a y = m * y + d := by
      filter_upwards [Ioo_mem_nhds hxpq.1 hxpq.2] with y hy
      exact heq y hy
    have hlin : HasDerivAt (fun y : ℝ => m * y + d) m x := by
      simpa using ((hasDerivAt_id x).const_mul m).add_const d
    exact hlin.congr_of_eventuallyEq hneigh |>.differentiableAt.differentiableWithinAt

theorem HalfLineH1.CorrectionBumps.exists_localReducedProfile_eq_affineOn_of_Ioo_subset_positivitySet
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hfree : Ioo a b ⊆ f.positivitySet) :
    ∃ m d : ℝ, ∀ x ∈ Ioo a b,
      B.localReducedProfile f a x = m * x + d := by
  obtain ⟨c, hc⟩ := B.exists_localReducedProfile_sub_eq_integral_const_sub_cdf hfmin ha hab
  let p : ℝ := (a + b) / 2
  have hp : p ∈ Ioo a b := by
    dsimp [p]
    constructor <;> linarith
  let μ := B.localReactionMeasure hfmin a b
  let k := measureCDF μ p
  let m := c - k
  let d := B.localReducedProfile f a p - m * p
  refine ⟨m, d, ?_⟩
  intro x hx
  have hsub : B.localReducedProfile f a x - B.localReducedProfile f a p =
      ∫ t in p..x, (c - measureCDF μ t) := hc hp hx
  have hint : (∫ t in p..x, (c - measureCDF μ t)) = (x - p) * m := by
    calc
      _ = ∫ t in p..x, m := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with t ht
        have ht' : t ∈ uIcc p x := uIoc_subset_uIcc ht
        have htI : t ∈ Ioo a b := by
          rcases le_total p x with hpx | hxp
          · rw [uIcc_of_le hpx] at ht'
            exact ⟨lt_of_lt_of_le hp.1 ht'.1, lt_of_le_of_lt ht'.2 hx.2⟩
          · rw [uIcc_of_ge hxp] at ht'
            exact ⟨lt_of_lt_of_le hx.1 ht'.1, lt_of_le_of_lt ht'.2 hp.2⟩
        have hcdf := B.measureCDF_localReactionMeasure_eq_of_mem_freeInterval
          hfmin ha hab hfree htI hp
        dsimp [m, k]
        rw [hcdf]
      _ = _ := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  dsimp [d]
  linarith [hsub, hint]

theorem HalfLineH1.CorrectionBumps.localReducedProfile_deriv_antitoneOn
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    AntitoneOn (deriv (B.localReducedProfile f a)) (Ioo a b) := by
  exact (B.localReducedProfile_concaveOn hfmin ha hab).antitoneOn_deriv
      (fun x hx => (B.localReducedProfile_differentiableOn hfmin ha hab x hx).differentiableAt
       (isOpen_Ioo.mem_nhds hx))

theorem HalfLineH1.CorrectionBumps.measureCDF_localReducedProfile_eq_const_sub_deriv
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ c, ∀ x ∈ Ioo a b,
      measureCDF (B.localReactionMeasure hfmin a b) x =
        c - deriv (B.localReducedProfile f a) x := by
  let μ := B.localReactionMeasure hfmin a b
  let _ : IsFiniteMeasure μ := B.localReactionMeasure_isFinite hfmin ha
  obtain ⟨c, hc⟩ := B.exists_localReducedProfile_sub_eq_integral_const_sub_cdf hfmin ha hab
  refine ⟨c, ?_⟩
  apply measureCDF_eq_const_sub_deriv_of_sub_eq_intervalIntegral
  · exact B.localReducedProfile_differentiableOn hfmin ha hab
  · intro x y hx hy
    simpa [μ] using hc hx hy

theorem continuousOn_deriv_of_differentiableOn_of_antitoneOn
    {v : ℝ → ℝ} {a b : ℝ}
    (hdiff : DifferentiableOn ℝ v (Ioo a b))
    (hanti : AntitoneOn (deriv v) (Ioo a b)) :
    ContinuousOn (deriv v) (Ioo a b) := by
  intro x hx
  have hcont : ContinuousAt (deriv v) x := by
    change Tendsto (deriv v) (𝓝 x) (𝓝 (deriv v x))
    apply tendsto_order.2
    constructor
    · intro m hmx
      let w : ℝ := (x + b) / 2
      have hw : w ∈ Ioo x b := by
        dsimp [w]
        constructor <;> linarith [hx.2]
      have hw' : w ∈ Ioo a b := ⟨lt_trans hx.1 hw.1, hw.2⟩
      by_cases hmw : m < deriv v w
      · filter_upwards [Iio_mem_nhds hw.1, Ioo_mem_nhds hx.1 hx.2] with y hyI hy
        exact lt_of_lt_of_le hmw (hanti hy hw' (le_of_lt hyI))
      · let t : ℝ := (m + deriv v x) / 2
        have hmt : m < t := by dsimp [t]; linarith
        have htx : t < deriv v x := by dsimp [t]; linarith
        have hD : ∀ z ∈ Icc x w, HasDerivWithinAt v (deriv v z) (Icc x w) z := by
          intro z hz
          have hzab : z ∈ Ioo a b :=
            ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hw.2⟩
          exact (hdiff z hzab).differentiableAt
            (Ioo_mem_nhds hzab.1 hzab.2) |>.hasDerivAt.hasDerivWithinAt
        obtain ⟨c, hc, hcv⟩ := exists_hasDerivWithinAt_eq_of_lt_of_gt
          hw.1.le hD htx ((le_of_not_gt hmw).trans_lt hmt)
        filter_upwards [Iio_mem_nhds hc.1, Ioo_mem_nhds hx.1 hx.2] with y hyI hy
        have hyc : c ∈ Ioo a b := ⟨lt_trans hx.1 hc.1, lt_trans hc.2 hw.2⟩
        exact lt_of_lt_of_le (by rw [hcv]; exact hmt) (hanti hy hyc hyI.le)
    · intro M hMx
      let u : ℝ := (a + x) / 2
      have hu : u ∈ Ioo a x := by
        dsimp [u]
        constructor <;> linarith [hx.1]
      have hu' : u ∈ Ioo a b := ⟨hu.1, lt_trans hu.2 hx.2⟩
      by_cases hMu : deriv v u < M
      · filter_upwards [Ioi_mem_nhds hu.2, Ioo_mem_nhds hx.1 hx.2] with y hyI hy
        exact lt_of_le_of_lt (hanti hu' hy (le_of_lt hyI)) hMu
      · let t : ℝ := (deriv v x + M) / 2
        have hxt : deriv v x < t := by dsimp [t]; linarith
        have htM : t < M := by dsimp [t]; linarith
        have hD : ∀ z ∈ Icc u x, HasDerivWithinAt v (deriv v z) (Icc u x) z := by
          intro z hz
          have hzab : z ∈ Ioo a b :=
            ⟨lt_of_lt_of_le hu.1 hz.1, lt_of_le_of_lt hz.2 hx.2⟩
          exact (hdiff z hzab).differentiableAt
            (Ioo_mem_nhds hzab.1 hzab.2) |>.hasDerivAt.hasDerivWithinAt
        obtain ⟨c, hc, hcv⟩ := exists_hasDerivWithinAt_eq_of_lt_of_gt
          hu.2.le hD (htM.trans_le (le_of_not_gt hMu)) hxt
        filter_upwards [Ioi_mem_nhds hc.2, Ioo_mem_nhds hx.1 hx.2] with y hyI hy
        have hca : c ∈ Ioo a b := ⟨lt_trans hu.1 hc.1, lt_trans hc.2 hx.2⟩
        exact lt_of_le_of_lt (hanti hca hy hyI.le) (by rw [hcv]; exact htM)
  exact hcont.continuousWithinAt

theorem HalfLineH1.CorrectionBumps.localReducedProfile_deriv_continuousOn
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ContinuousOn (deriv (B.localReducedProfile f a)) (Ioo a b) := by
  exact continuousOn_deriv_of_differentiableOn_of_antitoneOn
    (B.localReducedProfile_differentiableOn hfmin ha hab)
    (B.localReducedProfile_deriv_antitoneOn hfmin ha hab)



theorem HalfLineH1.CorrectionBumps.deriv_localReducedProfile_eq_forcingPrimitive_of_contact
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b x : ℝ} (ha : 0 < a) (hab : a < b)
    (hx : x ∈ Ioo a b) (hcontact : f.continuousRep x = 0) :
    deriv (B.localReducedProfile f a) x =
      forcingPrimitive (fun z => f.rayleighQuotient*f.continuousRep z -
        B.massMultiplier - B.momentMultiplier*z) a x := by
  exact (B.localReducedProfile_hasDerivAt_of_contact hfmin ha hab hx hcontact).deriv

theorem HalfLineH1.CorrectionBumps.exists_localReducedProfile_eq_affineOn_of_local_freeInterval
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b p q : ℝ}
    (ha : 0 < a) (hab : a < b) (hpq : p < q)
    (hinner : Ioo p q ⊆ Ioo a b)
    (hfree : Ioo p q ⊆ f.positivitySet) :
    ∃ m d : ℝ, ∀ x ∈ Ioo p q,
      B.localReducedProfile f a x = m*x+d := by
  obtain ⟨c, hc⟩ := B.exists_localReducedProfile_sub_eq_integral_const_sub_cdf hfmin ha hab
  let r : ℝ := (p + q) / 2
  have hr : r ∈ Ioo p q := by dsimp [r]; constructor <;> linarith
  let μ := B.localReactionMeasure hfmin a b
  let k := measureCDF μ r
  let m := c - k
  let d := B.localReducedProfile f a r - m * r
  refine ⟨m, d, ?_⟩
  intro x hx
  have hsub := hc (hinner hr) (hinner hx)
  have hint : (∫ t in r..x, (c - measureCDF μ t)) = (x - r) * m := by
    calc
      _ = ∫ t in r..x, m := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with t ht
        have ht' : t ∈ uIcc r x := uIoc_subset_uIcc ht
        have htI : t ∈ Ioo p q := by
          rcases le_total r x with hrx | hxr
          · rw [uIcc_of_le hrx] at ht'
            exact ⟨lt_of_lt_of_le hr.1 ht'.1, lt_of_le_of_lt ht'.2 hx.2⟩
          · rw [uIcc_of_ge hxr] at ht'
            exact ⟨lt_of_lt_of_le hx.1 ht'.1, lt_of_le_of_lt ht'.2 hr.2⟩
        have hcdf := B.measureCDF_localReactionMeasure_eq_of_local_freeInterval
          (a := a) (b := b) hfmin ha hab hfree hr htI
        dsimp [m, k]
        rw [hcdf]
      _ = _ := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  dsimp [d]
  linarith [hsub, hint]

theorem HalfLineH1.CorrectionBumps.deriv_localReducedProfile_eq_of_Icc_subset_positivitySet
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b x y : ℝ}
    (ha : 0<a) (hab : a<b)
    (hx : x∈Ioo a b) (hy : y∈Ioo a b) (hxy : x≤y)
    (hxypos : Icc x y ⊆ f.positivitySet) :
    deriv (B.localReducedProfile f a) x = deriv (B.localReducedProfile f a) y := by
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  have hopen : IsOpen (f.positivitySet ∩ Ioo a b) :=
    f.isOpen_positivitySet.inter isOpen_Ioo
  obtain ⟨p₀, qx, hxpq, hxpqsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.1 (hopen.mem_nhds ⟨hxypos ⟨le_rfl, hxy⟩, hx⟩)
  obtain ⟨py, q₀, hypq, hypqsub⟩ :=
    mem_nhds_iff_exists_Ioo_subset.1 (hopen.mem_nhds ⟨hxypos ⟨hxy, le_rfl⟩, hy⟩)
  let p := (p₀ + x) / 2
  let q := (y + q₀) / 2
  have hp : p ∈ Ioo p₀ qx := by
    dsimp [p]
    constructor <;> linarith [hxpq.1, hxpq.2]
  have hq : q ∈ Ioo py q₀ := by
    dsimp [q]
    constructor <;> linarith [hypq.1, hypq.2]
  have hpq : p < q := by
    dsimp [p, q]
    linarith [hxpq.1, hypq.2, hxy']
  have hinner : Ioo p q ⊆ Ioo a b := by
    intro z hz
    rcases lt_or_ge z x with hzx | hxz
    · have hzin : z ∈ Ioo p₀ qx := by
        exact ⟨lt_trans hp.1 hz.1, lt_trans hzx hxpq.2⟩
      exact (hxpqsub hzin).2
    · rcases lt_or_ge z y with hzy | hyz
      · exact ⟨hx.1.trans_le hxz, lt_trans hzy hy.2⟩
      · have hzin : z ∈ Ioo py q₀ := by
          exact ⟨hypq.1.trans_le hyz, lt_trans hz.2 hq.2⟩
        exact (hypqsub hzin).2
  have hfree : Ioo p q ⊆ f.positivitySet := by
    intro z hz
    rcases lt_or_ge z x with hzx | hxz
    · have hzin : z ∈ Ioo p₀ qx := by
        exact ⟨lt_trans hp.1 hz.1, lt_trans hzx hxpq.2⟩
      exact (hxpqsub hzin).1
    · rcases lt_or_ge z y with hzy | hyz
      · exact hxypos ⟨hxz, hzy.le⟩
      · have hzin : z ∈ Ioo py q₀ := by
          exact ⟨hypq.1.trans_le hyz, lt_trans hz.2 hq.2⟩
        exact (hypqsub hzin).1
  obtain ⟨m, d, heq⟩ := B.exists_localReducedProfile_eq_affineOn_of_local_freeInterval
    hfmin ha hab hpq hinner hfree
  have hx' : x ∈ Ioo p q := by
    exact ⟨by dsimp [p]; linarith [hxpq.1], by dsimp [q]; linarith [hypq.2, hxy']⟩
  have hy' : y ∈ Ioo p q := by
    exact ⟨by dsimp [p]; linarith [hxpq.1, hxy'], by dsimp [q]; linarith [hypq.2]⟩
  have hlin : ∀ z ∈ Ioo p q, HasDerivAt (fun w : ℝ => m*w+d) m z := by
    intro z hz
    simpa using ((hasDerivAt_id z).const_mul m).add_const d
  have hdx : HasDerivAt (B.localReducedProfile f a) m x := by
    exact (hlin x hx').congr_of_eventuallyEq <| by
      filter_upwards [Ioo_mem_nhds hx'.1 hx'.2] with z hz
      exact heq z hz
  have hdy : HasDerivAt (B.localReducedProfile f a) m y := by
    exact (hlin y hy').congr_of_eventuallyEq <| by
      filter_upwards [Ioo_mem_nhds hy'.1 hy'.2] with z hz
      exact heq z hz
  rw [hdx.deriv, hdy.deriv]

theorem HalfLineH1.CorrectionBumps.localReducedProfile_deriv_lipschitzOn
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b p q : ℝ}
    (ha : 0 < a) (hab : a < b) (hp : a < p) (hpq : p ≤ q) (hq : q < b) :
    ∃ C : NNReal, LipschitzOnWith C (deriv (B.localReducedProfile f a)) (Icc p q) := by
  let F : ℝ → ℝ := fun z => f.rayleighQuotient * f.continuousRep z -
    B.massMultiplier - B.momentMultiplier * z
  have hF : Continuous F := by
    dsimp [F]
    exact (((continuous_const.mul f.continuous_continuousRep).sub continuous_const).sub
      (continuous_const.mul continuous_id))
  obtain ⟨C, hC⟩ := forcingPrimitive_lipschitzOn (a := a) hF hpq
  refine ⟨C, ?_⟩
  have hordered : ∀ x ∈ Icc p q, ∀ y ∈ Icc p q, x ≤ y →
      dist (deriv (B.localReducedProfile f a) x)
          (deriv (B.localReducedProfile f a) y) ≤ (C : ℝ) * dist x y := by
    intro x hx y hy hxy
    have hxa : x ∈ Ioo a b := ⟨lt_of_lt_of_le hp hx.1, lt_of_le_of_lt hx.2 hq⟩
    have hya : y ∈ Ioo a b := ⟨lt_of_lt_of_le hp hy.1, lt_of_le_of_lt hy.2 hq⟩
    let Z : Set ℝ := Icc x y ∩ {z | f.continuousRep z = 0}
    have hZcompact : IsCompact Z := isCompact_Icc.inter_right
      (isClosed_eq f.continuous_continuousRep continuous_const)
    by_cases hZn : Z.Nonempty
    · obtain ⟨r, hr⟩ := hZcompact.exists_isLeast hZn
      obtain ⟨s, hs⟩ := hZcompact.exists_isGreatest hZn
      have hrmem : r ∈ Icc x y := hr.1.1
      have hsmem : s ∈ Icc x y := hs.1.1
      have hxr : x ≤ r := hrmem.1
      have hsy : s ≤ y := hsmem.2
      have hrs : r ≤ s := hr.2 hs.1
      have hrab : r ∈ Ioo a b := ⟨lt_of_lt_of_le hxa.1 hxr, lt_of_le_of_lt hrmem.2 hya.2⟩
      have hsab : s ∈ Ioo a b := ⟨lt_of_lt_of_le hxa.1 hsmem.1, lt_of_le_of_lt hsmem.2 hya.2⟩
      have heqr : deriv (B.localReducedProfile f a) x = deriv (B.localReducedProfile f a) r := by
        by_cases hxr' : x = r
        · simp [hxr']
        · have heq : Set.EqOn (deriv (B.localReducedProfile f a))
              (fun _ => deriv (B.localReducedProfile f a) x) (Ico x r) := by
            intro z hz
            have hzab : z ∈ Ioo a b := ⟨hxa.1.trans_le hz.1, hz.2.trans hrab.2⟩
            have hpos : Icc x z ⊆ f.positivitySet := by
              intro t ht
              have hnonneg := hfmin.1.nonnegative t
                (le_trans (le_of_lt ha) (le_trans (le_of_lt hp) (le_trans hx.1 ht.1)))
              by_contra hzero
              have htcontact : f.continuousRep t = 0 := le_antisymm
                (le_of_not_gt hzero) hnonneg
              have htZ : t ∈ Z := ⟨⟨ht.1, ht.2.trans (hz.2.le.trans hrmem.2)⟩, htcontact⟩
              exact (not_lt_of_ge (hr.2 htZ)) (ht.2.trans_lt hz.2)
            exact (B.deriv_localReducedProfile_eq_of_Icc_subset_positivitySet
              hfmin ha hab hxa hzab hz.1 hpos).symm
          have hxrlt : x < r := lt_of_le_of_ne hxr hxr'
          have hEq := heq.of_subset_closure
            ((B.localReducedProfile_deriv_continuousOn hfmin ha hab).mono (by
              intro t ht; exact ⟨lt_of_lt_of_le hxa.1 ht.1, lt_of_le_of_lt ht.2 hrab.2⟩))
            continuousOn_const Ico_subset_Icc_self (by rw [closure_Ico hxrlt.ne])
          exact (hEq ⟨hxr, le_rfl⟩).symm
      have heqs : deriv (B.localReducedProfile f a) y = deriv (B.localReducedProfile f a) s := by
        by_cases hsy' : s = y
        · simp [hsy']
        · have heq : Set.EqOn (deriv (B.localReducedProfile f a))
              (fun _ => deriv (B.localReducedProfile f a) y) (Ioc s y) := by
            intro z hz
            have hzab : z ∈ Ioo a b := ⟨hsab.1.trans hz.1, hz.2.trans_lt hya.2⟩
            have hpos : Icc z y ⊆ f.positivitySet := by
              intro t ht
              have hnonneg := hfmin.1.nonnegative t
                (le_trans (le_of_lt ha) (le_trans (le_of_lt hxa.1)
                  (le_trans hsmem.1 (hz.1.le.trans ht.1))))
              by_contra hzero
              have htcontact : f.continuousRep t = 0 := le_antisymm
                (le_of_not_gt hzero) hnonneg
              have htZ : t ∈ Z := ⟨⟨hsmem.1.trans (hz.1.le.trans ht.1), ht.2⟩, htcontact⟩
              exact (not_lt_of_ge (hs.2 htZ)) (hz.1.trans_le ht.1)
            exact (B.deriv_localReducedProfile_eq_of_Icc_subset_positivitySet
              hfmin ha hab hzab hya hz.2 hpos)
          have hsylt : s < y := lt_of_le_of_ne hsy hsy'
          have hEq := heq.of_subset_closure
            ((B.localReducedProfile_deriv_continuousOn hfmin ha hab).mono (by
              intro t ht; exact ⟨lt_of_lt_of_le hsab.1 ht.1, lt_of_le_of_lt ht.2 hya.2⟩))
            continuousOn_const Ioc_subset_Icc_self (by rw [closure_Ioc hsylt.ne])
          exact (hEq ⟨le_rfl, hsy⟩).symm
      have hbound := hC.dist_le_mul r ⟨le_trans hx.1 hrmem.1, le_trans hrmem.2 hy.2⟩
        s ⟨le_trans hx.1 hsmem.1, le_trans hsmem.2 hy.2⟩
      rw [heqr, heqs,
        B.deriv_localReducedProfile_eq_forcingPrimitive_of_contact hfmin ha hab hrab hr.1.2,
        B.deriv_localReducedProfile_eq_forcingPrimitive_of_contact hfmin ha hab hsab hs.1.2]
      have hrsdist : dist r s ≤ dist x y := by
        rw [Real.dist_eq, Real.dist_eq]
        rw [abs_of_nonpos (sub_nonpos.mpr hrs), abs_of_nonpos (sub_nonpos.mpr hxy)]
        linarith
      exact hbound.trans (mul_le_mul_of_nonneg_left hrsdist C.coe_nonneg)
    · have hpos : Icc x y ⊆ f.positivitySet := by
        intro z hz
        have hnonneg := hfmin.1.nonnegative z
          (le_trans (le_of_lt ha) (le_trans (le_of_lt hp) (le_trans hx.1 hz.1)))
        by_contra hnot
        have hzero : f.continuousRep z = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
        exact hZn ⟨z, ⟨hz, hzero⟩⟩
      have heq := B.deriv_localReducedProfile_eq_of_Icc_subset_positivitySet
        hfmin ha hab hxa hya hxy hpos
      simpa [heq] using (mul_nonneg C.coe_nonneg dist_nonneg)
  exact LipschitzOnWith.of_dist_le_mul (fun x hx y hy => by
     rcases le_total x y with hxy | hyx
     · exact hordered x hx y hy hxy
     · simpa [dist_comm] using hordered y hy x hx hyx)

theorem HalfLineH1.CorrectionBumps.continuousRep_hasDerivAt
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b x : ℝ}
    (ha : 0 < a) (hab : a < b) (hx : x ∈ Ioo a b) :
    HasDerivAt f.continuousRep
      (deriv (B.localReducedProfile f a) x -
        forcingPrimitive (fun z => f.rayleighQuotient * f.continuousRep z -
          B.massMultiplier - B.momentMultiplier*z) a x) x := by
  let F : ℝ → ℝ := fun z => f.rayleighQuotient * f.continuousRep z -
    B.massMultiplier - B.momentMultiplier * z
  have hF : Continuous F := by
    dsimp [F]
    exact (((continuous_const.mul f.continuous_continuousRep).sub continuous_const).sub
      (continuous_const.mul continuous_id))
  have hprof := (B.localReducedProfile_differentiableOn hfmin ha hab x hx).differentiableAt
    (Ioo_mem_nhds hx.1 hx.2) |>.hasDerivAt
  have hpot := forcingPotential_hasDerivAt hF a x
  have hsub := hprof.sub hpot
  change HasDerivAt (fun y => B.localReducedProfile f a y - forcingPotential F a y)
    (deriv (B.localReducedProfile f a) x - forcingPrimitive F a x) x at hsub
  have hfun : (fun y => B.localReducedProfile f a y - forcingPotential F a y) =
      f.continuousRep := by
    funext y
    simp [HalfLineH1.CorrectionBumps.localReducedProfile, F]
  rw [hfun] at hsub
  simpa [F] using hsub

theorem HalfLineH1.CorrectionBumps.continuousRep_differentiableOn
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    DifferentiableOn ℝ f.continuousRep (Ioo a b) := by
  intro x hx
  exact (B.continuousRep_hasDerivAt hfmin ha hab hx).differentiableAt.differentiableWithinAt

theorem HalfLineH1.CorrectionBumps.deriv_continuousRep_eq
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b x : ℝ}
    (ha : 0 < a) (hab : a < b) (hx : x ∈ Ioo a b) :
    deriv f.continuousRep x =
      deriv (B.localReducedProfile f a) x -
        forcingPrimitive (fun z => f.rayleighQuotient * f.continuousRep z -
          B.massMultiplier - B.momentMultiplier*z) a x :=
  (B.continuousRep_hasDerivAt hfmin ha hab hx).deriv

theorem HalfLineH1.CorrectionBumps.deriv_continuousRep_lipschitzOn
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b p q : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hp : a < p) (hpq : p ≤ q) (hq : q < b) :
    ∃ C : NNReal, LipschitzOnWith C (deriv f.continuousRep) (Icc p q) := by
  let F : ℝ → ℝ := fun z => f.rayleighQuotient * f.continuousRep z -
    B.massMultiplier - B.momentMultiplier * z
  have hF : Continuous F := by
    dsimp [F]
    exact (((continuous_const.mul f.continuous_continuousRep).sub continuous_const).sub
      (continuous_const.mul continuous_id))
  obtain ⟨C₁, hC₁⟩ := B.localReducedProfile_deriv_lipschitzOn
    hfmin ha hab hp hpq hq
  obtain ⟨C₂, hC₂⟩ := forcingPrimitive_lipschitzOn (a := a) hF hpq
  refine ⟨C₁ + C₂, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxI : x ∈ Ioo a b := ⟨lt_of_lt_of_le hp hx.1, lt_of_le_of_lt hx.2 hq⟩
  have hyI : y ∈ Ioo a b := ⟨lt_of_lt_of_le hp hy.1, lt_of_le_of_lt hy.2 hq⟩
  rw [B.deriv_continuousRep_eq hfmin ha hab hxI,
    B.deriv_continuousRep_eq hfmin ha hab hyI]
  have h₁ := hC₁.dist_le_mul x hx y hy
  have h₂ := hC₂.dist_le_mul x hx y hy
  calc
    dist (deriv (B.localReducedProfile f a) x - forcingPrimitive F a x)
        (deriv (B.localReducedProfile f a) y - forcingPrimitive F a y) ≤
        dist (deriv (B.localReducedProfile f a) x)
          (deriv (B.localReducedProfile f a) y) +
          dist (forcingPrimitive F a x) (forcingPrimitive F a y) := by
      exact dist_sub_sub_le _ _ _ _
    _ ≤ (C₁ : ℝ) * dist x y + (C₂ : ℝ) * dist x y :=
      add_le_add h₁ h₂
    _ = ((C₁ + C₂ : NNReal) : ℝ) * dist x y := by
      rw [NNReal.coe_add]
      ring

theorem HalfLineH1.CorrectionBumps.deriv_continuousRep_absolutelyContinuousOnInterval
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b p q : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hp : a < p) (hpq : p ≤ q) (hq : q < b) :
    AbsolutelyContinuousOnInterval (deriv f.continuousRep) p q := by
  obtain ⟨C, hC⟩ := B.deriv_continuousRep_lipschitzOn hfmin ha hab hp hpq hq
  have hC' : LipschitzOnWith C (deriv f.continuousRep) (uIcc p q) := by
    simpa [uIcc_of_le hpq] using hC
  exact hC'.absolutelyContinuousOnInterval

theorem HalfLineH1.CorrectionBumps.deriv_deriv_continuousRep_memLp_top
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b p q : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hp : a < p) (hpq : p ≤ q) (hq : q < b) :
    MemLp (deriv (deriv f.continuousRep)) ∞
      ((volume : Measure ℝ).restrict (Icc p q)) := by
  obtain ⟨C, hC⟩ := B.deriv_continuousRep_lipschitzOn hfmin ha hab hp hpq hq
  have hmeas : AEStronglyMeasurable (deriv (deriv f.continuousRep))
      ((volume : Measure ℝ).restrict (Icc p q)) :=
    (aestronglyMeasurable_deriv (deriv f.continuousRep)
      (volume : Measure ℝ)).restrict
  apply memLp_top_of_bound hmeas (C : ℝ)
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) p,
    Measure.ae_ne (volume : Measure ℝ) q] with x hxp hxq hxI
  by_cases hlt : p < x ∧ x < q
  · exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hlt.1 hlt.2) hC
  · exfalso
    exact hlt ⟨lt_of_le_of_ne hxI.1 (Ne.symm hxp),
      lt_of_le_of_ne hxI.2 hxq⟩

theorem HalfLineH1.CorrectionBumps.localReactionMeasure_restrict_le_smul_volume
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b p q : ℝ}
    (ha : 0 < a) (hab : a < b) (hp : a < p) (hpq : p ≤ q) (hq : q < b) :
    ∃ C : NNReal,
      (B.localReactionMeasure hfmin a b).restrict (Icc p q) ≤
        (C : ℝ≥0∞) • (volume.restrict (Icc p q)) := by
  let r : ℝ := (a + p) / 2
  have har : a < r := by dsimp [r]; linarith
  have hrp : r < p := by dsimp [r]; linarith
  obtain ⟨C, hCderiv⟩ := B.localReducedProfile_deriv_lipschitzOn
    hfmin ha hab har (le_trans hrp.le hpq) hq
  obtain ⟨c, hc⟩ := B.measureCDF_localReducedProfile_eq_const_sub_deriv
    hfmin ha hab
  let μ := B.localReactionMeasure hfmin a b
  let _ : IsFiniteMeasure μ := B.localReactionMeasure_isFinite hfmin ha
  have hCcdf : LipschitzOnWith C (measureCDF μ) (Icc r q) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxI : x ∈ Ioo a b := ⟨lt_of_lt_of_le har hx.1, lt_of_le_of_lt hx.2 hq⟩
    have hyI : y ∈ Ioo a b := ⟨lt_of_lt_of_le har hy.1, lt_of_le_of_lt hy.2 hq⟩
    rw [hc x hxI, hc y hyI]
    have h := hCderiv.dist_le_mul x hx y hy
    calc
      dist (c - deriv (B.localReducedProfile f a) x)
          (c - deriv (B.localReducedProfile f a) y) =
        dist (deriv (B.localReducedProfile f a) x)
          (deriv (B.localReducedProfile f a) y) := by
            rw [Real.dist_eq, Real.dist_eq]
            simp [abs_sub_comm]
      _ ≤ (C : ℝ) * dist x y := h
  refine ⟨C, ?_⟩
  simpa [μ] using clipped_measure_le_smul_volume_Icc hrp hpq hCcdf

theorem HalfLineH1.CorrectionBumps.localReactionMeasure_restrict_absolutelyContinuous
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b p q : ℝ}
    (ha : 0 < a) (hab : a < b) (hp : a < p) (hpq : p ≤ q) (hq : q < b) :
    (B.localReactionMeasure hfmin a b).restrict (Icc p q) ≪
      (volume : Measure ℝ).restrict (Icc p q) := by
  obtain ⟨C, hC⟩ := B.localReactionMeasure_restrict_le_smul_volume
    hfmin ha hab hp hpq hq
  exact Measure.absolutelyContinuous_of_le_smul hC

theorem HalfLineH1.CorrectionBumps.localReactionMeasure_restrict_rnDeriv_memLp_top
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b p q : ℝ}
    (ha : 0 < a) (hab : a < b) (hp : a < p) (hpq : p ≤ q) (hq : q < b) :
    MemLp
      (fun x => (((B.localReactionMeasure hfmin a b).restrict (Icc p q)).rnDeriv
        ((volume : Measure ℝ).restrict (Icc p q)) x).toReal)
      ∞ ((volume : Measure ℝ).restrict (Icc p q)) := by
  obtain ⟨C, hC⟩ := B.localReactionMeasure_restrict_le_smul_volume
    hfmin ha hab hp hpq hq
  let μ := B.localReactionMeasure hfmin a b
  let _ : IsFiniteMeasure μ := B.localReactionMeasure_isFinite hfmin ha
  simpa [μ] using rnDeriv_memLp_top_of_le_smul
    (μ := μ.restrict (Icc p q))
    (ν := (volume : Measure ℝ).restrict (Icc p q)) hC

end Analysis
end RayleighKernel
