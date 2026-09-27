import RayleighKernel.Analysis.HalfLineSobolevConverse
import RayleighKernel.Scaling
import RayleighKernel.Variational

noncomputable section
namespace RayleighKernel.Analysis

open ContinuousLinearMap MeasureTheory Set Filter
open scoped ContDiff ENNReal SchwartzMap Topology Convolution

theorem HalfLineH1.continuousRep_representativeData (u : HalfLineH1) :
    HalfLineRepresentativeData u.continuousRep := by
  refine ⟨u.continuousRep_zero, ?_, u.continuousRep_memLp,
    u.deriv_continuousRep_memLp, ?_, ?_, ?_⟩
  · intro R hR
    exact u.continuousRep_absolutelyContinuousOnInterval 0 R
  · apply (ae_restrict_iff' measurableSet_Iic).2
    filter_upwards with x
    exact u.continuousRep_eq_zero_of_nonpositive
  · exact u.deriv_continuousRep_ae_eq_zero_on_nonpositive
  · intro φ
    rw [u.toLp_continuousRep, u.toLp_deriv_continuousRep]
    exact u.weakDerivative_identity φ

structure RescaleRepresentativeRegularity (u : HalfLineH1) (a : ℝ) : Prop where
  trace_zero : RayleighKernel.rescale a u.continuousRep 0 = 0
  locally_absolutelyContinuous : ∀ R, 0 < R →
    AbsolutelyContinuousOnInterval (RayleighKernel.rescale a u.continuousRep) 0 R
  value_memLp : MemLp (RayleighKernel.rescale a u.continuousRep) 2 volume
  deriv_memLp : MemLp (deriv (RayleighKernel.rescale a u.continuousRep)) 2 volume
  value_ae_eq_zero_on_nonpositive :
    RayleighKernel.rescale a u.continuousRep =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0
  deriv_ae_eq_zero_on_nonpositive :
    deriv (RayleighKernel.rescale a u.continuousRep) =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0

theorem HalfLineH1.rescale_regularity (u : HalfLineH1) {a : ℝ} (ha : 0 < a) :
    RescaleRepresentativeRegularity u a := by
  let g : ℝ → ℝ := fun y => a ^ 2 * (u.weakDeriv : ℝ → ℝ) (a * y)
  have hqmp : Measure.QuasiMeasurePreserving (fun x : ℝ => a • x) volume volume :=
    Measure.quasiMeasurePreserving_smul volume ha.ne'
  have hgmeas : AEStronglyMeasurable g volume := by
    have hcomp := (Lp.memLp u.weakDeriv).aestronglyMeasurable
      |>.comp_quasiMeasurePreserving hqmp
    simpa [g, smul_eq_mul, Function.comp_def] using hcomp.const_mul (a ^ 2)
  have hg_sq : Integrable (fun x => g x ^ 2) volume := by
    have hbase := (Lp.memLp u.weakDeriv).integrable_sq
    have hc := hbase.comp_mul_left' ha.ne'
    convert hc.const_mul (a ^ 4) using 1
    · funext x
      dsimp [g]
      ring
  have hg : MemLp g 2 volume :=
    (memLp_two_iff_integrable_sq hgmeas).2 hg_sq
  have hderiv_ae : deriv (RayleighKernel.rescale a u.continuousRep) =ᵐ[volume] g := by
    filter_upwards [u.deriv_continuousRep_ae.comp_tendsto hqmp.tendsto_ae] with x hx
    rw [RayleighKernel.deriv_rescale]
    rw [show deriv u.continuousRep (a * x) = (u.weakDeriv : ℝ → ℝ) (a * x) by
      simpa [Function.comp_apply, smul_eq_mul] using hx]
  have hval_meas : AEStronglyMeasurable
      (RayleighKernel.rescale a u.continuousRep) volume := by
    unfold RayleighKernel.rescale
    exact (continuous_const.mul (u.continuous_continuousRep.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable
  have hval_sq : Integrable
      (fun x => (RayleighKernel.rescale a u.continuousRep x) ^ 2) volume := by
    have hc := u.continuousRep_sq_integrable.comp_mul_left' ha.ne'
    convert hc.const_mul (a ^ 2) using 1
    · funext x
      simp [RayleighKernel.rescale]
      ring
  have hval : MemLp (RayleighKernel.rescale a u.continuousRep) 2 volume :=
    (memLp_two_iff_integrable_sq hval_meas).2 hval_sq
  have hderiv : MemLp (deriv (RayleighKernel.rescale a u.continuousRep)) 2 volume :=
    MemLp.ae_eq hderiv_ae.symm hg
  have hprimitive : ∀ x : ℝ,
      (∫ t in 0..x, g t) = RayleighKernel.rescale a u.continuousRep x := by
    intro x
    change (∫ t in 0..x, g t) = a * u.continuousRep (a * x)
    rw [show u.continuousRep (a * x) =
        ∫ s in 0..a * x, (u.weakDeriv : ℝ → ℝ) s by rfl]
    calc
      _ = a ^ 2 * ∫ t in 0..x, (u.weakDeriv : ℝ → ℝ) (a * t) := by
        rw [← intervalIntegral.integral_const_mul]
      _ = a * (a * ∫ t in 0..x, (u.weakDeriv : ℝ → ℝ) (a * t)) := by ring
      _ = a * ∫ t in 0..a * x, (u.weakDeriv : ℝ → ℝ) t := by
        congr 1
        simpa [smul_eq_mul] using
          (intervalIntegral.smul_integral_comp_mul_left
            (u.weakDeriv : ℝ → ℝ) a (a := (0 : ℝ)) (b := x))
  refine ⟨?_, ?_, hval, hderiv, ?_, ?_⟩
  · simp [RayleighKernel.rescale, u.continuousRep_zero]
  · intro R hR
    have hgi : IntervalIntegrable g volume 0 R := by
      have hb := u.weakDeriv_intervalIntegrable 0 (a * R)
      have hc := hb.comp_mul_left (c := a)
      simpa [g, ha.ne'] using hc.const_mul (a ^ 2)
    have hac := hgi.absolutelyContinuousOnInterval_intervalIntegral
      (show (0 : ℝ) ∈ uIcc 0 R by simp [hR.le])
    apply hac.congr
    intro x hx
    exact hprimitive x
  · apply (ae_restrict_iff' measurableSet_Iic).2
    filter_upwards with x hx
    rw [RayleighKernel.rescale_apply, u.continuousRep_eq_zero_of_nonpositive]
    · simp
    · exact mul_nonpos_of_nonneg_of_nonpos ha.le hx
  · apply (ae_restrict_iff' measurableSet_Iic).2
    have hzero : ∀ᵐ y ∂volume, y ≤ 0 → (u.weakDeriv : ℝ → ℝ) y = 0 := by
      filter_upwards [(ae_restrict_iff' measurableSet_Iic).1
        u.weakDeriv_ae_eq_zero_on_nonpositive] with y hy hy0
      exact hy hy0
    filter_upwards [hderiv_ae, hqmp.tendsto_ae.eventually hzero] with x hx hzero'
    intro hxnonpos
    rw [hx]
    simp only [g]
    have hx0 : a * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hxnonpos
    have hz := hzero' hx0
    change a ^ 2 * (u.weakDeriv : ℝ → ℝ) (a • x) = 0
    rw [hz]
    simp

theorem HalfLineH1.integral_rescale_mul_schwartzDeriv
    (u : HalfLineH1) {a : ℝ} (ha : 0 < a) (φ : 𝓢(ℝ,ℝ)) :
    (∫ y : ℝ, RayleighKernel.rescale a u.continuousRep y * deriv (φ : ℝ → ℝ) y) =
      ∫ x : ℝ, u.continuousRep x * deriv (φ : ℝ → ℝ) (a⁻¹ * x) := by
  let F : ℝ → ℝ := fun x => u.continuousRep x * deriv (φ : ℝ → ℝ) (a⁻¹ * x)
  have hchange := MeasureTheory.Measure.integral_comp_mul_left F a
  have hF : (fun y : ℝ => F (a * y)) =
      fun y => u.continuousRep (a * y) * deriv (φ : ℝ → ℝ) y := by
    funext y; dsimp [F]; congr 2; field_simp [ha.ne']
  have habs : |a⁻¹| = a⁻¹ := abs_of_pos (inv_pos.mpr ha)
  calc
    _ = a * ∫ y : ℝ, F (a * y) := by
      rw [← integral_const_mul]; congr 1; funext y
      simp [RayleighKernel.rescale]; rw [congrFun hF y]; ring
    _ = a * (|a⁻¹| • ∫ x : ℝ, F x) := by rw [hchange]
    _ = ∫ x : ℝ, F x := by simp [habs, smul_eq_mul, ha.ne']
    _ = _ := by rfl

theorem HalfLineH1.integral_deriv_rescale_mul_schwartz
    (u : HalfLineH1) {a : ℝ} (ha : 0 < a) (φ : 𝓢(ℝ,ℝ)) :
    (∫ y : ℝ, deriv (RayleighKernel.rescale a u.continuousRep) y * φ y) =
      a * ∫ x : ℝ, deriv u.continuousRep x * φ (a⁻¹ * x) := by
  let D : ℝ → ℝ := fun x => deriv u.continuousRep x * φ (a⁻¹ * x)
  have hchange := MeasureTheory.Measure.integral_comp_mul_left D a
  have hD : (fun y : ℝ => D (a * y)) =
      fun y => deriv u.continuousRep (a * y) * φ y := by
    funext y; dsimp [D]; congr 2; field_simp [ha.ne']
  have habs : |a⁻¹| = a⁻¹ := abs_of_pos (inv_pos.mpr ha)
  calc
    _ = a ^ 2 * ∫ y : ℝ, D (a * y) := by
      rw [show (fun y : ℝ => deriv (RayleighKernel.rescale a u.continuousRep) y * φ y) =
          fun y => a ^ 2 * (deriv u.continuousRep (a * y) * φ y) by
        funext y; rw [RayleighKernel.deriv_rescale]; ring]
      rw [← integral_const_mul]; congr 1; funext y; rw [congrFun hD y]
    _ = a ^ 2 * (|a⁻¹| • ∫ x : ℝ, D x) := by rw [hchange]
    _ = a * ∫ x : ℝ, D x := by rw [habs]; simp only [smul_eq_mul]; field_simp [ha.ne']
    _ = _ := by rfl

theorem HalfLineH1.rescale_weakDerivative_identity
    (u : HalfLineH1) {a : ℝ} (ha : 0 < a)
    (hvalue : MemLp (RayleighKernel.rescale a u.continuousRep) 2 volume)
    (hderiv : MemLp (deriv (RayleighKernel.rescale a u.continuousRep)) 2 volume) :
    ∀ φ : 𝓢(ℝ,ℝ),
      l2Pairing (hvalue.toLp (RayleighKernel.rescale a u.continuousRep))
          (schwartzDeriv φ) =
        -l2Pairing (hderiv.toLp (deriv (RayleighKernel.rescale a u.continuousRep)))
          (schwartzValue φ) := by
  intro φ
  let ψ : 𝓢(ℝ,ℝ) :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (ContinuousLinearEquiv.smulLeft (Units.mk0 a⁻¹ (inv_ne_zero ha.ne')))) φ
  let χ : 𝓢(ℝ,ℝ) := a • ψ
  have hψ : ∀ x : ℝ, ψ x = φ (a⁻¹ * x) := by
    intro x; simp [ψ, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      ContinuousLinearEquiv.smulLeft_apply_apply]
  have hχ : ∀ x : ℝ, χ x = a * φ (a⁻¹ * x) := by
    intro x; simp [χ, hψ]
  have hχfun : (χ : ℝ → ℝ) = fun x => a * φ (a⁻¹ * x) := funext hχ
  have hχd : ∀ x : ℝ, deriv (χ : ℝ → ℝ) x =
      deriv (φ : ℝ → ℝ) (a⁻¹ * x) := by
    intro x; rw [hχfun, deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul]; field_simp [ha.ne']
  have hleft : l2Pairing (hvalue.toLp (RayleighKernel.rescale a u.continuousRep))
      (schwartzDeriv φ) = ∫ x, RayleighKernel.rescale a u.continuousRep x * deriv (φ : ℝ → ℝ) x := by
    rw [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral]; apply integral_congr_ae
    filter_upwards [hvalue.coeFn_toLp, (SchwartzMap.derivCLM ℝ ℝ φ).coeFn_toLp 2 volume] with x hx hφx
    simp [schwartzDeriv, schwartzValue, hx, hφx]
  have hright : l2Pairing (hderiv.toLp (deriv (RayleighKernel.rescale a u.continuousRep)))
      (schwartzValue φ) = ∫ x, deriv (RayleighKernel.rescale a u.continuousRep) x * φ x := by
    rw [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral]; apply integral_congr_ae
    filter_upwards [hderiv.coeFn_toLp, φ.coeFn_toLp 2 volume] with x hx hφx
    simp [schwartzValue, hx, hφx]
  have hu := u.weakDerivative_identity χ
  have hu' : (∫ x, u.continuousRep x * deriv (χ : ℝ → ℝ) x) =
      -(∫ x, deriv u.continuousRep x * χ x) := by
    rw [← u.toLp_continuousRep, ← u.toLp_deriv_continuousRep] at hu
    rw [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral] at hu
    have hleft' : (∫ x, ((ContinuousLinearMap.mul ℝ ℝ)
        (((u.continuousRep_memLp.toLp u.continuousRep : RealL2) : ℝ → ℝ) x)
        (((schwartzDeriv χ : RealL2) : ℝ → ℝ) x))) =
        ∫ x, u.continuousRep x * deriv (χ : ℝ → ℝ) x := by
      apply integral_congr_ae
      filter_upwards [u.continuousRep_memLp.coeFn_toLp,
        (SchwartzMap.derivCLM ℝ ℝ χ).coeFn_toLp 2 volume] with x hx hχx
      simp [schwartzDeriv, schwartzValue, hx, hχx]
    have hright' : (∫ x, ((ContinuousLinearMap.mul ℝ ℝ)
        (((u.deriv_continuousRep_memLp.toLp (deriv u.continuousRep) : RealL2) : ℝ → ℝ) x)
        (((schwartzValue χ : RealL2) : ℝ → ℝ) x))) =
        ∫ x, deriv u.continuousRep x * χ x := by
      apply integral_congr_ae
      filter_upwards [u.deriv_continuousRep_memLp.coeFn_toLp,
        χ.coeFn_toLp 2 volume] with x hx hχx
      simp [schwartzValue, hx, hχx]
    rw [hleft'] at hu
    have hpair : ((lpPairing volume 2 2 (ContinuousLinearMap.mul ℝ ℝ))
        (u.deriv_continuousRep_memLp.toLp (deriv u.continuousRep)))
          (schwartzValue χ) = ∫ x, deriv u.continuousRep x * χ x := by
      simpa [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral] using hright'
    rw [hpair] at hu; exact hu
  rw [hleft, hright]
  rw [u.integral_rescale_mul_schwartzDeriv ha φ,
    u.integral_deriv_rescale_mul_schwartz ha φ]
  have hleftχ : (∫ x, u.continuousRep x * deriv (φ : ℝ → ℝ) (a⁻¹ * x)) =
      ∫ x, u.continuousRep x * deriv (χ : ℝ → ℝ) x := by
    apply integral_congr_ae; filter_upwards with x; rw [hχd]
  have hrightχ : a * (∫ x, deriv u.continuousRep x * φ (a⁻¹ * x)) =
      ∫ x, deriv u.continuousRep x * χ x := by
    rw [← integral_const_mul]; apply integral_congr_ae
    filter_upwards with x; rw [hχ]; ring
  rw [hleftχ, hrightχ]; exact hu'

theorem HalfLineH1.rescale_representativeData (u : HalfLineH1) {a : ℝ} (ha : 0 < a) :
    HalfLineRepresentativeData (RayleighKernel.rescale a u.continuousRep) := by
  let hreg := u.rescale_regularity ha
  exact
    { trace_zero := hreg.trace_zero
      locally_absolutelyContinuous := hreg.locally_absolutelyContinuous
      value_memLp := hreg.value_memLp
      deriv_memLp := hreg.deriv_memLp
      value_ae_eq_zero_on_nonpositive := hreg.value_ae_eq_zero_on_nonpositive
      deriv_ae_eq_zero_on_nonpositive := hreg.deriv_ae_eq_zero_on_nonpositive
      weakDerivative_identity :=
        u.rescale_weakDerivative_identity ha hreg.value_memLp hreg.deriv_memLp }

def HalfLineH1.rescale (u : HalfLineH1) (a : ℝ) (ha : 0 < a) : HalfLineH1 :=
  HalfLineH1.ofRepresentative (RayleighKernel.rescale a u.continuousRep)
    (u.rescale_representativeData ha)

theorem HalfLineH1.continuousRep_rescale (u : HalfLineH1) {a : ℝ} (ha : 0 < a)
    {y : ℝ} (hy : y ∈ Ici 0) :
    (u.rescale a ha).continuousRep y = RayleighKernel.rescale a u.continuousRep y := by
  exact HalfLineH1.continuousRep_ofRepresentative _ _ hy

private theorem HalfLineH1.rescale_mass_integral (u : HalfLineH1) {a : ℝ} (ha : 0 < a) :
    RayleighKernel.mass (u.rescale a ha).continuousRep =
      RayleighKernel.mass (RayleighKernel.rescale a u.continuousRep) := by
  unfold RayleighKernel.mass
  apply setIntegral_congr_fun measurableSet_Ici
  intro y hy
  exact u.continuousRep_rescale ha hy

private theorem HalfLineH1.rescale_firstMoment_integral (u : HalfLineH1) {a : ℝ} (ha : 0 < a) :
    RayleighKernel.firstMoment (u.rescale a ha).continuousRep =
      RayleighKernel.firstMoment (RayleighKernel.rescale a u.continuousRep) := by
  unfold RayleighKernel.firstMoment
  apply setIntegral_congr_fun measurableSet_Ici
  intro y hy
  simp only
  rw [u.continuousRep_rescale ha hy]

theorem HalfLineH1.mass_rescale (u : HalfLineH1) {a : ℝ} (ha : 0 < a) :
    (u.rescale a ha).mass = u.mass := by
  rw [HalfLineH1.mass, HalfLineH1.mass, u.rescale_mass_integral,
    RayleighKernel.mass_rescale ha]

theorem HalfLineH1.firstMoment_rescale (u : HalfLineH1) {a : ℝ} (ha : 0 < a) :
    (u.rescale a ha).firstMoment = a⁻¹ * u.firstMoment := by
  rw [HalfLineH1.firstMoment, HalfLineH1.firstMoment, u.rescale_firstMoment_integral,
    RayleighKernel.firstMoment_rescale ha]

theorem HalfLineH1.squareEnergy_rescale (u : HalfLineH1) {a : ℝ} (ha : 0 < a) :
    (u.rescale a ha).squareEnergy = a * u.squareEnergy := by
  rw [← (u.rescale a ha).squareEnergy_continuousRep,
    ← u.squareEnergy_continuousRep]
  unfold RayleighKernel.squareEnergy
  have hfun : ∀ y ∈ Ici 0,
      (u.rescale a ha).continuousRep y ^ 2 =
        (RayleighKernel.rescale a u.continuousRep y) ^ 2 := by
    intro y hy
    rw [u.continuousRep_rescale ha hy]
  rw [show (∫ x in halfLine, (u.rescale a ha).continuousRep x ^ 2) =
      ∫ x in halfLine, (RayleighKernel.rescale a u.continuousRep x) ^ 2 by
    apply setIntegral_congr_fun measurableSet_Ici
    exact hfun]
  exact RayleighKernel.squareEnergy_rescale ha u.continuousRep

theorem HalfLineH1.dirichletEnergy_rescale (u : HalfLineH1) {a : ℝ} (ha : 0 < a) :
    (u.rescale a ha).dirichletEnergy = a ^ 3 * u.dirichletEnergy := by
  rw [← (u.rescale a ha).dirichletEnergy_continuousRep,
    ← u.dirichletEnergy_continuousRep]
  unfold RayleighKernel.dirichletEnergy
  have hderiv : ∀ᵐ x : ℝ, x ∈ Ioi 0 →
      deriv (u.rescale a ha).continuousRep x =
        deriv (RayleighKernel.rescale a u.continuousRep) x := by
    filter_upwards with x hx
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact u.continuousRep_rescale ha (show 0 ≤ y from le_of_lt hy)
  have heq : (∫ x in halfLine, deriv (u.rescale a ha).continuousRep x ^ 2) =
      ∫ x in halfLine, deriv (RayleighKernel.rescale a u.continuousRep) x ^ 2 := by
    apply setIntegral_congr_ae measurableSet_Ici
    filter_upwards [hderiv, MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with x hx hzero
    intro hmem
    have hm : 0 ≤ x := hmem
    exact congrArg (fun z : ℝ => z ^ 2) (hx (show x ∈ Ioi 0 from
      lt_of_le_of_ne hm (Ne.symm hzero)))
  rw [heq]
  exact RayleighKernel.dirichletEnergy_rescale ha u.continuousRep

theorem HalfLineH1.rayleighQuotient_rescale (u : HalfLineH1) {a : ℝ} (ha : 0 < a) :
    (u.rescale a ha).rayleighQuotient = a ^ 2 * u.rayleighQuotient := by
  rw [HalfLineH1.rayleighQuotient, HalfLineH1.rayleighQuotient,
    u.dirichletEnergy_rescale, u.squareEnergy_rescale]
  field_simp

theorem HalfLineH1.rescale_isAdmissible {L a : ℝ} (ha : 0 < a)
    {u : HalfLineH1} (hu : u.IsAdmissible L) :
    (u.rescale a ha).IsAdmissible (L / a) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [u.continuousRep_rescale ha hx]
    exact RayleighKernel.rescale_nonnegative ha.le hu.nonnegative hx
  · rw [show halfLine = Ici 0 by rfl]
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have hbase := (integrableOn_Ici_iff_integrableOn_Ioi).1 hu.integrable
    have hcomp := (integrableOn_Ioi_comp_mul_left_iff u.continuousRep 0 ha).2 (by simpa using hbase)
    rw [IntegrableOn]
    apply (hcomp.const_mul a).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [u.continuousRep_rescale ha (show 0 ≤ x from le_of_lt hx)]
    simp [RayleighKernel.rescale]
  · rw [show halfLine = Ici 0 by rfl]
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have hbase := (integrableOn_Ici_iff_integrableOn_Ioi).1 hu.firstMoment_integrable
    have hcomp := (integrableOn_Ioi_comp_mul_left_iff
      (fun x => x * u.continuousRep x) 0 ha).2 (by simpa using hbase)
    rw [IntegrableOn]
    apply hcomp.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [u.continuousRep_rescale ha (show 0 ≤ x from le_of_lt hx)]
    simp [RayleighKernel.rescale]
    ring
  · rw [HalfLineH1.mass_rescale, hu.mass_eq]
  · rw [HalfLineH1.firstMoment_rescale, hu.firstMoment_eq]
    field_simp

end RayleighKernel.Analysis
