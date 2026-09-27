import RayleighKernel.Analysis.ConvolutionLp
import RayleighKernel.Analysis.HalfLineSobolevRepresentative
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

noncomputable section
namespace RayleighKernel.Analysis

open ContinuousLinearMap MeasureTheory Set Filter
open scoped ContDiff ENNReal SchwartzMap Topology Convolution

def reflectedTranslate (ψ : ℝ → ℝ) (x : ℝ) : ℝ → ℝ := fun y => ψ (x - y)

def reflectedHomeomorph (x : ℝ) : ℝ ≃ₜ ℝ :=
  (Homeomorph.neg ℝ).trans (Homeomorph.addRight x)

theorem reflectedTranslate_eq_comp (ψ : ℝ → ℝ) (x : ℝ) :
    reflectedTranslate ψ x = ψ ∘ reflectedHomeomorph x := by
  funext y
  simp [reflectedTranslate, reflectedHomeomorph, sub_eq_add_neg, add_comm]

theorem reflectedTranslate_hasCompactSupport {ψ : ℝ → ℝ} (hψ : HasCompactSupport ψ) (x : ℝ) :
    HasCompactSupport (reflectedTranslate ψ x) := by
  rw [reflectedTranslate_eq_comp]
  exact hψ.comp_homeomorph (reflectedHomeomorph x)

theorem reflectedTranslate_contDiff {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (x : ℝ) :
    ContDiff ℝ ∞ (reflectedTranslate ψ x) := by
  change ContDiff ℝ ∞ (ψ ∘ fun y : ℝ => x-y)
  exact hψ.comp (contDiff_const.sub contDiff_id)

def reflectedSchwartz {ψ : ℝ → ℝ} (hψ : HasCompactSupport ψ)
    (hψd : ContDiff ℝ ∞ ψ) (x : ℝ) : 𝓢(ℝ, ℝ) :=
  (reflectedTranslate_hasCompactSupport hψ x).toSchwartzMap
    (reflectedTranslate_contDiff hψd x)

@[simp] theorem reflectedSchwartz_coeFn {ψ : ℝ → ℝ} (hψ : HasCompactSupport ψ)
    (hψd : ContDiff ℝ ∞ ψ) (x y : ℝ) :
    reflectedSchwartz hψ hψd x y = reflectedTranslate ψ x y := rfl

theorem reflectedTranslate_deriv {ψ : ℝ → ℝ} (hψd : ContDiff ℝ ∞ ψ) (x y : ℝ) :
    deriv (reflectedTranslate ψ x) y = -deriv ψ (x - y) := by
  have hinner : HasDerivAt (fun z : ℝ => x - z) (-1) y := by
    convert (hasDerivAt_id y).const_sub x using 1
    · simp
  have houter := (hψd.differentiable (by simp) (x - y)).hasDerivAt
  have hcomp := houter.comp y hinner
  change deriv (ψ ∘ fun z : ℝ => x - z) y = _
  simpa [Function.comp_def, mul_comm] using hcomp.deriv

theorem reflectedSchwartz_deriv_coeFn {ψ : ℝ → ℝ} (hψ : HasCompactSupport ψ)
    (hψd : ContDiff ℝ ∞ ψ) (x y : ℝ) :
    (SchwartzMap.derivCLM ℝ ℝ (reflectedSchwartz hψ hψd x)) y =
      -deriv ψ (x - y) := by
  change deriv (reflectedTranslate ψ x) y = _
  exact reflectedTranslate_deriv hψd x y

theorem reflectedSchwartz_pairing_value (ψ : ℝ → ℝ) (hψ : HasCompactSupport ψ)
    (hψd : ContDiff ℝ ∞ ψ) (u : RealL2) (x : ℝ) :
    l2Pairing u (schwartzValue (reflectedSchwartz hψ hψd x)) =
      ((u : ℝ → ℝ) ⋆[lsmul ℝ ℝ, volume] ψ) x := by
  rw [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral]
  rw [convolution_def]
  apply integral_congr_ae
  filter_upwards [(Lp.memLp u).coeFn_toLp,
    (reflectedSchwartz hψ hψd x).coeFn_toLp 2 volume] with t _ hφ
  simp [schwartzValue, hφ, reflectedSchwartz_coeFn, reflectedTranslate,
    smul_eq_mul]

theorem reflectedSchwartz_pairing_deriv (ψ : ℝ → ℝ) (hψ : HasCompactSupport ψ)
    (hψd : ContDiff ℝ ∞ ψ) (u : RealL2) (x : ℝ) :
    l2Pairing u (schwartzDeriv (reflectedSchwartz hψ hψd x)) =
      -((u : ℝ → ℝ) ⋆[lsmul ℝ ℝ, volume] deriv ψ) x := by
  rw [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral]
  have hpair :
      (∫ t, (u : ℝ → ℝ) t *
        (schwartzDeriv (reflectedSchwartz hψ hψd x)) t) =
      ∫ t, -((u : ℝ → ℝ) t * deriv ψ (x - t)) := by
    apply integral_congr_ae
    filter_upwards [(Lp.memLp u).coeFn_toLp,
      (SchwartzMap.derivCLM ℝ ℝ (reflectedSchwartz hψ hψd x)).coeFn_toLp 2 volume]
      with t hu hφ
    simp only [schwartzDeriv, schwartzValue, ContinuousLinearMap.coe_comp,
      Function.comp_apply]
    change (u : ℝ → ℝ) t *
      (((SchwartzMap.derivCLM ℝ ℝ (reflectedSchwartz hψ hψd x)).toLp 2 volume) : ℝ → ℝ) t = _
    rw [hφ]
    rw [reflectedSchwartz_deriv_coeFn hψ hψd x t]
    ring
  calc
    _ = ∫ t, -((u : ℝ → ℝ) t * deriv ψ (x - t)) := hpair
    _ = _ := by rw [integral_neg, convolution_def]; simp [smul_eq_mul]

theorem convolution_deriv_eq_of_weakDerivative_identity
    (u v : RealL2) (ψ : ℝ → ℝ) (hψ : HasCompactSupport ψ)
    (hψd : ContDiff ℝ ∞ ψ)
    (hweak : ∀ φ : 𝓢(ℝ,ℝ), l2Pairing u (schwartzDeriv φ) =
      -l2Pairing v (schwartzValue φ)) :
    u ⋆[lsmul ℝ ℝ, volume] deriv ψ = v ⋆[lsmul ℝ ℝ, volume] ψ := by
  funext x
  have h := hweak (reflectedSchwartz hψ hψd x)
  rw [reflectedSchwartz_pairing_deriv ψ hψ hψd u x,
    reflectedSchwartz_pairing_value ψ hψ hψd v x] at h
  linarith

theorem smoothFun_hasDerivAt_of_weakDerivative_identity
    (u v : RealL2) (ψ : ℝ → ℝ) (hψ : HasCompactSupport ψ)
    (hψd : ContDiff ℝ ∞ ψ) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hweak : ∀ φ : 𝓢(ℝ,ℝ), l2Pairing u (schwartzDeriv φ) =
      -l2Pairing v (schwartzValue φ)) (x : ℝ) :
    HasDerivAt (smoothFun ψ u) (smoothFun ψ v x) x := by
  have hconv := HasCompactSupport.hasDerivAt_convolution_right (L := lsmul ℝ ℝ)
    ((Lp.memLp u).locallyIntegrable (by norm_num)) hψ (hψd.of_le (by norm_num)) x
  have hu : smoothFun ψ u = (fun y => ((u : ℝ → ℝ) ⋆[lsmul ℝ ℝ, volume] ψ) y) := by
    funext y
    exact smoothFun_eq_convolution ψ hψd.continuous hψ0 u y
  rw [hu]
  rw [convolution_deriv_eq_of_weakDerivative_identity u v ψ hψ hψd hweak] at hconv
  rw [smoothFun_eq_convolution ψ hψd.continuous hψ0 v x]
  exact hconv

theorem mollifierKernel_contDiff (n : ℕ) : ContDiff ℝ ∞ (mollifierKernel n) := by
  exact (mollifierBump n).contDiff_normed

theorem mollifierKernel_hasDerivAt_of_weakDerivative_identity
    (u v : RealL2)
    (hweak : ∀ φ : 𝓢(ℝ,ℝ), l2Pairing u (schwartzDeriv φ) =
      -l2Pairing v (schwartzValue φ)) (n : ℕ) (x : ℝ) :
    HasDerivAt (smoothFun (mollifierKernel n) u)
      (smoothFun (mollifierKernel n) v x) x := by
  exact smoothFun_hasDerivAt_of_weakDerivative_identity u v (mollifierKernel n)
    (mollifierKernel_compactSupport n) (mollifierKernel_contDiff n)
    (mollifierKernel_nonneg n) hweak x

theorem mollifierKernel_deriv_smoothFun_of_weakDerivative_identity
    (u v : RealL2)
    (hweak : ∀ φ : 𝓢(ℝ,ℝ), l2Pairing u (schwartzDeriv φ) =
      -l2Pairing v (schwartzValue φ)) (n : ℕ) (x : ℝ) :
    deriv (smoothFun (mollifierKernel n) u) x =
      smoothFun (mollifierKernel n) v x :=
  (mollifierKernel_hasDerivAt_of_weakDerivative_identity u v hweak n x).deriv

def mollifierShift (n : ℕ) : ℝ := 2 * (mollifierBump n).rOut

def shiftedMollifiedFun (n : ℕ) (f : RealL2) (x : ℝ) : ℝ :=
  smoothFun (mollifierKernel n) f (x - mollifierShift n)

def shiftedMollifiedLp (n : ℕ) (f : RealL2) : RealL2 :=
  translateL2 (-(mollifierShift n))
    (smoothLp (mollifierKernel n) (mollifierKernel_continuous n)
      (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n)
      (mollifierKernel_integral n) f)

theorem mollifierShift_pos (n : ℕ) : 0 < mollifierShift n := by
  dsimp [mollifierShift]
  exact mul_pos (by norm_num) (ContDiffBump.rOut_pos (mollifierBump n))

theorem mollifierShift_tendsto_zero :
    Tendsto mollifierShift atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun n => 2 * (mollifierBump n).rOut) atTop (𝓝 (0 : ℝ))
  simpa using (tendsto_const_nhds.mul mollifierBump_rOut_tendsto)

theorem shiftedMollifiedLp_ae_eq (n : ℕ) (f : RealL2) :
    (shiftedMollifiedLp n f : ℝ → ℝ) =ᵐ[volume] shiftedMollifiedFun n f := by
  change (translateL2 (-(mollifierShift n))
      (smoothLp (mollifierKernel n) (mollifierKernel_continuous n)
        (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n)
        (mollifierKernel_integral n) f) : ℝ → ℝ) =ᵐ[volume] _
  have hxs0 := smoothLp_ae_eq (mollifierKernel n) (mollifierKernel_continuous n)
    (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n)
    (mollifierKernel_integral n) f
  have hxs' := (measurePreserving_add_right (volume : Measure ℝ)
    (-(mollifierShift n))).quasiMeasurePreserving.ae hxs0
  filter_upwards [translateL2_ae_eq (-(mollifierShift n))
      (smoothLp (mollifierKernel n) (mollifierKernel_continuous n)
        (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n)
        (mollifierKernel_integral n) f),
    hxs'] with x hx hxs
  rw [hx, hxs]
  simp [shiftedMollifiedFun, sub_eq_add_neg]

theorem shiftedMollifiedLp_tendsto (f : RealL2) :
    Tendsto (fun n => ‖shiftedMollifiedLp n f - f‖) atTop (𝓝 0) := by
  have htrans : Tendsto (fun n => translateL2 (-(mollifierShift n)) f - f)
      atTop (𝓝 0) := by
    have hzero : translateL2 (0 : ℝ) f = f := by
      apply Lp.ext
      simpa using translateL2_ae_eq 0 f
    have hc := ((continuous_translateL2 f).tendsto 0).comp
      (show Tendsto (fun n => -(mollifierShift n)) atTop (𝓝 (0 : ℝ)) by
        simpa using Filter.Tendsto.neg mollifierShift_tendsto_zero)
    have hc' : Tendsto (fun n => translateL2 (-(mollifierShift n)) f)
        atTop (𝓝 (translateL2 0 f)) := by
      exact hc.congr (fun n => rfl)
    rw [hzero] at hc'
    exact tendsto_sub_nhds_zero_iff.mpr hc'
  have hmol := mollifier_smoothLp_tendsto f
  have hfirst : Tendsto (fun n => ‖
      translateL2 (-(mollifierShift n))
        (smoothLp (mollifierKernel n) (mollifierKernel_continuous n)
          (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n)
          (mollifierKernel_integral n) f - f)‖) atTop (𝓝 0) := by
    simpa only [translateL2_norm] using hmol
  have hbound : Tendsto (fun n =>
      ‖translateL2 (-(mollifierShift n))
          (smoothLp (mollifierKernel n) (mollifierKernel_continuous n)
            (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n)
            (mollifierKernel_integral n) f - f)‖ +
        ‖translateL2 (-(mollifierShift n)) f - f‖) atTop (𝓝 0) := by
    simpa using hfirst.add htrans.norm
  have hsum : Tendsto (fun n => ‖
        translateL2 (-(mollifierShift n))
          (smoothLp (mollifierKernel n) (mollifierKernel_continuous n)
            (mollifierKernel_compactSupport n) (mollifierKernel_nonneg n)
            (mollifierKernel_integral n) f - f) +
        (translateL2 (-(mollifierShift n)) f - f)‖) atTop (𝓝 0) := by
    exact squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _))
      (Filter.Eventually.of_forall (fun n => norm_add_le _ _))
      hbound
  simpa [shiftedMollifiedLp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using hsum

theorem shiftedMollifiedFun_hasDerivAt_of_weakDerivative_identity
    (u v : RealL2)
    (hweak : ∀ φ : 𝓢(ℝ,ℝ), l2Pairing u (schwartzDeriv φ) =
      -l2Pairing v (schwartzValue φ)) (n : ℕ) (x : ℝ) :
    HasDerivAt (shiftedMollifiedFun n u) (shiftedMollifiedFun n v x) x := by
  have h := mollifierKernel_hasDerivAt_of_weakDerivative_identity u v hweak n
    (x - mollifierShift n)
  have hinner : HasDerivAt (fun z : ℝ => z - mollifierShift n) 1 x := by
    simpa using (hasDerivAt_id x).sub_const (mollifierShift n)
  change HasDerivAt (smoothFun (mollifierKernel n) u ∘
    (fun z : ℝ => z - mollifierShift n))
    (smoothFun (mollifierKernel n) v (x - mollifierShift n)) x
  simpa [one_mul] using h.comp x hinner

theorem shiftedMollifiedFun_deriv_of_weakDerivative_identity
    (u v : RealL2)
    (hweak : ∀ φ : 𝓢(ℝ,ℝ), l2Pairing u (schwartzDeriv φ) =
      -l2Pairing v (schwartzValue φ)) (n : ℕ) (x : ℝ) :
    deriv (shiftedMollifiedFun n u) x = shiftedMollifiedFun n v x :=
  (shiftedMollifiedFun_hasDerivAt_of_weakDerivative_identity u v hweak n x).deriv

theorem ae_eq_zero_of_ae_restrict_Iic_zero (u : RealL2)
    (hu0 : u =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0) :
    ∀ᵐ y ∂volume, y ≤ 0 → (u : ℝ → ℝ) y = 0 := by
  filter_upwards [(ae_restrict_iff' measurableSet_Iic).1 hu0] with y hy
  exact hy

theorem shiftedMollifiedFun_eq_zero_of_le_rOut (u : RealL2)
    (hu0 : u =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0) (n : ℕ) (x : ℝ)
    (hx : x ≤ (mollifierBump n).rOut) : shiftedMollifiedFun n u x = 0 := by
  rw [shiftedMollifiedFun, smoothFun_eq_convolution (mollifierKernel n)
    (mollifierKernel_continuous n) (mollifierKernel_nonneg n) u]
  rw [convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_eq_zero_of_ae_restrict_Iic_zero u hu0] with y hy
  by_cases hy0 : y ≤ 0
  · rw [hy hy0]
    simp
  · have hypos : 0 < y := lt_of_not_ge hy0
    have harg : (x - mollifierShift n) - y < -(mollifierBump n).rOut := by
      dsimp [mollifierShift]
      linarith
    have hnot : (x - mollifierShift n) - y ∉ tsupport (mollifierKernel n) := by
      rw [show mollifierKernel n = (mollifierBump n).normed volume by rfl,
        (mollifierBump n).tsupport_normed_eq]
      intro h
      have hdist : dist ((x - mollifierShift n) - y) 0 ≤ (mollifierBump n).rOut := by
        simpa [Metric.mem_closedBall, dist_comm] using h
      have hr : 0 < (mollifierBump n).rOut := ContDiffBump.rOut_pos _
      rw [Real.dist_eq, abs_of_neg (by linarith :
        (x - mollifierShift n) - y - 0 < 0)] at hdist
      linarith
    rw [image_eq_zero_of_notMem_tsupport hnot]
    simp

theorem shiftedMollifiedFun_tsupport_subset (u : RealL2)
    (hu0 : u =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0) (n : ℕ) :
    tsupport (shiftedMollifiedFun n u) ⊆ Ici (mollifierBump n).rOut := by
  rw [tsupport]
  apply closure_minimal
  · intro x hx
    by_contra h
    have hx' : x ≤ (mollifierBump n).rOut := le_of_not_ge h
    exact hx (shiftedMollifiedFun_eq_zero_of_le_rOut u hu0 n x hx')
  · exact isClosed_Ici

theorem shiftedMollifiedFun_tsupport_subset_Ioi_zero (u : RealL2)
    (hu0 : u =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0) (n : ℕ) :
    tsupport (shiftedMollifiedFun n u) ⊆ Ioi 0 := by
  intro x hx
  have h := shiftedMollifiedFun_tsupport_subset u hu0 n hx
  exact lt_of_lt_of_le (ContDiffBump.rOut_pos _) h

def expandingCutoff (n : ℕ) (x : ℝ) : ℝ :=
  mollifierBump 0 (((n + 1 : ℕ) : ℝ)⁻¹ * x)

theorem expandingCutoff_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (expandingCutoff n) := by
  exact (mollifierBump 0).contDiff.comp (contDiff_const.mul contDiff_id)

theorem expandingCutoff_nonneg (n : ℕ) (x : ℝ) : 0 ≤ expandingCutoff n x := by
  exact (mollifierBump 0).nonneg

theorem expandingCutoff_le_one (n : ℕ) (x : ℝ) : expandingCutoff n x ≤ 1 := by
  exact (mollifierBump 0).le_one

theorem expandingCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (expandingCutoff n) := by
  let e : ℝ ≃ₜ ℝ :=
    { toFun := fun x => ((n + 1 : ℕ) : ℝ)⁻¹ * x
      invFun := fun x => ((n + 1 : ℕ) : ℝ) * x
      left_inv := by intro x; field_simp
      right_inv := by intro x; field_simp
      continuous_toFun := (continuous_const.mul continuous_id)
      continuous_invFun := (continuous_const.mul continuous_id) }
  change HasCompactSupport ((mollifierBump 0) ∘ e)
  exact (mollifierBump 0).hasCompactSupport.comp_homeomorph e

theorem expandingCutoff_mul_memLp (n : ℕ) (f : RealL2) :
    MemLp (fun x => expandingCutoff n x * (f : ℝ → ℝ) x) 2 volume := by
  have hmeas : AEStronglyMeasurable
      (fun x => expandingCutoff n x * (f : ℝ → ℝ) x) volume :=
    (expandingCutoff_contDiff n).continuous.aestronglyMeasurable.mul
      (Lp.memLp f).aestronglyMeasurable
  apply MemLp.of_le_mul (Lp.memLp f) hmeas
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul]
  rw [abs_of_nonneg (expandingCutoff_nonneg n x)]
  exact mul_le_mul_of_nonneg_right (expandingCutoff_le_one n x) (abs_nonneg _)

def expandingCutoffLp (n : ℕ) (f : RealL2) : RealL2 :=
  (expandingCutoff_mul_memLp n f).toLp
    (fun x => expandingCutoff n x * (f : ℝ → ℝ) x)

theorem expandingCutoffLp_ae_eq (n : ℕ) (f : RealL2) :
    (expandingCutoffLp n f : ℝ → ℝ) =ᵐ[volume]
      fun x => expandingCutoff n x * (f : ℝ → ℝ) x := by
  exact MemLp.coeFn_toLp _

theorem expandingCutoffLp_sub_ae_eq (n : ℕ) (f g : RealL2) :
    (expandingCutoffLp n f - expandingCutoffLp n g : ℝ → ℝ) =ᵐ[volume]
      fun x => expandingCutoff n x * ((f - g : RealL2) : ℝ → ℝ) x := by
  filter_upwards [Lp.coeFn_sub (expandingCutoffLp n f) (expandingCutoffLp n g),
    expandingCutoffLp_ae_eq n f, expandingCutoffLp_ae_eq n g,
    Lp.coeFn_sub f g] with x hx hf hg hfg
  calc
    (expandingCutoffLp n f - expandingCutoffLp n g : ℝ → ℝ) x =
        ((expandingCutoffLp n f : ℝ → ℝ) x -
          (expandingCutoffLp n g : ℝ → ℝ) x) := by
      rfl
    _ = expandingCutoff n x * ((f : ℝ → ℝ) x - (g : ℝ → ℝ) x) := by
      rw [hf, hg]
      ring
    _ = expandingCutoff n x * ((f - g : RealL2) : ℝ → ℝ) x := by
      exact congrArg (fun z => expandingCutoff n x * z) hfg.symm

theorem expandingCutoffLp_contraction (n : ℕ) (f g : RealL2) :
    ‖expandingCutoffLp n f - expandingCutoffLp n g‖ ≤ ‖f - g‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (expandingCutoffLp n f) (expandingCutoffLp n g),
    expandingCutoffLp_sub_ae_eq n f g] with x hx hprod
  rw [show (expandingCutoffLp n f - expandingCutoffLp n g : RealL2) x =
      expandingCutoff n x * ((f - g : RealL2) : ℝ → ℝ) x by
        exact hx.trans hprod, Real.norm_eq_abs, abs_mul]
  rw [abs_of_nonneg (expandingCutoff_nonneg n x)]
  change expandingCutoff n x * |((f - g : RealL2) : ℝ → ℝ) x| ≤
    |((f - g : RealL2) : ℝ → ℝ) x|
  simpa using mul_le_mul_of_nonneg_right (expandingCutoff_le_one n x)
    (abs_nonneg (((f - g : RealL2) : ℝ → ℝ) x))

theorem expandingCutoff_tendsto_one (x : ℝ) :
    Tendsto (fun n => expandingCutoff n x) atTop (𝓝 1) := by
  have hscale : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹ * x)
      atTop (𝓝 0) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm]
      using ((tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) x).comp
        (tendsto_add_atTop_nat 1))
  refine (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr' ?_
  filter_upwards [hscale.eventually (Metric.closedBall_mem_nhds (0 : ℝ)
    (ContDiffBump.rIn_pos (mollifierBump 0)))]
    with n hn
  rw [expandingCutoff]
  symm
  exact (mollifierBump 0).one_of_mem_closedBall hn

theorem expandingCutoffLp_tendsto (f : RealL2) :
    Tendsto (fun n => ‖expandingCutoffLp n f - f‖) atTop (𝓝 0) := by
  have hdiff (n : ℕ) :
      ((expandingCutoffLp n f - f : RealL2) : ℝ → ℝ) =ᵐ[volume]
        fun x => (expandingCutoff n x - 1) * (f : ℝ → ℝ) x := by
    filter_upwards [Lp.coeFn_sub (expandingCutoffLp n f) f,
      expandingCutoffLp_ae_eq n f] with x hx hχ
    rw [show (expandingCutoffLp n f - f : RealL2) x =
      (expandingCutoffLp n f : ℝ → ℝ) x - (f : ℝ → ℝ) x by simpa using hx, hχ]
    ring
  have hnorm (n : ℕ) :
      ‖expandingCutoffLp n f - f‖ ^ 2 =
        ∫ x, ((expandingCutoff n x - 1) * (f : ℝ → ℝ) x) ^ 2 := by
    have h := norm_sq_eq_re_inner (𝕜 := ℝ) (expandingCutoffLp n f - f)
    rw [h, MeasureTheory.L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
    simp only [RCLike.re_to_real]
    have hi : (∫ x, ‖((expandingCutoffLp n f - f : RealL2) : ℝ → ℝ) x‖ ^ 2 ∂volume) =
        ∫ x, ((expandingCutoff n x - 1) * (f : ℝ → ℝ) x) ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [hdiff n] with x hx
      rw [hx]
      simp only [Real.norm_eq_abs, abs_mul]
      rw [← abs_mul, sq_abs]
    rw [hi]
  have hsq : Tendsto (fun n => ‖expandingCutoffLp n f - f‖ ^ 2)
      atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∫ x : ℝ, (0 : ℝ) ∂volume by simp]
    have hlim := tendsto_integral_of_dominated_convergence
      (fun x => ((f : ℝ → ℝ) x) ^ 2)
      (fun n => by
        have hm : AEStronglyMeasurable (fun x =>
            ((expandingCutoff n x - 1) * (f : ℝ → ℝ) x) ^ 2) volume := by
          exact (((expandingCutoff_contDiff n).continuous.aestronglyMeasurable.sub
            (measurable_const.aestronglyMeasurable)).mul
              (Lp.memLp f).aestronglyMeasurable).pow 2
        exact hm)
      (Lp.memLp f).integrable_sq
      (fun n => by
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_pow, abs_mul]
        have hχ : |expandingCutoff n x - 1| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [expandingCutoff_nonneg n x,
            expandingCutoff_le_one n x]
        calc
          (|expandingCutoff n x - 1| * |(f : ℝ → ℝ) x|) ^ 2 ≤
              (1 * |(f : ℝ → ℝ) x|) ^ 2 :=
            (sq_le_sq₀ (by positivity) (by positivity)).2
              (mul_le_mul_of_nonneg_right hχ (abs_nonneg _))
          _ = ((f : ℝ → ℝ) x) ^ 2 := by rw [one_mul, sq_abs])
      (Filter.Eventually.of_forall (fun x =>
        (expandingCutoff_tendsto_one x).sub tendsto_const_nhds |>.mul
          tendsto_const_nhds |>.pow 2))
    simpa [sub_self] using hlim.congr (fun n => (hnorm n).symm)
  have hnorm_nonneg : ∀ n, 0 ≤ ‖expandingCutoffLp n f - f‖ := fun n => norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  rcases (eventually_atTop.1 (hsq.eventually (gt_mem_nhds hεsq))) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (hnorm_nonneg n)]
  exact (sq_lt_sq₀ (hnorm_nonneg n) hε.le).mp (hN n hn)

theorem expandingCutoff_deriv (n : ℕ) (x : ℝ) :
    deriv (expandingCutoff n) x = ((n + 1 : ℕ) : ℝ)⁻¹ *
      deriv (mollifierBump 0 : ℝ → ℝ) (((n + 1 : ℕ) : ℝ)⁻¹ * x) := by
  have hinner : HasDerivAt (fun y : ℝ => ((n + 1 : ℕ) : ℝ)⁻¹ * y)
      (((n + 1 : ℕ) : ℝ)⁻¹) x := by
    simpa using (hasDerivAt_id x).const_mul (((n + 1 : ℕ) : ℝ)⁻¹)
  have houter : HasDerivAt (mollifierBump 0 : ℝ → ℝ)
      (deriv (mollifierBump 0 : ℝ → ℝ) (((n + 1 : ℕ) : ℝ)⁻¹ * x))
      (((n + 1 : ℕ) : ℝ)⁻¹ * x) :=
    have hd := ((mollifierBump 0).contDiff (n := ⊤)).differentiable
      (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
      (((n + 1 : ℕ) : ℝ)⁻¹ * x)
    hd.hasDerivAt
  have hcomp := houter.comp x hinner
  change deriv (fun y : ℝ => (mollifierBump 0)
    (((n + 1 : ℕ) : ℝ)⁻¹ * y)) x = _
  simpa [Function.comp_def, mul_comm] using hcomp.deriv

theorem mollifierBump_zero_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖deriv (mollifierBump 0 : ℝ → ℝ) x‖ ≤ C := by
  have hcont : Continuous (deriv (mollifierBump 0 : ℝ → ℝ)) :=
    have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (mollifierBump 0 : ℝ → ℝ) :=
      (mollifierBump 0).contDiff (n := ⊤)
    hsmooth.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := ((mollifierBump 0).hasCompactSupport.deriv).exists_bound_of_continuous hcont
  refine ⟨C, le_trans (norm_nonneg (deriv (mollifierBump 0 : ℝ → ℝ) 0)) (hC 0), hC⟩

theorem expandingCutoff_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
      ‖deriv (expandingCutoff n) x‖ ≤ C * (((n + 1 : ℕ) : ℝ)⁻¹) := by
  obtain ⟨C, hC0, hC⟩ := mollifierBump_zero_deriv_bound
  refine ⟨C, hC0, ?_⟩
  intro n x
  rw [expandingCutoff_deriv]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  calc
    ((n + 1 : ℕ) : ℝ)⁻¹ * ‖deriv (mollifierBump 0 : ℝ → ℝ)
        (((n + 1 : ℕ) : ℝ)⁻¹ * x)‖ ≤
        ((n + 1 : ℕ) : ℝ)⁻¹ * C :=
      mul_le_mul_of_nonneg_left (hC _) (inv_nonneg.mpr (by positivity))
    _ = C * ((n + 1 : ℕ) : ℝ)⁻¹ := by ring

theorem expandingCutoff_deriv_mul_memLp (n : ℕ) (f : RealL2) :
    MemLp (fun x => deriv (expandingCutoff n) x * (f : ℝ → ℝ) x) 2 volume := by
  obtain ⟨C, hC0, hC⟩ := expandingCutoff_deriv_bound
  have hmeas : AEStronglyMeasurable
      (fun x => deriv (expandingCutoff n) x * (f : ℝ → ℝ) x) volume :=
    ((expandingCutoff_contDiff n).continuous_deriv (by norm_num)).aestronglyMeasurable.mul
      (Lp.memLp f).aestronglyMeasurable
  apply MemLp.of_le_mul (Lp.memLp f) hmeas
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |deriv (expandingCutoff n) x| * |(f : ℝ → ℝ) x| ≤
        (C * (((n + 1 : ℕ) : ℝ)⁻¹)) * |(f : ℝ → ℝ) x| :=
      (by simpa [Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (hC n x) (abs_nonneg _))
    _ = C * (((n + 1 : ℕ) : ℝ)⁻¹) * |(f : ℝ → ℝ) x| := by ring

def expandingCutoffDerivMulLp (n : ℕ) (f : RealL2) : RealL2 :=
  (expandingCutoff_deriv_mul_memLp n f).toLp
    (fun x => deriv (expandingCutoff n) x * (f : ℝ → ℝ) x)

theorem expandingCutoffDerivMulLp_ae_eq (n : ℕ) (f : RealL2) :
    (expandingCutoffDerivMulLp n f : ℝ → ℝ) =ᵐ[volume]
      fun x => deriv (expandingCutoff n) x * (f : ℝ → ℝ) x := by
  exact MemLp.coeFn_toLp _

theorem expandingCutoffDerivMulLp_norm_tendsto (f : RealL2) :
    Tendsto (fun n => ‖expandingCutoffDerivMulLp n (shiftedMollifiedLp n f)‖)
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := expandingCutoff_deriv_bound
  have hscale : Tendsto (fun n : ℕ => C * (((n + 1 : ℕ) : ℝ)⁻¹))
      atTop (𝓝 0) := by
    have ht := (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) C).comp
      (tendsto_add_atTop_nat 1)
    refine ht.congr' ?_
    filter_upwards with n
    simp [div_eq_mul_inv, Nat.cast_add, Nat.cast_one]
  have hnorm : Tendsto (fun n => ‖shiftedMollifiedLp n f‖) atTop (𝓝 ‖f‖) := by
    exact tendsto_norm.comp ((tendsto_iff_norm_sub_tendsto_zero).mpr
      (shiftedMollifiedLp_tendsto f))
  have hev : ∀ᶠ n in atTop, ‖shiftedMollifiedLp n f‖ ≤ ‖f‖ + 1 := by
    filter_upwards [hnorm.eventually (gt_mem_nhds (by linarith : ‖f‖ + 1 > ‖f‖))]
    intro n hn
    linarith
  have hbound : ∀ n, ‖expandingCutoffDerivMulLp n (shiftedMollifiedLp n f)‖ ≤
      (C * (((n + 1 : ℕ) : ℝ)⁻¹)) * ‖shiftedMollifiedLp n f‖ := by
    intro n
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [expandingCutoffDerivMulLp_ae_eq n (shiftedMollifiedLp n f),
      (Lp.memLp (shiftedMollifiedLp n f)).coeFn_toLp] with x hx hf
    rw [hx, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_right (hC n x) (abs_nonneg _)).trans_eq
      (by rw [Real.norm_eq_abs])
  have hupper : Tendsto (fun n =>
      (C * (((n + 1 : ℕ) : ℝ)⁻¹)) * (‖f‖ + 1)) atTop (𝓝 0) := by
    simpa using hscale.mul_const (‖f‖ + 1)
  refine squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) ?_ hupper
  · filter_upwards [hev] with n hn
    exact (hbound n).trans (mul_le_mul_of_nonneg_left hn (by positivity))

theorem shiftedMollifiedFun_contDiff (n : ℕ) (f : RealL2) :
    ContDiff ℝ ∞ (shiftedMollifiedFun n f) := by
  have hc := (mollifierKernel_compactSupport n).contDiff_convolution_right
    (L := lsmul ℝ ℝ) ((Lp.memLp f).locallyIntegrable (by norm_num))
    (mollifierKernel_contDiff n)
  rw [show shiftedMollifiedFun n f =
      (fun x : ℝ => ((f : ℝ → ℝ) ⋆[lsmul ℝ ℝ, volume] mollifierKernel n) x) ∘
        (fun x : ℝ => x - mollifierShift n) by
      funext x
      simp [shiftedMollifiedFun, smoothFun_eq_convolution, mollifierKernel_continuous,
        mollifierKernel_nonneg]]
  exact hc.comp (contDiff_id.sub contDiff_const)

def cutoffMollifiedFun (n : ℕ) (f : RealL2) (x : ℝ) : ℝ :=
  expandingCutoff n x * shiftedMollifiedFun n f x

theorem cutoffMollifiedFun_contDiff (n : ℕ) (f : RealL2) :
    ContDiff ℝ ∞ (cutoffMollifiedFun n f) := by
  exact (expandingCutoff_contDiff n).mul (shiftedMollifiedFun_contDiff n f)

theorem cutoffMollifiedFun_hasCompactSupport (n : ℕ) (f : RealL2) :
    HasCompactSupport (cutoffMollifiedFun n f) := by
  exact (expandingCutoff_hasCompactSupport n).mul_right

def cutoffMollifiedSchwartz (n : ℕ) (f : RealL2) : 𝓢(ℝ, ℝ) :=
  (cutoffMollifiedFun_hasCompactSupport n f).toSchwartzMap
    (cutoffMollifiedFun_contDiff n f)

def cutoffMollifiedPositiveTest (n : ℕ) (u : RealL2)
    (hu0 : u =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0) : PositiveTestFunction :=
  ⟨cutoffMollifiedSchwartz n u, by
    exact tsupport_mul_subset_right.trans (shiftedMollifiedFun_tsupport_subset_Ioi_zero u hu0 n)⟩

theorem cutoffMollifiedPositiveTest_value (n : ℕ) (u : RealL2)
    (hu0 : u =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0) :
    positiveTestValue (cutoffMollifiedPositiveTest n u hu0) =
      expandingCutoffLp n (shiftedMollifiedLp n u) := by
  apply Lp.ext
  filter_upwards [(cutoffMollifiedSchwartz n u).coeFn_toLp 2 volume,
    expandingCutoffLp_ae_eq n (shiftedMollifiedLp n u), shiftedMollifiedLp_ae_eq n u]
    with x hφ hcut hshift
  change (((cutoffMollifiedSchwartz n u).toLp 2 volume : RealL2) : ℝ → ℝ) x = _
  rw [hφ, hcut, hshift]
  rfl

theorem cutoffMollifiedFun_deriv_of_weakDerivative_identity
    (u v : RealL2)
    (hweak : ∀ φ : 𝓢(ℝ,ℝ), l2Pairing u (schwartzDeriv φ) =
      -l2Pairing v (schwartzValue φ)) (n : ℕ) (x : ℝ) :
    deriv (cutoffMollifiedFun n u) x =
      deriv (expandingCutoff n) x * shiftedMollifiedFun n u x +
        expandingCutoff n x * shiftedMollifiedFun n v x := by
  exact (((expandingCutoff_contDiff n).differentiable (by norm_num) x).hasDerivAt.mul
    (shiftedMollifiedFun_hasDerivAt_of_weakDerivative_identity u v hweak n x)).deriv

theorem cutoffMollifiedPositiveTest_deriv (u v : RealL2)
    (hweak : ∀ φ : 𝓢(ℝ,ℝ), l2Pairing u (schwartzDeriv φ) =
      -l2Pairing v (schwartzValue φ)) (n : ℕ)
    (hu0 : u =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0) :
    positiveTestDeriv (cutoffMollifiedPositiveTest n u hu0) =
      expandingCutoffDerivMulLp n (shiftedMollifiedLp n u) +
        expandingCutoffLp n (shiftedMollifiedLp n v) := by
  apply Lp.ext
  filter_upwards [
    (SchwartzMap.derivCLM ℝ ℝ (cutoffMollifiedSchwartz n u)).coeFn_toLp 2 volume,
    Lp.coeFn_add (expandingCutoffDerivMulLp n (shiftedMollifiedLp n u))
      (expandingCutoffLp n (shiftedMollifiedLp n v)),
    expandingCutoffDerivMulLp_ae_eq n (shiftedMollifiedLp n u),
    expandingCutoffLp_ae_eq n (shiftedMollifiedLp n v),
    shiftedMollifiedLp_ae_eq n u, shiftedMollifiedLp_ae_eq n v]
      with x hder hadd hdu hdv hsu hsv
  change ((((SchwartzMap.derivCLM ℝ ℝ (cutoffMollifiedSchwartz n u)).toLp 2 volume :
    RealL2) : ℝ → ℝ) x) = _
  rw [hder, hadd]
  change deriv (cutoffMollifiedFun n u) x = _
  rw [cutoffMollifiedFun_deriv_of_weakDerivative_identity u v hweak n x]
  change _ = ((expandingCutoffDerivMulLp n (shiftedMollifiedLp n u) : RealL2) :
      ℝ → ℝ) x + ((expandingCutoffLp n (shiftedMollifiedLp n v) : RealL2) : ℝ → ℝ) x
  rw [hdu, hdv, hsu, hsv]

theorem expandingCutoffLp_shiftedMollifiedLp_tendsto (f : RealL2) :
    Tendsto (fun n => expandingCutoffLp n (shiftedMollifiedLp n f)) atTop (𝓝 f) := by
  have hshift : Tendsto (fun n => shiftedMollifiedLp n f) atTop (𝓝 f) :=
    (tendsto_iff_norm_sub_tendsto_zero).2 (shiftedMollifiedLp_tendsto f)
  have hshift0 : Tendsto (fun n => ‖shiftedMollifiedLp n f - f‖) atTop (𝓝 0) :=
    shiftedMollifiedLp_tendsto f
  have hcontract : ∀ n, ‖expandingCutoffLp n (shiftedMollifiedLp n f) -
      expandingCutoffLp n f‖ ≤ ‖shiftedMollifiedLp n f - f‖ := by
    intro n
    exact expandingCutoffLp_contraction n _ _
  have hfirst : Tendsto (fun n => ‖expandingCutoffLp n (shiftedMollifiedLp n f) -
      expandingCutoffLp n f‖) atTop (𝓝 0) := by
    exact squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _))
      (Filter.Eventually.of_forall hcontract) hshift0
  have hsecond : Tendsto (fun n => ‖expandingCutoffLp n f - f‖) atTop (𝓝 0) :=
    expandingCutoffLp_tendsto f
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  let upper : ℕ → ℝ := fun n =>
    ‖expandingCutoffLp n (shiftedMollifiedLp n f) - expandingCutoffLp n f‖ +
      ‖expandingCutoffLp n f - f‖
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using (hfirst.add hsecond)
  refine squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) ?_ hupper
  filter_upwards with n
  dsimp [upper]
  calc
    ‖expandingCutoffLp n (shiftedMollifiedLp n f) - f‖ =
        ‖(expandingCutoffLp n (shiftedMollifiedLp n f) - expandingCutoffLp n f) +
        (expandingCutoffLp n f - f)‖ := by
          congr 1
          abel
    _ ≤ _ := norm_add_le _ _

theorem cutoffMollifiedPositiveTest_value_tendsto (u : RealL2)
    (hu0 : u =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0) :
    Tendsto (fun n => positiveTestValue (cutoffMollifiedPositiveTest n u hu0))
      atTop (𝓝 u) := by
  rw [show (fun n => positiveTestValue (cutoffMollifiedPositiveTest n u hu0)) =
      (fun n => expandingCutoffLp n (shiftedMollifiedLp n u)) by
        funext n; exact cutoffMollifiedPositiveTest_value n u hu0]
  exact expandingCutoffLp_shiftedMollifiedLp_tendsto u

theorem cutoffMollifiedPositiveTest_deriv_tendsto (u v : RealL2)
    (hweak : ∀ φ : 𝓢(ℝ,ℝ), l2Pairing u (schwartzDeriv φ) =
      -l2Pairing v (schwartzValue φ))
    (hu0 : u =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0) :
    Tendsto (fun n => positiveTestDeriv (cutoffMollifiedPositiveTest n u hu0))
      atTop (𝓝 v) := by
  rw [show (fun n => positiveTestDeriv (cutoffMollifiedPositiveTest n u hu0)) =
      (fun n => expandingCutoffDerivMulLp n (shiftedMollifiedLp n u) +
        expandingCutoffLp n (shiftedMollifiedLp n v)) by
        funext n; exact cutoffMollifiedPositiveTest_deriv u v hweak n hu0]
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  have hdu : Tendsto (fun n => ‖expandingCutoffDerivMulLp n
      (shiftedMollifiedLp n u)‖) atTop (𝓝 0) :=
    expandingCutoffDerivMulLp_norm_tendsto u
  have hdv : Tendsto (fun n => ‖expandingCutoffLp n (shiftedMollifiedLp n v) - v‖)
      atTop (𝓝 0) := by
    exact (tendsto_iff_norm_sub_tendsto_zero).1
      (expandingCutoffLp_shiftedMollifiedLp_tendsto v)
  let upper : ℕ → ℝ := fun n =>
    ‖expandingCutoffDerivMulLp n (shiftedMollifiedLp n u)‖ +
      ‖expandingCutoffLp n (shiftedMollifiedLp n v) - v‖
  have hupp : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using hdu.add hdv
  refine squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) ?_ hupp
  filter_upwards with n
  dsimp [upper]
  calc
    ‖expandingCutoffDerivMulLp n (shiftedMollifiedLp n u) +
        expandingCutoffLp n (shiftedMollifiedLp n v) - v‖ =
      ‖expandingCutoffDerivMulLp n (shiftedMollifiedLp n u) +
        (expandingCutoffLp n (shiftedMollifiedLp n v) - v)‖ := by
          congr 1
          abel
    _ ≤ _ := norm_add_le _ _

theorem cutoffMollifiedPositiveTest_graph_tendsto (u v : RealL2)
    (hweak : ∀ φ : 𝓢(ℝ,ℝ), l2Pairing u (schwartzDeriv φ) =
      -l2Pairing v (schwartzValue φ))
    (hu0 : u =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0) :
    Tendsto (fun n => positiveTestGraph (cutoffMollifiedPositiveTest n u hu0)) atTop
      (𝓝 ((WithLp.prodContinuousLinearEquiv 2 ℝ RealL2 RealL2).symm (u, v))) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ RealL2 RealL2
  have hp : Tendsto (fun n =>
      (positiveTestValue (cutoffMollifiedPositiveTest n u hu0),
        positiveTestDeriv (cutoffMollifiedPositiveTest n u hu0))) atTop (𝓝 (u, v)) := by
    exact (cutoffMollifiedPositiveTest_value_tendsto u hu0).prodMk_nhds
      (cutoffMollifiedPositiveTest_deriv_tendsto u v hweak hu0)
  have he : Continuous e.symm := e.symm.continuous
  have := he.continuousAt.tendsto.comp hp
  change Tendsto (fun n => e.symm
    (positiveTestValue (cutoffMollifiedPositiveTest n u hu0),
      positiveTestDeriv (cutoffMollifiedPositiveTest n u hu0))) atTop (𝓝 (e.symm (u, v)))
  exact this

theorem graph_mem_halfLineH1Submodule_of_weakDerivative_core
    (u v : RealL2)
    (hu0 : u =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0)
    (hweak : ∀ φ : 𝓢(ℝ,ℝ), l2Pairing u (schwartzDeriv φ) =
      -l2Pairing v (schwartzValue φ)) :
    (WithLp.prodContinuousLinearEquiv 2 ℝ RealL2 RealL2).symm (u, v) ∈
      halfLineH1Submodule := by
  apply (Submodule.isClosed_topologicalClosure (LinearMap.range positiveTestGraph)).mem_of_tendsto
    (cutoffMollifiedPositiveTest_graph_tendsto u v hweak hu0)
  filter_upwards with n
  exact Submodule.le_topologicalClosure (LinearMap.range positiveTestGraph)
    ⟨cutoffMollifiedPositiveTest n u hu0, rfl⟩

theorem graph_mem_halfLineH1Submodule_of_weakDerivative
    (u v : RealL2)
    (hu0 : u =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0)
    (_hv0 : v =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0)
    (hweak : ∀ φ : 𝓢(ℝ,ℝ), l2Pairing u (schwartzDeriv φ) =
      -l2Pairing v (schwartzValue φ)) :
    (WithLp.prodContinuousLinearEquiv 2 ℝ RealL2 RealL2).symm (u, v) ∈
      halfLineH1Submodule :=
  graph_mem_halfLineH1Submodule_of_weakDerivative_core u v hu0 hweak

/-- The representative-level data needed to construct a half-line Sobolev function. -/
structure HalfLineRepresentativeData (f : ℝ → ℝ) : Prop where
  trace_zero : f 0 = 0
  locally_absolutelyContinuous : ∀ R, 0 < R → AbsolutelyContinuousOnInterval f 0 R
  value_memLp : MemLp f 2 volume
  deriv_memLp : MemLp (deriv f) 2 volume
  value_ae_eq_zero_on_nonpositive :
    f =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0
  deriv_ae_eq_zero_on_nonpositive :
    deriv f =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0
  weakDerivative_identity : ∀ φ : 𝓢(ℝ,ℝ),
    l2Pairing (value_memLp.toLp f) (schwartzDeriv φ) =
      -l2Pairing (deriv_memLp.toLp (deriv f)) (schwartzValue φ)

/-- The intrinsic half-line Sobolev element represented by `f`. -/
def HalfLineH1.ofRepresentative (f : ℝ → ℝ) (h : HalfLineRepresentativeData f) : HalfLineH1 :=
  ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ RealL2 RealL2).symm
      (h.value_memLp.toLp f, h.deriv_memLp.toLp (deriv f)),
    graph_mem_halfLineH1Submodule_of_weakDerivative
      (h.value_memLp.toLp f) (h.deriv_memLp.toLp (deriv f))
      (by
        filter_upwards [h.value_memLp.coeFn_toLp.filter_mono ae_restrict_le,
          h.value_ae_eq_zero_on_nonpositive] with x hx hzero
        rw [hx, hzero])
      (by
        filter_upwards [h.deriv_memLp.coeFn_toLp.filter_mono ae_restrict_le,
          h.deriv_ae_eq_zero_on_nonpositive] with x hx hzero
        rw [hx, hzero])
      h.weakDerivative_identity⟩

@[simp] theorem HalfLineH1.value_ofRepresentative (f : ℝ → ℝ)
    (h : HalfLineRepresentativeData f) :
    (HalfLineH1.ofRepresentative f h).value = h.value_memLp.toLp f := rfl

@[simp] theorem HalfLineH1.weakDeriv_ofRepresentative (f : ℝ → ℝ)
    (h : HalfLineRepresentativeData f) :
    (HalfLineH1.ofRepresentative f h).weakDeriv = h.deriv_memLp.toLp (deriv f) := rfl

theorem HalfLineH1.value_ofRepresentative_ae_eq (f : ℝ → ℝ)
    (h : HalfLineRepresentativeData f) :
    ((HalfLineH1.ofRepresentative f h).value : ℝ → ℝ) =ᵐ[volume] f := by
  rw [HalfLineH1.value_ofRepresentative]
  exact h.value_memLp.coeFn_toLp

theorem HalfLineH1.weakDeriv_ofRepresentative_ae_eq (f : ℝ → ℝ)
    (h : HalfLineRepresentativeData f) :
    ((HalfLineH1.ofRepresentative f h).weakDeriv : ℝ → ℝ) =ᵐ[volume] deriv f := by
  rw [HalfLineH1.weakDeriv_ofRepresentative]
  exact h.deriv_memLp.coeFn_toLp

theorem HalfLineH1.continuousRep_ofRepresentative (f : ℝ → ℝ)
    (h : HalfLineRepresentativeData f) {x : ℝ} (hx : x ∈ Ici 0) :
    (HalfLineH1.ofRepresentative f h).continuousRep x = f x := by
  symm
  apply HalfLineH1.eqOn_continuousRep_of_trace_deriv
    (HalfLineH1.ofRepresentative f h)
  · exact h.trace_zero
  · exact h.locally_absolutelyContinuous
  · filter_upwards [HalfLineH1.weakDeriv_ofRepresentative_ae_eq f h |>.filter_mono
      ae_restrict_le] with y hy
    rw [hy]
  · exact hx

theorem HalfLineH1.ofRepresentative_eq_of_ae_eq {f g : ℝ → ℝ}
    (hf : HalfLineRepresentativeData f) (hg : HalfLineRepresentativeData g)
    (hfg : f =ᵐ[volume] g) : HalfLineH1.ofRepresentative f hf =
      HalfLineH1.ofRepresentative g hg := by
  apply HalfLineH1.ext_value
  apply Lp.ext
  filter_upwards [HalfLineH1.value_ofRepresentative_ae_eq f hf,
    HalfLineH1.value_ofRepresentative_ae_eq g hg, hfg] with x hfx hgx hfgx
  exact hfx.trans (hfgx.trans hgx.symm)

end RayleighKernel.Analysis
