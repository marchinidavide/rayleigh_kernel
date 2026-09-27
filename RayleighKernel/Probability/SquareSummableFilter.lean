import RayleighKernel.Probability.FiniteLinearFilter
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Subspace

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ProbabilityTheory Topology
namespace RayleighKernel.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {r : ℤ → Ω → ℝ}

def coordinateLp (hr : IsWhiteInput r μ) (s : ℤ) : Lp ℝ 2 μ :=
  (hr.memLp s).toLp (r s)

theorem inner_toLp_mul {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  have hfg : (fun ω => (hg.toLp g : Ω → ℝ) ω * (hf.toLp f : Ω → ℝ) ω) =ᵐ[μ]
      (fun ω => f ω * g ω) := by
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hωf hωg
    simp [hωf, hωg, mul_comm]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [integral_congr_ae hfg]

theorem coordinateLp_orthonormal (hr : IsWhiteInput r μ) (t : ℤ) :
    Orthonormal ℝ (fun j : ℕ => coordinateLp hr (t - (j : ℤ))) := by
  rw [orthonormal_iff_ite]
  intro j k
  change inner ℝ ((hr.memLp (t - (j : ℤ))).toLp (r (t - (j : ℤ))))
      ((hr.memLp (t - (k : ℤ))).toLp (r (t - (k : ℤ)))) = _
  rw [inner_toLp_mul (hr.memLp _) (hr.memLp _)]
  by_cases h : j = k
  · subst k
    simpa [coordinateLp] using hr.secondMoment (t - (j : ℤ)) (t - (j : ℤ))
  · have h' : t - (j : ℤ) ≠ t - (k : ℤ) := by omega
    simpa [h, h'] using hr.secondMoment (t - (j : ℤ)) (t - (k : ℤ))

theorem weightedCoordinate_summable (hr : IsWhiteInput r μ) (w : Discrete.Kernel) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2)) :
    Summable (fun j => (w j) • coordinateLp hr (t - (j : ℤ))) := by
  exact (((coordinateLp_orthonormal hr t).orthogonalFamily).summable_iff_norm_sq_summable
    (fun j => w j)).mpr (by simpa using hw)

def partialSum (hr : IsWhiteInput r μ) (w : Discrete.Kernel) (t : ℤ) (N : ℕ) : Lp ℝ 2 μ :=
  ∑ j ∈ Finset.range N, (w j) • coordinateLp hr (t - (j : ℤ))

def infiniteSignalLp (hr : IsWhiteInput r μ) (w : Discrete.Kernel) (t : ℤ) : Lp ℝ 2 μ :=
  ∑' j, (w j) • coordinateLp hr (t - (j : ℤ))

theorem finiteSignal_toLp_eq_sum (hr : IsWhiteInput r μ)
    (N : ℕ) (w : Discrete.Kernel) (t : ℤ) :
    (finiteSignal_memLp (N := N) (w := w) (r := r) (μ := μ) hr t).toLp
        (finiteSignal N w r t) = partialSum hr w t N := by
  unfold partialSum
  apply Lp.ext
  have hleft := MemLp.coeFn_toLp
    (finiteSignal_memLp (N := N) (w := w) (r := r) (μ := μ) hr t)
  have hright := Lp.coeFn_finsetSum (Finset.range N)
    (fun j => (w j) • coordinateLp hr (t - (j : ℤ)))
  have hterm : ∀ j : ℕ, ((w j) • coordinateLp hr (t - (j : ℤ)) : Lp ℝ 2 μ) =ᵐ[μ]
      (fun ω => w j * r (t - (j : ℤ)) ω) := by
    intro j
    filter_upwards [Lp.coeFn_smul (w j) (coordinateLp hr (t - (j : ℤ))),
      MemLp.coeFn_toLp (hr.memLp (t - (j : ℤ)))] with ω h₁ h₂
    rw [h₁]
    change w j * (coordinateLp hr (t - (j : ℤ)) : Ω → ℝ) ω = _
    rw [show (coordinateLp hr (t - (j : ℤ)) : Ω → ℝ) ω =
      r (t - (j : ℤ)) ω by exact h₂]
  have hsum := eventuallyEq_sum (s := Finset.range N) (fun j hj => hterm j)
  filter_upwards [hleft, hright, hsum] with ω h₁ h₂ h₃
  calc
    _ = finiteSignal N w r t ω := h₁
    _ = ∑ j ∈ Finset.range N, w j * r (t - (j : ℤ)) ω := by simp [finiteSignal]
    _ = (∑ j ∈ Finset.range N,
        fun ω => ((w j) • coordinateLp hr (t - (j : ℤ)) : Lp ℝ 2 μ) ω) ω := by
      simpa only [Finset.sum_apply] using h₃.symm
    _ = (∑ j ∈ Finset.range N,
        (w j) • coordinateLp hr (t - (j : ℤ))) ω := by
      simpa only [Finset.sum_apply] using h₂.symm

theorem partialSum_tendsto (hr : IsWhiteInput r μ) (w : Discrete.Kernel) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2)) :
    Tendsto (fun N => partialSum hr w t N) atTop (𝓝 (infiniteSignalLp hr w t)) := by
  exact (weightedCoordinate_summable hr w t hw).hasSum.tendsto_sum_nat

theorem infiniteSignalLp_norm_sq (hr : IsWhiteInput r μ) (w : Discrete.Kernel) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2)) :
    ‖infiniteSignalLp hr w t‖ ^ 2 = Discrete.squareEnergy w := by
  let horth := (coordinateLp_orthonormal hr t).orthogonalFamily
  have hfinite : ∀ N : ℕ, ‖partialSum hr w t N‖ ^ 2 = ∑ j ∈ Finset.range N, (w j) ^ 2 := by
    intro N
    exact horth.norm_sum (fun j => w j) (Finset.range N) |>.trans (by
      apply Finset.sum_congr rfl
      intro j hj
      simp [sq])
  have hleft : Tendsto (fun N => ‖partialSum hr w t N‖ ^ 2) atTop
      (𝓝 (‖infiniteSignalLp hr w t‖ ^ 2)) :=
    ((continuous_norm.pow 2).tendsto _).comp (partialSum_tendsto hr w t hw)
  have hright : Tendsto (fun N => ∑ j ∈ Finset.range N, (w j) ^ 2) atTop
      (𝓝 (∑' j, (w j) ^ 2)) := hw.hasSum.tendsto_sum_nat
  rw [show (fun N => ‖partialSum hr w t N‖ ^ 2) =
      (fun N => ∑ j ∈ Finset.range N, (w j) ^ 2) from funext hfinite] at hleft
  have := tendsto_nhds_unique hleft hright
  simpa [Discrete.squareEnergy] using this

theorem integral_sq_eq_norm_sq (F : Lp ℝ 2 μ) :
    ∫ ω, (F : Ω → ℝ) ω ^ 2 ∂μ = ‖F‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  simp [pow_two]

theorem infiniteSignalLp_integral_eq_zero [IsProbabilityMeasure μ]
    (hr : IsWhiteInput r μ) (w : Discrete.Kernel) (t : ℤ)
    (hw : Summable (fun j => (w j)^2)) :
    ∫ ω, (infiniteSignalLp hr w t : Ω → ℝ) ω ∂μ = 0 := by
  let oneLp : Lp ℝ 2 μ :=
    (memLp_const (μ := μ) (p := 2) (1 : ℝ)).toLp (fun _ : Ω => (1 : ℝ))
  have hinner : ∀ s : ℤ, inner ℝ (coordinateLp hr s) oneLp = 0 := by
    intro s
    dsimp [oneLp, coordinateLp]
    rw [← MeasureTheory.MemLp.toLp_const 2 μ 1]
    rw [inner_toLp_mul (hr.memLp s) (memLp_const (μ := μ) (p := 2) (1 : ℝ))]
    simpa using hr.centered s
  have hpartial : ∀ N : ℕ, inner ℝ (partialSum hr w t N) oneLp = 0 := by
    intro N
    have hsum : ∀ s : Finset ℕ,
        inner ℝ (∑ j ∈ s, (w j) • coordinateLp hr (t - (j : ℤ))) oneLp = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert j s hj ih =>
        rw [Finset.sum_insert hj, inner_add_left, inner_smul_left, hinner, mul_zero, ih,
          add_zero]
    exact hsum (Finset.range N)
  have hlim : Tendsto (fun N => inner ℝ (partialSum hr w t N) oneLp) atTop
      (𝓝 (inner ℝ (infiniteSignalLp hr w t) oneLp)) :=
    (partialSum_tendsto hr w t hw).inner (tendsto_const_nhds : Tendsto (fun _ : ℕ => oneLp) atTop (𝓝 oneLp))
  have hzero : inner ℝ (infiniteSignalLp hr w t) oneLp = 0 := by
    apply tendsto_nhds_unique hlim
    simpa only [hpartial] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  rw [MeasureTheory.L2.inner_def] at hzero
  have hone : (oneLp : Ω → ℝ) =ᵐ[μ] (fun _ => (1 : ℝ)) :=
    (memLp_const (μ := μ) (p := 2) (1 : ℝ)).coeFn_toLp
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial] at hzero
  have hprod' : (fun ω => (oneLp : Ω → ℝ) ω *
      (infiniteSignalLp hr w t : Ω → ℝ) ω) =ᵐ[μ]
      (fun ω => (infiniteSignalLp hr w t : Ω → ℝ) ω) := by
    filter_upwards [hone] with ω hω
    rw [hω]
    simp
  rw [integral_congr_ae hprod'] at hzero
  simpa using hzero

theorem infiniteSignalLp_variance [IsProbabilityMeasure μ]
    (hr : IsWhiteInput r μ) (w : Discrete.Kernel) (t : ℤ)
    (hw : Summable (fun j => (w j)^2)) :
    Var[(infiniteSignalLp hr w t : Ω → ℝ); μ] = Discrete.squareEnergy w := by
  rw [ProbabilityTheory.variance_of_integral_eq_zero
    (Lp.aestronglyMeasurable (infiniteSignalLp hr w t)).aemeasurable
    (infiniteSignalLp_integral_eq_zero hr w t hw), integral_sq_eq_norm_sq,
    infiniteSignalLp_norm_sq hr w t hw]

theorem coe_sub_toLp_ae {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (fun ω => f ω - g ω) =ᵐ[μ] ((hf.toLp f - hg.toLp g : Lp ℝ 2 μ) : Ω → ℝ) := by
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with ω hsub hf' hg'
  rw [← hf', ← hg']
  simpa only [Pi.sub_apply] using hsub.symm

theorem toLp_sub_toLp {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    hf.toLp f - hg.toLp g = (hf.sub hg).toLp (fun ω => f ω - g ω) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp,
    (hf.sub hg).coeFn_toLp] with ω hsub hf' hg' hdiff
  calc
    _ = ((hf.toLp f : Ω → ℝ) ω - (hg.toLp g : Ω → ℝ) ω) := hsub
    _ = f ω - g ω := by rw [hf', hg']
    _ = _ := hdiff.symm

theorem partialSum_difference_correction
    (hr : IsWhiteInput r μ) (w : Discrete.Kernel) (t : ℤ) (N : ℕ) :
    partialSum hr w t N - partialSum hr w (t - 1) N =
      partialSum hr (Discrete.difference w) t (N + 1) -
        w N • coordinateLp hr (t - (N : ℤ)) := by
  rw [← finiteSignal_toLp_eq_sum hr N w t, ← finiteSignal_toLp_eq_sum hr N w (t - 1),
    ← finiteSignal_toLp_eq_sum hr (N + 1) (Discrete.difference w) t]
  rw [toLp_sub_toLp (finiteSignal_memLp (N := N) (w := w) hr t)
    (finiteSignal_memLp (N := N) (w := w) hr (t - 1))]
  apply Lp.ext
  have hright := Lp.coeFn_sub
    ((finiteSignal_memLp (N := N + 1) (w := Discrete.difference w) hr t).toLp
      (finiteSignal (N + 1) (Discrete.difference w) r t))
    (w N • coordinateLp hr (t - (N : ℤ)))
  filter_upwards [(finiteSignal_memLp (N := N) (w := w) hr t).coeFn_toLp,
    (finiteSignal_memLp (N := N) (w := w) hr (t - 1)).coeFn_toLp,
    (finiteSignal_memLp (N := N + 1) (w := Discrete.difference w) hr t).coeFn_toLp,
    Lp.coeFn_smul (w N) (coordinateLp hr (t - (N : ℤ))),
    ((finiteSignal_memLp (N := N) (w := w) hr t).sub
      (finiteSignal_memLp (N := N) (w := w) hr (t - 1))).coeFn_toLp,
    MemLp.coeFn_toLp (hr.memLp (t - (N : ℤ))), hright] with ω h₁ h₂ h₃ h₄ h₅ hcoord hright
  calc
    _ = finiteSignal N w r t ω - finiteSignal N w r (t - 1) ω := by
      convert h₅ using 1
    _ = finiteSignal (N + 1) (Discrete.difference w) r t ω - w N * r (t - (N : ℤ)) ω :=
      finiteSignal_difference_correction N w r t ω
    _ = ((finiteSignal_memLp (N := N + 1) (w := Discrete.difference w) hr t).toLp
      (finiteSignal (N + 1) (Discrete.difference w) r t) : Ω → ℝ) ω -
        (w N • coordinateLp hr (t - (N : ℤ)) : Lp ℝ 2 μ) ω := by
      rw [h₃, h₄]
      exact congrArg (fun x =>
        finiteSignal (N + 1) (Discrete.difference w) r t ω - w N * x) hcoord.symm
    _ = _ := hright.symm

theorem endpoint_decay (hr : IsWhiteInput r μ) (w : Discrete.Kernel) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2)) :
    Tendsto (fun N => (w N) • coordinateLp hr (t - (N : ℤ))) atTop (𝓝 0) := by
  exact (weightedCoordinate_summable hr w t hw).tendsto_atTop_zero

theorem infiniteSignalLp_difference (hr : IsWhiteInput r μ) (w : Discrete.Kernel) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2))
    (hdw : Summable (fun j => (Discrete.difference w j) ^ 2)) :
    infiniteSignalLp hr w t - infiniteSignalLp hr w (t - 1) =
      infiniteSignalLp hr (Discrete.difference w) t := by
  have hleft := (partialSum_tendsto hr w t hw).sub (partialSum_tendsto hr w (t - 1) hw)
  have hright := (partialSum_tendsto hr (Discrete.difference w) t hdw).comp
    (tendsto_add_atTop_nat 1)
  have hseq : Tendsto (fun N => partialSum hr (Discrete.difference w) t (N + 1) -
      (w N) • coordinateLp hr (t - (N : ℤ))) atTop
      (𝓝 (infiniteSignalLp hr (Discrete.difference w) t)) := by
    simpa [sub_zero] using hright.sub (endpoint_decay hr w t hw)
  have hcorr := hseq.congr' (Filter.Eventually.of_forall
      (fun N => (partialSum_difference_correction hr w t N).symm) :
      ∀ᶠ N in (atTop : Filter ℕ),
        partialSum hr (Discrete.difference w) t (N + 1) -
          (w N) • coordinateLp hr (t - (N : ℤ)) =
        partialSum hr w t N - partialSum hr w (t - 1) N)
  exact tendsto_nhds_unique hleft hcorr

theorem infiniteSignalLp_difference_ae (hr : IsWhiteInput r μ) (w : Discrete.Kernel) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2))
    (hdw : Summable (fun j => (Discrete.difference w j) ^ 2)) :
    (fun ω => (infiniteSignalLp hr w t : Ω → ℝ) ω -
        (infiniteSignalLp hr w (t - 1) : Ω → ℝ) ω) =ᵐ[μ]
      (infiniteSignalLp hr (Discrete.difference w) t : Ω → ℝ) := by
  filter_upwards [Lp.coeFn_sub (infiniteSignalLp hr w t) (infiniteSignalLp hr w (t - 1))] with ω hω
  calc
    _ = (infiniteSignalLp hr w t - infiniteSignalLp hr w (t - 1) : Lp ℝ 2 μ) ω := hω.symm
    _ = (infiniteSignalLp hr (Discrete.difference w) t : Lp ℝ 2 μ) ω :=
      congrArg (fun f : Lp ℝ 2 μ => f ω) (infiniteSignalLp_difference hr w t hw hdw)

theorem infiniteSignalLp_difference_variance [IsProbabilityMeasure μ]
    (hr : IsWhiteInput r μ) (w : Discrete.Kernel) (t : ℤ)
    (hw : Summable (fun j => (w j) ^ 2))
    (hdw : Summable (fun j => (Discrete.difference w j) ^ 2)) :
    Var[(fun ω => (infiniteSignalLp hr w t : Ω → ℝ) ω -
      (infiniteSignalLp hr w (t - 1) : Ω → ℝ) ω); μ] =
      Discrete.differenceEnergy w := by
  rw [ProbabilityTheory.variance_congr (infiniteSignalLp_difference_ae hr w t hw hdw),
    infiniteSignalLp_variance hr (Discrete.difference w) t hdw]
  rfl

end RayleighKernel.Probability
