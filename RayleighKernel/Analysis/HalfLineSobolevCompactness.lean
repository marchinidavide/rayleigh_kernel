import RayleighKernel.Analysis.HalfLineSobolevRepresentative
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Weak compactness in the half-line Sobolev space

This file packages sequential weak compactness for bounded sequences in `HalfLineH1`.  We send the
Hilbert space into its weak dual using the Riesz isometry and apply weak-star sequential compactness
of dual balls.
-/

noncomputable section

namespace RayleighKernel
namespace Analysis

open Filter MeasureTheory Set
open scoped ENNReal InnerProduct Topology

local instance : MeasureTheory.IsSeparable (volume : Measure ℝ) := inferInstance
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩

local instance : TopologicalSpace.SeparableSpace HalfLineH1 :=
  TopologicalSpace.SecondCountableTopology.to_separableSpace

/-- The norm of a Hilbert-space weak limit is bounded by every eventual uniform norm bound. -/
private theorem norm_le_of_tendsto_inner {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {l : Filter ι} [NeBot l] {u : ι → E} {v : E} {C : ℝ}
    (hweak : ∀ w : E, Tendsto (fun i ↦ inner ℝ (u i) w) l (𝓝 (inner ℝ v w)))
    (hu : ∀ᶠ i in l, ‖u i‖ ≤ C) : ‖v‖ ≤ C := by
  have hinner : inner ℝ v v ≤ C * ‖v‖ := le_of_tendsto (hweak v) <| by
    filter_upwards [hu] with i hi
    exact (real_inner_le_norm (u i) v).trans
      (mul_le_mul_of_nonneg_right hi (norm_nonneg v))
  rw [real_inner_self_eq_norm_mul_norm] at hinner
  by_cases hv : ‖v‖ = 0
  · obtain ⟨i, hi⟩ := hu.exists
    exact hv ▸ (norm_nonneg (u i)).trans hi
  · exact le_of_mul_le_mul_right hinner (lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv))

/-- Every norm-bounded sequence in `HalfLineH1` has a weakly convergent subsequence.  Weak
convergence is expressed by convergence of all Hilbert inner products. -/
theorem HalfLineH1.exists_weakly_convergent_subsequence {u : ℕ → HalfLineH1} {C : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ (ns : ℕ → ℕ) (v : HalfLineH1), StrictMono ns ∧
      ‖v‖ ≤ C ∧ ∀ w : HalfLineH1,
          Tendsto (fun n ↦ inner ℝ (u (ns n)) w) atTop (𝓝 (inner ℝ v w)) := by
  let j : HalfLineH1 → WeakDual ℝ HalfLineH1 := fun x ↦
    StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ HalfLineH1) x)
  have hjmem : ∀ n, j (u n) ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C := by
    intro n
    change WeakDual.toStrongDual (j (u n)) ∈
      Metric.closedBall (0 : StrongDual ℝ HalfLineH1) C
    refine (mem_closedBall_zero_iff
      (E := StrongDual ℝ HalfLineH1) (a := WeakDual.toStrongDual (j (u n))) (r := C)).2 ?_
    change ‖(InnerProductSpace.toDual ℝ HalfLineH1) (u n)‖ ≤ C
    rw [LinearIsometryEquiv.norm_map]
    exact hu n
  obtain ⟨a, _ha, ns, hns, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ HalfLineH1 0 C).subseq_of_frequently_in
      (Filter.Eventually.frequently (Filter.Eventually.of_forall hjmem))
  let v : HalfLineH1 := (InnerProductSpace.toDual ℝ HalfLineH1).symm
    (WeakDual.toStrongDual a)
  have hweak : ∀ w : HalfLineH1,
      Tendsto (fun n ↦ inner ℝ (u (ns n)) w) atTop (𝓝 (inner ℝ v w)) := by
    intro w
    have ht := (WeakDual.eval_continuous w).tendsto a |>.comp hlim
    have hfun : ((fun x ↦ x w) ∘ (fun x ↦ j (u x)) ∘ ns) =
        fun n ↦ inner ℝ (u (ns n)) w := by
      funext n
      simp only [Function.comp_apply, j, StrongDual.toWeakDual_apply,
        InnerProductSpace.toDual_apply_apply]
    have htarget : a w = inner ℝ v w := by
      exact InnerProductSpace.toDual_symm_apply.symm
    simpa only [hfun, htarget] using ht
  refine ⟨ns, v, hns, norm_le_of_tendsto_inner hweak ?_, hweak⟩
  exact Filter.Eventually.of_forall fun n ↦ hu (ns n)

/-- Weak convergence in `HalfLineH1` implies weak convergence of the value components in `L²`. -/
theorem HalfLineH1.tendsto_inner_value {ι : Type*} {l : Filter ι} {u : ι → HalfLineH1}
    {v : HalfLineH1}
    (hu : ∀ w : HalfLineH1,
      Tendsto (fun i ↦ inner ℝ (u i) w) l (𝓝 (inner ℝ v w))) (g : RealL2) :
    Tendsto (fun i ↦ inner ℝ (u i).value g) l (𝓝 (inner ℝ v.value g)) := by
  simpa only [ContinuousLinearMap.adjoint_inner_right] using hu ((HalfLineH1.value†) g)

/-- Weak convergence in `HalfLineH1` implies weak convergence of the weak-derivative components in
`L²`. -/
theorem HalfLineH1.tendsto_inner_weakDeriv {ι : Type*} {l : Filter ι}
    {u : ι → HalfLineH1} {v : HalfLineH1}
    (hu : ∀ w : HalfLineH1,
      Tendsto (fun i ↦ inner ℝ (u i) w) l (𝓝 (inner ℝ v w))) (g : RealL2) :
    Tendsto (fun i ↦ inner ℝ (u i).weakDeriv g) l
      (𝓝 (inner ℝ v.weakDeriv g)) := by
  simpa only [ContinuousLinearMap.adjoint_inner_right] using hu ((HalfLineH1.weakDeriv†) g)

/-- The `L²` norm of the value of a weak limit is bounded by every eventual uniform bound on the
value norms. -/
theorem HalfLineH1.norm_value_le_of_tendsto_inner {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ι → HalfLineH1} {v : HalfLineH1} {C : ℝ}
    (hweak : ∀ w : HalfLineH1,
      Tendsto (fun i ↦ inner ℝ (u i) w) l (𝓝 (inner ℝ v w)))
    (hu : ∀ᶠ i in l, ‖(u i).value‖ ≤ C) : ‖v.value‖ ≤ C :=
  norm_le_of_tendsto_inner (fun g ↦ HalfLineH1.tendsto_inner_value hweak g) hu

/-- The `L²` norm of the weak derivative of a weak limit is bounded by every eventual uniform bound
on the derivative norms. -/
theorem HalfLineH1.norm_weakDeriv_le_of_tendsto_inner {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ι → HalfLineH1} {v : HalfLineH1} {C : ℝ}
    (hweak : ∀ w : HalfLineH1,
      Tendsto (fun i ↦ inner ℝ (u i) w) l (𝓝 (inner ℝ v w)))
    (hu : ∀ᶠ i in l, ‖(u i).weakDeriv‖ ≤ C) : ‖v.weakDeriv‖ ≤ C :=
  norm_le_of_tendsto_inner (fun g ↦ HalfLineH1.tendsto_inner_weakDeriv hweak g) hu

/-- The weak-derivative norm of a weak `HalfLineH1` limit is bounded by the limit inferior of the
weak-derivative norms, provided the sequence has a fixed norm bound. -/
theorem HalfLineH1.norm_weakDeriv_le_liminf_of_tendsto_inner_of_bound
    {u : ℕ → HalfLineH1} {v : HalfLineH1} {B : ℝ}
    (hweak : ∀ w : HalfLineH1,
      Tendsto (fun n ↦ inner ℝ (u n) w) atTop (𝓝 (inner ℝ v w)))
    (hbound : ∀ n, ‖(u n).weakDeriv‖ ≤ B) :
    ‖v.weakDeriv‖ ≤ liminf (fun n ↦ ‖(u n).weakDeriv‖) atTop := by
  by_contra hnot
  have hlt : liminf (fun n ↦ ‖(u n).weakDeriv‖) atTop < ‖v.weakDeriv‖ :=
    lt_of_not_ge hnot
  let C : ℝ := (liminf (fun n ↦ ‖(u n).weakDeriv‖) atTop + ‖v.weakDeriv‖) / 2
  have hliminf_lt_C : liminf (fun n ↦ ‖(u n).weakDeriv‖) atTop < C := by
    change liminf (fun n ↦ ‖(u n).weakDeriv‖) atTop <
      (liminf (fun n ↦ ‖(u n).weakDeriv‖) atTop + ‖v.weakDeriv‖) / 2
    linarith
  have hC_lt_limit : C < ‖v.weakDeriv‖ := by
    change (liminf (fun n ↦ ‖(u n).weakDeriv‖) atTop + ‖v.weakDeriv‖) / 2 <
      ‖v.weakDeriv‖
    linarith
  have hcobounded : IsCoboundedUnder (· ≥ ·) atTop (fun n ↦ ‖(u n).weakDeriv‖) :=
    isCoboundedUnder_ge_of_eventually_le atTop (x := B)
      (Filter.Eventually.of_forall hbound)
  obtain ⟨ns, hns, hbelow⟩ := extraction_of_frequently_atTop
    (frequently_lt_of_liminf_lt hcobounded hliminf_lt_C)
  have hsubweak : ∀ w : HalfLineH1,
      Tendsto (fun k ↦ inner ℝ (u (ns k)) w) atTop (𝓝 (inner ℝ v w)) :=
    fun w ↦ (hweak w).comp hns.tendsto_atTop
  have hsubbound : ∀ᶠ k in atTop, ‖(u (ns k)).weakDeriv‖ ≤ C :=
    Filter.Eventually.of_forall fun k ↦ (hbelow k).le
  have hvbound := HalfLineH1.norm_weakDeriv_le_of_tendsto_inner hsubweak hsubbound
  exact (not_lt_of_ge hvbound) hC_lt_limit

/-- Weak convergence in `HalfLineH1` implies pointwise convergence of the canonical continuous
representatives. -/
theorem HalfLineH1.tendsto_continuousRep_of_tendsto_inner {ι : Type*} {l : Filter ι}
    {u : ι → HalfLineH1} {v : HalfLineH1}
    (hweak : ∀ w : HalfLineH1,
      Tendsto (fun i ↦ inner ℝ (u i) w) l (𝓝 (inner ℝ v w))) (x : ℝ) :
    Tendsto (fun i ↦ (u i).continuousRep x) l (𝓝 (v.continuousRep x)) := by
  have hs : volume (uIoc (0 : ℝ) x) ≠ ∞ := by
    simp [Real.volume_uIoc]
  let χ : RealL2 := indicatorConstLp 2 measurableSet_uIoc hs 1
  have hinner : ∀ z : HalfLineH1,
      inner ℝ z.weakDeriv χ = ∫ t in uIoc (0 : ℝ) x, (z.weakDeriv : ℝ → ℝ) t := by
    intro z
    rw [real_inner_comm]
    simpa [χ] using L2.inner_indicatorConstLp_one measurableSet_uIoc hs z.weakDeriv
  have ht := HalfLineH1.tendsto_inner_weakDeriv hweak χ
  simp_rw [hinner] at ht
  rw [show (fun i ↦ (u i).continuousRep x) = fun i ↦
      (if 0 ≤ x then 1 else -1 : ℝ) •
        ∫ t in uIoc (0 : ℝ) x, ((u i).weakDeriv : ℝ → ℝ) t by
    funext i
    exact intervalIntegral.intervalIntegral_eq_integral_uIoc _ _ _ _]
  rw [HalfLineH1.continuousRep,
    intervalIntegral.intervalIntegral_eq_integral_uIoc]
  exact ht.const_smul (if 0 ≤ x then 1 else -1 : ℝ)

/-- A uniform bound on weak derivatives gives equicontinuity of the canonical representatives. -/
theorem HalfLineH1.equicontinuous_continuousRep {ι : Type*} {u : ι → HalfLineH1} {C : ℝ}
    (_hC : 0 ≤ C) (hu : ∀ i, ‖(u i).weakDeriv‖ ≤ C) :
    Equicontinuous (fun i ↦ (u i).continuousRep) := by
  apply Metric.equicontinuous_of_continuity_modulus (fun t ↦ Real.sqrt t * C)
  · convert (Real.continuous_sqrt.continuousAt.mul_const C).tendsto using 1
    simp only [Real.sqrt_zero, zero_mul]
  · intro x y i
    rw [Real.dist_eq, Real.dist_eq]
    exact ((u i).abs_continuousRep_sub_le y x).trans <|
      mul_le_mul_of_nonneg_left (hu i) (Real.sqrt_nonneg _)

/-- A weakly convergent `HalfLineH1` sequence converges uniformly on every compact set provided its
weak derivatives have a uniform `L²` bound. -/
theorem HalfLineH1.tendstoUniformlyOn_continuousRep_of_tendsto_inner
    {u : ℕ → HalfLineH1} {v : HalfLineH1} {C : ℝ}
    (hC : 0 ≤ C) (hu : ∀ n, ‖(u n).weakDeriv‖ ≤ C)
    (hweak : ∀ w : HalfLineH1,
      Tendsto (fun n ↦ inner ℝ (u n) w) atTop (𝓝 (inner ℝ v w)))
    {K : Set ℝ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n ↦ (u n).continuousRep) v.continuousRep atTop K := by
  let F : ℕ → K → ℝ := fun n x ↦ (u n).continuousRep x
  let f : K → ℝ := fun x ↦ v.continuousRep x
  have heq : Equicontinuous F := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ :=
      Metric.equicontinuousAt_iff.mp
        (HalfLineH1.equicontinuous_continuousRep hC hu x.1) ε hε
    exact ⟨δ, hδ, fun y hy i ↦ by simpa only [F] using hmod y.1 hy i⟩
  have hpoint : Tendsto F atTop (𝓝 f) := by
    rw [tendsto_pi_nhds]
    exact fun x ↦ HalfLineH1.tendsto_continuousRep_of_tendsto_inner hweak x
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hunif : Tendsto (UniformFun.ofFun ∘ F) atTop (𝓝 (UniformFun.ofFun f)) :=
    (heq.tendsto_uniformFun_iff_pi atTop f).2 hpoint
  have hunif' : TendstoUniformly F f atTop :=
    UniformFun.tendsto_iff_tendstoUniformly.mp hunif
  exact (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe).2 hunif'

/-- Weak convergence with a uniform derivative bound gives local strong `L²` convergence of the
canonical representatives, expressed as convergence of the squared-error integral on a compact
set. -/
theorem HalfLineH1.tendsto_setIntegral_sq_sub_continuousRep_of_tendsto_inner
    {u : ℕ → HalfLineH1} {v : HalfLineH1} {C : ℝ}
    (hC : 0 ≤ C) (hu : ∀ n, ‖(u n).weakDeriv‖ ≤ C)
    (hweak : ∀ w : HalfLineH1,
      Tendsto (fun n ↦ inner ℝ (u n) w) atTop (𝓝 (inner ℝ v w)))
    {K : Set ℝ} (hK : IsCompact K) :
    Tendsto (fun n ↦ ∫ x in K, ((u n).continuousRep x - v.continuousRep x) ^ 2)
      atTop (𝓝 0) := by
  have hunif := HalfLineH1.tendstoUniformlyOn_continuousRep_of_tendsto_inner
    hC hu hweak hK
  have hubound := Metric.tendstoUniformlyOn_iff.mp hunif 1 zero_lt_one
  have hmeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (fun x ↦ ((u n).continuousRep x - v.continuousRep x) ^ 2)
        (volume.restrict K) := Filter.Eventually.of_forall fun n ↦
    (((u n).continuous_continuousRep.sub v.continuous_continuousRep).pow 2).aestronglyMeasurable
  have hbound : ∀ᶠ n in atTop, ∀ᵐ x ∂volume.restrict K,
      ‖((u n).continuousRep x - v.continuousRep x) ^ 2‖ ≤ (1 : ℝ) := by
    filter_upwards [hubound] with n hn
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with x hx
    have hdist : |(u n).continuousRep x - v.continuousRep x| < 1 := by
      simpa only [Real.dist_eq, abs_sub_comm] using hn x hx
    calc
      ‖((u n).continuousRep x - v.continuousRep x) ^ 2‖ =
          |(u n).continuousRep x - v.continuousRep x| ^ 2 := by
        simp only [Real.norm_eq_abs, abs_pow]
      _ ≤ 1 := by nlinarith [abs_nonneg ((u n).continuousRep x - v.continuousRep x)]
  have hlim : ∀ᵐ x ∂volume.restrict K,
      Tendsto (fun n ↦ ((u n).continuousRep x - v.continuousRep x) ^ 2)
        atTop (𝓝 (0 : ℝ)) := Filter.Eventually.of_forall fun x ↦ by
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (HalfLineH1.tendsto_continuousRep_of_tendsto_inner hweak x).sub_const
        (v.continuousRep x) |>.pow 2
  simpa only [integral_zero] using
    (tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict K)
      (fun _ ↦ (1 : ℝ)) hmeas hbound (by
        let _ : IsFiniteMeasure (volume.restrict K) :=
          isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
        exact integrable_const (1 : ℝ)) hlim)

/-- A bounded sequence in `HalfLineH1` has a subsequence converging weakly in `HalfLineH1` and
uniformly and strongly in local `L²` on every compact set through the canonical representatives. -/
theorem HalfLineH1.exists_weakly_and_locally_uniformly_convergent_subsequence
    {u : ℕ → HalfLineH1} {C : ℝ} (hC : 0 ≤ C) (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ (ns : ℕ → ℕ) (v : HalfLineH1), StrictMono ns ∧ ‖v‖ ≤ C ∧
      (∀ w : HalfLineH1,
        Tendsto (fun n ↦ inner ℝ (u (ns n)) w) atTop (𝓝 (inner ℝ v w))) ∧
      ∀ K : Set ℝ, IsCompact K →
        TendstoUniformlyOn (fun n ↦ (u (ns n)).continuousRep) v.continuousRep atTop K ∧
        Tendsto
          (fun n ↦ ∫ x in K, ((u (ns n)).continuousRep x - v.continuousRep x) ^ 2)
          atTop (𝓝 0) := by
  obtain ⟨ns, v, hns, hv, hweak⟩ := HalfLineH1.exists_weakly_convergent_subsequence hu
  refine ⟨ns, v, hns, hv, hweak, fun K hK ↦ ?_⟩
  have hderiv : ∀ n, ‖(u (ns n)).weakDeriv‖ ≤ C :=
    fun n ↦ (u (ns n)).norm_weakDeriv_le.trans (hu (ns n))
  exact ⟨HalfLineH1.tendstoUniformlyOn_continuousRep_of_tendsto_inner hC hderiv hweak hK,
    HalfLineH1.tendsto_setIntegral_sq_sub_continuousRep_of_tendsto_inner
      hC hderiv hweak hK⟩

end Analysis
end RayleighKernel
