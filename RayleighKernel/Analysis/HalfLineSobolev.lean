import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# The zero-trace Sobolev space on the half-line

This file starts the representative-free analytic model used by the variational problem.  We
embed a half-line function into the whole line by zero extension and record both its `L²` value and
its weak derivative.  The space is the closure, in the Hilbert graph norm, of smooth compactly
supported functions whose topological support is contained in `(0, ∞)`.

This is the standard realization of `H¹₀(0, ∞)` by zero extension.  Defining the boundary condition
through the closure avoids assigning point values to arbitrary `L²` representatives.  A continuous
representative and its trace will be constructed in the next layer.
-/

noncomputable section

namespace RayleighKernel
namespace Analysis

open MeasureTheory Set
open Filter
open scoped ENNReal SchwartzMap Topology

/-- Real-valued square-integrable functions on the whole line. -/
abbrev RealL2 : Type := Lp ℝ 2 (volume : Measure ℝ)

/-- The Hilbert product carrying a function and its weak derivative.

`WithLp 2` gives the graph norm `sqrt (‖u‖₂² + ‖v‖₂²)`, unlike Lean's default
maximum norm on an ordinary product. -/
abbrev H1Graph : Type := WithLp 2 (RealL2 × RealL2)

/-- Smooth whole-line test functions supported strictly inside the positive half-line. -/
def PositiveTestFunction : Submodule ℝ 𝓢(ℝ, ℝ) where
  carrier := {φ | tsupport φ ⊆ Ioi 0}
  zero_mem' := by simp
  add_mem' {φ ψ} hφ hψ :=
    (tsupport_add φ ψ).trans (union_subset hφ hψ)
  smul_mem' c φ hφ :=
    (tsupport_smul_subset_right (fun _ : ℝ => c) φ).trans hφ

/-- The `L²` class of a Schwartz function. -/
def schwartzValue : 𝓢(ℝ, ℝ) →L[ℝ] RealL2 :=
  SchwartzMap.toLpCLM ℝ ℝ 2 volume

/-- The `L²` class of the derivative of a Schwartz function. -/
def schwartzDeriv : 𝓢(ℝ, ℝ) →L[ℝ] RealL2 :=
  schwartzValue.comp (SchwartzMap.derivCLM ℝ ℝ)

/-- The `L²` value of a smooth positive-half-line test function. -/
def positiveTestValue : PositiveTestFunction →L[ℝ] RealL2 :=
  schwartzValue.comp PositiveTestFunction.subtypeL

/-- The `L²` derivative of a smooth positive-half-line test function. -/
def positiveTestDeriv : PositiveTestFunction →L[ℝ] RealL2 :=
  schwartzDeriv.comp PositiveTestFunction.subtypeL

/-- The value/derivative graph of a smooth positive-half-line test function. -/
def positiveTestGraphCLM : PositiveTestFunction →L[ℝ] H1Graph :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ RealL2 RealL2).symm.toContinuousLinearMap.comp
    (positiveTestValue.prod positiveTestDeriv)

/-- The linear-map form of `positiveTestGraphCLM`, used to form its range and closure. -/
def positiveTestGraph : PositiveTestFunction →ₗ[ℝ] H1Graph :=
  positiveTestGraphCLM.toLinearMap

/-- The `L²` pairing on the whole line. -/
def l2Pairing : RealL2 →L[ℝ] RealL2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing volume 2 2

/-- For real `L²`, the bilinear integral pairing is the Hilbert inner product. -/
theorem l2Pairing_eq_inner (f g : RealL2) : l2Pairing f g = inner ℝ f g := by
  rw [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral, L2.inner_def]
  congr 1
  funext x
  simp [RCLike.inner_apply, mul_comm]

/-- An `L²` weak derivative is unique when tested against all Schwartz functions. -/
theorem weakDerivative_unique {u v w : RealL2}
    (hv : ∀ φ : 𝓢(ℝ, ℝ),
      l2Pairing u (schwartzDeriv φ) = -l2Pairing v (schwartzValue φ))
    (hw : ∀ φ : 𝓢(ℝ, ℝ),
      l2Pairing u (schwartzDeriv φ) = -l2Pairing w (schwartzValue φ)) :
    v = w := by
  have hdense : DenseRange schwartzValue :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  apply hdense.eq_of_inner_left ℝ
  intro φ
  rw [← l2Pairing_eq_inner, ← l2Pairing_eq_inner]
  linarith [hv φ, hw φ]

/-- Residual of the weak-derivative identity against a Schwartz test function.

It is zero precisely when `∫ u φ' + ∫ v φ = 0` for the stored value/derivative pair `(u, v)`.
-/
def weakDerivativeResidual (φ : 𝓢(ℝ, ℝ)) : H1Graph →L[ℝ] ℝ :=
  ((l2Pairing.flip (schwartzDeriv φ)).comp (WithLp.fstL 2 ℝ RealL2 RealL2)) +
    ((l2Pairing.flip (schwartzValue φ)).comp (WithLp.sndL 2 ℝ RealL2 RealL2))

/-- Restrict the value component of an ambient graph pair to the nonpositive half-line. -/
def graphValueOnNonpositive :
    H1Graph →L[ℝ] Lp ℝ 2 ((volume : Measure ℝ).restrict (Iic 0)) :=
  (LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Iic 0)).comp
    (WithLp.fstL 2 ℝ RealL2 RealL2)

/-- Restrict the derivative component of an ambient graph pair to the nonpositive half-line. -/
def graphDerivOnNonpositive :
    H1Graph →L[ℝ] Lp ℝ 2 ((volume : Measure ℝ).restrict (Iic 0)) :=
  (LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Iic 0)).comp
    (WithLp.sndL 2 ℝ RealL2 RealL2)

private theorem positiveTestGraph_mem_ker_weakDerivativeResidual
    (φ : 𝓢(ℝ, ℝ)) (u : PositiveTestFunction) :
    positiveTestGraph u ∈ (weakDerivativeResidual φ).ker := by
  rw [LinearMap.mem_ker]
  change l2Pairing (positiveTestValue u) (schwartzDeriv φ) +
      l2Pairing (positiveTestDeriv u) (schwartzValue φ) = 0
  rw [show l2Pairing (positiveTestValue u) (schwartzDeriv φ) =
      ∫ x : ℝ, u.1 x * deriv φ x by
        rw [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral]
        apply integral_congr_ae
        filter_upwards [u.1.coeFn_toLp 2 volume,
          (SchwartzMap.derivCLM ℝ ℝ φ).coeFn_toLp 2 volume] with x hu hφ
        simp [positiveTestValue, schwartzValue, schwartzDeriv, hu, hφ]]
  rw [show l2Pairing (positiveTestDeriv u) (schwartzValue φ) =
      ∫ x : ℝ, deriv u.1 x * φ x by
        rw [l2Pairing, ContinuousLinearMap.lpPairing_eq_integral]
        apply integral_congr_ae
        filter_upwards [(SchwartzMap.derivCLM ℝ ℝ u.1).coeFn_toLp 2 volume,
          φ.coeFn_toLp 2 volume] with x hu hφ
        simp [positiveTestDeriv, schwartzValue, schwartzDeriv, hu, hφ]]
  linarith [SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul u.1 φ]

private theorem positiveTestGraph_mem_ker_graphValueOnNonpositive
    (u : PositiveTestFunction) : positiveTestGraph u ∈ graphValueOnNonpositive.ker := by
  rw [LinearMap.mem_ker, Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ (Iic 0) (positiveTestValue u),
    (u.1.coeFn_toLp 2 volume).filter_mono ae_restrict_le,
    ae_restrict_mem measurableSet_Iic] with x hx hcoe hx_nonpositive
  change ((LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Iic 0)) (positiveTestValue u) : ℝ → ℝ) x = 0
  rw [hx]
  change ((u.1.toLp 2 volume : RealL2) : ℝ → ℝ) x = 0
  rw [hcoe]
  have hx_support : x ∉ tsupport u.1 := fun hx' =>
    (not_lt_of_ge (show x ≤ 0 from hx_nonpositive)) (show 0 < x from u.2 hx')
  exact image_eq_zero_of_notMem_tsupport hx_support

private theorem positiveTestGraph_mem_ker_graphDerivOnNonpositive
    (u : PositiveTestFunction) : positiveTestGraph u ∈ graphDerivOnNonpositive.ker := by
  rw [LinearMap.mem_ker, Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ (Iic 0) (positiveTestDeriv u),
    (SchwartzMap.derivCLM ℝ ℝ u.1).coeFn_toLp 2 volume |>.filter_mono ae_restrict_le,
    ae_restrict_mem measurableSet_Iic] with x hx hcoe hx_nonpositive
  change ((LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Iic 0)) (positiveTestDeriv u) : ℝ → ℝ) x = 0
  rw [hx]
  change ((((SchwartzMap.derivCLM ℝ ℝ u.1).toLp 2 volume : RealL2) : ℝ → ℝ) x) = 0
  rw [hcoe]
  have hderiv_support : tsupport (deriv u.1) ⊆ tsupport u.1 := tsupport_deriv_subset
  have hx_support : x ∉ tsupport (deriv u.1) := fun hx' =>
    (not_lt_of_ge (show x ≤ 0 from hx_nonpositive))
      (show 0 < x from u.2 (hderiv_support hx'))
  exact image_eq_zero_of_notMem_tsupport hx_support

/-- The whole-line graph closure defining the zero-trace half-line Sobolev space. -/
def halfLineH1Submodule : Submodule ℝ H1Graph :=
  (LinearMap.range positiveTestGraph).topologicalClosure

/-- Hilbert-space membership criterion for the closed positive-test graph.  To prove that a graph
pair belongs to `HalfLineH1`, it suffices to prove that it is orthogonal to every pair orthogonal to
all smooth positive-half-line graph generators. -/
theorem graph_mem_halfLineH1Submodule_of_orthogonal
    {g : H1Graph}
    (hg : ∀ z : H1Graph,
      z ∈ (LinearMap.range positiveTestGraph)ᗮ → inner ℝ z g = 0) :
    g ∈ halfLineH1Submodule := by
  rw [halfLineH1Submodule, ← Submodule.orthogonal_orthogonal_eq_closure]
  rw [Submodule.mem_orthogonal]
  intro z hz
  simpa only [real_inner_comm] using hg z hz

/-- The stored second component satisfies the distributional derivative identity. -/
theorem halfLineH1Submodule_le_ker_weakDerivativeResidual (φ : 𝓢(ℝ, ℝ)) :
    halfLineH1Submodule ≤ (weakDerivativeResidual φ).ker := by
  apply Submodule.topologicalClosure_minimal
  · rintro _ ⟨u, rfl⟩
    exact positiveTestGraph_mem_ker_weakDerivativeResidual φ u
  · exact (weakDerivativeResidual φ).isClosed_ker

/-- The zero-extended value vanishes almost everywhere on `(-∞, 0]`. -/
theorem halfLineH1Submodule_le_ker_graphValueOnNonpositive :
    halfLineH1Submodule ≤ graphValueOnNonpositive.ker := by
  apply Submodule.topologicalClosure_minimal
  · rintro _ ⟨u, rfl⟩
    exact positiveTestGraph_mem_ker_graphValueOnNonpositive u
  · exact graphValueOnNonpositive.isClosed_ker

/-- The zero-extended weak derivative vanishes almost everywhere on `(-∞, 0]`. -/
theorem halfLineH1Submodule_le_ker_graphDerivOnNonpositive :
    halfLineH1Submodule ≤ graphDerivOnNonpositive.ker := by
  apply Submodule.topologicalClosure_minimal
  · rintro _ ⟨u, rfl⟩
    exact positiveTestGraph_mem_ker_graphDerivOnNonpositive u
  · exact graphDerivOnNonpositive.isClosed_ker

/-- `H¹₀(0, ∞)`, represented by the whole-line zero extension and its weak derivative. -/
abbrev HalfLineH1 : Type := ↥halfLineH1Submodule

noncomputable instance : CompleteSpace HalfLineH1 := by
  change CompleteSpace ↥((LinearMap.range positiveTestGraph).topologicalClosure)
  infer_instance

/-- Inclusion of the closed graph space into its ambient Hilbert product. -/
def HalfLineH1.toGraph : HalfLineH1 →L[ℝ] H1Graph :=
  halfLineH1Submodule.subtypeL

/-- The whole-line `L²` value of a half-line Sobolev function, extended by zero. -/
def HalfLineH1.value : HalfLineH1 →L[ℝ] RealL2 :=
  (WithLp.fstL 2 ℝ RealL2 RealL2).comp HalfLineH1.toGraph

/-- The whole-line weak derivative of a half-line Sobolev function, extended by zero. -/
def HalfLineH1.weakDeriv : HalfLineH1 →L[ℝ] RealL2 :=
  (WithLp.sndL 2 ℝ RealL2 RealL2).comp HalfLineH1.toGraph

@[simp]
theorem HalfLineH1.value_apply (u : HalfLineH1) :
    HalfLineH1.value u = u.1.fst := rfl

@[simp]
theorem HalfLineH1.weakDeriv_apply (u : HalfLineH1) :
    HalfLineH1.weakDeriv u = u.1.snd := rfl

/-- The defining integration-by-parts identity for the weak derivative. -/
theorem HalfLineH1.weakDerivative_identity (u : HalfLineH1) (φ : 𝓢(ℝ, ℝ)) :
    l2Pairing u.value (schwartzDeriv φ) = -l2Pairing u.weakDeriv (schwartzValue φ) := by
  have hu := halfLineH1Submodule_le_ker_weakDerivativeResidual φ u.2
  rw [LinearMap.mem_ker] at hu
  change l2Pairing u.value (schwartzDeriv φ) +
      l2Pairing u.weakDeriv (schwartzValue φ) = 0 at hu
  linarith

/-- The whole-line value is zero almost everywhere on the nonpositive half-line. -/
theorem HalfLineH1.value_ae_eq_zero_on_nonpositive (u : HalfLineH1) :
    u.value =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0 := by
  have hu := halfLineH1Submodule_le_ker_graphValueOnNonpositive u.2
  rw [LinearMap.mem_ker, Lp.eq_zero_iff_ae_eq_zero] at hu
  exact (LpToLpRestrictCLM_coeFn ℝ (Iic 0) u.value).symm.trans hu

/-- The whole-line weak derivative is zero almost everywhere on the nonpositive half-line. -/
theorem HalfLineH1.weakDeriv_ae_eq_zero_on_nonpositive (u : HalfLineH1) :
    u.weakDeriv =ᵐ[(volume : Measure ℝ).restrict (Iic 0)] 0 := by
  have hu := halfLineH1Submodule_le_ker_graphDerivOnNonpositive u.2
  rw [LinearMap.mem_ker, Lp.eq_zero_iff_ae_eq_zero] at hu
  exact (LpToLpRestrictCLM_coeFn ℝ (Iic 0) u.weakDeriv).symm.trans hu

/-- Restriction of the zero-extended value to the measure on `[0, ∞)`. -/
def HalfLineH1.valueOnHalfLine :
    HalfLineH1 →L[ℝ] Lp ℝ 2 ((volume : Measure ℝ).restrict (Ici 0)) :=
  (LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ici 0)).comp HalfLineH1.value

/-- Restriction of the zero-extended weak derivative to the measure on `[0, ∞)`. -/
def HalfLineH1.weakDerivOnHalfLine :
    HalfLineH1 →L[ℝ] Lp ℝ 2 ((volume : Measure ℝ).restrict (Ici 0)) :=
  (LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ici 0)).comp HalfLineH1.weakDeriv

/-- A generator belongs to the completed half-line Sobolev space. -/
def PositiveTestFunction.toHalfLineH1 (φ : PositiveTestFunction) : HalfLineH1 :=
  ⟨positiveTestGraph φ,
    Submodule.le_topologicalClosure (LinearMap.range positiveTestGraph) ⟨φ, rfl⟩⟩

@[simp]
theorem PositiveTestFunction.value_toHalfLineH1 (φ : PositiveTestFunction) :
    HalfLineH1.value (PositiveTestFunction.toHalfLineH1 φ) =
      SchwartzMap.toLpCLM ℝ ℝ 2 volume φ.1 := rfl

@[simp]
theorem PositiveTestFunction.weakDeriv_toHalfLineH1 (φ : PositiveTestFunction) :
    HalfLineH1.weakDeriv (PositiveTestFunction.toHalfLineH1 φ) =
      SchwartzMap.toLpCLM ℝ ℝ 2 volume (SchwartzMap.derivCLM ℝ ℝ φ.1) := rfl

/-- Every element of `HalfLineH1` is a graph-norm limit of positive-half-line test functions. -/
theorem HalfLineH1.exists_positiveTestFunction_sequence (u : HalfLineH1) :
    ∃ φ : ℕ → PositiveTestFunction,
      Tendsto (fun n ↦ PositiveTestFunction.toHalfLineH1 (φ n)) atTop (𝓝 u) := by
  have hu : u.1 ∈ closure (LinearMap.range positiveTestGraph : Set H1Graph) := by
    exact u.2
  obtain ⟨g, hg_range, hg_tendsto⟩ := mem_closure_iff_seq_limit.mp hu
  choose φ hφ using hg_range
  refine ⟨φ, tendsto_subtype_rng.mpr ?_⟩
  simpa only [PositiveTestFunction.toHalfLineH1, hφ] using hg_tendsto

/-- The value and weak derivative determine an element of `HalfLineH1`. -/
theorem HalfLineH1.ext {u v : HalfLineH1}
    (hvalue : u.value = v.value) (hderiv : u.weakDeriv = v.weakDeriv) : u = v := by
  apply Subtype.ext
  apply WithLp.equiv 2 (RealL2 × RealL2) |>.injective
  exact Prod.ext hvalue hderiv

/-- Two half-line Sobolev elements with the same `L²` value have the same weak derivative. -/
theorem HalfLineH1.weakDeriv_eq_of_value_eq {u v : HalfLineH1} (hvalue : u.value = v.value) :
    u.weakDeriv = v.weakDeriv := by
  apply weakDerivative_unique (u := u.value)
  · exact u.weakDerivative_identity
  · simpa only [hvalue] using v.weakDerivative_identity

/-- A half-line Sobolev element is determined by its `L²` value. -/
theorem HalfLineH1.ext_value {u v : HalfLineH1} (hvalue : u.value = v.value) : u = v :=
  HalfLineH1.ext hvalue (HalfLineH1.weakDeriv_eq_of_value_eq hvalue)

/-- The map from a half-line Sobolev element to its `L²` value is injective. -/
theorem HalfLineH1.value_injective : Function.Injective HalfLineH1.value :=
  fun _ _ ↦ HalfLineH1.ext_value

/-- The graph norm controls the whole-line `L²` value norm. -/
theorem HalfLineH1.norm_value_le (u : HalfLineH1) : ‖u.value‖ ≤ ‖u‖ := by
  change ‖u.1.fst‖ ≤ ‖u.1‖
  exact WithLp.norm_fst_le (α := RealL2) (β := RealL2) u.1

/-- The graph norm controls the whole-line weak-derivative norm. -/
theorem HalfLineH1.norm_weakDeriv_le (u : HalfLineH1) : ‖u.weakDeriv‖ ≤ ‖u‖ := by
  change ‖u.1.snd‖ ≤ ‖u.1‖
  exact WithLp.norm_snd_le (α := RealL2) (β := RealL2) u.1

/-- The half-line restriction of the value cannot increase its `L²` norm. -/
theorem HalfLineH1.norm_valueOnHalfLine_le (u : HalfLineH1) :
    ‖u.valueOnHalfLine‖ ≤ ‖u.value‖ := by
  exact norm_Lp_toLp_restrict_le (Ici 0) u.value

/-- Zero extension makes restriction to `[0, ∞)` preserve the value norm exactly. -/
theorem HalfLineH1.norm_valueOnHalfLine (u : HalfLineH1) :
    ‖u.valueOnHalfLine‖ = ‖u.value‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  change (eLpNorm (((LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ici 0)) u.value) : ℝ → ℝ) 2
    (volume.restrict (Ici 0))).toReal = (eLpNorm (u.value : ℝ → ℝ) 2 volume).toReal
  rw [eLpNorm_congr_ae (LpToLpRestrictCLM_coeFn ℝ (Ici 0) u.value)]
  have hzero : u.value =ᵐ[(volume : Measure ℝ).restrict (Ici 0)ᶜ] 0 := by
    apply ae_restrict_of_ae_restrict_of_subset (show (Ici (0 : ℝ))ᶜ ⊆ Iic 0 by grind)
    exact u.value_ae_eq_zero_on_nonpositive
  have hindicator : (Ici (0 : ℝ)).indicator (u.value : ℝ → ℝ) =ᵐ[volume] u.value :=
    indicator_ae_eq_of_restrict_compl_ae_eq_zero measurableSet_Ici hzero
  rw [← eLpNorm_congr_ae hindicator, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici]

/-- The half-line restriction of the weak derivative cannot increase its `L²` norm. -/
theorem HalfLineH1.norm_weakDerivOnHalfLine_le (u : HalfLineH1) :
    ‖u.weakDerivOnHalfLine‖ ≤ ‖u.weakDeriv‖ := by
  exact norm_Lp_toLp_restrict_le (Ici 0) u.weakDeriv

/-- Zero extension makes restriction to `[0, ∞)` preserve the derivative norm exactly. -/
theorem HalfLineH1.norm_weakDerivOnHalfLine (u : HalfLineH1) :
    ‖u.weakDerivOnHalfLine‖ = ‖u.weakDeriv‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  change (eLpNorm (((LpToLpRestrictCLM ℝ ℝ ℝ volume 2 (Ici 0)) u.weakDeriv) : ℝ → ℝ) 2
    (volume.restrict (Ici 0))).toReal = (eLpNorm (u.weakDeriv : ℝ → ℝ) 2 volume).toReal
  rw [eLpNorm_congr_ae (LpToLpRestrictCLM_coeFn ℝ (Ici 0) u.weakDeriv)]
  have hzero : u.weakDeriv =ᵐ[(volume : Measure ℝ).restrict (Ici 0)ᶜ] 0 := by
    apply ae_restrict_of_ae_restrict_of_subset (show (Ici (0 : ℝ))ᶜ ⊆ Iic 0 by grind)
    exact u.weakDeriv_ae_eq_zero_on_nonpositive
  have hindicator : (Ici (0 : ℝ)).indicator (u.weakDeriv : ℝ → ℝ) =ᵐ[volume] u.weakDeriv :=
    indicator_ae_eq_of_restrict_compl_ae_eq_zero measurableSet_Ici hzero
  rw [← eLpNorm_congr_ae hindicator, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici]

/-- The graph norm is exactly the half-line `H¹` norm of value and weak derivative. -/
theorem HalfLineH1.norm_sq_eq (u : HalfLineH1) :
    ‖u‖ ^ 2 = ‖u.valueOnHalfLine‖ ^ 2 + ‖u.weakDerivOnHalfLine‖ ^ 2 := by
  rw [u.norm_valueOnHalfLine, u.norm_weakDerivOnHalfLine]
  exact WithLp.prod_norm_sq_eq_of_L2 u.1

/-- Convergence in `HalfLineH1` implies convergence of values in `L²(ℝ)`. -/
theorem HalfLineH1.tendsto_value {ι : Type*} {l : Filter ι} {u : ι → HalfLineH1}
    {v : HalfLineH1} (hu : Tendsto u l (𝓝 v)) : Tendsto (fun i ↦ (u i).value) l (𝓝 v.value) :=
  HalfLineH1.value.continuous.tendsto v |>.comp hu

/-- Convergence in `HalfLineH1` implies convergence of weak derivatives in `L²(ℝ)`. -/
theorem HalfLineH1.tendsto_weakDeriv {ι : Type*} {l : Filter ι} {u : ι → HalfLineH1}
    {v : HalfLineH1} (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun i ↦ (u i).weakDeriv) l (𝓝 v.weakDeriv) :=
  HalfLineH1.weakDeriv.continuous.tendsto v |>.comp hu

end Analysis
end RayleighKernel
