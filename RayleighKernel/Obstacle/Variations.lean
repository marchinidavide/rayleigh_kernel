import RayleighKernel.Variational.Existence
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

noncomputable section

namespace RayleighKernel
namespace Analysis

open MeasureTheory Set
open scoped SchwartzMap Topology

/-- The intrinsic Rayleigh quotient is invariant under multiplication by a nonzero scalar. -/
theorem HalfLineH1.rayleighQuotient_smul {c : ℝ} (hc : c ≠ 0) (u : HalfLineH1) :
    (c • u).rayleighQuotient = u.rayleighQuotient := by
  rw [HalfLineH1.rayleighQuotient, HalfLineH1.dirichletEnergy,
    HalfLineH1.squareEnergy, HalfLineH1.rayleighQuotient,
    HalfLineH1.dirichletEnergy, HalfLineH1.squareEnergy]
  change ‖c • u.weakDeriv‖ ^ 2 / ‖c • u.value‖ ^ 2 =
    ‖u.weakDeriv‖ ^ 2 / ‖u.value‖ ^ 2
  rw [norm_smul, norm_smul]
  field_simp [hc]

/-- The intrinsic first variation of the Rayleigh quotient numerator minus its quotient multiple
of the denominator. -/
def HalfLineH1.firstVariation (f h : HalfLineH1) : ℝ :=
  inner ℝ f.weakDeriv h.weakDeriv - f.rayleighQuotient * inner ℝ f.value h.value

@[simp]
theorem HalfLineH1.firstVariation_zero_right (f : HalfLineH1) :
    f.firstVariation 0 = 0 := by
  simp [HalfLineH1.firstVariation]

theorem HalfLineH1.firstVariation_add (f h k : HalfLineH1) :
    f.firstVariation (h + k) = f.firstVariation h + f.firstVariation k := by
  simp [HalfLineH1.firstVariation, inner_add_right]
  ring_nf

theorem HalfLineH1.firstVariation_smul (f : HalfLineH1) (c : ℝ) (h : HalfLineH1) :
    f.firstVariation (c • h) = c * f.firstVariation h := by
  simp only [HalfLineH1.firstVariation, map_smul, real_inner_smul_right]
  ring_nf

/-- The scalar derivative of the intrinsic Rayleigh quotient along an affine variation. -/
theorem HalfLineH1.hasDerivAt_rayleighQuotient_smul_zero
    (f h : HalfLineH1) (hden : 0 < f.squareEnergy) :
    HasDerivAt (fun t : ℝ ↦ (f + t • h).rayleighQuotient)
      ((2 * inner ℝ f.weakDeriv h.weakDeriv * f.squareEnergy -
        f.dirichletEnergy * (2 * inner ℝ f.value h.value)) / f.squareEnergy ^ 2) 0 := by
  let A : ℝ → ℝ := fun t ↦ ‖(f + t • h).weakDeriv‖ ^ 2
  let B : ℝ → ℝ := fun t ↦ ‖(f + t • h).value‖ ^ 2
  have hlineD : HasDerivAt (fun t : ℝ ↦ (f + t • h).weakDeriv)
      h.weakDeriv 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) f.weakDeriv).add
      ((hasDerivAt_id (x := (0 : ℝ))).smul_const h.weakDeriv) using 1 <;>
      simp
    ext t
    simp
  have hlineV : HasDerivAt (fun t : ℝ ↦ (f + t • h).value)
      h.value 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) f.value).add
      ((hasDerivAt_id (x := (0 : ℝ))).smul_const h.value) using 1 <;>
      simp
    ext t
    simp
  have hA : HasDerivAt A (2 * inner ℝ f.weakDeriv h.weakDeriv) 0 := by
    simpa [A, real_inner_comm] using hlineD.norm_sq
  have hB : HasDerivAt B (2 * inner ℝ f.value h.value) 0 := by
    simpa [B, real_inner_comm] using hlineV.norm_sq
  have hq : HasDerivAt (fun t : ℝ ↦ A t / B t)
      ((2 * inner ℝ f.weakDeriv h.weakDeriv * B 0 -
        A 0 * (2 * inner ℝ f.value h.value)) / B 0 ^ 2) 0 := by
    exact hA.div hB (by simpa [B, HalfLineH1.squareEnergy] using ne_of_gt hden)
  convert hq using 1 <;>
    simp [A, B, HalfLineH1.rayleighQuotient, HalfLineH1.dirichletEnergy,
      HalfLineH1.squareEnergy]

theorem HalfLineH1.hasDerivAt_rayleighQuotient_smul_zero_eq_firstVariation
    (f h : HalfLineH1) (hden : 0 < f.squareEnergy) :
    HasDerivAt (fun t : ℝ ↦ (f + t • h).rayleighQuotient)
      (2 / f.squareEnergy * f.firstVariation h) 0 := by
  convert f.hasDerivAt_rayleighQuotient_smul_zero h hden using 1
  simp [HalfLineH1.firstVariation, HalfLineH1.rayleighQuotient,
    HalfLineH1.dirichletEnergy]
  field_simp [ne_of_gt hden]

/-- A right-sided quotient comparison implies nonnegativity of the first variation.

The comparison is expressed in terms of the right-hand secant slope so that this
lemma is independent of the particular feasibility argument producing it. -/
theorem HalfLineH1.firstVariation_nonneg_of_eventually_slope_nonneg
    (f h : HalfLineH1) (hden : 0 < f.squareEnergy)
    (hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ slope (fun s : ℝ ↦ (f + s • h).rayleighQuotient) 0 t) :
    0 ≤ f.firstVariation h := by
  have hder := f.hasDerivAt_rayleighQuotient_smul_zero_eq_firstVariation h hden
  have hnonneg_deriv : 0 ≤ 2 / f.squareEnergy * f.firstVariation h := by
    apply ge_of_tendsto hder.tendsto_slope_zero_right
    filter_upwards [hev] with t ht
    simpa [slope_def_field, div_eq_mul_inv, sub_zero, zero_add, smul_eq_mul, mul_comm] using ht
  have hcoef : 0 < 2 / f.squareEnergy := by positivity
  nlinarith [hnonneg_deriv, hcoef]

/-- Two-sided right-neighborhood quotient comparisons force the first variation to vanish. -/
theorem HalfLineH1.firstVariation_eq_zero_of_eventually_slope_nonneg
    (f h : HalfLineH1) (hden : 0 < f.squareEnergy)
    (hplus : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ slope (fun s : ℝ ↦ (f + s • h).rayleighQuotient) 0 t)
    (hminus : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ slope (fun s : ℝ ↦ (f + s • (-h)).rayleighQuotient) 0 t) :
    f.firstVariation h = 0 := by
  have hplus' := f.firstVariation_nonneg_of_eventually_slope_nonneg h hden hplus
  have hminus' := f.firstVariation_nonneg_of_eventually_slope_nonneg (-h) hden hminus
  rw [show -h = (-1 : ℝ) • h by simp, f.firstVariation_smul] at hminus'
  linarith

/-- The strict positivity set of the canonical representative. -/
def HalfLineH1.positivitySet (f : HalfLineH1) : Set ℝ :=
  {x | 0 < f.continuousRep x}

theorem HalfLineH1.isOpen_positivitySet (f : HalfLineH1) :
    IsOpen f.positivitySet := by
  exact f.continuous_continuousRep.isOpen_preimage _ isOpen_Ioi

theorem HalfLineH1.positivitySet_nonempty {L : ℝ} {f : HalfLineH1}
    (hf : f.IsAdmissible L) : f.positivitySet.Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hz : ∀ x, f.continuousRep x = 0 := by
    intro x
    by_cases hx : x ∈ halfLine
    · have hn := hf.nonnegative x hx
      have hp : ¬ 0 < f.continuousRep x := by
        intro hp
        have hmem : x ∈ f.positivitySet := hp
        rw [h] at hmem
        exact hmem.elim
      exact le_antisymm (le_of_not_gt hp) hn
    · exact f.continuousRep_eq_zero_of_nonpositive (le_of_not_ge (by simpa [halfLine] using hx))
  have hm : f.mass = 0 := by
    rw [HalfLineH1.mass, RayleighKernel.mass]
    simp_rw [hz]
    simp
  linarith [hf.mass_eq]

def PositiveTestFunction.testFirstMoment (φ : PositiveTestFunction) : ℝ :=
  ∫ x : ℝ, x * φ.1 x

def PositiveTestFunction.testMass (φ : PositiveTestFunction) : ℝ := ∫ x : ℝ, φ.1 x

lemma PositiveTestFunction.testMass_eq_mass (φ : PositiveTestFunction) :
    PositiveTestFunction.testMass φ = (PositiveTestFunction.toHalfLineH1 φ).mass := by
  rw [PositiveTestFunction.testMass, HalfLineH1.mass,
    show (PositiveTestFunction.toHalfLineH1 φ).continuousRep = φ.1 by
      funext x; exact PositiveTestFunction.continuousRep_toHalfLineH1 φ x]
  have hzero : ∀ x, x ∉ Ici 0 → φ.1 x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hts ↦ hx (by
      simpa [mem_Ici] using (φ.2 hts).le))
  rw [RayleighKernel.mass, halfLine]
  symm
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero

theorem testFirstMoment_bridge (φ : PositiveTestFunction) :
    PositiveTestFunction.testFirstMoment φ =
      (PositiveTestFunction.toHalfLineH1 φ).firstMoment := by
  rw [PositiveTestFunction.testFirstMoment,
    HalfLineH1.firstMoment, RayleighKernel.firstMoment,
    show (PositiveTestFunction.toHalfLineH1 φ).continuousRep = φ.1 by
      funext x; exact PositiveTestFunction.continuousRep_toHalfLineH1 φ x]
  have hzero : ∀ x, x ∉ Ici 0 → x * φ.1 x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hts ↦ hx (by
      simpa [mem_Ici] using (φ.2 hts).le)) |>.symm ▸ mul_zero x
  rw [halfLine]
  symm
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero

structure PositiveTestBumpIn (s : Set ℝ) where
  center : ℝ
  test : PositiveTestFunction
  center_mem : center ∈ s
  tsupport_subset : tsupport test.1 ⊆ s
  hasCompactSupport : HasCompactSupport test.1
  nonnegative : ∀ y, 0 ≤ test.1 y
  value_center : test.1 center = 1
  integrable : Integrable test.1
  firstMoment_integrable : Integrable (fun y => y * test.1 y)
  mass_pos : 0 < ∫ y : ℝ, test.1 y

lemma exists_positiveTestBumpIn
    {s : Set ℝ} {x : ℝ} (hs_open : IsOpen s) (hx : x ∈ s)
    (hs_pos : s ⊆ Ioi 0) :
    ∃ B : PositiveTestBumpIn s, B.center = x := by
  obtain ⟨g, hgs, hgc, hgd, hgr, hgx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (hs_open.mem_nhds hx)
  let sg : 𝓢(ℝ, ℝ) := hgc.toSchwartzMap (by simpa using hgd)
  let p : PositiveTestFunction := ⟨sg, hgs.trans hs_pos⟩
  have hp_nonneg : ∀ y, 0 ≤ p.1 y := by
    intro y
    exact hgr ⟨y, rfl⟩ |>.1
  have hp_center : p.1 x = 1 := by
    simpa [p, sg] using hgx
  have hp_int : Integrable p.1 := by
    change Integrable g
    exact hgd.continuous.integrable_of_hasCompactSupport hgc
  have hp_moment_int : Integrable (fun y => y * p.1 y) := by
    change Integrable (fun y => y * g y)
    exact (continuous_id.mul hgd.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hp_mass_pos : 0 < ∫ y : ℝ, p.1 y := by
    exact hgd.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hgc
      (by
        intro y
        exact hp_nonneg y)
      (by simpa [p, sg] using (show g x ≠ 0 by linarith [hgx]))
  refine ⟨⟨x, p, hx, hgs, hgc, hp_nonneg, hp_center, hp_int, hp_moment_int, hp_mass_pos⟩, rfl⟩

lemma separated_moment_determinant_pos
    {g h : ℝ → ℝ} {a b c d : ℝ}
    (hg_int : Integrable g) (hh_int : Integrable h)
    (hg_moment_int : Integrable (fun x => x * g x))
    (hh_moment_int : Integrable (fun x => x * h x))
    (hg_nonneg : ∀ x, 0 ≤ g x) (hh_nonneg : ∀ x, 0 ≤ h x)
    (hg_support : tsupport g ⊆ Ioo a b)
    (hh_support : tsupport h ⊆ Ioo c d) (hbc : b < c)
    (hg_pos : 0 < ∫ x, g x) (hh_pos : 0 < ∫ x, h x) :
    0 < (∫ x, g x) * (∫ x, x * h x) -
      (∫ x, h x) * (∫ x, x * g x) := by
  have hg_zero : ∀ x, x ∉ Ioo a b → g x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hs ↦ hx (hg_support hs))
  have hh_zero : ∀ x, x ∉ Ioo c d → h x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hs ↦ hx (hh_support hs))
  have hg_upper : ∫ x, x * g x ≤ b * ∫ x, g x := by
    calc
      (∫ x, x * g x) ≤ ∫ x, b * g x := by
        apply integral_mono (f := fun x => x * g x) (g := fun x => b * g x)
          hg_moment_int (hg_int.const_mul _)
        intro x
        by_cases hx : x ∈ Ioo a b
        · exact mul_le_mul_of_nonneg_right hx.2.le (hg_nonneg x)
        · simp [hg_zero x hx]
      _ = b * ∫ x, g x := by rw [integral_const_mul]
  have hh_lower : c * ∫ x, h x ≤ ∫ x, x * h x := by
    calc
      c * ∫ x, h x = ∫ x, c * h x := by rw [integral_const_mul]
      _ ≤ ∫ x, x * h x := by
        apply integral_mono (f := fun x => c * h x) (g := fun x => x * h x)
          (hh_int.const_mul _) hh_moment_int
        intro x
        by_cases hx : x ∈ Ioo c d
        · exact mul_le_mul_of_nonneg_right hx.1.le (hh_nonneg x)
        · simp [hh_zero x hx]
  have hgap : 0 < (c - b) * (∫ x, g x) * (∫ x, h x) := by positivity
  nlinarith

namespace HalfLineH1

structure CorrectionBumps (f : HalfLineH1) where
  bumpLeft : PositiveTestFunction
  bumpRight : PositiveTestFunction
  left_hasCompactSupport : HasCompactSupport bumpLeft.1
  right_hasCompactSupport : HasCompactSupport bumpRight.1
  left_nonnegative : ∀ x, 0 ≤ bumpLeft.1 x
  right_nonnegative : ∀ x, 0 ≤ bumpRight.1 x
  left_support : tsupport bumpLeft.1 ⊆ f.positivitySet
  right_support : tsupport bumpRight.1 ⊆ f.positivitySet
  determinant_pos : 0 <
    (PositiveTestFunction.toHalfLineH1 bumpLeft).mass *
        (PositiveTestFunction.toHalfLineH1 bumpRight).firstMoment -
      (PositiveTestFunction.toHalfLineH1 bumpRight).mass *
        (PositiveTestFunction.toHalfLineH1 bumpLeft).firstMoment

lemma exists_correctionBumps {L : ℝ} {f : HalfLineH1}
    (hf : f.IsAdmissible L) : Nonempty (CorrectionBumps f) := by
  have hpos : f.positivitySet ⊆ Ioi 0 := by
    intro y hy
    exact lt_of_not_ge fun hy0 ↦ hy.ne' (f.continuousRep_eq_zero_of_nonpositive hy0)
  obtain ⟨x, hx⟩ := f.positivitySet_nonempty hf
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (f.isOpen_positivitySet.mem_nhds hx)
  let e : ℝ := r / 8
  let a : ℝ := x - 3 * e
  let b : ℝ := x - e
  let c : ℝ := x + e
  let d : ℝ := x + 3 * e
  have he : 0 < e := by dsimp [e]; linarith
  have hleft_center : x - 2 * e ∈ Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith
  have hright_center : x + 2 * e ∈ Ioo c d := by
    constructor <;> dsimp [c, d] <;> linarith
  have hleft_ball : Ioo a b ⊆ Metric.ball x r := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [a, b, e] at hy ⊢
    constructor <;> linarith [hy.1, hy.2]
  have hright_ball : Ioo c d ⊆ Metric.ball x r := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [c, d, e] at hy ⊢
    constructor <;> linarith [hy.1, hy.2]
  have hleft : Ioo a b ⊆ f.positivitySet := hleft_ball.trans hball
  have hright : Ioo c d ⊆ f.positivitySet := hright_ball.trans hball
  obtain ⟨Bleft, hBleft⟩ := exists_positiveTestBumpIn isOpen_Ioo hleft_center
    (hleft.trans hpos)
  obtain ⟨Bright, hBright⟩ := exists_positiveTestBumpIn isOpen_Ioo hright_center
    (hright.trans hpos)
  have hdet := separated_moment_determinant_pos
    Bleft.integrable Bright.integrable Bleft.firstMoment_integrable
    Bright.firstMoment_integrable Bleft.nonnegative Bright.nonnegative
    Bleft.tsupport_subset Bright.tsupport_subset (by
      dsimp [b, c]
      linarith [he]) Bleft.mass_pos Bright.mass_pos
  have hmass_left := PositiveTestFunction.testMass_eq_mass Bleft.test
  have hmass_right := PositiveTestFunction.testMass_eq_mass Bright.test
  have hmoment_left := testFirstMoment_bridge Bleft.test
  have hmoment_right := testFirstMoment_bridge Bright.test
  refine ⟨⟨Bleft.test, Bright.test, Bleft.hasCompactSupport, Bright.hasCompactSupport,
    Bleft.nonnegative, Bright.nonnegative,
    Bleft.tsupport_subset.trans hleft, Bright.tsupport_subset.trans hright, ?_⟩⟩
  rw [← hmass_left, ← hmass_right, ← hmoment_left, ← hmoment_right]
  simpa [PositiveTestFunction.testMass, PositiveTestFunction.testFirstMoment] using hdet

end HalfLineH1

end Analysis
end RayleighKernel
