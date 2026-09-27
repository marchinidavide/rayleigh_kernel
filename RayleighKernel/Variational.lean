import RayleighKernel.Analysis.HalfLineSobolevCompactness
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!

This file records the analytic definitions used by the manuscript.  The Sobolev existence,
obstacle, and uniqueness arguments will be added in later stages of the formalization.
-/

noncomputable section

namespace RayleighKernel

open MeasureTheory Set
open scoped ENNReal Topology

/-- The closed nonnegative half-line. -/
def halfLine : Set ℝ := Set.Ici 0

/-- Total mass of a real-valued profile on the nonnegative half-line. -/
def mass (f : ℝ → ℝ) : ℝ := ∫ x in halfLine, f x

/-- First moment of a real-valued profile on the nonnegative half-line. -/
def firstMoment (f : ℝ → ℝ) : ℝ := ∫ x in halfLine, x * f x

/-- Squared `L²` energy of a profile on the nonnegative half-line. -/
def squareEnergy (f : ℝ → ℝ) : ℝ := ∫ x in halfLine, f x ^ 2

/-- Dirichlet energy, expressed using mathlib's everywhere-defined derivative. -/
def dirichletEnergy (f : ℝ → ℝ) : ℝ := ∫ x in halfLine, deriv f x ^ 2

/-- The Dirichlet Rayleigh quotient from the manuscript. -/
def rayleighQuotient (f : ℝ → ℝ) : ℝ := dirichletEnergy f / squareEnergy f

/-- The analytic conditions on a concrete representative with mean lookback `L`.

Integrability assumptions are included explicitly because the Bochner integral is defined to
be zero on nonintegrable functions. The local absolute-continuity condition is the
one-dimensional representative-level version of local `H¹` regularity used here.
-/
structure IsAdmissible (L : ℝ) (f : ℝ → ℝ) : Prop where
  nonnegative : ∀ x ∈ halfLine, 0 ≤ f x
  trace_zero : f 0 = 0
  locally_absolutelyContinuous : ∀ R, 0 < R → AbsolutelyContinuousOnInterval f 0 R
  integrable : IntegrableOn f halfLine
  firstMoment_integrable : IntegrableOn (fun x ↦ x * f x) halfLine
  square_integrable : IntegrableOn (fun x ↦ f x ^ 2) halfLine
  derivative_square_integrable : IntegrableOn (fun x ↦ deriv f x ^ 2) halfLine
  mass_eq : mass f = 1
  firstMoment_eq : firstMoment f = L

/-- A profile realizes the sharp value at lookback `L` if it is admissible and no admissible
profile has a smaller Rayleigh quotient. -/
def IsMinimizer (L : ℝ) (f : ℝ → ℝ) : Prop :=
  IsAdmissible L f ∧ ∀ g : ℝ → ℝ, IsAdmissible L g → rayleighQuotient f ≤ rayleighQuotient g

namespace Analysis

open Filter

/-- A uniform weak-derivative bound passes to the squared intrinsic Dirichlet energy of the weak
limit.  This is the fixed-bound form used when extracting bounded minimizing subsequences. -/
theorem HalfLineH1.dirichletEnergy_le_of_tendsto_inner_of_norm_weakDeriv_le
    {ι : Type*} {l : Filter ι} [NeBot l] {u : ι → HalfLineH1} {v : HalfLineH1} {C : ℝ}
    (hweak : ∀ w : HalfLineH1,
      Tendsto (fun i ↦ inner ℝ (u i) w) l (𝓝 (inner ℝ v w)))
    (hu : ∀ᶠ i in l, ‖(u i).weakDeriv‖ ≤ C) :
    ‖v.weakDeriv‖ ^ 2 ≤ C ^ 2 := by
  have hnorm := HalfLineH1.norm_weakDeriv_le_of_tendsto_inner hweak hu
  have hC : 0 ≤ C := by
    obtain ⟨i, hi⟩ := hu.exists
    exact le_trans (norm_nonneg _) hi
  exact (sq_le_sq₀ (norm_nonneg v.weakDeriv) hC).2 hnorm

/-- Total mass of the canonical representative of a half-line Sobolev element. -/
def HalfLineH1.mass (u : HalfLineH1) : ℝ :=
  RayleighKernel.mass u.continuousRep

/-- First moment of the canonical representative of a half-line Sobolev element. -/
def HalfLineH1.firstMoment (u : HalfLineH1) : ℝ :=
  RayleighKernel.firstMoment u.continuousRep

/-- Intrinsic squared `L²` energy of a half-line Sobolev element. -/
def HalfLineH1.squareEnergy (u : HalfLineH1) : ℝ :=
  ‖u.value‖ ^ 2

/-- Intrinsic Dirichlet energy of a half-line Sobolev element. -/
def HalfLineH1.dirichletEnergy (u : HalfLineH1) : ℝ :=
  ‖u.weakDeriv‖ ^ 2

/-- Intrinsic Rayleigh quotient of a half-line Sobolev element. -/
def HalfLineH1.rayleighQuotient (u : HalfLineH1) : ℝ :=
  u.dirichletEnergy / u.squareEnergy

/-- Unit mass prevents the intrinsic square-energy denominator from vanishing. -/
theorem HalfLineH1.squareEnergy_pos_of_mass_eq_one {u : HalfLineH1} (hmass : u.mass = 1) :
    0 < u.squareEnergy := by
  rw [HalfLineH1.squareEnergy]
  apply sq_pos_of_pos
  rw [norm_pos_iff]
  intro hzero
  have hmass_zero : u.mass = 0 := by
    rw [HalfLineH1.mass, RayleighKernel.mass]
    calc
      (∫ x in halfLine, u.continuousRep x) = ∫ _x in halfLine, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae u.continuousRep_ae_eq_value] with x hx
        rw [hx, hzero]
        simp
      _ = 0 := by simp
  linarith

/-- Intrinsic Dirichlet energy is weakly lower semicontinuous along a sequence with a fixed
weak-derivative bound. -/
theorem HalfLineH1.dirichletEnergy_le_liminf_of_tendsto_inner_of_bound
    {u : ℕ → HalfLineH1} {v : HalfLineH1} {B : ℝ}
    (hweak : ∀ w : HalfLineH1,
      Tendsto (fun n ↦ inner ℝ (u n) w) atTop (𝓝 (inner ℝ v w)))
    (hbound : ∀ n, ‖(u n).weakDeriv‖ ≤ B) :
    v.dirichletEnergy ≤ liminf (fun n ↦ (u n).dirichletEnergy) atTop := by
  have hBnonneg : 0 ≤ B := (norm_nonneg (u 0).weakDeriv).trans (hbound 0)
  have henergy_bound : ∀ n, (u n).dirichletEnergy ≤ B ^ 2 := by
    intro n
    rw [HalfLineH1.dirichletEnergy]
    exact (sq_le_sq₀ (norm_nonneg _) hBnonneg).2 (hbound n)
  have hcobounded : IsCoboundedUnder (· ≥ ·) atTop (fun n ↦ (u n).dirichletEnergy) :=
    isCoboundedUnder_ge_of_eventually_le atTop (x := B ^ 2)
      (Filter.Eventually.of_forall henergy_bound)
  have hliminf_nonneg : 0 ≤ liminf (fun n ↦ (u n).dirichletEnergy) atTop :=
    le_liminf_of_le hcobounded (Filter.Eventually.of_forall fun n ↦ by
      exact sq_nonneg ‖(u n).weakDeriv‖)
  by_contra hnot
  have hlt : liminf (fun n ↦ (u n).dirichletEnergy) atTop < v.dirichletEnergy :=
    lt_of_not_ge hnot
  let C : ℝ := (liminf (fun n ↦ (u n).dirichletEnergy) atTop + v.dirichletEnergy) / 2
  have hliminf_lt_C : liminf (fun n ↦ (u n).dirichletEnergy) atTop < C := by
    change liminf (fun n ↦ (u n).dirichletEnergy) atTop <
      (liminf (fun n ↦ (u n).dirichletEnergy) atTop + v.dirichletEnergy) / 2
    linarith
  have hC_lt_limit : C < v.dirichletEnergy := by
    change (liminf (fun n ↦ (u n).dirichletEnergy) atTop + v.dirichletEnergy) / 2 <
      v.dirichletEnergy
    linarith
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    have hvnonneg : 0 ≤ v.dirichletEnergy := sq_nonneg _
    positivity
  obtain ⟨ns, hns, hbelow⟩ := extraction_of_frequently_atTop
    (frequently_lt_of_liminf_lt hcobounded hliminf_lt_C)
  have hsubweak : ∀ w : HalfLineH1,
      Tendsto (fun k ↦ inner ℝ (u (ns k)) w) atTop (𝓝 (inner ℝ v w)) :=
    fun w ↦ (hweak w).comp hns.tendsto_atTop
  have hsubbound : ∀ᶠ k in atTop, ‖(u (ns k)).weakDeriv‖ ≤ Real.sqrt C := by
    apply Filter.Eventually.of_forall
    intro k
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hCnonneg]
    simpa only [HalfLineH1.dirichletEnergy] using (hbelow k).le
  have hlimit := HalfLineH1.dirichletEnergy_le_of_tendsto_inner_of_norm_weakDeriv_le
    hsubweak hsubbound
  rw [Real.sq_sqrt hCnonneg] at hlimit
  exact (not_lt_of_ge hlimit) hC_lt_limit

/-- A uniform quotient upper bound is closed under weak numerator convergence and strong
square-energy convergence. -/
theorem HalfLineH1.dirichletEnergy_le_mul_of_tendsto_squareEnergy_of_rayleighQuotient_le
    {u : ℕ → HalfLineH1} {v : HalfLineH1} {Q : ℝ}
    (hweak : ∀ w : HalfLineH1,
      Tendsto (fun n ↦ inner ℝ (u n) w) atTop (𝓝 (inner ℝ v w)))
    (hsquare : Tendsto (fun n ↦ (u n).squareEnergy) atTop (𝓝 v.squareEnergy))
    (hpositive : ∀ n, 0 < (u n).squareEnergy)
    (hquot : ∀ n, (u n).rayleighQuotient ≤ Q) :
    v.dirichletEnergy ≤ Q * v.squareEnergy := by
  have hQnonneg : 0 ≤ Q := by
    have hquot_nonneg : 0 ≤ (u 0).rayleighQuotient := by
      rw [HalfLineH1.rayleighQuotient]
      exact div_nonneg (sq_nonneg _) (le_of_lt (hpositive 0))
    exact hquot_nonneg.trans (hquot 0)
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hprod : Tendsto (fun n ↦ Q * (u n).squareEnergy) atTop
      (𝓝 (Q * v.squareEnergy)) := tendsto_const_nhds.mul hsquare
  have hevent : ∀ᶠ n in atTop,
      Q * (u n).squareEnergy < Q * v.squareEnergy + ε :=
    hprod.eventually_lt_const (by linarith)
  have htarget_nonneg : 0 ≤ Q * v.squareEnergy + ε := by
    have hvsquare : 0 ≤ v.squareEnergy := sq_nonneg _
    positivity
  have hnorm : ∀ᶠ n in atTop,
      ‖(u n).weakDeriv‖ ≤ Real.sqrt (Q * v.squareEnergy + ε) := by
    filter_upwards [hevent] with n hn
    have henergy : (u n).dirichletEnergy ≤ Q * (u n).squareEnergy := by
      have hq := hquot n
      rw [HalfLineH1.rayleighQuotient, div_le_iff₀ (hpositive n)] at hq
      exact hq
    rw [HalfLineH1.dirichletEnergy] at henergy
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt htarget_nonneg]
    exact henergy.trans hn.le
  have hlimit := HalfLineH1.dirichletEnergy_le_of_tendsto_inner_of_norm_weakDeriv_le
    hweak hnorm
  rw [Real.sq_sqrt htarget_nonneg] at hlimit
  exact hlimit

/-- A uniform quotient upper bound passes to a weak limit when the square energies converge and the
limiting denominator is positive. -/
theorem HalfLineH1.rayleighQuotient_le_of_tendsto_squareEnergy_of_le
    {u : ℕ → HalfLineH1} {v : HalfLineH1} {Q : ℝ}
    (hweak : ∀ w : HalfLineH1,
      Tendsto (fun n ↦ inner ℝ (u n) w) atTop (𝓝 (inner ℝ v w)))
    (hsquare : Tendsto (fun n ↦ (u n).squareEnergy) atTop (𝓝 v.squareEnergy))
    (hpositive : ∀ n, 0 < (u n).squareEnergy)
    (hvpositive : 0 < v.squareEnergy)
    (hquot : ∀ n, (u n).rayleighQuotient ≤ Q) :
    v.rayleighQuotient ≤ Q := by
  rw [HalfLineH1.rayleighQuotient, div_le_iff₀ hvpositive]
  exact HalfLineH1.dirichletEnergy_le_mul_of_tendsto_squareEnergy_of_rayleighQuotient_le
    hweak hsquare hpositive hquot

/-- The manuscript's admissibility conditions on the representative-free half-line Sobolev
space.  Trace, local absolute continuity, and both quadratic integrability conditions are built into
`HalfLineH1`; only positivity, the two `L¹` conditions, and normalization remain as fields. -/
structure HalfLineH1.IsAdmissible (L : ℝ) (u : HalfLineH1) : Prop where
  nonnegative : ∀ x ∈ halfLine, 0 ≤ u.continuousRep x
  integrable : IntegrableOn u.continuousRep halfLine
  firstMoment_integrable : IntegrableOn (fun x ↦ x * u.continuousRep x) halfLine
  mass_eq : u.mass = 1
  firstMoment_eq : u.firstMoment = L

/-- A Sobolev element realizes the sharp value at lookback `L` if it is admissible and minimizes the
intrinsic quotient over all admissible Sobolev elements. -/
def HalfLineH1.IsMinimizer (L : ℝ) (u : HalfLineH1) : Prop :=
  u.IsAdmissible L ∧
    ∀ v : HalfLineH1, v.IsAdmissible L → u.rayleighQuotient ≤ v.rayleighQuotient

/-- The set of intrinsic Rayleigh quotient values at lookback `L`. -/
def admissibleQuotients (L : ℝ) : Set ℝ :=
  {q | ∃ u : HalfLineH1, u.IsAdmissible L ∧ u.rayleighQuotient = q}

/-- The intrinsic sharp Rayleigh value. -/
def Lambda (L : ℝ) : ℝ := sInf (admissibleQuotients L)

theorem admissibleQuotients_nonempty {L : ℝ} {u : HalfLineH1}
    (hu : u.IsAdmissible L) : (admissibleQuotients L).Nonempty :=
  ⟨u.rayleighQuotient, u, hu, rfl⟩

theorem admissibleQuotients_bddBelow (L : ℝ) : BddBelow (admissibleQuotients L) := by
  refine ⟨0, ?_⟩
  rintro q ⟨u, hu, rfl⟩
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem Lambda_le_of_isAdmissible {L : ℝ} {u : HalfLineH1} (hu : u.IsAdmissible L) :
    Lambda L ≤ u.rayleighQuotient := by
  exact csInf_le (admissibleQuotients_bddBelow L) ⟨u, hu, rfl⟩

theorem exists_minimizing_sequence {L : ℝ} {hL : (admissibleQuotients L).Nonempty} :
    ∃ u : ℕ → HalfLineH1, (∀ n, (u n).IsAdmissible L) ∧
      Tendsto (fun n ↦ (u n).rayleighQuotient) atTop (𝓝 (Lambda L)) := by
  obtain ⟨q, hmono, hq, hq_mem⟩ := exists_seq_tendsto_sInf hL
    (admissibleQuotients_bddBelow L)
  choose u hu hquot using hq_mem
  refine ⟨u, hu, ?_⟩
  simpa only [Lambda, hquot] using hq

/-- Any minimizing sequence has an eventual uniform quotient bound. -/
theorem eventually_rayleighQuotient_le_of_tendsto_minimizing
    {L : ℝ} {q : ℕ → ℝ} (hq : Tendsto q atTop (𝓝 (Lambda L))) :
    ∃ Q : ℝ, ∀ᶠ n in atTop, q n ≤ Q := by
  have hpos : 0 < (1 : ℝ) := by norm_num
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hq (1 : ℝ) hpos
  refine ⟨Lambda L + 2, eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩⟩
  have h := hN n hn
  rw [Real.dist_eq, abs_lt] at h
  linarith

/-- The representative-level square energy agrees with the squared norm of the stored `L²`
value. -/
theorem HalfLineH1.squareEnergy_continuousRep (u : HalfLineH1) :
    RayleighKernel.squareEnergy u.continuousRep = u.squareEnergy := by
  simpa only [RayleighKernel.squareEnergy, HalfLineH1.squareEnergy, halfLine] using
    u.integral_continuousRep_sq_Ici_eq_norm_value_sq

/-- The representative-level Dirichlet energy agrees with the squared norm of the stored weak
derivative. -/
theorem HalfLineH1.dirichletEnergy_continuousRep (u : HalfLineH1) :
    RayleighKernel.dirichletEnergy u.continuousRep = u.dirichletEnergy := by
  simpa only [RayleighKernel.dirichletEnergy, HalfLineH1.dirichletEnergy, halfLine] using
    u.integral_deriv_continuousRep_sq_Ici_eq_norm_weakDeriv_sq

/-- The representative-level Rayleigh quotient is the intrinsic quotient of the stored `L²`
value and weak derivative. -/
theorem HalfLineH1.rayleighQuotient_continuousRep (u : HalfLineH1) :
    RayleighKernel.rayleighQuotient u.continuousRep = u.rayleighQuotient := by
  rw [RayleighKernel.rayleighQuotient, u.dirichletEnergy_continuousRep,
    u.squareEnergy_continuousRep]
  rfl

/-- To prove that a canonical Sobolev representative is admissible in the interim concrete API,
it remains only to establish nonnegativity, the two `L¹` conditions, and the two constraints.  All
Sobolev regularity and quadratic-integrability fields are automatic. -/
theorem HalfLineH1.isAdmissible_continuousRep {L : ℝ} (u : HalfLineH1)
    (h_nonnegative : ∀ x ∈ halfLine, 0 ≤ u.continuousRep x)
    (h_integrable : IntegrableOn u.continuousRep halfLine)
    (h_firstMoment_integrable : IntegrableOn (fun x ↦ x * u.continuousRep x) halfLine)
    (h_mass : RayleighKernel.mass u.continuousRep = 1)
    (h_firstMoment : RayleighKernel.firstMoment u.continuousRep = L) :
    RayleighKernel.IsAdmissible L u.continuousRep where
  nonnegative := h_nonnegative
  trace_zero := u.continuousRep_zero
  locally_absolutelyContinuous := fun R _ ↦
    u.continuousRep_absolutelyContinuousOnInterval 0 R
  integrable := h_integrable
  firstMoment_integrable := h_firstMoment_integrable
  square_integrable := u.continuousRep_sq_integrable.integrableOn
  derivative_square_integrable := u.deriv_continuousRep_sq_integrable.integrableOn
  mass_eq := h_mass
  firstMoment_eq := h_firstMoment

/-- Intrinsic Sobolev admissibility is exactly concrete admissibility of the canonical
representative. -/
theorem HalfLineH1.isAdmissible_iff_isAdmissible_continuousRep {L : ℝ} (u : HalfLineH1) :
    u.IsAdmissible L ↔ RayleighKernel.IsAdmissible L u.continuousRep := by
  constructor
  · intro h
    exact u.isAdmissible_continuousRep h.nonnegative h.integrable
      h.firstMoment_integrable h.mass_eq h.firstMoment_eq
  · intro h
    exact
      { nonnegative := h.nonnegative
        integrable := h.integrable
        firstMoment_integrable := h.firstMoment_integrable
        mass_eq := h.mass_eq
        firstMoment_eq := h.firstMoment_eq }

/-- A canonical representative that minimizes the interim concrete problem also minimizes the
intrinsic Sobolev problem.  The converse will follow from the remaining converse Sobolev
representation theorem. -/
theorem HalfLineH1.isMinimizer_of_isMinimizer_continuousRep {L : ℝ} {u : HalfLineH1}
    (hu : RayleighKernel.IsMinimizer L u.continuousRep) : u.IsMinimizer L := by
  refine ⟨u.isAdmissible_iff_isAdmissible_continuousRep.mpr hu.1, ?_⟩
  intro v hv
  rw [← u.rayleighQuotient_continuousRep, ← v.rayleighQuotient_continuousRep]
  exact hu.2 v.continuousRep (v.isAdmissible_iff_isAdmissible_continuousRep.mp hv)

/-- Markov's first-moment bound for the mass in `[R, ∞)`. -/
theorem HalfLineH1.tailMass_le_firstMoment_div {L R : ℝ} {u : HalfLineH1}
    (hu : u.IsAdmissible L) (hR : 0 < R) :
    (∫ x in Ici R, u.continuousRep x) ≤ L / R := by
  have hsubset : Ici R ⊆ halfLine := by
    intro x hx
    exact le_trans hR.le hx
  have htail_integrable : IntegrableOn u.continuousRep (Ici R) :=
    hu.integrable.mono_set hsubset
  have hmoment_tail_integrable :
      IntegrableOn (fun x ↦ x * u.continuousRep x) (Ici R) :=
    hu.firstMoment_integrable.mono_set hsubset
  calc
    (∫ x in Ici R, u.continuousRep x) ≤
        ∫ x in Ici R, R⁻¹ * (x * u.continuousRep x) := by
      apply setIntegral_mono_ae_restrict htail_integrable
        (hmoment_tail_integrable.const_mul R⁻¹)
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      have hnonneg := hu.nonnegative x (hsubset hx)
      calc
        u.continuousRep x = R⁻¹ * (R * u.continuousRep x) := by field_simp
        _ ≤ R⁻¹ * (x * u.continuousRep x) := by
          gcongr
          exact hx
    _ = R⁻¹ * ∫ x in Ici R, x * u.continuousRep x := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ R⁻¹ * ∫ x in halfLine, x * u.continuousRep x := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hR.le)
      apply setIntegral_mono_set hu.firstMoment_integrable
      · filter_upwards [ae_restrict_mem (μ := volume) (s := halfLine) measurableSet_Ici] with x hx
        exact mul_nonneg hx (hu.nonnegative x hx)
      · exact Filter.Eventually.of_forall hsubset
    _ = R⁻¹ * L := by exact congrArg (R⁻¹ * ·) hu.firstMoment_eq
    _ = L / R := by rw [div_eq_mul_inv, mul_comm]

/-- The square-energy tail is controlled by the mass tail and the global Sobolev supremum bound. -/
theorem HalfLineH1.tailSquareEnergy_le_of_isAdmissible {L R : ℝ} {u : HalfLineH1}
    (hu : u.IsAdmissible L) (hR : 0 < R) :
    (∫ x in Ici R, u.continuousRep x ^ 2) ≤
      Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) *
        (∫ x in Ici R, u.continuousRep x) := by
  have hsubset : Ici R ⊆ halfLine := by
    intro x hx
    exact le_trans hR.le hx
  have hleft : IntegrableOn (fun x ↦ u.continuousRep x ^ 2) (Ici R) :=
    u.continuousRep_sq_integrable.integrableOn.mono_set hsubset
  have hright : IntegrableOn
      (fun x ↦ Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) * u.continuousRep x) (Ici R) :=
    (hu.integrable.mono_set hsubset).const_mul _
  have hnonneg : 0 ≤ 2 * ‖u.value‖ * ‖u.weakDeriv‖ := by positivity
  calc
    (∫ x in Ici R, u.continuousRep x ^ 2) ≤
        ∫ x in Ici R, Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) *
          u.continuousRep x := by
      apply setIntegral_mono_ae_restrict hleft hright
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      have hu_nonneg : 0 ≤ u.continuousRep x := hu.nonnegative x (hsubset hx)
      have hpoint := u.continuousRep_sq_le x
      have hsqrt : 0 ≤ Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) := Real.sqrt_nonneg _
      have hsqrt_sq : (Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖)) ^ 2 =
          2 * ‖u.value‖ * ‖u.weakDeriv‖ := Real.sq_sqrt hnonneg
      have hz : u.continuousRep x ≤ Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) := by
        nlinarith [sq_nonneg (Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) +
          u.continuousRep x)]
      calc
        u.continuousRep x ^ 2 = u.continuousRep x * u.continuousRep x := by ring
        _ ≤ Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) * u.continuousRep x :=
          mul_le_mul_of_nonneg_right hz hu_nonneg
    _ = Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) *
        (∫ x in Ici R, u.continuousRep x) := by
      rw [← MeasureTheory.integral_const_mul]

/-- A nonnegative tail is controlled by its mass and a pointwise supremum bound. -/
theorem HalfLineH1.tailSquareEnergy_le_of_nonnegative_of_le {R S : ℝ} {u : HalfLineH1}
    (hnonneg : ∀ x ∈ Ici R, 0 ≤ u.continuousRep x)
    (hsup : ∀ x ∈ Ici R, u.continuousRep x ≤ S)
    (hInt : IntegrableOn u.continuousRep (Ici R)) :
    (∫ x in Ici R, u.continuousRep x ^ 2) ≤
      S * (∫ x in Ici R, u.continuousRep x) := by
  have hleft : IntegrableOn (fun x => u.continuousRep x ^ 2) (Ici R) :=
    u.continuousRep_sq_integrable.integrableOn
  have hright : IntegrableOn (fun x => S * u.continuousRep x) (Ici R) := hInt.const_mul S
  calc
    (∫ x in Ici R, u.continuousRep x ^ 2) ≤
        ∫ x in Ici R, S * u.continuousRep x := by
      apply setIntegral_mono_ae_restrict hleft hright
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      simpa only [pow_two] using
        (mul_le_mul_of_nonneg_right (hsup x hx) (hnonneg x hx))
    _ = S * (∫ x in Ici R, u.continuousRep x) := by
      rw [← MeasureTheory.integral_const_mul]

/-- A unit-length initial interval and a tail-mass envelope give a uniform half-line `L¹` bound. -/
theorem HalfLineH1.integral_continuousRep_Ici_zero_le_add_of_tailMass
    {E B : ℝ} {u : HalfLineH1} (hB : ‖u.weakDeriv‖ ≤ B)
    (hInt : IntegrableOn u.continuousRep (Ici 0))
    (hTail : ∫ x in Ici 1, u.continuousRep x ≤ E) :
    ∫ x in Ici 0, u.continuousRep x ≤ B + E := by
  have hsub : Ico (0 : ℝ) 1 ∪ Ici 1 = Ici 0 := Ico_union_Ici_eq_Ici (by norm_num)
  have htailInt : IntegrableOn u.continuousRep (Ici 1) :=
    hInt.mono_set (show Ici (1 : ℝ) ⊆ Ici 0 by
      intro x hx
      exact le_trans (show (0 : ℝ) ≤ 1 by norm_num) hx)
  have hsplit : (∫ x in Ico (0 : ℝ) 1, u.continuousRep x) +
      ∫ x in Ici 1, u.continuousRep x = ∫ x in Ici 0, u.continuousRep x := by
    rw [← setIntegral_union (μ := volume)
      (Set.disjoint_left.mpr (by
        intro x hx hy
        exact (not_lt_of_ge hy) hx.2)) measurableSet_Ici
      (hInt.mono_set (by intro x hx; exact hx.1)) htailInt]
    rw [hsub]
  have hsmall : ∫ x in Ico (0 : ℝ) 1, u.continuousRep x ≤ B := by
    calc
      (∫ x in Ico (0 : ℝ) 1, u.continuousRep x) ≤
          ∫ _ in Ico (0 : ℝ) 1, B := by
        apply setIntegral_mono_on (hInt.mono_set (by intro x hx; exact hx.1))
          (integrableOn_const (by simp [Real.volume_Ico]) (by simp)) measurableSet_Ico
        intro x hx
        have hz := u.continuousRep_eq_zero_of_nonpositive (by norm_num : (0 : ℝ) ≤ 0)
        have hdist : |u.continuousRep x| ≤ Real.sqrt |x - 0| * ‖u.weakDeriv‖ := by
          simpa [hz, abs_sub_comm] using u.abs_continuousRep_sub_le x 0
        have hsqrt : Real.sqrt |x - 0| ≤ 1 := by
          rw [Real.sqrt_le_iff]
          constructor
          · positivity
          · simpa only [sub_zero, one_pow] using
              (abs_of_nonneg hx.1).trans_le (le_of_lt hx.2)
        have habs : |u.continuousRep x| ≤ B := by
          calc
            |u.continuousRep x| ≤ Real.sqrt |x - 0| * ‖u.weakDeriv‖ := hdist
            _ ≤ 1 * B := mul_le_mul hsqrt hB (by positivity) (by positivity)
            _ = B := one_mul _
        exact le_trans (le_abs_self _) habs
      _ = B := by simp
  rw [← hsplit]
  linarith

 theorem HalfLineH1.tendsto_uniform_tailSquareEnergy_of_tailMass
    {B : ℝ} {u : ℕ → HalfLineH1} {η : ℝ → ℝ}
    (hnonneg : ∀ n x, x ∈ Ici (0 : ℝ) → 0 ≤ (u n).continuousRep x)
    (hInt : ∀ n, IntegrableOn (u n).continuousRep (Ici 0))
    (hB : ∀ n, ‖(u n).weakDeriv‖ ≤ B)
    (hTail : ∀ n R, 0 ≤ R →
      (∫ x in Ici R, (u n).continuousRep x) ≤ η R)
    (hη : Tendsto η atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ R in atTop, ∀ n,
      (∫ x in Ici R, (u n).continuousRep x ^ 2) < ε := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg ((u 0).weakDeriv)) (hB 0)
  have hη1 : 0 ≤ η 1 := by
    exact le_trans
      (setIntegral_nonneg measurableSet_Ici (fun x hx => hnonneg 0 x
        (le_trans (show (0 : ℝ) ≤ 1 by norm_num) hx)))
      (hTail 0 1 (by norm_num))
  let M : ℝ := B + η 1
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  let A : ℝ := 1 + 2 * M ^ 2 * B
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hnorm : ∀ n, ‖(u n).value‖ ≤ A := by
    intro n
    have hWhole := (u n).continuousRep_integrable_of_integrableOn_halfLine (hInt n)
    have hL1 : (∫ x : ℝ, |(u n).continuousRep x|) ≤ M := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
        rw [(u n).continuousRep_eq_zero_of_nonpositive (le_of_not_ge hx), abs_zero])]
      calc
        (∫ x in Ici 0, |(u n).continuousRep x|) =
            ∫ x in Ici 0, (u n).continuousRep x := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
          rw [abs_of_nonneg (hnonneg n x hx)]
        _ ≤ B + η 1 := (u n).integral_continuousRep_Ici_zero_le_add_of_tailMass
          (hB n) (hInt n) (hTail n 1 (by norm_num))
    have hcube : ‖(u n).value‖ ^ 3 ≤ 2 * M ^ 2 * B := by
      have hGN := (u n).norm_value_cubed_le hWhole
      calc
        ‖(u n).value‖ ^ 3 ≤ 2 * (∫ x : ℝ, |(u n).continuousRep x|) ^ 2 *
            ‖(u n).weakDeriv‖ := hGN
        _ ≤ 2 * M ^ 2 * B := by
          calc
            2 * (∫ x : ℝ, |(u n).continuousRep x|) ^ 2 * ‖(u n).weakDeriv‖ ≤
                2 * M ^ 2 * ‖(u n).weakDeriv‖ := by
              have hMnonneg : 0 ≤ M := hM0
              have hI0 : 0 ≤ ∫ x : ℝ, |(u n).continuousRep x| :=
                integral_nonneg (fun _ => abs_nonneg _)
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hI0 hL1 2) (by positivity))
                (norm_nonneg _)
            _ ≤ 2 * M ^ 2 * B := by
              gcongr
              exact hB n
    by_cases hone : ‖(u n).value‖ ≤ 1
    · exact hone.trans (by dsimp [A]; nlinarith [hM0, hB0])
    · have hself : ‖(u n).value‖ ≤ ‖(u n).value‖ ^ 3 := by
        nlinarith [norm_nonneg (u n).value, sq_nonneg (‖(u n).value‖ - 1)]
      calc
        ‖(u n).value‖ ≤ ‖(u n).value‖ ^ 3 := hself
        _ ≤ 2 * M ^ 2 * B := hcube
        _ ≤ A := by dsimp [A]; nlinarith
  let S : ℝ := Real.sqrt (2 * A * B)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hbound : ∀ n R, 0 ≤ R →
      (∫ x in Ici R, (u n).continuousRep x ^ 2) ≤ S * η R := by
    intro n R hR
    have htailInt : IntegrableOn (u n).continuousRep (Ici R) :=
      (hInt n).mono_set (by intro x hx; exact le_trans hR hx)
    apply ((u n).tailSquareEnergy_le_of_nonnegative_of_le
      (fun x hx => hnonneg n x (le_trans hR hx))
      (fun x hx => ?_) htailInt).trans
    · exact mul_le_mul_of_nonneg_left (hTail n R hR) hS0
    · have hpoint := (u n).continuousRep_sq_le x
      have hnonnegx := hnonneg n x (le_trans hR hx)
      have hn := hnorm n
      have hd := hB n
      have hprod : 2 * ‖(u n).value‖ * ‖(u n).weakDeriv‖ ≤ 2 * A * B := by
        calc
          2 * ‖(u n).value‖ * ‖(u n).weakDeriv‖ ≤
              2 * A * ‖(u n).weakDeriv‖ := by gcongr
          _ ≤ 2 * A * B := by gcongr
      have hsqrt : Real.sqrt (2 * ‖(u n).value‖ * ‖(u n).weakDeriv‖) ≤ S := by
        dsimp [S]
        exact Real.sqrt_le_sqrt hprod
      have hsq : S ^ 2 = 2 * A * B := by
        dsimp [S]
        exact Real.sq_sqrt (by positivity)
      have hle : (u n).continuousRep x ≤ S := by
        nlinarith [sq_nonneg (S + (u n).continuousRep x)]
      exact hle
  intro ε hε
  have hlim : Tendsto (fun R => S * η R) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hη)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim ε hε
  filter_upwards [eventually_ge_atTop (0 : ℝ), eventually_ge_atTop N] with R hR hN' n
  have hsmall := hN R hN'
  have hηR : 0 ≤ η R := le_trans
    (setIntegral_nonneg measurableSet_Ici (fun x hx => hnonneg 0 x (le_trans hR hx)))
    (hTail 0 R hR)
  have hprod : 0 ≤ S * η R := mul_nonneg hS0 hηR
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hprod] at hsmall
  exact (hbound n R hR).trans_lt hsmall

/-- The denominator cannot degenerate under the unit-mass and first-moment constraints.  This is
Lemma `lem:l2` in the manuscript. -/
theorem HalfLineH1.one_div_eight_mul_le_squareEnergy {L : ℝ} {u : HalfLineH1}
    (hu : u.IsAdmissible L) (hL : 0 < L) :
    1 / (8 * L) ≤ u.squareEnergy := by
  let s : Set ℝ := Ico 0 (2 * L)
  have hs : MeasurableSet s := measurableSet_Ico
  have hμs : volume s ≠ ∞ := by
    rw [Real.volume_Ico]
    finiteness
  let χ : RealL2 := indicatorConstLp 2 hs hμs 1
  have hinner : inner ℝ χ u.value = ∫ x in s, (u.value : ℝ → ℝ) x := by
    simpa [χ] using L2.inner_indicatorConstLp_one hs hμs u.value
  have hnorm : ‖χ‖ = Real.sqrt (2 * L) := by
    simp only [χ]
    rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top]
    simp [s, Real.volume_Ico, Measure.real, hL.le, Real.sqrt_eq_rpow]
  have hvalue_integral : (∫ x in s, (u.value : ℝ → ℝ) x) =
      ∫ x in s, u.continuousRep x := by
    apply integral_congr_ae
    exact ae_restrict_of_ae u.continuousRep_ae_eq_value.symm
  have htail : (∫ x in Ici (2 * L), u.continuousRep x) ≤ 1 / 2 := by
    have h := HalfLineH1.tailMass_le_firstMoment_div hu (by positivity : 0 < 2 * L)
    calc
      (∫ x in Ici (2 * L), u.continuousRep x) ≤ L / (2 * L) := h
      _ = 1 / 2 := by field_simp
  have hsplit : (∫ x in s, u.continuousRep x) +
      ∫ x in Ici (2 * L), u.continuousRep x = 1 := by
    rw [← setIntegral_union (by
        apply Set.disjoint_left.mpr
        intro x hxs hxt
        exact (not_lt_of_ge hxt) hxs.2)
      measurableSet_Ici
      (hu.integrable.mono_set (by intro x hx; exact hx.1))
      (hu.integrable.mono_set (by intro x hx; exact le_trans (by positivity : 0 ≤ 2 * L) hx))]
    rw [Ico_union_Ici_eq_Ici (by positivity)]
    exact hu.mass_eq
  have hhalf : 1 / 2 ≤ ∫ x in s, u.continuousRep x := by
    linarith
  have hCS : |∫ x in s, u.continuousRep x| ≤ Real.sqrt (2 * L) * ‖u.value‖ := by
    rw [← hvalue_integral, ← hinner, ← hnorm]
    exact abs_real_inner_le_norm χ u.value
  have hnormlower : 1 / 2 ≤ Real.sqrt (2 * L) * ‖u.value‖ :=
    hhalf.trans (le_abs_self _ |>.trans hCS)
  rw [HalfLineH1.squareEnergy]
  have hsqrt : Real.sqrt (2 * L) ^ 2 = 2 * L := Real.sq_sqrt (by positivity)
  have hmul : 1 / 4 ≤ (Real.sqrt (2 * L) * ‖u.value‖) ^ 2 := by
    nlinarith
  rw [mul_pow, hsqrt] at hmul
  rw [div_le_iff₀' (by positivity : 0 < 8 * L)]
  nlinarith

/-- For a nonnegative admissible profile of unit mass, the polynomial
Gagliardo--Nirenberg estimate simplifies to `‖u‖₂³ ≤ 2 ‖u'‖₂`. -/
theorem HalfLineH1.norm_value_cubed_le_two_mul_norm_weakDeriv {L : ℝ} {u : HalfLineH1}
    (hu : u.IsAdmissible L) : ‖u.value‖ ^ 3 ≤ 2 * ‖u.weakDeriv‖ := by
  have hWhole : Integrable u.continuousRep :=
    u.continuousRep_integrable_of_integrableOn_halfLine hu.integrable
  have hL1 : (∫ x : ℝ, |u.continuousRep x|) = 1 := by
    calc
      (∫ x : ℝ, |u.continuousRep x|) = ∫ x in halfLine, |u.continuousRep x| := by
        apply (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_).symm
        rw [u.continuousRep_eq_zero_of_nonpositive
          (le_of_not_ge (by simpa only [halfLine, mem_Ici] using hx)), abs_zero]
      _ = ∫ x in halfLine, u.continuousRep x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
        rw [abs_of_nonneg (hu.nonnegative x hx)]
      _ = 1 := hu.mass_eq
  simpa only [hL1, one_pow, mul_one] using u.norm_value_cubed_le hWhole

/-- A common derivative bound turns the first-moment tail estimate into a quantitative square-energy
tail estimate. -/
theorem HalfLineH1.tailSquareEnergy_le_of_norm_weakDeriv_le {L R B : ℝ} {u : HalfLineH1}
    (hu : u.IsAdmissible L) (hR : 0 < R) (hB : ‖u.weakDeriv‖ ≤ B) :
    (∫ x in Ici R, u.continuousRep x ^ 2) ≤
      Real.sqrt (2 * (1 + 2 * B) * B) * (L / R) := by
  have hBnonneg : 0 ≤ B := le_trans (norm_nonneg _) hB
  have hvalue : ‖u.value‖ ≤ 1 + 2 * B := by
    by_cases hone : ‖u.value‖ ≤ 1
    · exact hone.trans (by nlinarith)
    · have hself : ‖u.value‖ ≤ ‖u.value‖ ^ 3 := by
        nlinarith [norm_nonneg u.value, sq_nonneg (‖u.value‖ - 1)]
      have hGN := HalfLineH1.norm_value_cubed_le_two_mul_norm_weakDeriv hu
      exact hself.trans (hGN.trans (by nlinarith [pow_nonneg hBnonneg 3]))
  have hprod : 2 * ‖u.value‖ * ‖u.weakDeriv‖ ≤ 2 * (1 + 2 * B) * B := by
    calc
      2 * ‖u.value‖ * ‖u.weakDeriv‖ ≤
          2 * (1 + 2 * B) * ‖u.weakDeriv‖ := by
        gcongr
      _ ≤ 2 * (1 + 2 * B) * B := by
        gcongr
  have hsqrt : Real.sqrt (2 * ‖u.value‖ * ‖u.weakDeriv‖) ≤
      Real.sqrt (2 * (1 + 2 * B) * B) := Real.sqrt_le_sqrt hprod
  have htail := HalfLineH1.tailMass_le_firstMoment_div hu hR
  have htail_nonneg : 0 ≤ ∫ x in Ici R, u.continuousRep x :=
    setIntegral_nonneg measurableSet_Ici fun x hx ↦ hu.nonnegative x (le_trans hR.le hx)
  have hroot_nonneg : 0 ≤ Real.sqrt (2 * (1 + 2 * B) * B) := Real.sqrt_nonneg _
  have hLR_nonneg : 0 ≤ L / R := by
    have hL : 0 ≤ L := by
      have h := hu.firstMoment_eq
      have hmass : 0 ≤ u.firstMoment := by
        rw [HalfLineH1.firstMoment]
        exact setIntegral_nonneg measurableSet_Ici fun x hx ↦
          mul_nonneg hx (hu.nonnegative x (by simpa [halfLine] using hx))
      linarith
    positivity
  exact (HalfLineH1.tailSquareEnergy_le_of_isAdmissible hu hR).trans (by
    gcongr)

/-- The preceding tail estimate is uniform over an admissible sequence with a common derivative
bound. -/
theorem HalfLineH1.tailSquareEnergy_le_of_isAdmissible_seq_of_norm_weakDeriv_le
    {L B R : ℝ} {u : ℕ → HalfLineH1} (hu : ∀ n, (u n).IsAdmissible L)
    (hB : ∀ n, ‖(u n).weakDeriv‖ ≤ B) (hR : 0 < R) (n : ℕ) :
    (∫ x in Ici R, (u n).continuousRep x ^ 2) ≤
      Real.sqrt (2 * (1 + 2 * B) * B) * (L / R) :=
  HalfLineH1.tailSquareEnergy_le_of_norm_weakDeriv_le (hu n) hR (hB n)

/-- The explicit uniform square-energy tail bound tends to zero as the cutoff tends to infinity. -/
theorem HalfLineH1.tendsto_uniform_tailSquareEnergy_bound {L B : ℝ} :
    Tendsto (fun R : ℝ ↦ Real.sqrt (2 * (1 + 2 * B) * B) * (L / R))
      atTop (𝓝 0) := by
  simpa only [div_eq_mul_inv, mul_zero] using
    (tendsto_const_nhds.mul
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero :
        Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0))))

/-- A bounded intrinsic quotient gives an explicit weak-derivative bound for an admissible
profile. -/
theorem HalfLineH1.norm_weakDeriv_le_of_rayleighQuotient_le {L Q : ℝ} {u : HalfLineH1}
    (hu : u.IsAdmissible L) (hQ : u.rayleighQuotient ≤ Q) :
    ‖u.weakDeriv‖ ≤ 1 + 4 * Q ^ 3 := by
  have hvalue_pos : 0 < ‖u.value‖ := by
    apply norm_pos_iff.mpr
    intro hzero
    have hmass_zero : u.mass = 0 := by
      rw [HalfLineH1.mass, RayleighKernel.mass]
      calc
        (∫ x in halfLine, u.continuousRep x) = ∫ _x in halfLine, (0 : ℝ) := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae u.continuousRep_ae_eq_value] with x hx
          rw [hx, hzero]
          simp
        _ = 0 := by simp
    linarith [hu.mass_eq]
  have hquot : ‖u.weakDeriv‖ ^ 2 ≤ Q * ‖u.value‖ ^ 2 := by
    rw [HalfLineH1.rayleighQuotient, HalfLineH1.dirichletEnergy,
      HalfLineH1.squareEnergy, div_le_iff₀ (sq_pos_of_pos hvalue_pos)] at hQ
    exact hQ
  have hQnonneg : 0 ≤ Q := by
    by_contra hQneg
    have : u.rayleighQuotient < 0 := hQ.trans_lt (lt_of_not_ge hQneg)
    exact (not_lt_of_ge (div_nonneg (sq_nonneg _) (sq_nonneg _))) this
  have hGN := HalfLineH1.norm_value_cubed_le_two_mul_norm_weakDeriv hu
  rcases (norm_nonneg u.weakDeriv).eq_or_lt with hzero | hderiv_pos
  · rw [← hzero]
    positivity
  · have hquot_cube := pow_le_pow_left₀ (sq_nonneg ‖u.weakDeriv‖) hquot 3
    have hGN_sq := pow_le_pow_left₀ (by positivity : 0 ≤ ‖u.value‖ ^ 3) hGN 2
    have hscaled := mul_le_mul_of_nonneg_left hGN_sq (pow_nonneg hQnonneg 3)
    have hpower : ‖u.weakDeriv‖ ^ 6 ≤ 4 * Q ^ 3 * ‖u.weakDeriv‖ ^ 2 := by
      calc
        ‖u.weakDeriv‖ ^ 6 = (‖u.weakDeriv‖ ^ 2) ^ 3 := by ring
        _ ≤ (Q * ‖u.value‖ ^ 2) ^ 3 := hquot_cube
        _ = Q ^ 3 * (‖u.value‖ ^ 3) ^ 2 := by ring
        _ ≤ Q ^ 3 * (2 * ‖u.weakDeriv‖) ^ 2 := hscaled
        _ = 4 * Q ^ 3 * ‖u.weakDeriv‖ ^ 2 := by ring
    have hfourth : ‖u.weakDeriv‖ ^ 4 ≤ 4 * Q ^ 3 := by
      rw [show ‖u.weakDeriv‖ ^ 6 = ‖u.weakDeriv‖ ^ 4 * ‖u.weakDeriv‖ ^ 2 by ring]
        at hpower
      exact le_of_mul_le_mul_right hpower (sq_pos_of_pos hderiv_pos)
    by_cases hone : ‖u.weakDeriv‖ ≤ 1
    · exact hone.trans (by nlinarith [pow_nonneg hQnonneg 3])
    · have hself : ‖u.weakDeriv‖ ≤ ‖u.weakDeriv‖ ^ 4 := by
        nlinarith [norm_nonneg u.weakDeriv, sq_nonneg (‖u.weakDeriv‖ - 1)]
      exact hself.trans (hfourth.trans (le_add_of_nonneg_left zero_le_one))

/-- Every admissible sequence with a common quotient bound is uniformly bounded in
`HalfLineH1`. -/
theorem HalfLineH1.norm_le_of_isAdmissible_of_rayleighQuotient_le {L Q : ℝ} {u : HalfLineH1}
    (hu : u.IsAdmissible L) (hQ : u.rayleighQuotient ≤ Q) :
    ‖u‖ ≤ 4 + 12 * Q ^ 3 := by
  have hderiv := HalfLineH1.norm_weakDeriv_le_of_rayleighQuotient_le hu hQ
  have hvalue_sq := HalfLineH1.norm_value_cubed_le_two_mul_norm_weakDeriv hu
  have hvalue : ‖u.value‖ ≤ 1 + 2 * ‖u.weakDeriv‖ := by
    by_cases hone : ‖u.value‖ ≤ 1
    · exact hone.trans (by nlinarith [norm_nonneg u.weakDeriv])
    · have hself : ‖u.value‖ ≤ ‖u.value‖ ^ 3 := by
        nlinarith [norm_nonneg u.value, sq_nonneg (‖u.value‖ - 1)]
      exact hself.trans (hvalue_sq.trans (le_add_of_nonneg_left zero_le_one))
  have hnorm_sq : ‖u‖ ^ 2 = ‖u.value‖ ^ 2 + ‖u.weakDeriv‖ ^ 2 := by
    simpa only [u.norm_valueOnHalfLine, u.norm_weakDerivOnHalfLine] using u.norm_sq_eq
  have hnorm : ‖u‖ ≤ ‖u.value‖ + ‖u.weakDeriv‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    rw [hnorm_sq]
    nlinarith [mul_nonneg (norm_nonneg u.value) (norm_nonneg u.weakDeriv)]
  calc
    ‖u‖ ≤ ‖u.value‖ + ‖u.weakDeriv‖ := hnorm
    _ ≤ 1 + 3 * ‖u.weakDeriv‖ := by linarith
    _ ≤ 1 + 3 * (1 + 4 * Q ^ 3) := by gcongr
    _ = 4 + 12 * Q ^ 3 := by ring

/-- A bounded-quotient admissible sequence has a subsequence with all the weak and local compactness
properties required by the direct method. -/
theorem HalfLineH1.exists_compact_subsequence_of_isAdmissible_of_rayleighQuotient_le
    {L Q : ℝ} {u : ℕ → HalfLineH1} (hu : ∀ n, (u n).IsAdmissible L)
    (hQ : ∀ n, (u n).rayleighQuotient ≤ Q) :
    ∃ (ns : ℕ → ℕ) (v : HalfLineH1), StrictMono ns ∧ ‖v‖ ≤ 4 + 12 * Q ^ 3 ∧
      (∀ w : HalfLineH1,
        Tendsto (fun n ↦ inner ℝ (u (ns n)) w) atTop (𝓝 (inner ℝ v w))) ∧
      ∀ K : Set ℝ, IsCompact K →
        TendstoUniformlyOn (fun n ↦ (u (ns n)).continuousRep) v.continuousRep atTop K ∧
        Tendsto
          (fun n ↦ ∫ x in K, ((u (ns n)).continuousRep x - v.continuousRep x) ^ 2)
          atTop (𝓝 0) := by
  have hQnonneg : 0 ≤ Q := by
    have hquot_nonneg : 0 ≤ (u 0).rayleighQuotient :=
      div_nonneg (sq_nonneg _) (sq_nonneg _)
    exact hquot_nonneg.trans (hQ 0)
  exact HalfLineH1.exists_weakly_and_locally_uniformly_convergent_subsequence
    (by nlinarith [pow_nonneg hQnonneg 3])
    (fun n ↦ HalfLineH1.norm_le_of_isAdmissible_of_rayleighQuotient_le (hu n) (hQ n))

/-- Compact-local uniform convergence implies convergence of the corresponding set integrals over a
compact set. -/
theorem HalfLineH1.tendsto_setIntegral_continuousRep_of_tendstoUniformlyOn
    {u : ℕ → HalfLineH1} {v : HalfLineH1} {K : Set ℝ} (hK : IsCompact K)
    (hunif : TendstoUniformlyOn (fun n ↦ (u n).continuousRep) v.continuousRep atTop K) :
    Tendsto (fun n ↦ ∫ x in K, (u n).continuousRep x) atTop
      (𝓝 (∫ x in K, v.continuousRep x)) := by
  have hbound := Metric.tendstoUniformlyOn_iff.mp hunif 1 zero_lt_one
  have hmeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (u n).continuousRep (volume.restrict K) :=
    Filter.Eventually.of_forall fun n ↦
      (u n).continuous_continuousRep.aestronglyMeasurable
  have hdom : ∀ᶠ n in atTop, ∀ᵐ x ∂volume.restrict K,
      ‖(u n).continuousRep x‖ ≤ |v.continuousRep x| + 1 := by
    filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with x hx
    have hdist := hn x hx
    rw [Real.dist_eq] at hdist
    calc
      |(u n).continuousRep x| ≤ |v.continuousRep x| +
          |(u n).continuousRep x - v.continuousRep x| := by
        calc
          |(u n).continuousRep x| =
              |v.continuousRep x + ((u n).continuousRep x - v.continuousRep x)| := by
            congr 1
            ring
          _ ≤ |v.continuousRep x| +
              |(u n).continuousRep x - v.continuousRep x| := abs_add_le _ _
      _ ≤ |v.continuousRep x| + 1 := by
        rw [abs_sub_comm] at hdist
        exact add_le_add_right hdist.le _
  have hlim : ∀ᵐ x ∂volume.restrict K,
      Tendsto (fun n ↦ (u n).continuousRep x) atTop (𝓝 (v.continuousRep x)) := by
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with x hx
    exact hunif.tendsto_at hx
  simpa using
    (tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict K)
      (fun x ↦ |v.continuousRep x| + 1) hmeas hdom
      ((v.continuous_continuousRep.abs.add continuous_const).continuousOn
        |>.integrableOn_compact hK) hlim)

/-- Multiplication by a fixed continuous weight preserves compact-local integral convergence. -/
theorem HalfLineH1.tendsto_setIntegral_mul_continuousRep_of_tendstoUniformlyOn
    {g : ℝ → ℝ} (hg : Continuous g) {u : ℕ → HalfLineH1} {v : HalfLineH1}
    {K : Set ℝ} (hK : IsCompact K)
    (hunif : TendstoUniformlyOn (fun n ↦ (u n).continuousRep) v.continuousRep atTop K) :
    Tendsto (fun n ↦ ∫ x in K, g x * (u n).continuousRep x) atTop
      (𝓝 (∫ x in K, g x * v.continuousRep x)) := by
  have hbound := Metric.tendstoUniformlyOn_iff.mp hunif 1 zero_lt_one
  have hmeas : ∀ᶠ n in atTop,
      AEStronglyMeasurable (fun x ↦ g x * (u n).continuousRep x)
        (volume.restrict K) :=
    Filter.Eventually.of_forall fun n ↦
      (hg.mul (u n).continuous_continuousRep).aestronglyMeasurable
  have hdom : ∀ᶠ n in atTop, ∀ᵐ x ∂volume.restrict K,
      ‖g x * (u n).continuousRep x‖ ≤ |g x| * (|v.continuousRep x| + 1) := by
    filter_upwards [hbound] with n hn
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with x hx
    have hdist := hn x hx
    rw [Real.dist_eq] at hdist
    calc
      ‖g x * (u n).continuousRep x‖ = |g x| * |(u n).continuousRep x| := by
        simp only [Real.norm_eq_abs, abs_mul]
      _ ≤ |g x| * (|v.continuousRep x| + 1) := by
        gcongr
        calc
          |(u n).continuousRep x| ≤ |v.continuousRep x| +
              |(u n).continuousRep x - v.continuousRep x| := by
            calc
              |(u n).continuousRep x| =
                  |v.continuousRep x + ((u n).continuousRep x - v.continuousRep x)| := by
                congr 1
                ring
              _ ≤ |v.continuousRep x| +
                  |(u n).continuousRep x - v.continuousRep x| := abs_add_le _ _
          _ ≤ |v.continuousRep x| + 1 := by
            rw [abs_sub_comm] at hdist
            exact add_le_add_right hdist.le _
  have hlim : ∀ᵐ x ∂volume.restrict K,
      Tendsto (fun n ↦ g x * (u n).continuousRep x) atTop
        (𝓝 (g x * v.continuousRep x)) := by
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with x hx
    exact tendsto_const_nhds.mul (hunif.tendsto_at hx)
  simpa using
    (tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict K)
      (fun x ↦ |g x| * (|v.continuousRep x| + 1)) hmeas hdom
      ((hg.abs.mul (v.continuous_continuousRep.abs.add continuous_const)).continuousOn
        |>.integrableOn_compact hK) hlim)

/-- The canonical representative has vanishing square-energy tails. -/
theorem HalfLineH1.tendsto_continuousRep_sq_integral_Ici_zero (v : HalfLineH1) :
    Tendsto (fun R : ℝ ↦ ∫ x in Ici R, v.continuousRep x ^ 2) atTop (𝓝 0) := by
  exact MeasureTheory.tendsto_integral_Ici_zero tendsto_id

/-- Compact-local uniform limits preserve pointwise nonnegativity on the half-line. -/
theorem HalfLineH1.nonnegative_of_tendstoUniformlyOn
    {L : ℝ} {u : ℕ → HalfLineH1} {v : HalfLineH1}
    (hu : ∀ n, (u n).IsAdmissible L)
    (hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ (u n).continuousRep) v.continuousRep atTop K) :
    ∀ x ∈ halfLine, 0 ≤ v.continuousRep x := by
  intro x hx
  have hpoint : Tendsto (fun n ↦ (u n).continuousRep x) atTop
      (𝓝 (v.continuousRep x)) :=
    (hunif {x} isCompact_singleton).tendsto_at (mem_singleton x)
  exact ge_of_tendsto' hpoint (fun n ↦ (hu n).nonnegative x hx)

/-- A compactness limit has at least the mass retained on every bounded interval by the approximants.
This is the local half of the mass-passage argument. -/
theorem HalfLineH1.compact_mass_lower_bound_of_tendstoUniformlyOn
    {L : ℝ} {u : ℕ → HalfLineH1} {v : HalfLineH1}
    (hu : ∀ n, (u n).IsAdmissible L)
    (hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ (u n).continuousRep) v.continuousRep atTop K)
    {R : ℝ} (hR : 0 < R) :
    1 - L / R ≤ ∫ x in Icc 0 R, v.continuousRep x := by
  have hlocal := HalfLineH1.tendsto_setIntegral_continuousRep_of_tendstoUniformlyOn
    (u := u) (v := v) (isCompact_Icc) (hunif (Icc 0 R) isCompact_Icc)
  have hseq : ∀ n, 1 - L / R ≤ ∫ x in Icc 0 R, (u n).continuousRep x := by
    intro n
    have htail := HalfLineH1.tailMass_le_firstMoment_div (hu n) hR
    have hsplit : (∫ x in Ico 0 R, (u n).continuousRep x) +
        ∫ x in Ici R, (u n).continuousRep x = 1 := by
      rw [← setIntegral_union (by
          apply Set.disjoint_left.mpr
          intro x hxs hxt
          exact (not_lt_of_ge hxt) hxs.2)
        measurableSet_Ici
        ((hu n).integrable.mono_set (by intro x hx; exact hx.1))
        ((hu n).integrable.mono_set (by intro x hx; exact le_trans hR.le hx))]
      rw [Ico_union_Ici_eq_Ici hR.le]
      exact (hu n).mass_eq
    have hIco : 1 - L / R ≤ ∫ x in Ico 0 R, (u n).continuousRep x := by
      linarith
    simpa only [integral_Icc_eq_integral_Ico] using hIco
  exact ge_of_tendsto' hlocal hseq

/-- The compact-interval mass of a compactness limit cannot exceed the unit mass of the
approximants. -/
theorem HalfLineH1.compact_mass_upper_bound_of_tendstoUniformlyOn
    {L : ℝ} {u : ℕ → HalfLineH1} {v : HalfLineH1}
    (hu : ∀ n, (u n).IsAdmissible L)
    (hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ (u n).continuousRep) v.continuousRep atTop K)
    {R : ℝ} :
    (∫ x in Icc 0 R, v.continuousRep x) ≤ 1 := by
  have hlocal := HalfLineH1.tendsto_setIntegral_continuousRep_of_tendstoUniformlyOn
    (u := u) (v := v) (isCompact_Icc) (hunif (Icc 0 R) isCompact_Icc)
  have hseq : ∀ n, (∫ x in Icc 0 R, (u n).continuousRep x) ≤ 1 := by
    intro n
    rw [← (hu n).mass_eq]
    apply setIntegral_mono_set (hu n).integrable
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      exact (hu n).nonnegative x hx
    · exact Filter.Eventually.of_forall (fun x hx ↦ hx.1)
  exact le_of_tendsto' hlocal hseq

/-- The mass-passage conclusion for a compactness subsequence, stated with an explicit compact-tail
lower bound and the already available nonnegative-limit integrability interface. -/
theorem HalfLineH1.mass_eq_one_of_compact_mass_bounds
    {L : ℝ} {u : ℕ → HalfLineH1} {v : HalfLineH1}
    (hu : ∀ n, (u n).IsAdmissible L)
    (hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ (u n).continuousRep) v.continuousRep atTop K)
    (_hv : ∀ x ∈ halfLine, 0 ≤ v.continuousRep x)
    (hint : IntegrableOn v.continuousRep halfLine)
    (hlower : ∀ R : ℝ, 0 < R →
      1 - L / R ≤ ∫ x in Icc 0 R, v.continuousRep x) :
    v.mass = 1 := by
  have hmass_tendsto : Tendsto (fun R : ℝ ↦
      ∫ x in Icc 0 R, v.continuousRep x) atTop (𝓝 v.mass) := by
    have hcover : AECover (volume.restrict halfLine) atTop
        (fun R : ℝ ↦ Icc 0 R) := by
      refine ⟨?_, fun R ↦ measurableSet_Icc⟩
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      filter_upwards [eventually_ge_atTop x] with R hR
      exact ⟨hx, hR⟩
    have h := hcover.integral_tendsto_of_countably_generated
      hint
    convert h using 1
    · ext R
      rw [show (volume.restrict halfLine).restrict (Icc 0 R) = volume.restrict (Icc 0 R) by
        apply Measure.restrict_restrict_of_subset
        exact Icc_subset_Ici_self]
    · rfl
  have hupper : v.mass ≤ 1 := by
    apply le_of_tendsto hmass_tendsto
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact HalfLineH1.compact_mass_upper_bound_of_tendstoUniformlyOn hu hunif
      (R := R)
  have hleft : Tendsto (fun R : ℝ ↦ 1 - L / R) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := L)).mul tendsto_inv_atTop_zero)
    simpa only [div_eq_mul_inv, mul_zero, sub_zero] using h
  have hlower_mass : 1 ≤ v.mass := by
    apply le_of_tendsto_of_tendsto hleft hmass_tendsto
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact hlower R hR
  exact le_antisymm hupper hlower_mass

/-- The squared tail of the difference of two canonical representatives is bounded by the sum of
their squared tails. -/
theorem HalfLineH1.tail_continuousRep_sub_sq_le
    {u v : HalfLineH1} {R : ℝ} :
    (∫ x in Ici R, (u.continuousRep x - v.continuousRep x) ^ 2) ≤
      2 * (∫ x in Ici R, u.continuousRep x ^ 2) +
        2 * (∫ x in Ici R, v.continuousRep x ^ 2) := by
  have hleft : IntegrableOn (fun x ↦
      (u.continuousRep x - v.continuousRep x) ^ 2) (Ici R) := by
    exact ((u.continuousRep_memLp.sub v.continuousRep_memLp).integrable_sq).integrableOn
  have hu : IntegrableOn (fun x ↦ u.continuousRep x ^ 2) (Ici R) :=
    u.continuousRep_sq_integrable.integrableOn
  have hv : IntegrableOn (fun x ↦ v.continuousRep x ^ 2) (Ici R) :=
    v.continuousRep_sq_integrable.integrableOn
  have hright : IntegrableOn (fun x ↦
      2 * u.continuousRep x ^ 2 + 2 * v.continuousRep x ^ 2) (Ici R) :=
    (hu.const_mul 2).add (hv.const_mul 2)
  calc
    (∫ x in Ici R, (u.continuousRep x - v.continuousRep x) ^ 2) ≤
        ∫ x in Ici R, 2 * u.continuousRep x ^ 2 + 2 * v.continuousRep x ^ 2 := by
      apply setIntegral_mono_ae_restrict hleft hright
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      nlinarith [sq_nonneg (u.continuousRep x + v.continuousRep x)]
    _ = 2 * (∫ x in Ici R, u.continuousRep x ^ 2) +
        2 * (∫ x in Ici R, v.continuousRep x ^ 2) := by
      have hu' : Integrable (fun x ↦ u.continuousRep x ^ 2)
          (volume.restrict (Ici R)) := hu
      have hv' : Integrable (fun x ↦ v.continuousRep x ^ 2)
          (volume.restrict (Ici R)) := hv
      calc
        (∫ x in Ici R, 2 * u.continuousRep x ^ 2 + 2 * v.continuousRep x ^ 2) =
            ∫ x in Ici R, (2 : ℝ) • u.continuousRep x ^ 2 +
              (2 : ℝ) • v.continuousRep x ^ 2 := by
          apply integral_congr_ae
          filter_upwards with x
          simp [smul_eq_mul]
        _ = (∫ x in Ici R, (2 : ℝ) • u.continuousRep x ^ 2) +
            ∫ x in Ici R, (2 : ℝ) • v.continuousRep x ^ 2 := by
          exact integral_add (hu'.smul (2 : ℝ)) (hv'.smul (2 : ℝ))
        _ = 2 * (∫ x in Ici R, u.continuousRep x ^ 2) +
            2 * (∫ x in Ici R, v.continuousRep x ^ 2) := by
          rw [hu'.integral_smul, hv'.integral_smul]
          simp [smul_eq_mul]

/-- Local squared-error convergence plus the uniform tail estimate gives global strong `L²`
convergence of canonical representatives. -/
theorem HalfLineH1.tendsto_global_continuousRep_sq_sub_of_local
    {L B : ℝ} {u : ℕ → HalfLineH1} {v : HalfLineH1}
    (hu : ∀ n, (u n).IsAdmissible L) (hB : ∀ n, ‖(u n).weakDeriv‖ ≤ B)
    (hlocal : ∀ R : ℝ, 0 < R →
      Tendsto (fun n ↦ ∫ x in Icc 0 R,
        ((u n).continuousRep x - v.continuousRep x) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x in halfLine,
      ((u n).continuousRep x - v.continuousRep x) ^ 2) atTop (𝓝 0) := by
  have htail_bound : Tendsto (fun R : ℝ ↦
      2 * (Real.sqrt (2 * (1 + 2 * B) * B) * (L / R) +
        ∫ x in Ici R, v.continuousRep x ^ 2)) atTop (𝓝 0) := by
    simpa only [zero_add, add_zero, mul_zero] using
      ((HalfLineH1.tendsto_uniform_tailSquareEnergy_bound (L := L) (B := B)).add
        (HalfLineH1.tendsto_continuousRep_sq_integral_Ici_zero v)).const_mul 2
  have hBnonneg : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hLnonneg : 0 ≤ L := by
    have hm : 0 ≤ (u 0).firstMoment := by
      rw [HalfLineH1.firstMoment]
      exact setIntegral_nonneg measurableSet_Ici fun x hx ↦
        mul_nonneg hx ((hu 0).nonnegative x (by simpa [halfLine] using hx))
    linarith [(hu 0).firstMoment_eq]
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htail_bound (ε / 2) (by linarith)
  let R : ℝ := max N 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right N 1)
  have hRN : N ≤ R := le_max_left N 1
  have htail_small : 2 * (Real.sqrt (2 * (1 + 2 * B) * B) * (L / R) +
      ∫ x in Ici R, v.continuousRep x ^ 2) < ε / 2 := by
    have hnonneg : 0 ≤ 2 * (Real.sqrt (2 * (1 + 2 * B) * B) * (L / R) +
        ∫ x in Ici R, v.continuousRep x ^ 2) := by
      have htailv : 0 ≤ ∫ x in Ici R, v.continuousRep x ^ 2 :=
        setIntegral_nonneg measurableSet_Ici fun _ _ ↦ sq_nonneg _
      positivity
    have h := hN R hRN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at h
    exact h
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp (hlocal R hR) (ε / 2) (by linarith)
  refine ⟨M, fun n hn ↦ ?_⟩
  have hlocal_small := hM n hn
  have htail_diff : (∫ x in Ici R,
      ((u n).continuousRep x - v.continuousRep x) ^ 2) ≤
      2 * (Real.sqrt (2 * (1 + 2 * B) * B) * (L / R) +
        ∫ x in Ici R, v.continuousRep x ^ 2) := by
    have htail_quad := HalfLineH1.tail_continuousRep_sub_sq_le
      (u := u n) (v := v) (R := R)
    exact htail_quad.trans <| by
      have hu_tail := HalfLineH1.tailSquareEnergy_le_of_norm_weakDeriv_le
        (hu n) hR (hB n)
      have hv_nonneg : 0 ≤ 2 * (∫ x in Ici R, v.continuousRep x ^ 2) := by positivity
      nlinarith
  have hsplit : (∫ x in halfLine,
      ((u n).continuousRep x - v.continuousRep x) ^ 2) =
      (∫ x in Ico 0 R, ((u n).continuousRep x - v.continuousRep x) ^ 2) +
        ∫ x in Ici R, ((u n).continuousRep x - v.continuousRep x) ^ 2 := by
    rw [show halfLine = Ico 0 R ∪ Ici R by
      rw [Ico_union_Ici_eq_Ici hR.le, halfLine]]
    apply setIntegral_union
    · exact Set.disjoint_left.mpr (by
        intro x hx htx
        exact (not_lt_of_ge htx) hx.2)
    · exact measurableSet_Ici
    · exact ((u n).continuousRep_memLp.sub v.continuousRep_memLp).integrable_sq.integrableOn
    · exact ((u n).continuousRep_memLp.sub v.continuousRep_memLp).integrable_sq.integrableOn
  rw [hsplit]
  have hlocal_co : (∫ x in Ico 0 R,
      ((u n).continuousRep x - v.continuousRep x) ^ 2) < ε / 2 := by
    have h := hlocal_small
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
      0 ≤ ∫ x in Icc 0 R, ((u n).continuousRep x - v.continuousRep x) ^ 2)] at h
    simpa only [integral_Icc_eq_integral_Ico] using h
  have hnonneg : 0 ≤ ∫ x in Ico 0 R,
      ((u n).continuousRep x - v.continuousRep x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ico fun _ _ ↦ sq_nonneg _
  have htail_nonneg : 0 ≤ ∫ x in Ici R,
      ((u n).continuousRep x - v.continuousRep x) ^ 2 :=
    setIntegral_nonneg measurableSet_Ici (fun _ _ ↦ sq_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (add_nonneg hnonneg htail_nonneg)]
  nlinarith

/-- Global strong representative convergence is equivalent to convergence of the intrinsic square
energies. -/
theorem HalfLineH1.tendsto_squareEnergy_of_tendsto_global_continuousRep_sq_sub
    {u : ℕ → HalfLineH1} {v : HalfLineH1}
    (hglobal : Tendsto (fun n ↦ ∫ x in halfLine,
      ((u n).continuousRep x - v.continuousRep x) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (u n).squareEnergy) atTop (𝓝 v.squareEnergy) := by
  have hrep : ∀ n, (u n - v).continuousRep =
      (u n).continuousRep - v.continuousRep := by
    intro n
    rw [sub_eq_add_neg, HalfLineH1.continuousRep_add]
    have hneg : (-v).continuousRep = -v.continuousRep := by
      simpa using (HalfLineH1.continuousRep_smul (-1 : ℝ) v)
    rw [hneg]
    ring
  have heq : ∀ n, (∫ x in halfLine,
      ((u n).continuousRep x - v.continuousRep x) ^ 2) =
      ‖(u n).value - v.value‖ ^ 2 := by
    intro n
    have h := (u n - v).integral_continuousRep_sq_Ici_eq_norm_value_sq
    rw [hrep n] at h
    exact h
  have hnorm : Tendsto (fun n ↦ ‖(u n).value - v.value‖ ^ 2) atTop (𝓝 0) := by
    simpa only [heq] using hglobal
  have hdiff : Tendsto (fun n ↦ ‖(u n).value - v.value‖) atTop (𝓝 0) := by
    have hsqroot := (Real.continuous_sqrt.continuousAt.tendsto.comp hnorm)
    have heqnorm : (fun n ↦ ‖(u n).value - v.value‖) =
        (fun n ↦ Real.sqrt (‖(u n).value - v.value‖ ^ 2)) := by
      funext n
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [heqnorm]
    convert hsqroot using 1
    ext n
    rfl
    simp
  have hsq : Tendsto (fun n ↦ ‖(u n).value‖ ^ 2) atTop (𝓝 (‖v.value‖ ^ 2)) := by
    have hvalue : Tendsto (fun n ↦ (u n).value) atTop (𝓝 v.value) :=
      (tendsto_iff_norm_sub_tendsto_zero).2 hdiff
    exact (continuous_norm.continuousAt.tendsto.comp hvalue).pow 2
  simpa only [HalfLineH1.squareEnergy] using hsq

/-- Compact mass bounds and nonnegativity make the limiting canonical representative integrable on
the half-line. -/
theorem HalfLineH1.integrableOn_continuousRep_of_nonnegative_of_compact_mass_le_one
    {v : HalfLineH1} (hv : ∀ x ∈ halfLine, 0 ≤ v.continuousRep x)
    (hcompact : ∀ R : ℝ, 0 < R →
      (∫ x in Icc 0 R, v.continuousRep x) ≤ 1) :
    IntegrableOn v.continuousRep halfLine := by
  have hfi : ∀ R : ℝ, IntegrableOn v.continuousRep (Icc 0 R) := by
    intro R
    exact v.continuous_continuousRep.continuousOn.integrableOn_compact isCompact_Icc
  have hbound : ∀ᶠ R in atTop,
      ∫ x in Icc 0 R, ‖v.continuousRep x‖ ≤ (1 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    apply le_trans ?_ (hcompact R hR)
    apply setIntegral_mono_ae_restrict
    · exact v.continuous_continuousRep.norm.continuousOn.integrableOn_compact isCompact_Icc
    · exact hfi R
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hv x (by simpa [halfLine] using hx.1))]
  have hcover : AECover (volume.restrict halfLine) atTop
      (fun R : ℝ ↦ Icc 0 R) := by
    refine ⟨?_, fun R ↦ measurableSet_Icc⟩
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    filter_upwards [eventually_ge_atTop x] with R hR
    exact ⟨hx, hR⟩
  exact hcover.integrable_of_integral_norm_bounded 1 (by
    intro R
    exact (hfi R).mono_measure Measure.restrict_le_self) (by
      filter_upwards [hbound] with R hR
      rw [show (volume.restrict halfLine).restrict (Icc 0 R) = volume.restrict (Icc 0 R) by
        apply Measure.restrict_restrict_of_subset
        exact Icc_subset_Ici_self]
      exact hR)

/-- Unit mass passes to the limit along an admissible compactness subsequence with local uniform
convergence. -/
theorem HalfLineH1.mass_eq_one_of_isAdmissible_of_tendstoUniformlyOn
    {L : ℝ} {u : ℕ → HalfLineH1} {v : HalfLineH1}
    (hu : ∀ n, (u n).IsAdmissible L)
    (hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ (u n).continuousRep) v.continuousRep atTop K) :
    v.mass = 1 := by
  have hv : ∀ x ∈ halfLine, 0 ≤ v.continuousRep x :=
    HalfLineH1.nonnegative_of_tendstoUniformlyOn hu hunif
  have hupper : ∀ R : ℝ, 0 < R →
      (∫ x in Icc 0 R, v.continuousRep x) ≤ 1 := by
    intro R hR
    exact HalfLineH1.compact_mass_upper_bound_of_tendstoUniformlyOn hu hunif
      (R := R)
  have hint := HalfLineH1.integrableOn_continuousRep_of_nonnegative_of_compact_mass_le_one
    hv hupper
  have hlower : ∀ R : ℝ, 0 < R →
      1 - L / R ≤ ∫ x in Icc 0 R, v.continuousRep x := by
    intro R hR
    exact HalfLineH1.compact_mass_lower_bound_of_tendstoUniformlyOn hu hunif hR
  exact HalfLineH1.mass_eq_one_of_compact_mass_bounds hu hunif hv hint hlower

/-- First moments pass to the compactness limit with the Fatou bound `m ≤ L`. -/
theorem HalfLineH1.firstMoment_integrableOn_and_le_of_isAdmissible_of_tendstoUniformlyOn
    {L : ℝ} {u : ℕ → HalfLineH1} {v : HalfLineH1}
    (hu : ∀ n, (u n).IsAdmissible L)
    (hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ (u n).continuousRep) v.continuousRep atTop K) :
    IntegrableOn (fun x ↦ x * v.continuousRep x) halfLine ∧
      v.firstMoment ≤ L := by
  have hv : ∀ x ∈ halfLine, 0 ≤ v.continuousRep x :=
    HalfLineH1.nonnegative_of_tendstoUniformlyOn hu hunif
  have hcompact : ∀ R : ℝ, 0 < R →
      (∫ x in Icc 0 R, x * v.continuousRep x) ≤ L := by
    intro R hR
    have hlocal := HalfLineH1.tendsto_setIntegral_mul_continuousRep_of_tendstoUniformlyOn
      (g := fun x ↦ x) continuous_id (u := u) (v := v) isCompact_Icc
      (hunif (Icc 0 R) isCompact_Icc)
    have hseq : ∀ n, (∫ x in Icc 0 R, x * (u n).continuousRep x) ≤ L := by
      intro n
      rw [← (hu n).firstMoment_eq]
      apply setIntegral_mono_set (hu n).firstMoment_integrable
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
        exact mul_nonneg hx ((hu n).nonnegative x hx)
      · exact Filter.Eventually.of_forall (fun x hx ↦ hx.1)
    exact le_of_tendsto' hlocal hseq
  have hlocal_int : ∀ R : ℝ,
      IntegrableOn (fun x ↦ x * v.continuousRep x) (Icc 0 R) := by
    intro R
    exact (continuousOn_id.mul v.continuous_continuousRep.continuousOn).integrableOn_compact
      isCompact_Icc
  have hbound : ∀ᶠ R in atTop,
      ∫ x in Icc 0 R, ‖x * v.continuousRep x‖ ≤ L := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have hEq : (∫ x in Icc 0 R, ‖x * v.continuousRep x‖) =
        ∫ x in Icc 0 R, x * v.continuousRep x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg hx.1 (hv x (by exact hx.1))
    rw [hEq]
    exact hcompact R hR
  have hcover : AECover (volume.restrict halfLine) atTop
      (fun R : ℝ ↦ Icc 0 R) := by
    refine ⟨?_, fun R ↦ measurableSet_Icc⟩
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    filter_upwards [eventually_ge_atTop x] with R hR
    exact ⟨hx, hR⟩
  have hinter : Integrable (fun x ↦ x * v.continuousRep x)
      (volume.restrict halfLine) := hcover.integrable_of_integral_norm_bounded L (by
    intro R
    exact (hlocal_int R).mono_measure Measure.restrict_le_self) (by
      filter_upwards [hbound] with R hR
      rw [show (volume.restrict halfLine).restrict (Icc 0 R) = volume.restrict (Icc 0 R) by
        apply Measure.restrict_restrict_of_subset
        exact Icc_subset_Ici_self]
      exact hR)
  have hmoment_tendsto : Tendsto (fun R : ℝ ↦
      ∫ x in Icc 0 R, x * v.continuousRep x ∂(volume.restrict halfLine)) atTop
        (𝓝 (∫ x, x * v.continuousRep x ∂(volume.restrict halfLine))) :=
    hcover.integral_tendsto_of_countably_generated hinter
  have hLnonneg : 0 ≤ L := by
    have hm : 0 ≤ (u 0).firstMoment := by
      rw [HalfLineH1.firstMoment]
      exact setIntegral_nonneg measurableSet_Ici fun x hx ↦
        mul_nonneg hx ((hu 0).nonnegative x (by simpa [halfLine] using hx))
    linarith [(hu 0).firstMoment_eq]
  have hle : (∫ x, x * v.continuousRep x ∂(volume.restrict halfLine)) ≤ L := by
    refine le_of_tendsto' hmoment_tendsto ?_
    intro R
    by_cases hR : 0 < R
    · rw [show (volume.restrict halfLine).restrict (Icc 0 R) = volume.restrict (Icc 0 R) by
        apply Measure.restrict_restrict_of_subset
        exact Icc_subset_Ici_self]
      exact hcompact R hR
    · rcases eq_or_lt_of_le (le_of_not_gt hR) with hzero | hneg
      · subst R
        simpa [v.continuousRep_zero] using hLnonneg
      · simpa [Icc_eq_empty_of_lt hneg] using hLnonneg
  exact ⟨hinter, by
    simpa [HalfLineH1.firstMoment, RayleighKernel.firstMoment, halfLine] using hle⟩

/-- A continuous nonnegative unit-mass representative has strictly positive first moment. -/
theorem HalfLineH1.firstMoment_pos_of_mass_eq_one_of_nonnegative
    {v : HalfLineH1} (hv : ∀ x ∈ halfLine, 0 ≤ v.continuousRep x)
    (hmass : v.mass = 1)
    (hInt : IntegrableOn (fun x ↦ x * v.continuousRep x) halfLine) :
    0 < v.firstMoment := by
  have hnonneg : 0 ≤ v.firstMoment := by
    rw [HalfLineH1.firstMoment]
    exact setIntegral_nonneg measurableSet_Ici fun x hx ↦
      mul_nonneg hx (hv x hx)
  by_contra hnot
  have hzero : v.firstMoment = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hzero' : (∫ x in halfLine, x * v.continuousRep x) = 0 := by
    simpa [HalfLineH1.firstMoment, RayleighKernel.firstMoment] using hzero
  have hae : ∀ᵐ x ∂volume.restrict halfLine, x * v.continuousRep x = 0 := by
    have hnonneg : 0 ≤ᵐ[volume.restrict halfLine]
        (fun x ↦ x * v.continuousRep x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      exact mul_nonneg hx (hv x hx)
    exact (setIntegral_eq_zero_iff_of_nonneg_ae hnonneg hInt).mp hzero'
  have hvzero : ∀ᵐ x ∂volume.restrict (Ioi 0), v.continuousRep x = 0 := by
    have hprod := ae_restrict_of_ae_restrict_of_subset Ioi_subset_Ici_self hae
    filter_upwards [hprod, ae_restrict_mem measurableSet_Ioi] with x hx hxmem
    have hxpos : 0 < x := by
      exact hxmem
    exact (mul_eq_zero.mp hx).resolve_left (ne_of_gt hxpos)
  have hvzero_on : Set.EqOn v.continuousRep 0 (Ioi 0) :=
    Measure.eqOn_open_of_ae_eq hvzero isOpen_Ioi
      v.continuous_continuousRep.continuousOn continuous_zero.continuousOn
  have hmass_zero : v.mass = 0 := by
    rw [HalfLineH1.mass, RayleighKernel.mass]
    apply setIntegral_eq_zero_of_ae_eq_zero
    filter_upwards with x
    intro hx
    by_cases hx0 : x ≤ 0
    · exact v.continuousRep_eq_zero_of_nonpositive hx0
    · exact hvzero_on (lt_of_not_ge hx0)
  linarith

/-- Every canonical representative in a compactness limit has the zero trace. -/
theorem HalfLineH1.zero_trace_continuousRep (_v : HalfLineH1) :
    _v.continuousRep 0 = 0 := by
  exact _v.continuousRep_zero

/-- Extract a compactness subsequence from a uniformly quotient-bounded admissible sequence and pass
the unit-mass and first-moment inequalities to its limit. -/
theorem exists_bounded_quotient_limit
    {L Q : ℝ} {u : ℕ → HalfLineH1} (hu : ∀ n, (u n).IsAdmissible L)
    (hQ : ∀ n, (u n).rayleighQuotient ≤ Q) :
    ∃ (ns : ℕ → ℕ) (v : HalfLineH1), StrictMono ns ∧
      (∀ n, (u (ns n)).IsAdmissible L) ∧
      (∀ n, (u (ns n)).rayleighQuotient ≤ Q) ∧
      (∀ x ∈ halfLine, 0 ≤ v.continuousRep x) ∧ v.mass = 1 ∧
      IntegrableOn (fun x ↦ x * v.continuousRep x) halfLine ∧
      0 < v.firstMoment ∧ v.firstMoment ≤ L := by
  obtain ⟨ns, v, hns, _hvbound, hweak, hcompact⟩ :=
    HalfLineH1.exists_compact_subsequence_of_isAdmissible_of_rayleighQuotient_le hu hQ
  have hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ (u (ns n)).continuousRep) v.continuousRep atTop K :=
    fun K hK ↦ (hcompact K hK).1
  let uSub : ℕ → HalfLineH1 := fun n ↦ u (ns n)
  have huSub : ∀ n, (uSub n).IsAdmissible L := fun n ↦ hu (ns n)
  have hunifSub : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ (uSub n).continuousRep) v.continuousRep atTop K :=
    fun K hK ↦ hunif K hK
  have hmass := HalfLineH1.mass_eq_one_of_isAdmissible_of_tendstoUniformlyOn huSub hunifSub
  have hvnonneg := HalfLineH1.nonnegative_of_tendstoUniformlyOn huSub hunifSub
  have hmoment := HalfLineH1.firstMoment_integrableOn_and_le_of_isAdmissible_of_tendstoUniformlyOn
    huSub hunifSub
  have hfirstpos := HalfLineH1.firstMoment_pos_of_mass_eq_one_of_nonnegative
    hvnonneg hmass hmoment.1
  exact ⟨ns, v, hns, huSub, (fun n ↦ hQ (ns n)), hvnonneg, hmass, hmoment.1,
    hfirstpos, hmoment.2⟩

/-- Global square-error convergence for a compactness subsequence with a fixed derivative bound. -/
theorem global_squareEnergy_tendsto_of_compact_subsequence
    {L B : ℝ} {u : ℕ → HalfLineH1} {v : HalfLineH1}
    (hu : ∀ n, (u n).IsAdmissible L)
    (hB : ∀ n, ‖(u n).weakDeriv‖ ≤ B)
    (hlocal : ∀ R : ℝ, 0 < R →
      Tendsto (fun n ↦ ∫ x in Icc 0 R,
        ((u n).continuousRep x - v.continuousRep x) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x in halfLine,
      ((u n).continuousRep x - v.continuousRep x) ^ 2) atTop (𝓝 0) :=
  HalfLineH1.tendsto_global_continuousRep_sq_sub_of_local hu hB hlocal

/-- Global strong convergence implies convergence of the intrinsic square-energy denominator. -/
theorem squareEnergy_tendsto_of_global_squareEnergy_tendsto
    {u : ℕ → HalfLineH1} {v : HalfLineH1}
    (hglobal : Tendsto (fun n ↦ ∫ x in halfLine,
      ((u n).continuousRep x - v.continuousRep x) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (u n).squareEnergy) atTop (𝓝 v.squareEnergy) :=
  HalfLineH1.tendsto_squareEnergy_of_tendsto_global_continuousRep_sq_sub hglobal

/-- The compactness and constraint data obtained from a uniformly quotient-bounded admissible
sequence.  A structure avoids the elaboration cost of a deeply nested existential/conjunction. -/
structure DirectMethodLimitData (L Q : ℝ) (u : ℕ → HalfLineH1) where
  ns : ℕ → ℕ
  limit : HalfLineH1
  strictMono_ns : StrictMono ns
  admissible_subseq : ∀ n, (u (ns n)).IsAdmissible L
  quotient_le : ∀ n, (u (ns n)).rayleighQuotient ≤ Q
  weak_tendsto : ∀ w : HalfLineH1,
    Tendsto (fun n ↦ inner ℝ (u (ns n)) w) atTop (𝓝 (inner ℝ limit w))
  local_squareError_tendsto : ∀ K : Set ℝ, IsCompact K →
    Tendsto (fun n ↦ ∫ x in K,
      ((u (ns n)).continuousRep x - limit.continuousRep x) ^ 2) atTop (𝓝 0)
  squareEnergy_tendsto :
    Tendsto (fun n ↦ (u (ns n)).squareEnergy) atTop (𝓝 limit.squareEnergy)
  nonnegative : ∀ x ∈ halfLine, 0 ≤ limit.continuousRep x
  mass_eq : limit.mass = 1
  firstMoment_integrable :
    IntegrableOn (fun x ↦ x * limit.continuousRep x) halfLine
  firstMoment_pos : 0 < limit.firstMoment
  firstMoment_le : limit.firstMoment ≤ L

/-- Construct all direct-method limit data from a pointwise quotient bound. -/
theorem exists_directMethodLimitData
    {L Q : ℝ} {u : ℕ → HalfLineH1} (hu : ∀ n, (u n).IsAdmissible L)
    (hQ : ∀ n, (u n).rayleighQuotient ≤ Q) :
    Nonempty (DirectMethodLimitData L Q u) := by
  obtain ⟨ns, v, hns, _hvbound, hweak, hcompact⟩ :=
    HalfLineH1.exists_compact_subsequence_of_isAdmissible_of_rayleighQuotient_le hu hQ
  let uSub : ℕ → HalfLineH1 := fun n ↦ u (ns n)
  have huSub : ∀ n, (uSub n).IsAdmissible L := fun n ↦ hu (ns n)
  have hQSub : ∀ n, (uSub n).rayleighQuotient ≤ Q := fun n ↦ hQ (ns n)
  have hunif : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ (uSub n).continuousRep) v.continuousRep atTop K :=
    fun K hK ↦ (hcompact K hK).1
  have hnonnegative := HalfLineH1.nonnegative_of_tendstoUniformlyOn huSub hunif
  have hmass := HalfLineH1.mass_eq_one_of_isAdmissible_of_tendstoUniformlyOn huSub hunif
  have hmoment := HalfLineH1.firstMoment_integrableOn_and_le_of_isAdmissible_of_tendstoUniformlyOn
    huSub hunif
  have hmoment_pos := HalfLineH1.firstMoment_pos_of_mass_eq_one_of_nonnegative
    hnonnegative hmass hmoment.1
  have hB : ∀ n, ‖(uSub n).weakDeriv‖ ≤ 1 + 4 * Q ^ 3 := fun n ↦
    HalfLineH1.norm_weakDeriv_le_of_rayleighQuotient_le (huSub n) (hQSub n)
  have hglobal := global_squareEnergy_tendsto_of_compact_subsequence huSub hB
    (fun R _hR ↦ (hcompact (Icc 0 R) isCompact_Icc).2)
  have hsquare := squareEnergy_tendsto_of_global_squareEnergy_tendsto hglobal
  exact ⟨{
    ns := ns
    limit := v
    strictMono_ns := hns
    admissible_subseq := huSub
    quotient_le := hQSub
    weak_tendsto := hweak
    local_squareError_tendsto := fun K hK ↦ (hcompact K hK).2
    squareEnergy_tendsto := hsquare
    nonnegative := hnonnegative
    mass_eq := hmass
    firstMoment_integrable := hmoment.1
    firstMoment_pos := hmoment_pos
    firstMoment_le := hmoment.2
  }⟩

/-- The direct-method limit of a uniformly quotient-bounded admissible sequence remains in the same
quotient sublevel. -/
theorem DirectMethodLimitData.limit_rayleighQuotient_le
    {L Q : ℝ} {u : ℕ → HalfLineH1} (d : DirectMethodLimitData L Q u) :
    d.limit.rayleighQuotient ≤ Q := by
  apply HalfLineH1.rayleighQuotient_le_of_tendsto_squareEnergy_of_le
    d.weak_tendsto d.squareEnergy_tendsto
  · exact fun n ↦ HalfLineH1.squareEnergy_pos_of_mass_eq_one (d.admissible_subseq n).mass_eq
  · exact HalfLineH1.squareEnergy_pos_of_mass_eq_one d.mass_eq
  · exact d.quotient_le

end Analysis

end RayleighKernel
