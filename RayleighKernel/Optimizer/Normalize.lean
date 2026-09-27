import RayleighKernel.Optimizer.ODE
import RayleighKernel.Profile.Derivatives
import RayleighKernel.Profile.Consistency

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open RayleighKernel
namespace RayleighKernel.Analysis.HalfLineH1

private theorem harmonic_representation_on_Ioo
    {h h' : ℝ → ℝ} {K k : ℝ} (hk : k ≠ 0)
    (hh : ∀ x ∈ Set.Ioo 0 K, HasDerivAt h (h' x) x)
    (hh' : ∀ x ∈ Set.Ioo 0 K, HasDerivAt h' (-(k^2) * h x) x) :
    ∃ A C : ℝ, ∀ x ∈ Set.Ioo 0 K,
      h x = A * Real.sin (k*x) + C * Real.cos (k*x) := by
  let U : ℝ → ℝ := fun x => h' x * Real.cos (k*x) + k*h x*Real.sin (k*x)
  let V : ℝ → ℝ := fun x => h' x * Real.sin (k*x) - k*h x*Real.cos (k*x)
  have hU : ∀ x ∈ Set.Ioo 0 K, HasDerivAt U 0 x := by
    intro x hx
    have hsin : HasDerivAt (fun z : ℝ => Real.sin (k*z)) (Real.cos (k*x) * k) x := by
      convert (Real.hasDerivAt_sin (k*x)).comp x (hasDerivAt_const_mul k) using 1
      · rfl
    have hcos : HasDerivAt (fun z : ℝ => Real.cos (k*z)) (-Real.sin (k*x) * k) x := by
      convert (Real.hasDerivAt_cos (k*x)).comp x (hasDerivAt_const_mul k) using 1
      · rfl
    have h1 : HasDerivAt (fun z => h' z * Real.cos (k * z))
        ((-(k^2) * h x) * Real.cos (k * x) + h' x * (-Real.sin (k * x) * k)) x := by
      convert (hh' x hx).mul hcos using 1
    have h2 : HasDerivAt (fun z => k * h z * Real.sin (k * z))
        ((k * h' x) * Real.sin (k * x) + (k * h x) * (Real.cos (k * x) * k)) x := by
      convert ((hh x hx).const_mul k).mul hsin using 1
    convert h1.add h2 using 1
    ring
  have hV : ∀ x ∈ Set.Ioo 0 K, HasDerivAt V 0 x := by
    intro x hx
    have hsin : HasDerivAt (fun z : ℝ => Real.sin (k*z)) (Real.cos (k*x) * k) x := by
      convert (Real.hasDerivAt_sin (k*x)).comp x (hasDerivAt_const_mul k) using 1
      · rfl
    have hcos : HasDerivAt (fun z : ℝ => Real.cos (k*z)) (-Real.sin (k*x) * k) x := by
      convert (Real.hasDerivAt_cos (k*x)).comp x (hasDerivAt_const_mul k) using 1
      · rfl
    have h3 : HasDerivAt (fun z => h' z * Real.sin (k * z))
        ((-(k^2) * h x) * Real.sin (k * x) + h' x * (Real.cos (k * x) * k)) x := by
      convert (hh' x hx).mul hsin using 1
    have h4 : HasDerivAt (fun z => k * h z * Real.cos (k * z))
        ((k * h' x) * Real.cos (k * x) + (k * h x) * (-Real.sin (k * x) * k)) x := by
      convert ((hh x hx).const_mul k).mul hcos using 1
    convert h3.sub h4 using 1
    ring
  have hUc : DifferentiableOn ℝ U (Set.Ioo 0 K) := by
    intro x hx
    exact (hU x hx).differentiableAt.differentiableWithinAt
  have hUd : (Set.Ioo 0 K).EqOn (deriv U) 0 := by
    intro x hx
    exact (hU x hx).deriv
  have hVc : DifferentiableOn ℝ V (Set.Ioo 0 K) := by
    intro x hx
    exact (hV x hx).differentiableAt.differentiableWithinAt
  have hVd : (Set.Ioo 0 K).EqOn (deriv V) 0 := by
    intro x hx
    exact (hV x hx).deriv
  obtain ⟨u, hu⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    isPreconnected_Ioo hUc hUd
  obtain ⟨v, hv⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero
    isPreconnected_Ioo hVc hVd
  refine ⟨u / k, -v / k, ?_⟩
  intro x hx
  have hux := hu x hx
  have hvx := hv x hx
  dsimp [U, V] at hux hvx
  have htrig := Real.sin_sq_add_cos_sq (k*x)
  have hcombine :
      u * Real.sin (k*x) - v * Real.cos (k*x) = k * h x := by
    calc
      _ = U x * Real.sin (k*x) - V x * Real.cos (k*x) := by
        rw [← hux, ← hvx]
      _ = k * h x * (Real.sin (k*x)^2 + Real.cos (k*x)^2) := by
        dsimp [U, V]
        ring
      _ = k * h x := by rw [htrig]; ring
  calc
    h x = (k * h x) / k := by field_simp [hk]
    _ = (u * Real.sin (k*x) - v * Real.cos (k*x)) / k := by rw [hcombine]
    _ = (u / k) * Real.sin (k*x) + (-v / k) * Real.cos (k*x) := by
      field_simp [hk]
      ring

/-- The positive support endpoint used in the dimensionless normalization. -/
def minimizerSupport (f : HalfLineH1) : ℝ := f.positivityHullEndpoint

/-- The amplitude/slope quotient in the affine forcing term. -/
def minimizerSlope (f : HalfLineH1) (B : f.CorrectionBumps) : ℝ :=
  B.momentMultiplier / f.rayleighQuotient

/-- The dimensionless frequency of a minimizer. -/
def minimizerParameter (f : HalfLineH1) : ℝ :=
  Real.sqrt f.rayleighQuotient * f.minimizerSupport

/-- The value of a minimizer after the support and amplitude normalization. -/
def normalizedMinimizerValue (f : HalfLineH1) (B : f.CorrectionBumps) (y : ℝ) : ℝ :=
  f.continuousRep (f.minimizerSupport * y) /
    (f.minimizerSlope B * f.minimizerSupport)

theorem minimizerSupport_pos
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : 0 < f.minimizerSupport := by
  exact positivityHullEndpoint_pos_of_isMinimizer hL hfmin B

theorem minimizerRayleighQuotient_pos
    {L : ℝ} (_hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L) :
    0 < f.rayleighQuotient := by
  exact rayleighQuotient_pos_of_mass_eq_one hfmin.1.mass_eq

theorem minimizerSlope_pos
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : 0 < f.minimizerSlope B := by
  exact B.momentMultiplier_div_rayleighQuotient_pos_of_isMinimizer hL hfmin

theorem minimizerParameter_pos
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : 0 < f.minimizerParameter := by
  unfold minimizerParameter
  exact mul_pos (Real.sqrt_pos.2 (minimizerRayleighQuotient_pos hL hfmin))
    (minimizerSupport_pos hL hfmin B)

theorem minimizerParameter_ne_zero
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : f.minimizerParameter ≠ 0 := by
  exact (minimizerParameter_pos hL hfmin B).ne'

theorem normalizedMinimizerValue_zero
    {L : ℝ} (_hL : 0 < L) {f : HalfLineH1} (_hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : f.normalizedMinimizerValue B 0 = 0 := by
  unfold normalizedMinimizerValue
  rw [mul_zero, f.continuousRep_zero, zero_div]

theorem normalizedMinimizerValue_one
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : f.normalizedMinimizerValue B 1 = 0 := by
  unfold normalizedMinimizerValue
  rw [mul_one]
  change f.continuousRep f.positivityHullEndpoint /
    (f.minimizerSlope B * f.minimizerSupport) = 0
  rw [continuousRep_positivityHullEndpoint_eq_zero hL hfmin B, zero_div]

theorem normalizedMinimizerValue_deriv_one
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    deriv (fun y => f.normalizedMinimizerValue B y) 1 = 0 := by
  unfold normalizedMinimizerValue
  have hK := minimizerSupport_pos hL hfmin B
  have hD := minimizerSlope_pos hL hfmin B
  have hder := (hasDerivAt_continuousRep_positivityHullEndpoint_zero hL hfmin B)
  have hcomp : HasDerivAt (fun y => f.continuousRep (f.minimizerSupport * y)) 0 1 := by
    unfold minimizerSupport
    have hder' : HasDerivAt f.continuousRep 0 (f.positivityHullEndpoint * 1) := by
      simpa using hder
    convert hder'.comp 1 (hasDerivAt_const_mul f.positivityHullEndpoint) using 1
    · rfl
    · simp
  have hden : f.minimizerSlope B * f.minimizerSupport ≠ 0 :=
    mul_ne_zero hD.ne' hK.ne'
  have hquot := hcomp.div_const (f.minimizerSlope B * f.minimizerSupport)
  simpa [deriv_zero, hden] using hquot.deriv

theorem minimizer_value_representation
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    ∃ A : ℝ, ∀ x ∈ Icc 0 f.minimizerSupport,
      f.continuousRep x =
        A * Real.sin (Real.sqrt f.rayleighQuotient * x) +
          (-B.massMultiplier / f.rayleighQuotient) *
            (Real.cos (Real.sqrt f.rayleighQuotient * x) - 1) +
          f.minimizerSlope B * x := by
  let K := f.minimizerSupport
  let q := f.rayleighQuotient
  let k := Real.sqrt q
  let D := f.minimizerSlope B
  let a := B.massMultiplier
  let b := B.momentMultiplier
  have hK : 0 < K := by exact minimizerSupport_pos hL hfmin B
  have hq : 0 < q := by exact minimizerRayleighQuotient_pos hL hfmin
  have hq0 : q ≠ 0 := hq.ne'
  have hk : k ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  have hk2 : k^2 = q := by dsimp [k]; exact Real.sq_sqrt hq.le
  have hfirst : ∀ x ∈ Ioo 0 K,
      HasDerivAt (fun z => f.continuousRep z - (a / q + D*z))
        (deriv f.continuousRep x - D) x := by
    intro x hx
    have hx' : x ∈ Ioo 0 f.positivityHullEndpoint := by
      simpa [K, minimizerSupport] using hx
    have h := continuousRep_hasDerivAt_on_Ioo_positivityHullEndpoint hL hfmin B hx'
    convert h.sub ((hasDerivAt_const x (a / q)).add ((hasDerivAt_id x).const_mul D)) using 1
    · funext z
      dsimp [a, q, D]
    · dsimp [a, q, D]
      ring
  have hsecond : ∀ x ∈ Ioo 0 K,
      HasDerivAt (fun z => deriv f.continuousRep z - D)
        (-(k^2) * (f.continuousRep x - (a / q + D*x))) x := by
    intro x hx
    have hx' : x ∈ Ioo 0 f.positivityHullEndpoint := by
      simpa [K, minimizerSupport] using hx
    have h :=
      RayleighKernel.Analysis.HalfLineH1.hasDerivAt_deriv_continuousRep_on_Ioo_positivityHullEndpoint
        hL hfmin B hx'
    convert h.sub (hasDerivAt_const x D) using 1
    have hD : D = b / q := by rfl
    rw [hD]
    rw [hk2]
    dsimp [a, b, q]
    rw [show f.rayleighQuotient = q from rfl] at h ⊢
    field_simp [hq0]
    ring
  obtain ⟨A, C, hrep⟩ := harmonic_representation_on_Ioo hk hfirst hsecond
  let rhs : ℝ → ℝ := fun x => A * Real.sin (k*x) + C * Real.cos (k*x) + a/q + D*x
  have hraw : EqOn f.continuousRep rhs (Ioo 0 K) := by
    intro x hx
    have h := hrep x hx
    dsimp [rhs]
    have := congrArg (fun z => z + (a/q + D*x)) h
    linarith
  have rhsContinuous : Continuous rhs := by
    fun_prop
  have hclosure := hraw.closure f.continuous_continuousRep rhsContinuous
  have hclosed : EqOn f.continuousRep rhs (Icc 0 K) := by
    rw [closure_Ioo hK.ne] at hclosure
    exact hclosure
  have hzero := hclosed ⟨le_rfl, hK.le⟩
  have hC : C = -a/q := by
    dsimp [rhs] at hzero
    rw [f.continuousRep_zero] at hzero
    simp at hzero
    field_simp [hq0] at hzero ⊢
    linarith [hzero]
  refine ⟨A, ?_⟩
  intro x hx
  have h := hclosed hx
  dsimp [rhs, K, k, q, D, a] at h ⊢
  dsimp [a] at hC
  change C = -B.massMultiplier / f.rayleighQuotient at hC
  rw [hC] at h
  convert h using 1
  ring_nf

theorem normalized_value_representation
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    ∃ A C : ℝ,
      (∀ y ∈ Set.Icc (0 : ℝ) 1,
        f.normalizedMinimizerValue B y =
          A * Real.sin (f.minimizerParameter * y) +
          C * (Real.cos (f.minimizerParameter * y) - 1) + y) ∧
      A * Real.sin f.minimizerParameter +
          C * (Real.cos f.minimizerParameter - 1) + 1 = 0 := by
  obtain ⟨Araw, hA⟩ := minimizer_value_representation hL hfmin B
  let Abar := Araw / (f.minimizerSlope B * f.minimizerSupport)
  let Cbar := (-B.massMultiplier / f.rayleighQuotient) /
    (f.minimizerSlope B * f.minimizerSupport)
  have hK : 0 < f.minimizerSupport := minimizerSupport_pos hL hfmin B
  have hD : 0 < f.minimizerSlope B := minimizerSlope_pos hL hfmin B
  have hden : f.minimizerSlope B * f.minimizerSupport ≠ 0 :=
    mul_ne_zero hD.ne' hK.ne'
  have hrepr : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      f.normalizedMinimizerValue B y =
        Abar * Real.sin (f.minimizerParameter * y) +
          Cbar * (Real.cos (f.minimizerParameter * y) - 1) + y := by
    intro y hy
    have hKy : f.minimizerSupport * y ∈ Set.Icc 0 f.minimizerSupport := by
      constructor
      · exact mul_nonneg hK.le hy.1
      · nlinarith [mul_le_mul_of_nonneg_left hy.2 hK.le]
    have htarg : Real.sqrt f.rayleighQuotient *
        (f.minimizerSupport * y) = f.minimizerParameter * y := by
      unfold minimizerParameter
      ring
    have hraw := hA (f.minimizerSupport * y) hKy
    unfold normalizedMinimizerValue
    rw [htarg] at hraw
    rw [hraw]
    dsimp [Abar, Cbar]
    field_simp [hden]
  refine ⟨Abar, Cbar, hrepr, ?_⟩
  have hboundary := hrepr 1 ⟨zero_le_one, le_rfl⟩
  rw [normalizedMinimizerValue_one hL hfmin B] at hboundary
  simpa using hboundary.symm

theorem minimizerParameter_cos_ne_one
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    Real.cos f.minimizerParameter ≠ 1 := by
  obtain ⟨A, C, hrepr, hboundary⟩ :=
    normalized_value_representation hL hfmin B
  intro hcos
  let t := f.minimizerParameter
  have hsin_sq : Real.sin t ^ 2 = 0 := by
    have htrig := Real.sin_sq_add_cos_sq t
    rw [hcos] at htrig
    nlinarith
  have hsin : Real.sin t = 0 := (sq_eq_zero_iff.mp hsin_sq)
  have hboundary' := hboundary
  dsimp [t] at hsin
  rw [hcos, hsin] at hboundary'
  norm_num at hboundary'

theorem boundary_system_inconsistent_at_two_pi_nat
    (A C : ℝ) {n : ℕ} (_hn : 1 ≤ n) :
    A * Real.sin (2 * Real.pi * (n : ℝ)) +
        C * (Real.cos (2 * Real.pi * (n : ℝ)) - 1) + 1 ≠ 0 := by
  have hsin : Real.sin (2 * Real.pi * (n : ℝ)) = 0 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using Real.sin_nat_mul_pi (2 * n)
  have hcos : Real.cos (2 * Real.pi * (n : ℝ)) = 1 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using Real.cos_nat_mul_two_pi n
  rw [hsin, hcos]
  norm_num

theorem normalized_representation_with_explicit_coefficients
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    ∃ A C : ℝ,
      (∀ y ∈ Icc (0:ℝ) 1,
        f.normalizedMinimizerValue B y =
          A * Real.sin (f.minimizerParameter*y) +
           C * (Real.cos (f.minimizerParameter*y)-1)+y) ∧
      C = (-B.massMultiplier / f.rayleighQuotient) /
        (f.minimizerSlope B * f.minimizerSupport) ∧
      A * Real.sin f.minimizerParameter +
          C * (Real.cos f.minimizerParameter-1)+1=0 ∧
      f.minimizerParameter*A*Real.cos f.minimizerParameter -
          f.minimizerParameter*C*Real.sin f.minimizerParameter + 1=0 := by
  obtain ⟨Araw, hA⟩ := minimizer_value_representation hL hfmin B
  let K := f.minimizerSupport
  let q := f.rayleighQuotient
  let k := Real.sqrt q
  let D := f.minimizerSlope B
  let Craw := -B.massMultiplier / q
  let rawRhs : ℝ → ℝ := fun x =>
    Araw * Real.sin (k*x) + Craw * (Real.cos (k*x)-1) + D*x
  let Abar := Araw / (D*K)
  let Cbar := Craw / (D*K)
  have hK : 0 < K := by exact minimizerSupport_pos hL hfmin B
  have hq : 0 < q := by exact minimizerRayleighQuotient_pos hL hfmin
  have hk : 0 < k := Real.sqrt_pos.2 hq
  have hD : 0 < D := by exact minimizerSlope_pos hL hfmin B
  have hden : D*K ≠ 0 := mul_ne_zero hD.ne' hK.ne'
  have hA' : ∀ x ∈ Icc (0:ℝ) K, f.continuousRep x = rawRhs x := by
    intro x hx
    have h := hA x hx
    dsimp [rawRhs, K, q, k, D, Craw]
    simpa using h
  have hev : rawRhs =ᶠ[𝓝[Iic K] K] f.continuousRep := by
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨Ioi 0, Ioi_mem_nhds hK, ?_⟩
    intro x hx
    exact (hA' x ⟨le_of_lt hx.1, hx.2⟩).symm
  have hsmooth : HasDerivWithinAt f.continuousRep 0 (Iic K) K := by
    exact (hasDerivAt_continuousRep_positivityHullEndpoint_zero hL hfmin B).hasDerivWithinAt
  have hrawDeriv : HasDerivAt rawRhs
      (k*Araw*Real.cos (k*K) - k*Craw*Real.sin (k*K) + D) K := by
    dsimp [rawRhs]
    have hs := ((Real.hasDerivAt_sin (k*K)).comp K (hasDerivAt_const_mul k)).const_mul Araw
    have hc := ((Real.hasDerivAt_cos (k*K)).comp K (hasDerivAt_const_mul k)).sub_const 1
    have hc' := hc.const_mul Craw
    have hi := (hasDerivAt_id K).const_mul D
    convert (hs.add hc').add hi using 1
    · funext z
      simp [id]
    · ring
  have hrawWithin : HasDerivWithinAt rawRhs 0 (Iic K) K := by
    exact (hev.hasDerivWithinAt_iff (by rw [hA' K ⟨hK.le, le_rfl⟩])).mpr hsmooth
  have hexp : derivWithin rawRhs (Iic K) K =
      k*Araw*Real.cos (k*K) - k*Craw*Real.sin (k*K) + D :=
    hrawDeriv.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic K)
  have hslope : k*Araw*Real.cos (k*K) - k*Craw*Real.sin (k*K) + D = 0 := by
    rw [← hexp]
    exact hrawWithin.derivWithin (uniqueDiffWithinAt_Iic K)
  have hrepr : ∀ y ∈ Icc (0:ℝ) 1,
      f.normalizedMinimizerValue B y =
        Abar * Real.sin (f.minimizerParameter*y) +
          Cbar * (Real.cos (f.minimizerParameter*y)-1)+y := by
    intro y hy
    have hKy : K*y ∈ Icc (0:ℝ) K := ⟨mul_nonneg hK.le hy.1,
      by nlinarith [mul_le_mul_of_nonneg_left hy.2 hK.le]⟩
    have ht : k*(K*y) = f.minimizerParameter*y := by
      dsimp [k, K, q, minimizerParameter]
      ring
    have h := hA' (K*y) hKy
    unfold normalizedMinimizerValue
    change f.continuousRep (K*y) / (D*K) = _
    rw [h]
    dsimp [rawRhs]
    rw [ht]
    dsimp [Abar, Cbar, rawRhs]
    field_simp [hden]
  refine ⟨Abar, Cbar, hrepr, rfl, ?_, ?_⟩
  · have h := hrepr 1 ⟨zero_le_one, le_rfl⟩
    rw [normalizedMinimizerValue_one hL hfmin B] at h
    simpa using h.symm
  · have hk2 : k^2 = q := by dsimp [k]; exact Real.sq_sqrt hq.le
    have hp : f.minimizerParameter = k*K := by
      dsimp [minimizerParameter, k, K, q]
    rw [hp]
    dsimp [Abar, Cbar]
    field_simp [hden]
    dsimp [D, Craw] at hslope
    nlinarith [hslope]

theorem normalized_representation_with_boundaries
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    ∃ A C : ℝ,
      (∀ y ∈ Icc (0:ℝ) 1,
        f.normalizedMinimizerValue B y =
          A * Real.sin (f.minimizerParameter*y) +
            C * (Real.cos (f.minimizerParameter*y)-1)+y) ∧
      A * Real.sin f.minimizerParameter +
          C * (Real.cos f.minimizerParameter-1)+1=0 ∧
      f.minimizerParameter*A*Real.cos f.minimizerParameter -
          f.minimizerParameter*C*Real.sin f.minimizerParameter + 1=0 := by
  obtain ⟨A, C, hrepr, _, hvalue, hslope⟩ :=
    normalized_representation_with_explicit_coefficients hL hfmin B
  exact ⟨A, C, hrepr, hvalue, hslope⟩

theorem no_boundary_value_solution_of_cos_eq_one
    {t : ℝ} (hcos : Real.cos t = 1) :
    ¬ ∃ A C : ℝ, A * Real.sin t + C * (Real.cos t - 1) + 1 = 0 := by
  rintro ⟨A, C, hvalue⟩
  have hsin : Real.sin t = 0 := by
    have htrig := Real.sin_sq_add_cos_sq t
    rw [hcos] at htrig
    nlinarith
  rw [hcos] at hvalue
  rw [hsin] at hvalue
  norm_num at hvalue

theorem no_boundary_value_solution_at_nat_mul_two_pi
    {n : ℕ} (hn : 1 ≤ n) :
    ¬ ∃ A C : ℝ,
      A * Real.sin ((2 * Real.pi) * n) +
        C * (Real.cos ((2 * Real.pi) * n) - 1) + 1 = 0 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcos : Real.cos ((2 * Real.pi) * n) = 1 := by
    simpa [mul_comm, hnreal] using Real.cos_nat_mul_two_pi n
  exact no_boundary_value_solution_of_cos_eq_one hcos

theorem minimizerParameter_ne_nat_mul_two_pi
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {n : ℕ} (hn : 1 ≤ n) :
    f.minimizerParameter ≠ (2 * Real.pi) * n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  intro hparameter
  apply minimizerParameter_cos_ne_one hL hfmin B
  rw [hparameter]
  simpa [mul_comm, hnreal] using Real.cos_nat_mul_two_pi n

theorem boundary_coefficients_eq_profile
    {t A C : ℝ} (ht : t ≠ 0) (hcos : Real.cos t ≠ 1)
    (hvalue : A * Real.sin t + C * (Real.cos t - 1) + 1 = 0)
    (hslope : t * A * Real.cos t - t * C * Real.sin t + 1 = 0) :
    A = RayleighKernel.Profile.coefficientA t ∧
      C = RayleighKernel.Profile.coefficientC t := by
  have htrig := Real.sin_sq_add_cos_sq t
  have hCeq : C * (t * (Real.cos t - 1)) = t * Real.cos t - Real.sin t := by
    linear_combination Real.sin t * hslope - t * Real.cos t * hvalue +
      t * C * htrig
  have hden : t * (Real.cos t - 1) ≠ 0 := mul_ne_zero ht (sub_ne_zero.mpr hcos)
  have hC : C = RayleighKernel.Profile.coefficientC t := by
    unfold RayleighKernel.Profile.coefficientC
    field_simp [hden]
    simpa [mul_assoc] using hCeq
  have hAeq : A * (t * (Real.cos t - 1)) = t * Real.sin t + Real.cos t - 1 := by
    linear_combination -t * Real.sin t * hvalue -
      (Real.cos t - 1) * hslope + t * A * htrig
  have hA : A = RayleighKernel.Profile.coefficientA t := by
    unfold RayleighKernel.Profile.coefficientA
    field_simp [hden]
    simpa [mul_assoc] using hAeq
  exact ⟨hA, hC⟩

theorem coefficientC_minimizerParameter_eq_firstMoment_div_support
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    RayleighKernel.Profile.coefficientC f.minimizerParameter =
      L / f.minimizerSupport := by
  obtain ⟨A, C, hrepr, hCbar, hvalue, hslope⟩ :=
    normalized_representation_with_explicit_coefficients hL hfmin B
  have hcoeff := boundary_coefficients_eq_profile
    (minimizerParameter_ne_zero hL hfmin B)
    (minimizerParameter_cos_ne_one hL hfmin B) hvalue hslope
  have hq := minimizerRayleighQuotient_pos hL hfmin
  have hD := minimizerSlope_pos hL hfmin B
  have hK := minimizerSupport_pos hL hfmin B
  have hbal := B.massMultiplier_add_momentMultiplier_mul_eq_zero hL hfmin
  rw [← hcoeff.2, hCbar]
  unfold minimizerSlope
  have hb : B.momentMultiplier ≠ 0 := by
    intro hb
    unfold minimizerSlope at hD
    rw [hb, zero_div] at hD
    exact (ne_of_gt hD) rfl
  field_simp [hq.ne', hD.ne', hK.ne', hb]
  nlinarith [hbal]

theorem normalizedMinimizerValue_eq_profile_value
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    f.normalizedMinimizerValue B y =
      RayleighKernel.Profile.value f.minimizerParameter y := by
  obtain ⟨A, C, hrepr, hvalue, hslope⟩ :=
    normalized_representation_with_boundaries hL hfmin B
  have hcoeff := boundary_coefficients_eq_profile
    (minimizerParameter_ne_zero hL hfmin B)
    (minimizerParameter_cos_ne_one hL hfmin B) hvalue hslope
  rw [hrepr y hy, hcoeff.1, hcoeff.2]
  rfl

theorem integral_continuousRep_zero_minimizerSupport
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    (∫ x in (0 : ℝ)..f.minimizerSupport, f.continuousRep x) = 1 := by
  let K := f.minimizerSupport
  have hsupp : Function.support f.continuousRep ⊆ Ioc (0 : ℝ) K := by
    intro x hx
    have hxs := support_continuousRep_subset_Icc_positivityHullEndpoint hL hfmin B hx
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_ne hxs.1 (Ne.symm (by
        intro hx0
        exact hx (by simp [hx0, f.continuousRep_zero])))
    · simpa [K, minimizerSupport] using hxs.2
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp]
  have hInt := f.continuousRep_integrable_of_integrableOn_halfLine hfmin.1.integrable
  have hmass : (∫ x : ℝ, f.continuousRep x) = 1 := by
    have hcomp : (∫ x in (Ici (0 : ℝ))ᶜ, f.continuousRep x) = 0 := by
      apply integral_eq_zero_of_ae
      refine (ae_restrict_iff' measurableSet_Ici.compl).2 ?_
      filter_upwards with x hx
      exact f.continuousRep_eq_zero_of_nonpositive
        (le_of_lt (by simpa [mem_Ici] using hx))
    have hdecomp := integral_add_compl (s := Ici (0 : ℝ)) measurableSet_Ici hInt
    rw [hcomp] at hdecomp
    rw [← hfmin.1.mass_eq]
    unfold HalfLineH1.mass RayleighKernel.mass halfLine
    linarith
  exact hmass

theorem integral_mul_continuousRep_zero_minimizerSupport
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    (∫ x in (0 : ℝ)..f.minimizerSupport, x * f.continuousRep x) = L := by
  let K := f.minimizerSupport
  have hsupp : Function.support (fun x => x * f.continuousRep x) ⊆ Ioc (0 : ℝ) K := by
    intro x hx
    have hxs : x ∈ Function.support f.continuousRep := by
      intro hz
      exact hx (by simp [hz])
    have hxs' := support_continuousRep_subset_Icc_positivityHullEndpoint hL hfmin B hxs
    refine ⟨?_, ?_⟩
    · exact lt_of_le_of_ne hxs'.1 (Ne.symm (by
        intro hx0
        exact hx (by simp [hx0, f.continuousRep_zero])))
    · simpa [K, minimizerSupport] using hxs'.2
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp]
  have hInt : Integrable (fun x => x * f.continuousRep x) := by
    rw [← integrableOn_univ]
    rw [← show Iic (0 : ℝ) ∪ Ici 0 = univ from Iic_union_Ici]
    apply IntegrableOn.union
    · exact (integrableOn_congr_fun
        (f := fun x => x * f.continuousRep x) (g := fun _ : ℝ => 0) (s := Iic 0)
        (fun x hx => by simp [f.continuousRep_eq_zero_of_nonpositive hx])
        measurableSet_Iic).mpr integrableOn_zero
    · exact hfmin.1.firstMoment_integrable
  have hcomp : (∫ x in (Ici (0 : ℝ))ᶜ, x * f.continuousRep x) = 0 := by
    apply integral_eq_zero_of_ae
    refine (ae_restrict_iff' measurableSet_Ici.compl).2 ?_
    filter_upwards with x hx
    rw [f.continuousRep_eq_zero_of_nonpositive
      (le_of_lt (by simpa [mem_Ici] using hx))]
    simp
  have hdecomp := integral_add_compl (s := Ici (0 : ℝ)) measurableSet_Ici hInt
  rw [hcomp] at hdecomp
  rw [← hfmin.1.firstMoment_eq]
  unfold HalfLineH1.firstMoment RayleighKernel.firstMoment halfLine
  linarith

theorem momentZero_minimizerParameter
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    RayleighKernel.Profile.momentZero f.minimizerParameter =
      1 / (f.minimizerSlope B * f.minimizerSupport ^ 2) := by
  let K := f.minimizerSupport
  let D := f.minimizerSlope B
  have hK : 0 < K := minimizerSupport_pos hL hfmin B
  have heq : (∫ y in (0 : ℝ)..1, RayleighKernel.Profile.value f.minimizerParameter y) =
      ∫ y in (0 : ℝ)..1, f.normalizedMinimizerValue B y := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact (normalizedMinimizerValue_eq_profile_value hL hfmin B
      (by simpa [uIcc_of_le zero_le_one] using hy)).symm
  rw [RayleighKernel.Profile.momentZero, heq]
  have hscale : (∫ y in (0 : ℝ)..1, f.continuousRep (K * y)) = K⁻¹ := by
    rw [intervalIntegral.integral_comp_mul_left (f := f.continuousRep)
      (a := (0 : ℝ)) (b := 1) hK.ne']
    simp [K, integral_continuousRep_zero_minimizerSupport hL hfmin B, smul_eq_mul]
  calc
    (∫ y in (0 : ℝ)..1, f.normalizedMinimizerValue B y) =
        (D * K)⁻¹ * ∫ y in (0 : ℝ)..1, f.continuousRep (K * y) := by
          unfold normalizedMinimizerValue
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro y hy
          ring
    _ = 1 / (D * K ^ 2) := by
      rw [hscale]
      dsimp [D, K]
      field_simp

theorem momentOne_minimizerParameter
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    RayleighKernel.Profile.momentOne f.minimizerParameter =
      L / (f.minimizerSlope B * f.minimizerSupport ^ 3) := by
  let K := f.minimizerSupport
  let D := f.minimizerSlope B
  have hK : 0 < K := minimizerSupport_pos hL hfmin B
  have heq : (∫ y in (0 : ℝ)..1, y * RayleighKernel.Profile.value
        f.minimizerParameter y) =
      ∫ y in (0 : ℝ)..1, y * f.normalizedMinimizerValue B y := by
    apply intervalIntegral.integral_congr
    intro y hy
    simpa using congrArg (fun z : ℝ => y * z)
      (normalizedMinimizerValue_eq_profile_value hL hfmin B
        (by simpa [uIcc_of_le zero_le_one] using hy)).symm
  rw [RayleighKernel.Profile.momentOne, heq]
  have hscale : (∫ y in (0 : ℝ)..1, y * f.continuousRep (K * y)) =
      L / K ^ 2 := by
    have hc := intervalIntegral.integral_comp_mul_left
      (f := fun x => x * f.continuousRep x) (a := (0 : ℝ)) (b := 1) hK.ne'
    have hfirst := integral_mul_continuousRep_zero_minimizerSupport hL hfmin B
    calc
      (∫ y in (0 : ℝ)..1, y * f.continuousRep (K * y)) =
          K⁻¹ * ∫ y in (0 : ℝ)..1, (K * y) * f.continuousRep (K * y) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro y hy
            field_simp
      _ = K⁻¹ * (K⁻¹ • ∫ x in (0 : ℝ)..K, x * f.continuousRep x) := by
            rw [hc]
            congr 2
            simp
      _ = L / K ^ 2 := by
            rw [hfirst]
            simp [smul_eq_mul]
            field_simp
  calc
    (∫ y in (0 : ℝ)..1, y * f.normalizedMinimizerValue B y) =
        (D * K)⁻¹ * ∫ y in (0 : ℝ)..1, y * f.continuousRep (K * y) := by
          unfold normalizedMinimizerValue
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro y hy
          ring
    _ = L / (D * K ^ 3) := by
      rw [hscale]
      dsimp [D, K]
      field_simp

theorem minimizerParameter_eq_tStar
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    f.minimizerParameter = RayleighKernel.Profile.tStar := by
  let K := f.minimizerSupport
  let D := f.minimizerSlope B
  let t := f.minimizerParameter
  have hK : 0 < K := minimizerSupport_pos hL hfmin B
  have hD : 0 < D := minimizerSlope_pos hL hfmin B
  have ht : 0 < t := minimizerParameter_pos hL hfmin B
  have htwopi : t < 2 * Real.pi := by
    by_contra h
    have hge : 2 * Real.pi ≤ t := le_of_not_gt h
    by_cases heq : t = 2 * Real.pi
    · apply minimizerParameter_cos_ne_one hL hfmin B
      rw [show f.minimizerParameter = 2 * Real.pi from heq]
      exact Real.cos_two_pi
    · have hneg := RayleighKernel.Profile.exists_value_neg_of_two_pi_lt
        (lt_of_le_of_ne hge (Ne.symm heq))
        (by exact fun hc => minimizerParameter_cos_ne_one hL hfmin B (by simpa [hc]))
      obtain ⟨y, hy, hval⟩ := hneg
      have hnon := hfmin.1.nonnegative (K * y) (by
        simp only [halfLine]
        exact mul_nonneg hK.le hy.1.le)
      have heqv := normalizedMinimizerValue_eq_profile_value hL hfmin B
        ⟨hy.1.le, hy.2.le⟩
      have hden : 0 < f.minimizerSlope B * f.minimizerSupport :=
        mul_pos hD hK
      have hnorm : 0 ≤ f.normalizedMinimizerValue B y := by
        unfold normalizedMinimizerValue
        exact div_nonneg hnon hden.le
      rw [heqv] at hnorm
      exact (not_lt_of_ge hnorm) hval
  have hzero := momentZero_minimizerParameter hL hfmin B
  have hone := momentOne_minimizerParameter hL hfmin B
  have hC := coefficientC_minimizerParameter_eq_firstMoment_div_support hL hfmin B
  have hcons : RayleighKernel.Profile.coefficientC t *
        RayleighKernel.Profile.momentZero t = RayleighKernel.Profile.momentOne t := by
    rw [hC, hzero, hone]
    field_simp
  exact (RayleighKernel.Profile.coefficientC_mul_momentZero_eq_momentOne_iff_tStar ht htwopi).mp hcons

end RayleighKernel.Analysis.HalfLineH1
