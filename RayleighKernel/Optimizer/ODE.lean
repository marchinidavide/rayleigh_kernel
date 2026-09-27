import RayleighKernel.Optimizer.Geometry
import RayleighKernel.Obstacle.HomogeneousKKT

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open RayleighKernel
namespace RayleighKernel.Analysis.HalfLineH1

theorem CorrectionBumps.localReducedProfile_eq_affineOn_of_restrict_eq_zero
    {L : ℝ} {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {a b p q : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : a < p) (hpq : p < q) (hq : q < b)
    (hzero : (B.localReactionMeasure hfmin a b).restrict (Icc p q) = 0) :
    ∃ m d : ℝ, ∀ x ∈ Ioo p q,
      B.localReducedProfile f a x = m * x + d := by
  obtain ⟨c, hc⟩ := B.exists_localReducedProfile_sub_eq_integral_const_sub_cdf
    hfmin ha hab
  let μ := B.localReactionMeasure hfmin a b
  let m := c - measureCDF μ p
  let d := B.localReducedProfile f a p - m * p
  have hcdf : ∀ x ∈ Ioo p q, measureCDF μ x = measureCDF μ p := by
    intro x hx
    have hz : μ (Ioc p x) = 0 := by
      have hsub : Ioc p x ⊆ Icc p q := by
        intro y hy
        exact ⟨le_of_lt hy.1, le_trans hy.2 hx.2.le⟩
      exact measure_mono_null hsub (by
        have := congrArg (fun ν : Measure ℝ => ν Set.univ) hzero
        rw [Measure.restrict_apply MeasurableSet.univ] at this
        simpa using this)
    have hdecomp : Iic x = Iic p ∪ Ioc p x := by
      ext y
      constructor
      · intro hy
        by_cases h : y ≤ p
        · exact Or.inl h
        · exact Or.inr ⟨lt_of_not_ge h, hy⟩
      · rintro (hy | hy)
        · exact hy.trans hx.1.le
        · exact hy.2
    have hadd := measure_union (μ := μ)
      (show Disjoint (Iic p) (Ioc p x) by
        rw [Set.disjoint_left]
        intro y hy₁ hy₂
        exact (not_lt_of_ge hy₁) hy₂.1) measurableSet_Ioc
    have hmeasure : μ (Iic x) = μ (Iic p) := by
      rw [hdecomp, hadd, hz, add_zero]
    simpa [measureCDF, MeasureTheory.measureReal_def] using
      congrArg ENNReal.toReal hmeasure
  refine ⟨m, d, ?_⟩
  intro x hx
  have hsub := hc (show p ∈ Ioo a b from ⟨hp, lt_trans hpq hq⟩)
    (show x ∈ Ioo a b from ⟨lt_trans hp hx.1, lt_trans hx.2 hq⟩)
  have hint : (∫ t in p..x, (c - measureCDF μ t)) = (x - p) * m := by
    calc
      _ = ∫ t in p..x, m := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with t ht
        have ht' : t ∈ uIcc p x := uIoc_subset_uIcc ht
        have htI : t ∈ Ioo p q := by
          rcases le_total p x with hpx | hxp
          · rw [uIcc_of_le hpx] at ht'
            rw [uIoc_of_le hpx] at ht
            exact ⟨ht.1, lt_of_le_of_lt ht'.2 hx.2⟩
          · rw [uIcc_of_ge hxp] at ht'
            exact (False.elim ((not_le_of_gt hx.1) hxp))
        dsimp [m]
        rw [hcdf t htI]
      _ = _ := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul]
  dsimp [d]
  linarith [hsub, hint]

theorem CorrectionBumps.hasDerivAt_deriv_continuousRep_of_mem_positivityHullInterior
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {p q x : ℝ}
    (hpq : p < q) (hcompact : Icc p q ⊆ f.positivityHullInterior)
    (hx : x ∈ Ioo p q) :
    HasDerivAt (deriv f.continuousRep)
      (-(f.rayleighQuotient * f.continuousRep x - B.massMultiplier -
        B.momentMultiplier * x)) x := by
  have hp : 0 < p := by
    have := (hcompact ⟨le_rfl, hpq.le⟩).1
    exact this
  obtain ⟨z, hz, hqz⟩ := (hcompact ⟨hpq.le, le_rfl⟩).2
  let a' : ℝ := p / 2
  let b' : ℝ := (q + z) / 2
  have ha' : 0 < a' := by dsimp [a']; linarith
  have ha'p : a' < p := by dsimp [a']; linarith
  have hqb' : q < b' := by dsimp [b']; linarith
  have hab' : a' < b' := by dsimp [a', b']; linarith
  have hglobal := B.reactionMeasure_positivityHullInterior_eq_zero hL hfmin
  have hzero : (B.localReactionMeasure hfmin a' b').restrict (Icc p q) = 0 := by
    apply Measure.measure_univ_eq_zero.mp
    rw [Measure.restrict_apply MeasurableSet.univ]
    rw [univ_inter]
    rw [HalfLineH1.CorrectionBumps.localReactionMeasure,
      Measure.map_apply continuous_subtype_val.measurable measurableSet_Icc,
      Measure.restrict_apply
        (measurableSet_Icc.preimage continuous_subtype_val.measurable)]
    apply measure_mono_null _ hglobal
    intro y hy
    exact hcompact hy.1
  obtain ⟨m, d, hline⟩ := B.localReducedProfile_eq_affineOn_of_restrict_eq_zero
    hfmin ha' hab' ha'p hpq hqb' hzero
  let F : ℝ → ℝ := fun y => f.rayleighQuotient * f.continuousRep y -
    B.massMultiplier - B.momentMultiplier * y
  have hF : Continuous F := by
    dsimp [F]
    exact (((continuous_const.mul f.continuous_continuousRep).sub continuous_const).sub
      (continuous_const.mul continuous_id))
  have hprof : HasDerivAt (B.localReducedProfile f a') m x := by
    have hlin : HasDerivAt (fun y : ℝ => m * y + d) m x := by
      simpa using ((hasDerivAt_id x).const_mul m).add_const d
    apply hlin.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hline y hy
  have hderivF : HasDerivAt (fun y => forcingPrimitive F a' y) (F x) x :=
    forcingPrimitive_hasDerivAt hF a' x
  have hderiv : HasDerivAt (deriv f.continuousRep)
      (-F x) x := by
    have heq : ∀ᶠ y in nhds x, deriv f.continuousRep y =
        m - forcingPrimitive F a' y := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      rw [B.deriv_continuousRep_eq hfmin ha' hab'
        ⟨lt_trans ha'p hy.1, lt_trans hy.2 hqb'⟩]
      have hl := (hline y hy)
      have hlin : HasDerivAt (fun t : ℝ => m * t + d) m y := by
        simpa using ((hasDerivAt_id y).const_mul m).add_const d
      have hcongr := hlin.congr_of_eventuallyEq (by
        filter_upwards [Ioo_mem_nhds hy.1 hy.2] with t ht
        exact hline t ht)
      have hdy : deriv (B.localReducedProfile f a') y = m := hcongr.deriv
      rw [hdy]
    have hfun : HasDerivAt (fun y => m - forcingPrimitive F a' y) (-F x) x := by
      have hh := (hasDerivAt_const x m).add hderivF.neg
      convert hh using 1
      simp
    exact hfun.congr_of_eventuallyEq heq
  simpa [F] using hderiv

theorem CorrectionBumps.ode_on_Ioo_of_Icc_subset_positivityHullInterior
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {p q : ℝ} (hpq : p < q)
    (hcompact : Icc p q ⊆ f.positivityHullInterior) :
    ∀ x ∈ Ioo p q,
      deriv (deriv f.continuousRep) x + f.rayleighQuotient * f.continuousRep x =
        B.massMultiplier + B.momentMultiplier * x := by
  intro x hx
  have h := B.hasDerivAt_deriv_continuousRep_of_mem_positivityHullInterior
    hL hfmin hpq hcompact hx
  have hd := h.deriv
  linarith [hd]

theorem positivityHullInterior_eq_Ioi_of_not_bddAbove
    {f : HalfLineH1} (h : ¬ BddAbove f.positivityHullInterior) :
    f.positivityHullInterior = Ioi 0 := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := (not_bddAbove_iff.mp h) x
    obtain ⟨_, z, hz, hyz⟩ := hy
    exact ⟨hx, z, hz, hxy.trans hyz⟩


private lemma not_secondDeriv_ge_on_Ioi_of_tendsto_zero
    {g g' g'' : ℝ → ℝ} {R c : ℝ} (hc : 0 < c)
    (hg : ∀ x ∈ Ioi R, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioi R, HasDerivAt g' (g'' x) x)
    (hcurv : ∀ x ∈ Ioi R, c ≤ g'' x)
    (hlim : Tendsto g atTop (𝓝 0)) : False := by
  let r : ℝ := R + 1
  have hr : R < r := by dsimp [r]; linarith
  let D : Set ℝ := Ici r
  have hD : Convex ℝ D := convex_Ici r
  have hg'c : ContinuousOn g' D := by
    intro x hx
    have hxR : R < x := lt_of_lt_of_le hr hx
    exact (hg' x hxR).continuousAt.continuousWithinAt
  have hg'd : DifferentiableOn ℝ g' (interior D) := by
    intro x hx
    have hxD : r < x := by simpa [D, interior_Ici] using hx
    have hxR : R < x := lt_trans hr hxD
    exact (hg' x hxR).differentiableAt.differentiableWithinAt
  have hcurv' : ∀ x ∈ interior D, c ≤ deriv g' x := by
    intro x hx
    have hxD : r < x := by simpa [D, interior_Ici] using hx
    have hxR : R < x := lt_trans hr hxD
    rw [(hg' x hxR).deriv]
    exact hcurv x hxR
  obtain ⟨X, hX, hX1⟩ : ∃ X, r ≤ X ∧ 1 ≤ g' r + c * (X - r) := by
    by_cases h : 1 ≤ g' r
    · exact ⟨r, le_rfl, by simpa⟩
    · let X := r + (1 - g' r) / c
      refine ⟨X, ?_, ?_⟩
      · dsimp [X]; linarith [div_pos (sub_pos.mpr (lt_of_not_ge h)) hc]
      · dsimp [X]; field_simp; linarith
  have hg'lower : ∀ y ∈ Ici r, X ≤ y → 1 ≤ g' y := by
    intro y hy hXy
    have hsec := hD.mul_sub_le_image_sub_of_le_deriv hg'c hg'd hcurv' r
      (show r ∈ D by simp [D]) y (by simpa [D] using hy) (le_trans hX hXy)
    have hry : r ≤ y := le_trans hX hXy
    have hbase : 1 ≤ g' r + c * (y - r) := by
      have hyminus : 0 ≤ y - r := sub_nonneg.mpr hry
      nlinarith [hX1]
    linarith
  let E : Set ℝ := Ici X
  have hgc : ContinuousOn g E := by
    intro x hx
    have hxX : X ≤ x := by simpa [E] using hx
    have hxR : R < x := lt_of_lt_of_le hr (le_trans hX hxX)
    exact (hg x hxR).continuousAt.continuousWithinAt
  have hgd : DifferentiableOn ℝ g (interior E) := by
    intro x hx
    have hxX : X < x := by simpa [E, interior_Ici] using hx
    have hxR : R < x := lt_of_lt_of_le hr (le_trans hX hxX.le)
    exact (hg x hxR).differentiableAt.differentiableWithinAt
  have hgd1 : ∀ x ∈ interior E, 1 ≤ deriv g x := by
    intro x hx
    have hxX : X < x := by simpa [E, interior_Ici] using hx
    have hxR : R < x := lt_of_lt_of_le hr (le_trans hX hxX.le)
    rw [(hg x hxR).deriv]
    exact hg'lower x (le_trans hX hxX.le) hxX.le
  have hsmall : ∀ᶠ x in atTop, |g x| < (1 : ℝ) / 4 := by
    rw [Metric.tendsto_atTop] at hlim
    simpa [Real.dist_eq] using hlim (1 / 4) (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  have h0 := hN (max N X) (le_max_left _ _)
  have h1 := hN (max N X + 1) (by linarith [le_max_left N X, le_max_right N X])
  have hgrowth := (convex_Ici X).mul_sub_le_image_sub_of_le_deriv
    hgc hgd hgd1 (max N X) (show X ≤ max N X from le_max_right _ _)
    (max N X + 1) (show X ≤ max N X + 1 by linarith [le_max_right N X])
      (by linarith)
  norm_num at hgrowth
  nlinarith [abs_lt.mp h0, abs_lt.mp h1, hgrowth]

private lemma not_secondDeriv_le_of_nonneg
    {g g' g'' : ℝ → ℝ} {R c : ℝ} (hc : 0 < c)
    (hg : ∀ x ∈ Ioi R, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Ioi R, HasDerivAt g' (g'' x) x)
    (hcurv : ∀ x ∈ Ioi R, g'' x ≤ -c)
    (hlim : Tendsto g atTop (𝓝 0)) : False := by
  exact not_secondDeriv_ge_on_Ioi_of_tendsto_zero (g := fun x => -g x)
    (g' := fun x => -g' x) (g'' := fun x => -g'' x) hc
    (fun x hx => (hg x hx).neg) (fun x hx => (hg' x hx).neg)
    (by intro x hx; linarith [hcurv x hx]) (by simpa using hlim.neg)

private lemma eq_zero_on_Ioi_of_secondDeriv_eq_neg_mul_of_nonneg_of_tendsto_zero
    {g g' g'' : ℝ → ℝ} {R q : ℝ} (hq : 0 < q)
    (hg' : ∀ x ∈ Ioi R, HasDerivAt g (g' x) x)
    (hg'' : ∀ x ∈ Ioi R, HasDerivAt g' (g'' x) x)
    (hode : ∀ x ∈ Ioi R, g'' x = -q * g x)
    (hnonneg : ∀ x ∈ Ioi R, 0 ≤ g x)
    (hlim : Tendsto g atTop (𝓝 0)) : ∀ x ∈ Ioi R, g x = 0 := by
  intro x hx
  by_contra hne
  have hxpos : 0 < g x := lt_of_le_of_ne (hnonneg x hx) (Ne.symm hne)
  have hsmall : ∀ᶠ y in atTop, |g y| < g x / 2 := by
    rw [Metric.tendsto_atTop] at hlim
    simpa [Real.dist_eq] using hlim (g x / 2) (by linarith)
  obtain ⟨y, hyx, hy⟩ : ∃ y, x < y ∧ |g y| < g x / 2 := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
    refine ⟨max (N + 1) (x + 1), ?_, hN _ (by linarith [le_max_left (N + 1) (x + 1)])⟩
    exact lt_of_lt_of_le (lt_add_of_pos_right x zero_lt_one) (le_max_right _ _)
  have hgy : g y < g x / 2 := (abs_lt.mp hy).2
  have hslxy : (g y - g x) / (y - x) < 0 := by
    apply div_neg_of_neg_of_pos <;> linarith
  have hconc : ConcaveOn ℝ (Ioi R) g := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (f := g) (f' := g') (f'' := g'')
      (convex_Ioi R) ?_ ?_ ?_ ?_
    · intro z hz; exact (hg' z hz).continuousAt.continuousWithinAt
    · intro z hz; exact (hg' z (by simpa [interior_Ioi] using hz)).hasDerivWithinAt
    · intro z hz; exact (hg'' z (by simpa [interior_Ioi] using hz)).hasDerivWithinAt
    · intro z hz
      have hz' : z ∈ Ioi R := by simpa [interior_Ioi] using hz
      rw [hode z hz']; nlinarith [hq, hnonneg z hz']
  have hzden : 0 < -(g y - g x) / (y - x) :=
    div_pos (neg_pos.mpr (by linarith [hslxy])) (sub_pos.mpr hyx)
  let z := y + (g y + 1) / (-(g y - g x) / (y - x))
  have hyz : y < z := by
    dsimp [z]
    have : 0 < g y + 1 := by linarith [hnonneg y (lt_trans hx hyx)]
    exact lt_add_of_pos_right y (div_pos this hzden)
  have hzray : z ∈ Ioi R := lt_trans hx hyx |>.trans hyz
  have hslope := hconc.slope_anti_adjacent hx hzray hyx hyz
  have hgz : g z < 0 := by
    have hcalc : g z - g y ≤ (z - y) * ((g y - g x) / (y - x)) := by
      rw [div_le_iff₀ (sub_pos.mpr hyz)] at hslope
      nlinarith [hslope]
    have heq : (z - y) * ((g y - g x) / (y - x)) = -(g y + 1) := by
      dsimp [z]
      have hden2 : g y - g x ≠ 0 := ne_of_lt (by linarith [hslxy])
      rw [div_eq_mul_inv]
      field_simp [hden2, ne_of_gt (sub_pos.mpr hyx)]
      ring
    rw [heq] at hcalc
    linarith
  exact (not_lt_of_ge (hnonneg z hzray)) hgz

private lemma eventually_one_le_affine_sub_of_pos_slope
    {g : ℝ → ℝ} {q a b : ℝ} (_hq : 0 < q) (hb : 0 < b)
    (hlim : Tendsto g atTop (𝓝 0)) : ∃ R, ∀ x ∈ Ioi R, 1 ≤ a + b*x - q*g x := by
  have hsmall : ∀ᶠ x in atTop, |q * g x| < (1 : ℝ) / 2 := by
    have hqg : Tendsto (fun x => q * g x) atTop (𝓝 0) := by simpa using hlim.const_mul q
    rw [Metric.tendsto_atTop] at hqg
    simpa [Real.dist_eq] using hqg (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  refine ⟨max N ((3 / 2 - a) / b), ?_⟩
  intro x hx
  have hNx := le_trans (le_max_left _ _) (show max N ((3 / 2 - a) / b) < x from hx).le
  have hsmallx := hN x hNx
  have hax := lt_of_le_of_lt (le_max_right _ _) (show max N ((3 / 2 - a) / b) < x from hx)
  have hlin : 3 / 2 - a < b * x := by rw [div_lt_iff₀ hb] at hax; simpa [mul_comm] using hax
  linarith [abs_lt.mp hsmallx]

private lemma eventually_affine_sub_le_neg_one_of_neg_slope
    {g : ℝ → ℝ} {q a b : ℝ} (_hq : 0 < q) (hb : b < 0)
    (hlim : Tendsto g atTop (𝓝 0)) : ∃ R, ∀ x ∈ Ioi R, a + b*x - q*g x ≤ -1 := by
  have hsmall : ∀ᶠ x in atTop, |q * g x| < (1 : ℝ) / 2 := by
    have hqg : Tendsto (fun x => q * g x) atTop (𝓝 0) := by simpa using hlim.const_mul q
    rw [Metric.tendsto_atTop] at hqg
    simpa [Real.dist_eq] using hqg (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  refine ⟨max N ((-3 / 2 - a) / b), ?_⟩
  intro x hx
  have hNx := le_trans (le_max_left _ _) (show max N ((-3 / 2 - a) / b) < x from hx).le
  have hsmallx := hN x hNx
  have hax := lt_of_le_of_lt (le_max_right _ _) (show max N ((-3 / 2 - a) / b) < x from hx)
  have hlin : b * x < -3 / 2 - a := by rw [div_lt_iff_of_neg hb] at hax; simpa [mul_comm] using hax
  linarith [abs_lt.mp hsmallx]

private lemma eventually_half_le_const_sub_of_pos
    {g : ℝ → ℝ} {q a : ℝ} (_hq : 0 < q) (ha : 0 < a)
    (hlim : Tendsto g atTop (𝓝 0)) : ∃ R, ∀ x ∈ Ioi R, a/2 ≤ a - q*g x := by
  have hsmall : ∀ᶠ x in atTop, |q * g x| < a / 2 := by
    have hqg : Tendsto (fun x => q * g x) atTop (𝓝 0) := by simpa using hlim.const_mul q
    rw [Metric.tendsto_atTop] at hqg
    simpa [Real.dist_eq] using hqg (a / 2) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  refine ⟨N, ?_⟩
  intro x hx
  linarith [abs_lt.mp (hN x hx.le)]

private lemma eventually_const_sub_le_neg_half_of_neg
    {g : ℝ → ℝ} {q a : ℝ} (_hq : 0 < q) (ha : a < 0)
    (hlim : Tendsto g atTop (𝓝 0)) : ∃ R, ∀ x ∈ Ioi R, a - q*g x ≤ -((-a)/2) := by
  have hsmall : ∀ᶠ x in atTop, |q * g x| < (-a) / 2 := by
    have hqg : Tendsto (fun x => q * g x) atTop (𝓝 0) := by simpa using hlim.const_mul q
    rw [Metric.tendsto_atTop] at hqg
    simpa [Real.dist_eq] using hqg ((-a) / 2) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  refine ⟨N, ?_⟩
  intro x hx
  linarith [abs_lt.mp (hN x hx.le)]

private lemma firstDeriv_on_Ioi_of_hull_eq
    {L : ℝ} (_hL : 0 < L) {f : RayleighKernel.Analysis.HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (hHull : f.positivityHullInterior = Ioi 0) :
    ∀ x ∈ Ioi 0, HasDerivAt f.continuousRep (deriv f.continuousRep x) x := by
  intro x hx
  have hxpos : 0 < x := hx
  have hpq : x / 2 < 2 * x := by linarith
  have hcompact : Icc (x / 2) (2 * x) ⊆ f.positivityHullInterior := by
    rw [hHull]; intro y hy; exact lt_of_lt_of_le (by linarith) hy.1
  have hxmid : x ∈ Ioo (x / 2) (2 * x) := by constructor <;> linarith
  have hraw := B.continuousRep_hasDerivAt hfmin (by linarith : 0 < x / 2) hpq hxmid
  have heq := hraw.deriv
  convert hraw using 1

private lemma secondDeriv_on_Ioi_of_hull_eq
    {L : ℝ} (hL : 0 < L) {f : RayleighKernel.Analysis.HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (hHull : f.positivityHullInterior = Ioi 0) :
    ∀ x ∈ Ioi 0, HasDerivAt (deriv f.continuousRep)
      (B.massMultiplier + B.momentMultiplier*x - f.rayleighQuotient*f.continuousRep x) x := by
  intro x hx
  have hxpos : 0 < x := hx
  have hpq : x / 2 < 2 * x := by linarith
  have hcompact : Icc (x / 2) (2 * x) ⊆ f.positivityHullInterior := by
    rw [hHull]; intro y hy; exact lt_of_lt_of_le (by linarith) hy.1
  have hxmid : x ∈ Ioo (x / 2) (2 * x) := by constructor <;> linarith
  have h := B.hasDerivAt_deriv_continuousRep_of_mem_positivityHullInterior hL hfmin hpq hcompact hxmid
  convert h using 1
  ring

theorem CorrectionBumps.positivityHullInterior_bddAbove_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : BddAbove f.positivityHullInterior := by
  by_contra hnot
  have hHull := positivityHullInterior_eq_Ioi_of_not_bddAbove hnot
  let g := f.continuousRep
  let g' := deriv f.continuousRep
  let g'' := deriv (deriv f.continuousRep)
  let q := f.rayleighQuotient
  let a := B.massMultiplier
  let b := B.momentMultiplier
  have hfirst := firstDeriv_on_Ioi_of_hull_eq hL hfmin B hHull
  have hsecond := secondDeriv_on_Ioi_of_hull_eq hL hfmin B hHull
  have hq : 0 < q := by
    dsimp [q]
    exact rayleighQuotient_pos_of_mass_eq_one hfmin.1.mass_eq
  have hlim : Tendsto g atTop (𝓝 0) := by
    dsimp [g]
    exact f.tendsto_continuousRep_atTop
  have hsecond' : ∀ x ∈ Ioi 0, HasDerivAt g' (g'' x) x := by
    intro x hx
    have hd := (hsecond x hx).deriv
    change HasDerivAt (deriv f.continuousRep) (deriv (deriv f.continuousRep) x) x
    rw [hd]
    exact hsecond x hx
  have hcurv : a = 0 ∧ b = 0 := by
    by_cases hb : b < 0
    · obtain ⟨R, hR⟩ := eventually_affine_sub_le_neg_one_of_neg_slope
        (g := g) (q := q) (a := a) (b := b) hq hb hlim
      exfalso
      apply not_secondDeriv_le_of_nonneg (g := g) (g' := g') (g'' := g'')
        (R := max R 0) (c := 1) (by norm_num)
      · intro x hx; exact hfirst x (lt_of_le_of_lt (le_max_right R 0) hx)
      · intro x hx; exact hsecond' x (lt_of_le_of_lt (le_max_right R 0) hx)
      · intro x hx
        have ht := hR x (lt_of_le_of_lt (le_max_left R 0) hx)
        have hd := (hsecond x (lt_of_le_of_lt (le_max_right R 0) hx)).deriv
        dsimp [g,g',g'',q,a] at *
        rw [hd]
        exact ht
      · exact hlim
    · by_cases hb' : 0 < b
      · obtain ⟨R, hR⟩ := eventually_one_le_affine_sub_of_pos_slope
          (g := g) (q := q) (a := a) (b := b) hq hb' hlim
        exfalso
        apply not_secondDeriv_ge_on_Ioi_of_tendsto_zero (g := g) (g' := g') (g'' := g'')
          (R := max R 0) (c := 1) (by norm_num)
        · intro x hx; exact hfirst x (lt_of_le_of_lt (le_max_right R 0) hx)
        · intro x hx; exact hsecond' x (lt_of_le_of_lt (le_max_right R 0) hx)
        · intro x hx
          have ht := hR x (lt_of_le_of_lt (le_max_left R 0) hx)
          have hd := (hsecond x (lt_of_le_of_lt (le_max_right R 0) hx)).deriv
          dsimp [g,g',g'',q,a] at *
          rw [hd]
          exact ht
        · exact hlim
      · have hb0 : b = 0 := le_antisymm (not_lt.mp hb') (not_lt.mp hb)
        have hb0' : B.momentMultiplier = 0 := by simpa [b] using hb0
        subst b
        by_cases ha : a < 0
        · obtain ⟨R, hR⟩ := eventually_const_sub_le_neg_half_of_neg
            (g := g) (q := q) (a := a) hq ha hlim
          exfalso
          apply not_secondDeriv_le_of_nonneg (g := g) (g' := g') (g'' := g'')
            (R := max R 0) (c := (-a)/2) (by linarith)
          · intro x hx; exact hfirst x (lt_of_le_of_lt (le_max_right R 0) hx)
          · intro x hx; exact hsecond' x (lt_of_le_of_lt (le_max_right R 0) hx)
          · intro x hx
            have ht := hR x (lt_of_le_of_lt (le_max_left R 0) hx)
            have hd := (hsecond x (lt_of_le_of_lt (le_max_right R 0) hx)).deriv
            dsimp [g,g',g'',q,a] at *
            rw [hb0'] at hd
            rw [hd]
            simpa using ht
          · exact hlim
        · by_cases ha' : 0 < a
          · obtain ⟨R, hR⟩ := eventually_half_le_const_sub_of_pos
              (g := g) (q := q) (a := a) hq ha' hlim
            exfalso
            apply not_secondDeriv_ge_on_Ioi_of_tendsto_zero (g := g) (g' := g') (g'' := g'')
              (R := max R 0) (c := a/2) (by linarith)
            · intro x hx; exact hfirst x (lt_of_le_of_lt (le_max_right R 0) hx)
            · intro x hx; exact hsecond' x (lt_of_le_of_lt (le_max_right R 0) hx)
            · intro x hx
              have ht := hR x (lt_of_le_of_lt (le_max_left R 0) hx)
              have hd := (hsecond x (lt_of_le_of_lt (le_max_right R 0) hx)).deriv
              dsimp [g,g',g'',q,a] at *
              rw [hb0'] at hd
              rw [hd]
              simpa using ht
            · exact hlim
          · exact ⟨le_antisymm (not_lt.mp ha') (not_lt.mp ha), hb0⟩
  rcases hcurv with ⟨ha0, hb0⟩
  have hzero : ∀ x ∈ Ioi 0, g x = 0 := by
    apply eq_zero_on_Ioi_of_secondDeriv_eq_neg_mul_of_nonneg_of_tendsto_zero hq
    · intro x hx; exact hfirst x hx
    · intro x hx
      simpa [g', g''] using hsecond x hx
    · intro x hx
      have hd := (hsecond x hx).deriv
      have ha0' : B.massMultiplier = 0 := by simpa [a] using ha0
      have hb0' : B.momentMultiplier = 0 := by simpa [b] using hb0
      rw [ha0', hb0'] at hd
      dsimp [g, q]
      rw [ha0', hb0']
      linarith [hd]
    · intro x hx
      exact hfmin.1.nonnegative x (by simpa [halfLine] using (le_of_lt hx))
    · exact hlim
  have hmass0 : f.mass = 0 := by
    rw [HalfLineH1.mass, RayleighKernel.mass]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    by_cases hx0 : x = 0
    · subst x; exact f.continuousRep_zero
    · exact hzero x (lt_of_le_of_ne hx (Ne.symm hx0))
  linarith [hfmin.1.mass_eq, hmass0]

def positivityHullEndpoint (f : HalfLineH1) : ℝ := sSup f.positivityHullInterior

theorem positivityHullEndpoint_pos_of_isAdmissible
    {L : ℝ} {f : HalfLineH1} (hf : f.IsAdmissible L)
    (hbounded : BddAbove f.positivityHullInterior) :
    0 < f.positivityHullEndpoint := by
  obtain ⟨x, hx⟩ := f.positivitySet_nonempty hf
  have hxin : x ∈ f.positivityHullInterior :=
    f.positivitySet_subset_positivityHullInterior hx
  have hxK : x ≤ f.positivityHullEndpoint := by
    exact le_csSup hbounded hxin
  exact lt_of_lt_of_le hxin.1 hxK

theorem positivityHullInterior_eq_Ioo_positivityHullEndpoint
    {L : ℝ} {f : HalfLineH1} (hf : f.IsAdmissible L)
    (hbounded : BddAbove f.positivityHullInterior) :
    f.positivityHullInterior = Ioo 0 f.positivityHullEndpoint := by
  let K := f.positivityHullEndpoint
  have hKpos : 0 < K := positivityHullEndpoint_pos_of_isAdmissible hf hbounded
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (f.isOpen_positivityHullInterior) x hx
    have hz := hball (show dist (x + ε / 2) x < ε by
      rw [Real.dist_eq, abs_of_nonneg (by linarith)]
      linarith)
    exact lt_of_lt_of_le (by linarith) (le_csSup hbounded hz)
  · intro x hx
    obtain ⟨p, hp⟩ := f.positivitySet_nonempty hf
    obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup
      ⟨_, f.positivitySet_subset_positivityHullInterior hp⟩ hx.2
    obtain ⟨z, hz, hyz⟩ := hy.2
    exact ⟨hx.1, z, hz, hxy.trans hyz⟩

theorem positivityHullEndpoint_pos_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : 0 < f.positivityHullEndpoint := by
  apply positivityHullEndpoint_pos_of_isAdmissible hfmin.1
  exact B.positivityHullInterior_bddAbove_of_isMinimizer hL hfmin

theorem continuousRep_eq_zero_of_positivityHullEndpoint_le
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {x : ℝ}
    (hx : f.positivityHullEndpoint ≤ x) : f.continuousRep x = 0 := by
  by_cases hx0 : x ≤ 0
  · exact f.continuousRep_eq_zero_of_nonpositive hx0
  · have hxnot : x ∉ f.positivityHullInterior := by
      rw [positivityHullInterior_eq_Ioo_positivityHullEndpoint hfmin.1
        (B.positivityHullInterior_bddAbove_of_isMinimizer hL hfmin)]
      intro hmem
      exact (not_lt_of_ge hx) hmem.2
    by_contra hne
    have hnonneg := hfmin.1.nonnegative x (by
      simpa [halfLine] using (le_of_lt (lt_of_not_ge hx0)))
    have hpos : x ∈ f.positivitySet := lt_of_le_of_ne hnonneg (Ne.symm hne)
    exact hxnot (f.positivitySet_subset_positivityHullInterior hpos)

theorem support_continuousRep_subset_Icc_positivityHullEndpoint
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    Function.support f.continuousRep ⊆ Icc 0 f.positivityHullEndpoint := by
  intro x hx
  refine ⟨?_, ?_⟩
  · by_contra hx0
    have hxneg : x ≤ 0 := le_of_not_gt (by linarith)
    exact hx (f.continuousRep_eq_zero_of_nonpositive hxneg)
  · exact le_of_not_gt fun hxK =>
      hx (continuousRep_eq_zero_of_positivityHullEndpoint_le hL hfmin B hxK.le)

theorem continuousRep_hasCompactSupport_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : HasCompactSupport f.continuousRep := by
  refine HasCompactSupport.intro (K := Icc 0 f.positivityHullEndpoint) isCompact_Icc ?_
  intro x hx
  by_contra hne
  exact hx (support_continuousRep_subset_Icc_positivityHullEndpoint hL hfmin B hne)

theorem continuousRep_positivityHullEndpoint_eq_zero
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    f.continuousRep f.positivityHullEndpoint = 0 :=
  continuousRep_eq_zero_of_positivityHullEndpoint_le hL hfmin B le_rfl

theorem hasDerivAt_continuousRep_positivityHullEndpoint_zero
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    HasDerivAt f.continuousRep 0 f.positivityHullEndpoint := by
  let K := f.positivityHullEndpoint
  have hK : 0 < K := positivityHullEndpoint_pos_of_isMinimizer hL hfmin B
  have hcontact := continuousRep_positivityHullEndpoint_eq_zero hL hfmin B
  apply B.continuousRep_hasDerivAt_zero_of_contact hfmin
    (a := K / 2) (b := 2 * K) (x := K)
  · linarith
  · linarith
  · constructor <;> linarith
  · exact hcontact

theorem deriv_continuousRep_positivityHullEndpoint_eq_zero
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    deriv f.continuousRep f.positivityHullEndpoint = 0 :=
  (hasDerivAt_continuousRep_positivityHullEndpoint_zero hL hfmin B).deriv

theorem CorrectionBumps.massMultiplier_add_momentMultiplier_mul_eq_zero
    {L : ℝ} (_hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    B.massMultiplier + B.momentMultiplier * L = 0 := by
  obtain ⟨B₁⟩ := exists_centeredCorrectionBump hfmin.1
  exact HalfLineH1.balance_from_centered_bridge hfmin B₁ B

private lemma hasDerivAt_continuousRep_zero_of_endpoint_lt
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {x : ℝ}
    (hx : f.positivityHullEndpoint < x) : HasDerivAt f.continuousRep 0 x := by
  have hev : ∀ᶠ y in 𝓝 x, f.continuousRep y = 0 := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact continuousRep_eq_zero_of_positivityHullEndpoint_le hL hfmin B hy.le
  have hc : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x := hasDerivAt_const x 0
  apply hc.congr_of_eventuallyEq
  filter_upwards [hev] with y hy
  exact hy

theorem CorrectionBumps.momentMultiplier_nonneg_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : 0 ≤ B.momentMultiplier := by
  have hK : 0 < f.positivityHullEndpoint :=
    positivityHullEndpoint_pos_of_isMinimizer hL hfmin B
  have hbal := B.massMultiplier_add_momentMultiplier_mul_eq_zero hL hfmin
  by_contra hb
  have hb' : B.momentMultiplier < 0 := lt_of_not_ge hb
  let A : ℝ := max f.positivityHullEndpoint L + 1
  let C : ℝ := A + 1
  have hAC : A < C := by dsimp [C]; linarith
  obtain ⟨η, hηcompact, hηsupport, hηnonneg, hηint⟩ :=
    exists_normalized_schwartz_bump_Ioo (a := A) (b := C) hAC
  have hApos : 0 < A := by
    dsimp [A]
    have hm : 0 < max f.positivityHullEndpoint L :=
      lt_of_lt_of_le hK (le_max_left _ _)
    linarith
  have hKA : f.positivityHullEndpoint ≤ A := by
    dsimp [A]
    linarith [le_max_left f.positivityHullEndpoint L]
  have hLA : L < A := by
    dsimp [A]
    linarith [le_max_right f.positivityHullEndpoint L]
  have hsupport_pos : tsupport η ⊆ Ioi (0 : ℝ) :=
    hηsupport.trans (fun x hx => lt_trans hApos hx.1)
  have hηzero : ∀ x, η x ≠ 0 → f.positivityHullEndpoint ≤ x := by
    intro x hx
    exact hKA.trans (hηsupport (subset_closure hx)).1.le
  have hvalue : ∫ x : ℝ, f.continuousRep x * η x = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    by_cases hx : η x = 0
    · simp [hx]
    · rw [continuousRep_eq_zero_of_positivityHullEndpoint_le hL hfmin B (hηzero x hx)]
      simp
  have hderiv : ∫ x : ℝ, (f.weakDeriv : ℝ → ℝ) x * deriv η x = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [f.deriv_continuousRep_ae] with x hx
    by_cases hdx : deriv η x = 0
    · simp [hdx]
    · have hxt : x ∈ tsupport (deriv η) := subset_closure hdx
      have hxt' : x ∈ tsupport η := tsupport_deriv_subset hxt
      have hxA : A < x := (hηsupport hxt').1
      have hxK : f.positivityHullEndpoint < x := lt_of_le_of_lt hKA hxA
      rw [← hx]
      rw [(hasDerivAt_continuousRep_zero_of_endpoint_lt hL hfmin B hxK).deriv]
      simp
  have hmoment : L < ∫ x : ℝ, x * η x := by
    have hpoint : ∀ x, A * η x ≤ x * η x := by
      intro x
      by_cases hx : η x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_right
          (le_of_lt (hηsupport (subset_closure hx)).1) (hηnonneg x)
    have hmono : ∫ x : ℝ, A * η x ≤ ∫ x : ℝ, x * η x := by
      apply integral_mono
      · exact (η.continuous.integrable_of_hasCompactSupport hηcompact).const_mul A
      · exact (continuous_id.mul η.continuous).integrable_of_hasCompactSupport
          (hηcompact.mul_left)
      · exact fun x => hpoint x
    have hAint : ∫ x : ℝ, A * η x = A := by
      rw [integral_const_mul, hηint]
      ring
    rw [hAint] at hmono
    exact hLA.trans_le hmono
  have hk := B.weak_KKT_equation_schwartz hfmin η hηcompact hsupport_pos
  rw [hderiv, hvalue, hηint] at hk
  have hr : 0 ≤ ∫ x : Ioi (0 : ℝ), η x ∂B.reactionMeasure hfmin :=
    MeasureTheory.integral_nonneg (fun x => hηnonneg (x : ℝ))
  have hmass : B.massMultiplier = -B.momentMultiplier * L := by
    linarith [hbal]
  rw [hmass] at hk
  nlinarith

private lemma g18_firstDeriv_on_hull
    {L : ℝ} (_hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (hHull : f.positivityHullInterior = Ioo 0 f.positivityHullEndpoint)
    {x : ℝ} (hx : x ∈ f.positivityHullInterior) :
    HasDerivAt f.continuousRep (deriv f.continuousRep x) x := by
  have hx0 : 0 < x := (hHull ▸ hx).1
  let u : ℝ := (x + f.positivityHullEndpoint) / 2
  have hxK : x < f.positivityHullEndpoint := (hHull ▸ hx).2
  have hxu : x < u := by dsimp [u]; linarith
  have huK : u < f.positivityHullEndpoint := by dsimp [u]; linarith
  have hpq : x / 2 < u := by dsimp [u]; linarith
  have hcompact : Icc (x / 2) u ⊆ f.positivityHullInterior := by
    rw [hHull]
    intro y hy
    exact ⟨lt_of_lt_of_le (by linarith) hy.1, lt_of_le_of_lt hy.2 huK⟩
  have hxmid : x ∈ Ioo (x / 2) u := by constructor <;> linarith
  have hraw := B.continuousRep_hasDerivAt hfmin (by linarith : 0 < x / 2) hpq hxmid
  have heq := hraw.deriv
  have hfull : HasDerivAt f.continuousRep (deriv f.continuousRep x) x := by
    convert hraw using 1
  exact hfull

private lemma g18_secondDeriv_on_hull
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) (hHull : f.positivityHullInterior = Ioo 0 f.positivityHullEndpoint)
    {x : ℝ} (hx : x ∈ f.positivityHullInterior) :
    HasDerivAt (deriv f.continuousRep)
      (B.massMultiplier + B.momentMultiplier*x - f.rayleighQuotient*f.continuousRep x) x := by
  have hx0 : 0 < x := (hHull ▸ hx).1
  let u : ℝ := (x + f.positivityHullEndpoint) / 2
  have hxK : x < f.positivityHullEndpoint := (hHull ▸ hx).2
  have hxu : x < u := by dsimp [u]; linarith
  have huK : u < f.positivityHullEndpoint := by dsimp [u]; linarith
  have hpq : x / 2 < u := by dsimp [u]; linarith
  have hcompact : Icc (x / 2) u ⊆ f.positivityHullInterior := by
    rw [hHull]
    intro y hy
    exact ⟨lt_of_lt_of_le (by linarith) hy.1, lt_of_le_of_lt hy.2 huK⟩
  have hxmid : x ∈ Ioo (x / 2) u := by constructor <;> linarith
  have h := B.hasDerivAt_deriv_continuousRep_of_mem_positivityHullInterior
    hL hfmin hpq hcompact hxmid
  convert h using 1
  ring

theorem continuousRep_hasDerivAt_on_Ioo_positivityHullEndpoint
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {x : ℝ}
    (hx : x ∈ Ioo 0 f.positivityHullEndpoint) :
    HasDerivAt f.continuousRep (deriv f.continuousRep x) x := by
  have hbounded := B.positivityHullInterior_bddAbove_of_isMinimizer hL hfmin
  have hHull := positivityHullInterior_eq_Ioo_positivityHullEndpoint hfmin.1 hbounded
  exact g18_firstDeriv_on_hull hL hfmin B hHull (hHull.symm ▸ hx)

theorem deriv_continuousRep_hasDerivAt_on_Ioo_positivityHullEndpoint
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {x : ℝ}
    (hx : x ∈ Ioo 0 f.positivityHullEndpoint) :
    HasDerivAt (deriv f.continuousRep)
      (deriv (deriv f.continuousRep) x) x := by
  have hbounded := B.positivityHullInterior_bddAbove_of_isMinimizer hL hfmin
  have hHull := positivityHullInterior_eq_Ioo_positivityHullEndpoint hfmin.1 hbounded
  have h := g18_secondDeriv_on_hull hL hfmin B hHull (hHull.symm ▸ hx)
  convert h using 1
  exact h.deriv

theorem hasDerivAt_deriv_continuousRep_on_Ioo_positivityHullEndpoint
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) {x : ℝ}
    (hx : x ∈ Ioo 0 f.positivityHullEndpoint) :
    HasDerivAt (deriv f.continuousRep)
      (B.massMultiplier + B.momentMultiplier * x -
        f.rayleighQuotient * f.continuousRep x) x := by
  have hbounded := B.positivityHullInterior_bddAbove_of_isMinimizer hL hfmin
  have hHull := positivityHullInterior_eq_Ioo_positivityHullEndpoint hfmin.1 hbounded
  exact g18_secondDeriv_on_hull hL hfmin B hHull (hHull.symm ▸ hx)

theorem CorrectionBumps.momentMultiplier_ne_zero_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : B.momentMultiplier ≠ 0 := by
  intro hb
  have hbounded := B.positivityHullInterior_bddAbove_of_isMinimizer hL hfmin
  let K := f.positivityHullEndpoint
  have hHull : f.positivityHullInterior = Ioo 0 K := by
    dsimp [K]
    exact positivityHullInterior_eq_Ioo_positivityHullEndpoint hfmin.1 hbounded
  have hK : 0 < K := by
    dsimp [K]
    exact positivityHullEndpoint_pos_of_isMinimizer hL hfmin B
  have ha : B.massMultiplier = 0 := by
    have hbal := B.massMultiplier_add_momentMultiplier_mul_eq_zero hL hfmin
    simpa [hb] using hbal
  have hq : 0 < f.rayleighQuotient := rayleighQuotient_pos_of_mass_eq_one hfmin.1.mass_eq
  let D : Set ℝ := Icc (K / 2) K
  have hconc : ConcaveOn ℝ D f.continuousRep := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (f := f.continuousRep)
      (f' := deriv f.continuousRep) (f'' := fun x => -f.rayleighQuotient * f.continuousRep x)
      (show Convex ℝ D by change Convex ℝ (Icc (K / 2) K); exact convex_Icc _ _) ?_ ?_ ?_ ?_
    · intro x hx; exact f.continuous_continuousRep.continuousAt.continuousWithinAt
    · intro x hx
      have hxI : x ∈ Ioo (K / 2) K := by
        change x ∈ interior D at hx
        rw [show D = Icc (K / 2) K by rfl] at hx
        simpa only [interior_Icc] using hx
      have hx' : x ∈ f.positivityHullInterior := by
        rw [hHull]
        exact ⟨by linarith [hK, hxI.1], hxI.2⟩
      exact (g18_firstDeriv_on_hull hL hfmin B (by simpa [K] using hHull) hx').hasDerivWithinAt
    · intro x hx
      have hxI : x ∈ Ioo (K / 2) K := by
        change x ∈ interior D at hx
        rw [show D = Icc (K / 2) K by rfl] at hx
        simpa only [interior_Icc] using hx
      have hx' : x ∈ f.positivityHullInterior := by
        rw [hHull]
        exact ⟨by linarith [hK, hxI.1], hxI.2⟩
      have hd := g18_secondDeriv_on_hull hL hfmin B (by simpa [K] using hHull) hx'
      rw [ha, hb] at hd
      have hd' : HasDerivWithinAt (deriv f.continuousRep)
          (-f.rayleighQuotient * f.continuousRep x) (interior D) x := by
        convert hd.hasDerivWithinAt using 1
        ring
      exact hd'
    · intro x hx
      have hxI : x ∈ Ioo (K / 2) K := by
        change x ∈ interior (Icc (K / 2) K) at hx
        simpa only [interior_Icc] using hx
      have hx' : x ∈ f.positivityHullInterior := by
        rw [hHull]
        exact ⟨by linarith [hK, hxI.1], hxI.2⟩
      have hnon : 0 ≤ f.continuousRep x := hfmin.1.nonnegative x (by
        simpa [halfLine] using (le_of_lt (lt_trans (by linarith [hK]) hxI.1)))
      convert neg_nonpos.mpr (mul_nonneg hq.le hnon) using 1
      ring
  have hhalf : K / 2 < K := by linarith
  have hpHull : K / 2 ∈ f.positivityHullInterior := by
    rw [hHull]
    exact ⟨by linarith, hhalf⟩
  rcases hpHull with ⟨_, w, hwPos, hpw⟩
  change 0 < f.continuousRep w at hwPos
  have hwHull := f.positivitySet_subset_positivityHullInterior hwPos
  rw [hHull] at hwHull
  have hwD : w ∈ D := ⟨hpw.le, hwHull.2.le⟩
  have hKD : K ∈ D := ⟨hhalf.le, le_rfl⟩
  have hslope := hconc.le_slope_of_hasDerivAt hwD hKD hwHull.2
    (by simpa [K] using hasDerivAt_continuousRep_positivityHullEndpoint_zero hL hfmin B)
  have hKzero : f.continuousRep K = 0 := by
    simpa [K] using continuousRep_positivityHullEndpoint_eq_zero hL hfmin B
  have hneg : slope f.continuousRep w K < 0 := by
    rw [slope_def_field]
    have hnum : f.continuousRep K - f.continuousRep w < 0 := by rw [hKzero]; linarith [hwPos]
    exact div_neg_of_neg_of_pos hnum (sub_pos.mpr hwHull.2)
  exact (not_lt_of_ge hslope) hneg

theorem CorrectionBumps.momentMultiplier_pos_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : 0 < B.momentMultiplier :=
  lt_of_le_of_ne (B.momentMultiplier_nonneg_of_isMinimizer hL hfmin)
    (Ne.symm (B.momentMultiplier_ne_zero_of_isMinimizer hL hfmin))

theorem CorrectionBumps.momentMultiplier_div_rayleighQuotient_pos_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) : 0 < B.momentMultiplier / f.rayleighQuotient :=
  div_pos (B.momentMultiplier_pos_of_isMinimizer hL hfmin)
    (rayleighQuotient_pos_of_mass_eq_one hfmin.1.mass_eq)

end RayleighKernel.Analysis.HalfLineH1
