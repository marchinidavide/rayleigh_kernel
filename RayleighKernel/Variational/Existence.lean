import RayleighKernel.Variational.Scaling
import RayleighKernel.Variational.Triangular

noncomputable section

namespace RayleighKernel.Analysis

open Filter MeasureTheory Set
open scoped Topology

theorem HalfLineH1.rayleighQuotient_pos_of_mass_eq_one {u : HalfLineH1}
    (hmass : u.mass = 1) : 0 < u.rayleighQuotient := by
  have hden : 0 < u.squareEnergy := u.squareEnergy_pos_of_mass_eq_one hmass
  have hnum : 0 < u.dirichletEnergy := by
    rw [HalfLineH1.dirichletEnergy]
    rcases eq_or_lt_of_le (norm_nonneg u.weakDeriv) with hz | hz
    · have hzero : ∀ x : ℝ, u.continuousRep x = 0 := by
        intro x
        have h := u.abs_continuousRep_sub_le 0 x
        rw [u.continuousRep_zero, sub_zero] at h
        rw [← hz] at h
        simpa using (abs_eq_zero.mp (le_antisymm (by simpa using h) (abs_nonneg _)))
      have hmzero : u.mass = 0 := by
        rw [HalfLineH1.mass, RayleighKernel.mass]
        apply integral_eq_zero_of_ae
        filter_upwards with x
        rw [hzero x]
        simp
      linarith
    · exact sq_pos_of_pos hz
  rw [HalfLineH1.rayleighQuotient]
  exact div_pos hnum hden

theorem DirectMethodLimitData.limit_rayleighQuotient_le_of_tendsto
    {L Q : ℝ} {u : ℕ → HalfLineH1} (d : DirectMethodLimitData L Q u)
    {ell : ℝ} (hq : Tendsto (fun n ↦ (u n).rayleighQuotient) atTop (𝓝 ell)) :
    d.limit.rayleighQuotient ≤ ell := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hq ε hε
  let w : ℕ → HalfLineH1 := fun n ↦ u (d.ns (n + N))
  have hshift : Tendsto (fun n : ℕ ↦ n + N) atTop atTop := tendsto_add_atTop_nat N
  have hns : Tendsto d.ns atTop atTop := d.strictMono_ns.tendsto_atTop
  have hweak : ∀ z : HalfLineH1,
      Tendsto (fun n ↦ inner ℝ (w n) z) atTop (𝓝 (inner ℝ d.limit z)) := by
    intro z
    exact (d.weak_tendsto z).comp hshift
  have hsquare : Tendsto (fun n ↦ (w n).squareEnergy) atTop
      (𝓝 d.limit.squareEnergy) := d.squareEnergy_tendsto.comp hshift
  have hbound : ∀ n, (w n).rayleighQuotient ≤ ell + ε := by
    intro n
    have hh := hN (d.ns (n + N)) (by
      exact (d.strictMono_ns.id_le N).trans
        (d.strictMono_ns.monotone (by omega)))
    rw [Real.dist_eq, abs_lt] at hh
    linarith
  exact HalfLineH1.rayleighQuotient_le_of_tendsto_squareEnergy_of_le hweak hsquare
    (fun n ↦ HalfLineH1.squareEnergy_pos_of_mass_eq_one
      (d.admissible_subseq (n + N)).mass_eq)
    (HalfLineH1.squareEnergy_pos_of_mass_eq_one d.mass_eq) hbound

theorem DirectMethodLimitData.limit_isAdmissible_firstMoment
    {L Q : ℝ} {u : ℕ → HalfLineH1} (d : DirectMethodLimitData L Q u) :
    d.limit.IsAdmissible d.limit.firstMoment := by
  have hIcc : IntegrableOn d.limit.continuousRep (Icc 0 1) :=
    d.limit.continuous_continuousRep.continuousOn.integrableOn_compact isCompact_Icc
  have htail : IntegrableOn d.limit.continuousRep (Ici 1) := by
    have hi : IntegrableOn (fun x ↦ x * d.limit.continuousRep x) (Ici 1) :=
      d.firstMoment_integrable.mono_set (by intro x hx; exact le_trans (show (0 : ℝ) ≤ 1 by norm_num) hx)
    have hi' : Integrable (fun x ↦ x * d.limit.continuousRep x)
        (volume.restrict (Ici 1)) := hi
    refine hi'.mono d.limit.continuous_continuousRep.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (d.nonnegative x (le_trans (show (0 : ℝ) ≤ 1 by norm_num) hx)),
      Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_trans (show (0 : ℝ) ≤ 1 by norm_num) hx)]
    have hn := d.nonnegative x (le_trans (show (0 : ℝ) ≤ 1 by norm_num) hx)
    rw [abs_of_nonneg hn]
    nlinarith [mul_nonneg (sub_nonneg.mpr (show (1 : ℝ) ≤ x by exact hx)) hn]
  have hint : IntegrableOn d.limit.continuousRep halfLine := by
    rw [show halfLine = Icc 0 1 ∪ Ici 1 by
      rw [Icc_union_Ici_eq_Ici (by norm_num), halfLine]]
    exact hIcc.union htail
  exact ⟨d.nonnegative, hint, d.firstMoment_integrable, d.mass_eq, rfl⟩

theorem exists_isAdmissible_rayleighQuotient_eq_Lambda {L : ℝ} (hL : 0 < L) :
    ∃ u : HalfLineH1, u.IsAdmissible L ∧ u.rayleighQuotient = Lambda L := by
  obtain ⟨u, hu, hq⟩ := exists_minimizing_sequence
    (hL := admissibleQuotients_nonempty_of_pos hL)
  obtain ⟨Q, hev⟩ := eventually_rayleighQuotient_le_of_tendsto_minimizing hq
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  let v : ℕ → HalfLineH1 := fun n ↦ u (n + N)
  have hv : ∀ n, (v n).IsAdmissible L := fun n ↦ hu (n + N)
  have hvQ : ∀ n, (v n).rayleighQuotient ≤ Q := by
    intro n
    exact hN (n + N) (Nat.le_add_left N n)
  have hvq : Tendsto (fun n ↦ (v n).rayleighQuotient) atTop (𝓝 (Lambda L)) :=
    hq.comp (tendsto_add_atTop_nat N)
  obtain ⟨d⟩ := exists_directMethodLimitData hv hvQ
  have hupper : d.limit.rayleighQuotient ≤ Lambda L :=
    d.limit_rayleighQuotient_le_of_tendsto hvq
  have hmpos := d.firstMoment_pos
  have hmle := d.firstMoment_le
  have hm_eq : d.limit.firstMoment = L := by
    by_contra hne
    have hmlt : d.limit.firstMoment < L := lt_of_le_of_ne hmle hne
    let a : ℝ := d.limit.firstMoment / L
    have ha : 0 < a := div_pos hmpos hL
    have ha1 : a < 1 := (div_lt_one hL).2 hmlt
    have hscaled : (d.limit.rescale a ha).IsAdmissible L := by
      have h := d.limit.rescale_isAdmissible ha d.limit_isAdmissible_firstMoment
      convert h using 1
      dsimp [a]
      field_simp [ne_of_gt hL]
    have hlower := Lambda_le_of_isAdmissible hscaled
    have hqscale := d.limit.rayleighQuotient_rescale ha
    have hpos := HalfLineH1.rayleighQuotient_pos_of_mass_eq_one d.mass_eq
    have hstrict : a ^ 2 * d.limit.rayleighQuotient < d.limit.rayleighQuotient := by
      have ha0 : 0 ≤ a := ha.le
      have hs : a ^ 2 < 1 := by nlinarith
      nlinarith
    rw [hqscale] at hlower
    linarith
  have hdadm := d.limit_isAdmissible_firstMoment
  have hfinal : d.limit.IsAdmissible L := by
    exact { hdadm with firstMoment_eq := hm_eq }
  refine ⟨d.limit, hfinal, le_antisymm hupper (Lambda_le_of_isAdmissible hfinal)⟩

theorem exists_isMinimizer {L : ℝ} (hL : 0 < L) :
    ∃ u : HalfLineH1, u.IsMinimizer L := by
  obtain ⟨u, hu, hq⟩ := exists_isAdmissible_rayleighQuotient_eq_Lambda hL
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact hq ▸ Lambda_le_of_isAdmissible hv

end RayleighKernel.Analysis
