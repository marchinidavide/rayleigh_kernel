import RayleighKernel.Discrete.MomentPassage

noncomputable section
namespace RayleighKernel.Discrete

open Set Filter Topology MeasureTheory
open RayleighKernel.Analysis
open RayleighKernel.Analysis.HalfLineH1

abbrev scaledAdmissibleValues (h L : ℝ) : Set ℝ :=
  {q : ℝ | ∃ w : Kernel, IsAdmissible h L w ∧
    q = (h⁻¹)^2 * rayleighQuotient w}

theorem eventually_scaledAdmissibleValues_nonempty (L : ℝ) (hL : 0 < L) :
    ∀ᶠ h in 𝓝[>] 0, (scaledAdmissibleValues h L).Nonempty := by
  obtain ⟨w, hw, hq⟩ := exists_discreteRecovery L hL
  filter_upwards [hw] with h hh
  exact ⟨(h⁻¹)^2 * rayleighQuotient (w h), w h, hh, rfl⟩

theorem exists_scaledAdmissibleValue_lt_sInf_add (L : ℝ) (_hL : 0 < L)
    {h ε : ℝ} (_hh : 0 < h) (hε : 0 < ε)
    (hnonempty : (scaledAdmissibleValues h L).Nonempty) :
    ∃ w : Kernel, IsAdmissible h L w ∧
      (h⁻¹)^2 * rayleighQuotient w < scaledDiscreteMinimum h L + ε := by
  have hlt := Real.lt_sInf_add_pos
    (s := scaledAdmissibleValues h L) hnonempty hε
  rcases hlt with ⟨q, hq, hqinf⟩
  rcases hq with ⟨w, hw, rfl⟩
  exact ⟨w, hw, hqinf⟩

private structure NearMinimizerData (L : ℝ) where
  mesh : ℕ → ℝ
  eps : ℕ → ℝ
  w : ℕ → Kernel
  hmesh : Tendsto mesh atTop (𝓝[>] 0)
  heps : ∀ n, 0 < eps n
  heps_le : ∀ n, eps n ≤ 1
  heps_lim : Tendsto eps atTop (𝓝 0)
  hw : ∀ n, IsAdmissible (mesh n) L (w n)
  hnear : ∀ n, (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) ≤
    scaledDiscreteMinimum (mesh n) L + eps n

private theorem select_bad_nearMinimizers
    (L : ℝ) (hL : 0 < L) {δ : ℝ} (_hδ : 0 < δ)
    {mesh : ℕ → ℝ} (hmesh : Tendsto mesh atTop (𝓝[>] 0))
    (hbad : ∀ n, scaledDiscreteMinimum (mesh n) L <
      Analysis.Lambda L - δ) :
    ∃ d : NearMinimizerData L, ∀ n,
      scaledDiscreteMinimum (d.mesh n) L < Analysis.Lambda L - δ := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 <|
    ((tendsto_nhdsWithin_iff.mp hmesh).2).and
      (hmesh (eventually_scaledAdmissibleValues_nonempty L hL))
  let eps : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  let w : ℕ → Kernel := fun n => Classical.choose
    (exists_scaledAdmissibleValue_lt_sInf_add L hL
      (h := mesh (N + n)) (ε := eps n)
      (hN (N + n) (Nat.le_add_right N n)).1 (by positivity)
      (hN (N + n) (Nat.le_add_right N n)).2)
  let mesh' : ℕ → ℝ := fun n => mesh (N + n)
  have hw : ∀ n, IsAdmissible (mesh' n) L (w n) := by
    intro n
    exact (Classical.choose_spec
      (exists_scaledAdmissibleValue_lt_sInf_add L hL
        (h := mesh (N + n)) (ε := eps n)
        (hN (N + n) (Nat.le_add_right N n)).1 (by positivity)
        (hN (N + n) (Nat.le_add_right N n)).2)).1
  have heps : ∀ n, 0 < eps n := by
    intro n
    dsimp [eps]
    positivity
  have heps_lim : Tendsto eps atTop (𝓝 0) := by
    convert (tendsto_inv_atTop_zero.comp
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add_atTop
        tendsto_natCast_atTop_atTop)) using 1
    · funext n
      simp [eps, add_comm]
  have hmesh' : Tendsto mesh' atTop (𝓝[>] 0) := by
    convert hmesh.comp (tendsto_add_atTop_nat N) using 1
    funext n
    simp [mesh', add_comm]
  have hnear : ∀ n, (mesh' n)⁻¹ ^ 2 * rayleighQuotient (w n) ≤
      scaledDiscreteMinimum (mesh' n) L + eps n := by
    intro n
    exact le_of_lt (Classical.choose_spec
      (exists_scaledAdmissibleValue_lt_sInf_add L hL
        (h := mesh (N + n)) (ε := eps n)
        (hN (N + n) (Nat.le_add_right N n)).1 (by positivity)
        (hN (N + n) (Nat.le_add_right N n)).2)).2
  have heps_le : ∀ n, eps n ≤ 1 := by
    intro n
    have hp : (0 : ℝ) < n + 1 := by positivity
    apply (div_le_iff₀ hp).2
    linarith
  refine ⟨⟨mesh', eps, w, hmesh', heps, heps_le, heps_lim, hw, hnear⟩, ?_⟩
  intro n
  exact hbad (N + n)

private structure CompactLimitData (L : ℝ) (mesh : ℕ → ℝ) (w : ℕ → Kernel)
    (hw : ∀ n, IsAdmissible (mesh n) L (w n)) where
  ns : ℕ → ℕ
  ell : ℝ
  C : ℝ
  v : HalfLineH1
  hns : StrictMono ns
  hell : ell < Analysis.Lambda L
  hC : 0 ≤ C
  hv : ‖v‖ ≤ C + 1
  hscaled : Tendsto (fun n => (mesh (ns n))⁻¹ ^ 2 *
      rayleighQuotient (w (ns n))) atTop (𝓝 ell)
  hweak : ∀ z : HalfLineH1, Tendsto (fun n => inner ℝ
      (shiftedInterpolantH1 (w (ns n)) (hw (ns n))) z) atTop
        (𝓝 (inner ℝ v z))
  hunif : ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun n ↦ shiftedInterpolant (mesh (ns n)) (w (ns n)))
      v.continuousRep atTop K
  hsq : ∀ K : Set ℝ, IsCompact K → Tendsto
      (fun n ↦ ∫ x in K, (shiftedInterpolant (mesh (ns n)) (w (ns n)) x -
        v.continuousRep x) ^ 2) atTop (𝓝 0)
  hmesh : Tendsto (fun n ↦ mesh (ns n)) atTop (𝓝[>] 0)
  hq_le : ∀ n, (mesh (ns n))⁻¹ ^ 2 * rayleighQuotient (w (ns n)) ≤
    Analysis.Lambda L + 1

private theorem bad_quotient_compact_subsequence
    (L : ℝ) (hL : 0 < L) {δ : ℝ} (hδ : 0 < δ)
    (d : NearMinimizerData L) (hbad : ∀ n, scaledDiscreteMinimum (d.mesh n) L <
      Analysis.Lambda L - δ) : ∃ cd : CompactLimitData L d.mesh d.w d.hw, ∀ n,
      scaledDiscreteMinimum (d.mesh (cd.ns n)) L < Analysis.Lambda L - δ := by
  let q : ℕ → ℝ := fun n => (d.mesh n)⁻¹ ^ 2 * rayleighQuotient (d.w n)
  have hq_nonneg : ∀ n, 0 ≤ q n := fun n =>
    mul_nonneg (sq_nonneg _) (d.hw n).rayleighQuotient_nonneg
  have hq_upper : ∀ n, q n ≤ Analysis.Lambda L + 1 := by
    intro n
    have he := d.heps_le n
    have hn := d.hnear n
    have hb := hbad n
    change q n ≤ _
    dsimp [q]
    linarith
  obtain ⟨ell, hell, ns, hns, hqns⟩ :=
    isCompact_Icc.isSeqCompact (fun n => ⟨hq_nonneg n, hq_upper n⟩)
  have hell_le : ell ≤ Analysis.Lambda L - δ := by
    have hh := le_of_tendsto_of_tendsto' hqns
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => Analysis.Lambda L - δ)
        atTop (𝓝 (Analysis.Lambda L - δ))).add (d.heps_lim.comp hns.tendsto_atTop))
    simpa [q] using hh (fun n => by
      have hn := d.hnear (ns n)
      have hb := hbad (ns n)
      change q (ns n) ≤ _
      dsimp [q]
      linarith)
  have hell_lt : ell < Analysis.Lambda L := by linarith
  let mesh' : ℕ → ℝ := fun n => d.mesh (ns n)
  let eps' : ℕ → ℝ := fun n => d.eps (ns n)
  let w' : ℕ → Kernel := fun n => d.w (ns n)
  have hmesh' : Tendsto mesh' atTop (𝓝[>] 0) := d.hmesh.comp hns.tendsto_atTop
  have heps' : Tendsto eps' atTop (𝓝 0) := d.heps_lim.comp hns.tendsto_atTop
  have hw' : ∀ n, IsAdmissible (mesh' n) L (w' n) := fun n => d.hw (ns n)
  have hnear' : ∀ n, (mesh' n)⁻¹ ^ 2 * rayleighQuotient (w' n) ≤
      scaledDiscreteMinimum (mesh' n) L + eps' n := fun n => d.hnear (ns n)
  obtain ⟨ks, v, C, hks, hC, hv, hweak, hlocal⟩ :=
    exists_shiftedInterpolant_compact_subsequence_of_nearMinimizer L hL
      hmesh' heps' hw' hnear'
  let ns' : ℕ → ℕ := fun n => ns (ks n)
  have hmesh0 : Tendsto (fun n => mesh' (ks n)) atTop (𝓝[>] 0) :=
    hmesh'.comp hks.tendsto_atTop
  have hw0 : ∀ n, IsAdmissible (mesh' (ks n)) L (w' (ks n)) := fun n => hw' (ks n)
  have hq_le0 : ∀ n, (mesh' (ks n))⁻¹ ^ 2 * rayleighQuotient (w' (ks n)) ≤
      Analysis.Lambda L + 1 := fun n => hq_upper (ns (ks n))
  refine ⟨⟨ns', ell, C, v, hns.comp hks, hell_lt, hC, hv, ?_, ?_, ?_, ?_, hmesh0, ?_⟩, ?_⟩
  · exact hqns.comp hks.tendsto_atTop
  · intro z
    simpa only [ns', mesh', w'] using hweak z
  · intro K hK
    simpa only [ns', mesh', w'] using (hlocal K hK).1
  · intro K hK
    simpa only [ns', mesh', w'] using (hlocal K hK).2
  · exact hq_le0
  · intro n
    exact hbad (ns' n)

private theorem bad_sequence_contradiction
    (L : ℝ) (hL : 0 < L) {δ : ℝ} (hδ : 0 < δ)
    {mesh : ℕ → ℝ} (hmesh : Tendsto mesh atTop (𝓝[>] 0))
    (hbad : ∀ n, scaledDiscreteMinimum (mesh n) L < Analysis.Lambda L - δ) : False := by
  obtain ⟨d, hd⟩ := select_bad_nearMinimizers L hL hδ hmesh hbad
  obtain ⟨cd, hcd⟩ := bad_quotient_compact_subsequence L hL hδ d hd
  have hmesh0 : Tendsto (fun n ↦ d.mesh (cd.ns n)) atTop (𝓝 0) :=
    (tendsto_nhdsWithin_iff.1 cd.hmesh).1
  have hbound : ∀ n, ‖shiftedInterpolantH1 (d.w (cd.ns n))
      (d.hw (cd.ns n))‖ ≤ (1 + 4 * (Analysis.Lambda L + 1)) +
        (Analysis.Lambda L + 1) * (1 + 4 * (Analysis.Lambda L + 1)) + 1 := by
    intro n
    let Q : ℝ := Analysis.Lambda L + 1
    let C0 : ℝ := (1 + 4 * Q) + Q * (1 + 4 * Q)
    have hsq := norm_shiftedInterpolantH1_sq_le_of_scaled_rayleighQuotient_le
      (d.hw (cd.ns n)) (cd.hq_le n)
    have hC0 : 0 ≤ C0 := by
      dsimp [C0]
      have hn := norm_nonneg (shiftedInterpolantH1 (d.w (cd.ns n)) (d.hw (cd.ns n)))
      nlinarith [hsq, sq_nonneg (‖shiftedInterpolantH1 (d.w (cd.ns n))
        (d.hw (cd.ns n))‖)]
    have henergy : interpolantH1Energy (d.mesh (cd.ns n)) (d.w (cd.ns n)) ≤ C0 := by
      rw [← norm_shiftedInterpolantH1_sq (d.hw (cd.ns n))]
      exact hsq
    have hb := norm_shiftedInterpolantH1_le_add_one_of_interpolantH1Energy_le
      (d.hw (cd.ns n)) hC0 henergy
    simpa [Q, C0] using hb
  have hglobal : Tendsto (fun n ↦ ∫ x in halfLine,
      (shiftedInterpolant (d.mesh (cd.ns n)) (d.w (cd.ns n)) x -
        cd.v.continuousRep x) ^ 2) atTop (𝓝 0) := by
    apply tendsto_global_shiftedInterpolant_sq_sub_of_local hmesh0
      (fun n ↦ d.hw (cd.ns n)) hbound
    intro R hR
    exact (cd.hsq (Icc 0 R) isCompact_Icc)
  let data : ShiftedLimitData L cd.v := shiftedLimitData_of_tendstoUniformlyOn
    hmesh0 (fun n ↦ d.hw (cd.ns n)) cd.hunif
  have hvq : cd.v.rayleighQuotient ≤ cd.ell := by
    apply shiftedInterpolantH1_rayleighQuotient_le_of_tendsto_scaled
      hmesh0 (fun n ↦ d.hw (cd.ns n)) hbound cd.hweak hglobal data.mass_eq
    exact cd.hscaled
  have hvqL : cd.v.rayleighQuotient ≤ Analysis.Lambda L := hvq.trans cd.hell.le
  have hadm := data.isAdmissible_of_rayleighQuotient_le_Lambda hL hvqL
  have hLam := Analysis.Lambda_le_of_isAdmissible hadm
  have hLamEll : Analysis.Lambda L ≤ cd.ell := hLam.trans hvq
  exact (not_lt_of_ge hLamEll) cd.hell

theorem tendsto_scaledDiscreteMinimum_of_tendsto_mesh
    (L : ℝ) (hL : 0 < L) {mesh : ℕ → ℝ}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0)) :
    Tendsto (fun n ↦ scaledDiscreteMinimum (mesh n) L)
      atTop (𝓝 (Analysis.Lambda L)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hu := eventually_scaledDiscreteMinimum_le_add L hL hε2
  have hu' : ∀ᶠ n in atTop, scaledDiscreteMinimum (mesh n) L ≤
      Analysis.Lambda L + ε / 2 := by
    filter_upwards [hmesh hu] with n hn
    rw [Analysis.HalfLineH1.rayleighQuotient_eq_Lambda_of_isMinimizer hL
      (Analysis.HalfLineH1.optimizer_isMinimizer hL)] at hn
    exact hn
  have hl : ∀ᶠ n in atTop, Analysis.Lambda L - ε / 2 ≤
      scaledDiscreteMinimum (mesh n) L := by
    by_contra hnot
    rw [not_eventually] at hnot
    have hf : Filter.Frequently (fun n => scaledDiscreteMinimum (mesh n) L <
        Analysis.Lambda L - ε / 2) atTop := hnot.mono fun n hn => lt_of_not_ge hn
    obtain ⟨ns, hns, hbelow⟩ := extraction_of_frequently_atTop hf
    have hmesh' : Tendsto (fun n => mesh (ns n)) atTop (𝓝[>] 0) :=
      hmesh.comp hns.tendsto_atTop
    exact bad_sequence_contradiction L hL hε2 hmesh' (fun n => hbelow n)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu'.and hl)
  refine ⟨N, ?_⟩
  intro n hn
  have hh := hN n hn
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith [hh.2, hε], by linarith [hh.1, hε]⟩

theorem tendsto_scaledDiscreteMinimum (L : ℝ) (hL : 0 < L) :
    Tendsto (fun h : ℝ => scaledDiscreteMinimum h L)
      (𝓝[>] 0) (𝓝 (Analysis.Lambda L)) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain hlim := tendsto_scaledDiscreteMinimum_of_tendsto_mesh L hL hns
  exact ⟨id, by simpa [Function.comp_def] using hlim⟩

theorem tendsto_scaled_rayleighQuotient_of_nearMinimizer
    (L : ℝ) (hL : 0 < L)
    {mesh eps : ℕ → ℝ} {w : ℕ → Kernel}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0))
    (heps : Tendsto eps atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hnear : ∀ n, (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) ≤
      scaledDiscreteMinimum (mesh n) L + eps n) :
    Tendsto (fun n ↦ (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n))
      atTop (𝓝 (Analysis.Lambda L)) := by
  let q : ℕ → ℝ := fun n ↦ (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n)
  have hlow : ∀ n, scaledDiscreteMinimum (mesh n) L ≤ q n := fun n =>
    scaledDiscreteMinimum_le_of_isAdmissible (hw n)
  have hmin := tendsto_scaledDiscreteMinimum_of_tendsto_mesh L hL hmesh
  apply Metric.tendsto_atTop.2
  intro δ hδ
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hmin (δ / 3) (by linarith)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 heps (δ / 3) (by linarith)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hm := hN₁ n (le_trans (le_max_left _ _) hn)
  have he := hN₂ n (le_trans (le_max_right _ _) hn)
  have hu := hnear n
  have hl := hlow n
  rw [Real.dist_eq, abs_lt] at hm he
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith
  · linarith

private theorem identify_compact_nearMinimizer_limit
    (L : ℝ) (hL : 0 < L) {mesh eps : ℕ → ℝ} {w : ℕ → Kernel}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0)) (heps : Tendsto eps atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hnear : ∀ n, (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) ≤
      scaledDiscreteMinimum (mesh n) L + eps n) {v : HalfLineH1} {B : ℝ}
    (hbound : ∀ n, ‖shiftedInterpolantH1 (w n) (hw n)‖ ≤ B)
    (hweak : ∀ z, Tendsto (fun n => inner ℝ (shiftedInterpolantH1 (w n) (hw n)) z) atTop
      (𝓝 (inner ℝ v z)))
    (hunif : ∀ K, IsCompact K → TendstoUniformlyOn
      (fun n ↦ shiftedInterpolant (mesh n) (w n)) v.continuousRep atTop K)
    (hsq : ∀ K, IsCompact K → Tendsto (fun n => ∫ x in K,
      (shiftedInterpolant (mesh n) (w n) x - v.continuousRep x) ^ 2) atTop (𝓝 0)) :
    v = optimizer L hL := by
  have hmesh0 : Tendsto mesh atTop (𝓝 0) := (tendsto_nhdsWithin_iff.1 hmesh).1
  have hq := tendsto_scaled_rayleighQuotient_of_nearMinimizer L hL hmesh heps hw hnear
  have hglobal : Tendsto (fun n => ∫ x in halfLine,
      (shiftedInterpolant (mesh n) (w n) x - v.continuousRep x) ^ 2) atTop (𝓝 0) := by
    apply tendsto_global_shiftedInterpolant_sq_sub_of_local hmesh0 hw hbound
    intro R hR
    exact hsq (Icc 0 R) isCompact_Icc
  let d : ShiftedLimitData L v := shiftedLimitData_of_tendstoUniformlyOn hmesh0 hw hunif
  have hvq : v.rayleighQuotient ≤ Analysis.Lambda L := by
    apply (shiftedInterpolantH1_rayleighQuotient_le_of_tendsto_scaled
      hmesh0 hw hbound hweak hglobal d.mass_eq hq).trans
    exact le_rfl
  have hadm : v.IsAdmissible L := d.isAdmissible_of_rayleighQuotient_le_Lambda hL hvq
  have hmin : v.IsMinimizer L := ⟨hadm, fun u hu =>
    le_trans hvq (Analysis.Lambda_le_of_isAdmissible hu)⟩
  exact eq_optimizer_of_isMinimizer hL hmin

private structure AlignedShiftedSubsequence (L : ℝ) (hL : 0 < L)
    (mesh : ℕ → ℝ) (w : ℕ → Kernel)
    (hw : ∀ n, IsAdmissible (mesh n) L (w n)) (ns : ℕ → ℕ) where
  ms : ℕ → ℕ
  hms : StrictMono ms
  hinner : ∀ z : HalfLineH1, Tendsto (fun k => inner ℝ
    (shiftedInterpolantH1 (w (ns (ms k))) (hw (ns (ms k)))) z) atTop
    (𝓝 (inner ℝ (optimizer L hL) z))
  hglobal : Tendsto (fun k => ∫ x in halfLine,
    (shiftedInterpolant (mesh (ns (ms k))) (w (ns (ms k))) x -
      (optimizer L hL).continuousRep x) ^ 2) atTop (𝓝 0)
  hunif : ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
    (fun k ↦ shiftedInterpolant (mesh (ns (ms k))) (w (ns (ms k))))
    (optimizer L hL).continuousRep atTop K

private def extract_aligned_shifted_subsequence
    (L : ℝ) (hL : 0 < L) {mesh eps : ℕ → ℝ} {w : ℕ → Kernel}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0)) (heps : Tendsto eps atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hnear : ∀ n, (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) ≤
      scaledDiscreteMinimum (mesh n) L + eps n) (ns : ℕ → ℕ) (hns : StrictMono ns) :
    AlignedShiftedSubsequence L hL mesh w hw ns := by
  have hqns := (tendsto_scaled_rayleighQuotient_of_nearMinimizer L hL
    hmesh heps hw hnear).comp hns.tendsto_atTop
  let hNexists := Metric.tendsto_atTop.1 hqns 1 (by norm_num)
  let N : ℕ := Classical.choose hNexists
  have hN : ∀ n ≥ N, dist (((fun n => (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n)) ∘ ns) n)
      (Analysis.Lambda L) < 1 := Classical.choose_spec hNexists
  let meshT : ℕ → ℝ := fun n => mesh (ns (N + n))
  let epsT : ℕ → ℝ := fun n => eps (ns (N + n))
  let wT : ℕ → Kernel := fun n => w (ns (N + n))
  have htail : Tendsto (fun n : ℕ => N + n) atTop atTop := by
    simpa [Nat.add_comm] using (tendsto_add_atTop_nat N)
  have hnstail : Tendsto (fun n => ns (N + n)) atTop atTop :=
    hns.tendsto_atTop.comp htail
  have hmeshT : Tendsto meshT atTop (𝓝[>] 0) := hmesh.comp hnstail
  have hepsT : Tendsto epsT atTop (𝓝 0) := heps.comp hnstail
  have hwT : ∀ n, IsAdmissible (meshT n) L (wT n) := fun n => hw (ns (N+n))
  have hnearT : ∀ n, (meshT n)⁻¹ ^ 2 * rayleighQuotient (wT n) ≤
      scaledDiscreteMinimum (meshT n) L + epsT n := by
    intro n
    simpa [meshT, epsT, wT] using hnear (ns (N+n))
  have hqT : ∀ n, (meshT n)⁻¹ ^ 2 * rayleighQuotient (wT n) ≤ Analysis.Lambda L + 1 := by
    intro n
    have hh := hN (N+n) (Nat.le_add_right N n)
    rw [Real.dist_eq, abs_lt] at hh
    have hu : ((fun n => (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n)) ∘ ns) (N+n) <
        Analysis.Lambda L + 1 := by linarith [hh.2]
    simpa [meshT, wT, Function.comp_def] using le_of_lt hu
  let Q : ℝ := Analysis.Lambda L + 1
  let C0 : ℝ := (1 + 4 * Q) + Q * (1 + 4 * Q)
  have hsq0 := norm_shiftedInterpolantH1_sq_le_of_scaled_rayleighQuotient_le
    (hwT 0) (by simpa [Q] using hqT 0)
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    nlinarith [hsq0, sq_nonneg ‖shiftedInterpolantH1 (wT 0) (hwT 0)‖]
  have hboundT : ∀ n, ‖shiftedInterpolantH1 (wT n) (hwT n)‖ ≤ C0 + 1 := by
    intro n
    have hsq := norm_shiftedInterpolantH1_sq_le_of_scaled_rayleighQuotient_le
      (hwT n) (by simpa [Q] using hqT n)
    have henergy : interpolantH1Energy (meshT n) (wT n) ≤ C0 := by
      rw [← norm_shiftedInterpolantH1_sq (hwT n)]
      simpa [Q, C0] using hsq
    exact norm_shiftedInterpolantH1_le_add_one_of_interpolantH1Energy_le
      (hwT n) hC0 henergy
  let hcompact := exists_shiftedInterpolant_compact_subsequence_of_nearMinimizer L hL
    hmeshT hepsT hwT hnearT
  let ks := Classical.choose hcompact
  have hcompact' := Classical.choose_spec hcompact
  let v := Classical.choose hcompact'
  have hcompact'' := Classical.choose_spec hcompact'
  let C := Classical.choose hcompact''
  have hcompact''' := Classical.choose_spec hcompact''
  have hks : StrictMono ks := hcompact'''.1
  have hC : 0 ≤ C := hcompact'''.2.1
  have hvnorm : ‖v‖ ≤ C + 1 := hcompact'''.2.2.1
  have hweak : ∀ z : HalfLineH1, Tendsto (fun n ↦ inner ℝ
      (shiftedInterpolantH1 (wT (ks n)) (hwT (ks n))) z) atTop
      (𝓝 (inner ℝ v z)) := hcompact'''.2.2.2.1
  have hlocal : ∀ K : Set ℝ, IsCompact K →
      TendstoUniformlyOn (fun n ↦ shiftedInterpolant (meshT (ks n)) (wT (ks n)))
        v.continuousRep atTop K ∧
      Tendsto (fun n => ∫ x in K, (shiftedInterpolant (meshT (ks n))
        (wT (ks n)) x - v.continuousRep x) ^ 2) atTop (𝓝 0) :=
    hcompact'''.2.2.2.2
  have hv : v = optimizer L hL := by
    apply identify_compact_nearMinimizer_limit L hL
      (mesh := fun n => meshT (ks n)) (eps := fun n => epsT (ks n)) (w := fun n => wT (ks n))
      (hmeshT.comp hks.tendsto_atTop) (hepsT.comp hks.tendsto_atTop)
      (fun n => hwT (ks n)) (fun n => hnearT (ks n)) (fun n => hboundT (ks n))
      hweak (fun K hK => (hlocal K hK).1) (fun K hK => (hlocal K hK).2)
  let ms : ℕ → ℕ := fun k => N + ks k
  have hms : StrictMono ms := fun a b hab => Nat.add_lt_add_left (hks hab) N
  have hmesh0 : Tendsto meshT atTop (𝓝 0) := (tendsto_nhdsWithin_iff.1 hmeshT).1
  have hglobal : Tendsto (fun k => ∫ x in halfLine,
      (shiftedInterpolant (mesh (ns (ms k))) (w (ns (ms k))) x -
        (optimizer L hL).continuousRep x) ^ 2) atTop (𝓝 0) := by
    have hg := tendsto_global_shiftedInterpolant_sq_sub_of_local
      (hmesh0.comp hks.tendsto_atTop) (fun n => hwT (ks n)) (fun n => hboundT (ks n)) (v := v)
    have hg' := hg (fun R hR => (hlocal (Icc 0 R) isCompact_Icc).2)
    simpa [ms, meshT, wT, hv] using hg'
  have hunif : ∀ K : Set ℝ, IsCompact K → TendstoUniformlyOn
      (fun k ↦ shiftedInterpolant (mesh (ns (ms k))) (w (ns (ms k))))
      (optimizer L hL).continuousRep atTop K := by
    intro K hK
    simpa [ms, meshT, wT, hv] using (hlocal K hK).1
  exact ⟨ms, hms, by intro z; simpa [ms, meshT, wT, hv] using hweak z, hglobal, hunif⟩

private theorem tendsto_of_every_strictMono_subsequence_has_further_tendsto
    {x : ℕ → ℝ} {a : ℝ}
    (hsub : ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ms : ℕ → ℕ, StrictMono ms ∧
      Tendsto (fun k => x (ns (ms k))) atTop (𝓝 a)) : Tendsto x atTop (𝓝 a) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, dist (x n) a ≥ ε := by
    rw [Filter.frequently_atTop]
    intro N
    by_contra hN
    push Not at hN
    exact hnot ⟨N, fun n hn => hN n hn⟩
  obtain ⟨ns, hns, hbad⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ms, hms, hlim⟩ := hsub ns hns
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ε hε
  exact (not_lt_of_ge (hbad (ms (max N 0)))) (hN (max N 0) (le_max_left _ _))

theorem tendsto_inner_shiftedInterpolantH1_optimizer_of_nearMinimizer
    (L : ℝ) (hL : 0 < L) {mesh eps : ℕ → ℝ} {w : ℕ → Kernel}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0)) (heps : Tendsto eps atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hnear : ∀ n, (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) ≤
      scaledDiscreteMinimum (mesh n) L + eps n) (z : HalfLineH1) :
    Tendsto (fun n => inner ℝ (shiftedInterpolantH1 (w n) (hw n)) z) atTop
      (𝓝 (inner ℝ (optimizer L hL) z)) := by
  apply tendsto_of_every_strictMono_subsequence_has_further_tendsto
  intro ns hns
  obtain ⟨ms, hms, hinner, -, -⟩ := extract_aligned_shifted_subsequence
    L hL hmesh heps hw hnear ns hns
  exact ⟨ms, hms, hinner z⟩

theorem tendsto_global_shiftedInterpolant_sq_sub_optimizer_of_nearMinimizer
    (L : ℝ) (hL : 0 < L) {mesh eps : ℕ → ℝ} {w : ℕ → Kernel}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0)) (heps : Tendsto eps atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hnear : ∀ n, (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) ≤
      scaledDiscreteMinimum (mesh n) L + eps n) :
    Tendsto (fun n => ∫ x in halfLine, (shiftedInterpolant (mesh n) (w n) x -
      (optimizer L hL).continuousRep x) ^ 2) atTop (𝓝 0) := by
  apply tendsto_of_every_strictMono_subsequence_has_further_tendsto
  intro ns hns
  obtain ⟨ms, hms, -, hglobal, -⟩ := extract_aligned_shifted_subsequence
    L hL hmesh heps hw hnear ns hns
  exact ⟨ms, hms, hglobal⟩

theorem tendstoUniformlyOn_shiftedInterpolant_optimizer_of_nearMinimizer
    (L : ℝ) (hL : 0 < L) {mesh eps : ℕ → ℝ} {w : ℕ → Kernel}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0)) (heps : Tendsto eps atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hnear : ∀ n, (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) ≤
      scaledDiscreteMinimum (mesh n) L + eps n) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n ↦ shiftedInterpolant (mesh n) (w n))
      (optimizer L hL).continuousRep atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hnot
  rw [not_eventually] at hnot
  have hfreq : ∃ᶠ n in atTop, ¬ ∀ x ∈ K,
      dist ((optimizer L hL).continuousRep x) (shiftedInterpolant (mesh n) (w n) x) < ε := hnot
  obtain ⟨ns, hns, hbad⟩ := extraction_of_frequently_atTop hfreq
  let p := extract_aligned_shifted_subsequence L hL hmesh heps hw hnear ns hns
  have hsub := (Metric.tendstoUniformlyOn_iff.mp (p.hunif K hK)) ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsub
  have hbadN := hbad (p.ms (max N 0))
  simp only [not_forall, not_lt] at hbadN
  obtain ⟨x, hxK, hx⟩ := hbadN
  exact (not_lt_of_ge hx) (hN (max N 0) (le_max_left _ _) x hxK)

private theorem whole_shiftedInterpolant_sq_sub_eq_halfLine
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w)
    (opt : HalfLineH1) (hopt : ∀ x ≤ 0, opt.continuousRep x = 0) :
    (∫ x : ℝ, (shiftedInterpolant h w x - opt.continuousRep x) ^ 2) =
      ∫ x in halfLine, (shiftedInterpolant h w x - opt.continuousRep x) ^ 2 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  have hu := shiftedInterpolant_eq_zero_of_nonpos (w := w) hw.h_pos (le_of_not_ge hx)
  rw [hu, hopt x (le_of_not_ge hx)]
  simp

private theorem interpolant_memLp_of_admissible
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    MemLp (interpolant h w) 2 volume := by
  exact (memLp_two_iff_integrable_sq
    ((continuous_interpolant hw.h_pos).aestronglyMeasurable)).2
    (integrable_sq_interpolant hw)

private theorem interpolant_value_eq_translate_shiftedInterpolantH1
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    (interpolant_memLp_of_admissible hw).toLp (interpolant h w) =
      Analysis.translateL2 h (shiftedInterpolantH1 w hw).value := by
  apply Lp.ext
  have hval := (shiftedInterpolant_value_memLp_of_admissible hw).coeFn_toLp
  have hval' : (fun x =>
      (shiftedInterpolant_value_memLp_of_admissible hw).toLp (shiftedInterpolant h w) (x + h)) =ᵐ[volume]
      fun x => shiftedInterpolant h w (x + h) := by
    exact (measurePreserving_add_right (volume : Measure ℝ) h).quasiMeasurePreserving.ae_eq_comp
      (shiftedInterpolant_value_memLp_of_admissible hw).coeFn_toLp
  filter_upwards [(interpolant_memLp_of_admissible hw).coeFn_toLp,
    Analysis.translateL2_ae_eq h (shiftedInterpolantH1 w hw).value, hval'] with x hx htrans hvalx
  rw [hx, htrans]
  rw [← value_shiftedInterpolantH1 hw] at hvalx
  rw [hvalx]
  unfold shiftedInterpolant
  show interpolant h w x = interpolant h w ((x + h) - h)
  congr 1
  ring

private theorem deriv_interpolant_memLp_of_admissible
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    MemLp (deriv (interpolant h w)) 2 volume := by
  exact (memLp_two_iff_integrable_sq (by fun_prop)).2
    (integrable_sq_deriv_interpolant hw)

private theorem interpolant_deriv_eq_translate_shiftedInterpolantH1
    {h L : ℝ} {w : Kernel} (hw : IsAdmissible h L w) :
    (deriv_interpolant_memLp_of_admissible hw).toLp (deriv (interpolant h w)) =
      Analysis.translateL2 h (shiftedInterpolantH1 w hw).weakDeriv := by
  apply Lp.ext
  have hder := (shiftedInterpolant_deriv_memLp_of_admissible hw).coeFn_toLp
  have hder' : (fun x =>
      (shiftedInterpolant_deriv_memLp_of_admissible hw).toLp
        (deriv (shiftedInterpolant h w)) (x + h)) =ᵐ[volume]
      fun x => deriv (shiftedInterpolant h w) (x + h) := by
    exact (measurePreserving_add_right (volume : Measure ℝ) h).quasiMeasurePreserving.ae_eq_comp
      (shiftedInterpolant_deriv_memLp_of_admissible hw).coeFn_toLp
  filter_upwards [(deriv_interpolant_memLp_of_admissible hw).coeFn_toLp,
    Analysis.translateL2_ae_eq h (shiftedInterpolantH1 w hw).weakDeriv, hder'] with x hx htrans hderx
  rw [hx, htrans]
  rw [← weakDeriv_shiftedInterpolantH1 hw] at hderx
  rw [hderx, shiftedInterpolant_deriv_eq]
  congr 1
  ring

def interpolantH1Graph {h L : ℝ} (w : Kernel) (hw : IsAdmissible h L w) :
    H1Graph :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ RealL2 RealL2).symm
    (Analysis.translateL2 h (shiftedInterpolantH1 w hw).value,
     Analysis.translateL2 h (shiftedInterpolantH1 w hw).weakDeriv)

theorem interpolantH1Graph_fst_ae_eq {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    (((interpolantH1Graph w hw).fst : RealL2) : ℝ → ℝ) =ᵐ[volume] interpolant h w := by
  change (Analysis.translateL2 h (shiftedInterpolantH1 w hw).value : ℝ → ℝ) =ᵐ[volume]
    interpolant h w
  rw [← interpolant_value_eq_translate_shiftedInterpolantH1 hw]
  exact (interpolant_memLp_of_admissible hw).coeFn_toLp

theorem interpolantH1Graph_snd_ae_eq {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    (((interpolantH1Graph w hw).snd : RealL2) : ℝ → ℝ) =ᵐ[volume] deriv (interpolant h w) := by
  change (Analysis.translateL2 h (shiftedInterpolantH1 w hw).weakDeriv : ℝ → ℝ) =ᵐ[volume]
    deriv (interpolant h w)
  rw [← interpolant_deriv_eq_translate_shiftedInterpolantH1 hw]
  exact (deriv_interpolant_memLp_of_admissible hw).coeFn_toLp

private theorem translate_comp_neg (h : ℝ) (g : RealL2) :
    Analysis.translateL2 h (Analysis.translateL2 (-h) g) = g := by
  apply Lp.ext
  have hgx := (measurePreserving_add_right (volume : Measure ℝ) h).quasiMeasurePreserving.ae_eq_comp
    (Analysis.translateL2_ae_eq (-h) g)
  filter_upwards [Analysis.translateL2_ae_eq h (Analysis.translateL2 (-h) g), hgx] with x hx hgx
  rw [hx]
  simpa [Function.comp_def] using hgx

private theorem translate_inner_adjoint (h : ℝ) (f g : RealL2) :
    inner ℝ (Analysis.translateL2 h f) g =
      inner ℝ f (Analysis.translateL2 (-h) g) := by
  calc
    inner ℝ (Analysis.translateL2 h f) g =
        inner ℝ (Analysis.translateL2 h f)
          (Analysis.translateL2 h (Analysis.translateL2 (-h) g)) := by
      rw [translate_comp_neg h g]
    _ = inner ℝ f (Analysis.translateL2 (-h) g) :=
      (Analysis.translateL2 h).inner_map_map f (Analysis.translateL2 (-h) g)

private theorem tendsto_inner_of_tendsto_inner_of_norm_bound
    {mesh : ℕ → ℝ} {u : ℕ → RealL2} {v : RealL2} {B : ℝ}
    (hweak : ∀ z : RealL2, Tendsto (fun n => inner ℝ (u n) z) atTop (𝓝 (inner ℝ v z)))
    (hbound : ∀ᶠ n in atTop, ‖u n‖ ≤ B) (g : RealL2)
    (htest : Tendsto (fun n => Analysis.translateL2 (-mesh n) g) atTop (𝓝 g)) :
    Tendsto (fun n => inner ℝ (u n) (Analysis.translateL2 (-mesh n) g)) atTop
      (𝓝 (inner ℝ v g)) := by
  have hdiff : Tendsto (fun n => ‖Analysis.translateL2 (-mesh n) g - g‖) atTop (𝓝 0) := by
    simpa using (htest.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => g) atTop (𝓝 g))).norm
  have hprod : Tendsto (fun n => B * ‖Analysis.translateL2 (-mesh n) g - g‖) atTop (𝓝 0) :=
    by simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => B) atTop (𝓝 B)).mul hdiff)
  have hzero : Tendsto (fun n => inner ℝ (u n)
      (Analysis.translateL2 (-mesh n) g - g)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)) hprod
    · filter_upwards with n; exact norm_nonneg _
    · filter_upwards [hbound] with n hn
      exact norm_inner_le_norm _ _ |>.trans (by gcongr)
  have hadd : ∀ n, inner ℝ (u n) (Analysis.translateL2 (-mesh n) g) =
      inner ℝ (u n) g + inner ℝ (u n) (Analysis.translateL2 (-mesh n) g - g) := by
    intro n
    rw [← inner_add_right]
    congr 1
    abel
  have hsum := (hweak g).add hzero
  rw [show (fun n => inner ℝ (u n) (Analysis.translateL2 (-mesh n) g)) =
      (fun n => inner ℝ (u n) g + inner ℝ (u n)
        (Analysis.translateL2 (-mesh n) g - g)) by funext n; exact hadd n]
  simpa using hsum

theorem tendsto_inner_interpolantH1Graph_components_optimizer_of_nearMinimizer
    (L : ℝ) (hL : 0 < L) {mesh eps : ℕ → ℝ} {w : ℕ → Kernel}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0)) (heps : Tendsto eps atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hnear : ∀ n, (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) ≤
      scaledDiscreteMinimum (mesh n) L + eps n) (g : RealL2) :
    Tendsto (fun n => inner ℝ (interpolantH1Graph (w n) (hw n)).fst g) atTop
      (𝓝 (inner ℝ (optimizer L hL).value g)) ∧
    Tendsto (fun n => inner ℝ (interpolantH1Graph (w n) (hw n)).snd g) atTop
      (𝓝 (inner ℝ (optimizer L hL).weakDeriv g)) := by
  obtain ⟨C, hC, henergy⟩ := eventually_interpolantH1Energy_le_of_nearMinimizer
    L hL hmesh heps hw hnear
  let B : ℝ := C + 1
  have hbound : ∀ᶠ n in atTop, ‖shiftedInterpolantH1 (w n) (hw n)‖ ≤ B := by
    filter_upwards [henergy] with n hn
    exact norm_shiftedInterpolantH1_le_add_one_of_interpolantH1Energy_le (hw n) hC hn
  have hmesh0 : Tendsto mesh atTop (𝓝 0) := (tendsto_nhdsWithin_iff.mp hmesh).1
  have htest : Tendsto (fun n => Analysis.translateL2 (-mesh n) g) atTop (𝓝 g) := by
    have hc := ((Analysis.continuous_translateL2 g).tendsto 0).comp
      (show Tendsto (fun n => -mesh n) atTop (𝓝 0) by simpa using hmesh0.neg)
    have hz : Analysis.translateL2 (0 : ℝ) g = g := by
      apply Lp.ext
      simpa using Analysis.translateL2_ae_eq 0 g
    simpa [Function.comp_def, hz] using hc
  have hweak : ∀ z : RealL2, Tendsto (fun n =>
      inner ℝ (shiftedInterpolantH1 (w n) (hw n)).value z) atTop
      (𝓝 (inner ℝ (optimizer L hL).value z)) := by
    intro z
    exact HalfLineH1.tendsto_inner_value
      (fun y => tendsto_inner_shiftedInterpolantH1_optimizer_of_nearMinimizer
        L hL hmesh heps hw hnear y) z
  have hweakD : ∀ z : RealL2, Tendsto (fun n =>
      inner ℝ (shiftedInterpolantH1 (w n) (hw n)).weakDeriv z) atTop
      (𝓝 (inner ℝ (optimizer L hL).weakDeriv z)) := by
    intro z
    exact HalfLineH1.tendsto_inner_weakDeriv
      (fun y => tendsto_inner_shiftedInterpolantH1_optimizer_of_nearMinimizer
        L hL hmesh heps hw hnear y) z
  have hval := tendsto_inner_of_tendsto_inner_of_norm_bound
    (u := fun n => (shiftedInterpolantH1 (w n) (hw n)).value)
    (v := (optimizer L hL).value) (B := B)
    hweak (hbound.mono fun n hn => (HalfLineH1.norm_value_le _).trans hn) g htest
  have hder := tendsto_inner_of_tendsto_inner_of_norm_bound
    (u := fun n => (shiftedInterpolantH1 (w n) (hw n)).weakDeriv)
    (v := (optimizer L hL).weakDeriv) (B := B)
    hweakD (hbound.mono fun n hn => (HalfLineH1.norm_weakDeriv_le _).trans hn) g htest
  constructor
  · convert hval using 1
    funext n
    rw [show (interpolantH1Graph (w n) (hw n)).fst =
      Analysis.translateL2 (mesh n) (shiftedInterpolantH1 (w n) (hw n)).value by rfl,
      translate_inner_adjoint]
  · convert hder using 1
    funext n
    rw [show (interpolantH1Graph (w n) (hw n)).snd =
      Analysis.translateL2 (mesh n) (shiftedInterpolantH1 (w n) (hw n)).weakDeriv by rfl,
      translate_inner_adjoint]

theorem tendsto_inner_interpolantH1Graph_optimizer_of_nearMinimizer
    (L : ℝ) (hL : 0 < L) {mesh eps : ℕ → ℝ} {w : ℕ → Kernel}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0)) (heps : Tendsto eps atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hnear : ∀ n, (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) ≤
      scaledDiscreteMinimum (mesh n) L + eps n) (z : H1Graph) :
    Tendsto (fun n => inner ℝ (interpolantH1Graph (w n) (hw n)) z) atTop
      (𝓝 (inner ℝ ((optimizer L hL : HalfLineH1).1 : H1Graph) z)) := by
  obtain ⟨h1, h2⟩ := tendsto_inner_interpolantH1Graph_components_optimizer_of_nearMinimizer
    L hL hmesh heps hw hnear (WithLp.ofLp z).1
  obtain ⟨h1', h2'⟩ := tendsto_inner_interpolantH1Graph_components_optimizer_of_nearMinimizer
    L hL hmesh heps hw hnear (WithLp.ofLp z).2
  rw [WithLp.prod_inner_apply]
  convert h1.add h2' using 1 <;> rfl

private theorem tendsto_norm_of_tendsto_sq_norm {x : ℕ → RealL2}
    (hx : Tendsto (fun n => ‖x n‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ‖x n‖) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hx) (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have hs : ‖x n‖ ^ 2 < ε ^ 2 := by
    simpa [Real.dist_eq, abs_of_nonneg (sq_nonneg (‖x n‖))] using hN n hn
  nlinarith [norm_nonneg (x n)]

theorem tendsto_global_interpolant_sq_sub_optimizer_of_nearMinimizer
    (L : ℝ) (hL : 0 < L) {mesh eps : ℕ → ℝ} {w : ℕ → Kernel}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0)) (heps : Tendsto eps atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hnear : ∀ n, (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) ≤
      scaledDiscreteMinimum (mesh n) L + eps n) :
    Tendsto (fun n => ∫ x in halfLine,
      (interpolant (mesh n) (w n) x - (optimizer L hL).continuousRep x)^2)
      atTop (𝓝 0) := by
  let opt := optimizer L hL
  let u : ℕ → HalfLineH1 := fun n => shiftedInterpolantH1 (w n) (hw n)
  let orig : ℕ → RealL2 := fun n =>
    (interpolant_memLp_of_admissible (hw n)).toLp (interpolant (mesh n) (w n))
  have hshift := tendsto_global_shiftedInterpolant_sq_sub_optimizer_of_nearMinimizer
    L hL hmesh heps hw hnear
  have hshiftNormEq : ∀ n, ‖(u n).value - opt.value‖^2 =
      ∫ x in halfLine, (shiftedInterpolant (mesh n) (w n) x - opt.continuousRep x)^2 := by
    intro n
    have hval : (u n - opt).value = (u n).value - opt.value := by rfl
    calc
      ‖(u n).value - opt.value‖ ^ 2 = ‖(u n - opt).value‖ ^ 2 := by rw [hval]
      _ = ∫ x : ℝ, (u n - opt).continuousRep x ^ 2 :=
        (HalfLineH1.integral_continuousRep_sq_eq_norm_value_sq (u n - opt)).symm
      _ = ∫ x : ℝ, (shiftedInterpolant (mesh n) (w n) x - opt.continuousRep x)^2 := by
        congr 1
        funext x
        rw [sub_eq_add_neg, HalfLineH1.continuousRep_add, continuousRep_neg]
        rw [continuousRep_shiftedInterpolantH1_eq (hw n)]
        simp only [Pi.add_apply, Pi.neg_apply]
        ring
      _ = ∫ x in halfLine, (shiftedInterpolant (mesh n) (w n) x - opt.continuousRep x)^2 :=
        whole_shiftedInterpolant_sq_sub_eq_halfLine (hw n) opt
          (fun x hx => opt.continuousRep_eq_zero_of_nonpositive hx)
  have hshiftNorm : Tendsto (fun n => ‖(u n).value - opt.value‖) atTop (𝓝 0) := by
    apply tendsto_norm_of_tendsto_sq_norm (x := fun n => (u n).value - opt.value)
    convert hshift using 1
    funext n
    rw [hshiftNormEq n]
  have hmesh0 : Tendsto mesh atTop (𝓝 0) := (tendsto_nhdsWithin_iff.mp hmesh).1
  have hzero : Analysis.translateL2 (0 : ℝ) opt.value = opt.value := by
    apply Lp.ext
    simpa using Analysis.translateL2_ae_eq 0 opt.value
  have ht : Tendsto (fun n => Analysis.translateL2 (mesh n) opt.value)
      atTop (𝓝 opt.value) := by
    have hc := ((Analysis.continuous_translateL2 opt.value).tendsto 0).comp hmesh0
    rw [hzero] at hc
    simpa only [Function.comp_def] using hc
  have htransNorm : Tendsto (fun n => ‖Analysis.translateL2 (mesh n) opt.value - opt.value‖)
      atTop (𝓝 0) := by
    have hh := (ht.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => opt.value)
      atTop (𝓝 opt.value))).norm
    have hz : ‖opt.value - opt.value‖ = 0 := by simp
    rw [hz] at hh
    exact hh
  have hnormOrig : Tendsto (fun n => ‖orig n - opt.value‖) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hshiftNorm (ε / 2) (by linarith)
    obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 htransNorm (ε / 2) (by linarith)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    have hu := hN₁ n (le_trans (le_max_left _ _) hn)
    have hv := hN₂ n (le_trans (le_max_right _ _) hn)
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hu hv
    have heq : orig n - opt.value =
        Analysis.translateL2 (mesh n) ((u n).value - opt.value) +
          (Analysis.translateL2 (mesh n) opt.value - opt.value) := by
      rw [show orig n = Analysis.translateL2 (mesh n) (u n).value by
        simpa [orig, u] using interpolant_value_eq_translate_shiftedInterpolantH1 (hw n)]
      simp only [map_sub]
      abel
    rw [heq]
    calc
      ‖Analysis.translateL2 (mesh n) ((u n).value - opt.value) +
          (Analysis.translateL2 (mesh n) opt.value - opt.value)‖ ≤
          ‖Analysis.translateL2 (mesh n) ((u n).value - opt.value)‖ +
            ‖Analysis.translateL2 (mesh n) opt.value - opt.value‖ := norm_add_le _ _
      _ = ‖(u n).value - opt.value‖ +
          ‖Analysis.translateL2 (mesh n) opt.value - opt.value‖ := by
        rw [Analysis.translateL2_norm]
      _ < ε := by linarith
  have hsqOrig : Tendsto (fun n => ‖orig n - opt.value‖ ^ 2) atTop (𝓝 0) := by
    have hh := hnormOrig.pow 2
    simpa using hh
  have hwhole : ∀ n, (∫ x : ℝ, (interpolant (mesh n) (w n) x - opt.continuousRep x)^2) =
      ‖orig n - opt.value‖^2 := by
    intro n
    rw [← real_inner_self_eq_norm_sq (orig n - opt.value), L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(interpolant_memLp_of_admissible (hw n)).coeFn_toLp,
      opt.continuousRep_memLp.coeFn_toLp, opt.continuousRep_ae_eq_value,
      Lp.coeFn_sub (orig n) opt.value] with x hx ho hv hsub
    dsimp [orig] at hsub ⊢
    rw [hsub, hx]
    have hvo : (opt.1.fst : ℝ → ℝ) x = opt.continuousRep x := hv.symm
    rw [hvo]
    simp only [starRingEnd_apply, TrivialStar.star_trivial]
    ring
  refine squeeze_zero' (Eventually.of_forall (fun n => by
    simpa [halfLine] using
      (setIntegral_nonneg measurableSet_Ici (fun _ _ => sq_nonneg _)))) ?_ hsqOrig
  filter_upwards with n
  calc
    ∫ x in halfLine, (interpolant (mesh n) (w n) x - opt.continuousRep x)^2 ≤
        ∫ x in (Set.univ : Set ℝ), (interpolant (mesh n) (w n) x - opt.continuousRep x)^2 := by
      refine setIntegral_mono_set ?_ ?_ ?_
      · exact ((interpolant_memLp_of_admissible (hw n)).sub opt.continuousRep_memLp).integrable_sq.integrableOn
      · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
      · exact Filter.Eventually.of_forall (fun x _ => Set.mem_univ x)
    _ = ‖orig n - opt.value‖ ^ 2 := by simpa only [setIntegral_univ] using hwhole n

private theorem tendstoUniformly_optimizer_translate
    (L : ℝ) (hL : 0 < L) {mesh : ℕ → ℝ}
    (hmesh : Tendsto mesh atTop (𝓝 0)) :
    TendstoUniformly (fun n x => (optimizer L hL).continuousRep (x + mesh n))
      (optimizer L hL).continuousRep atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuous_iff.mp
    (optimizer L hL).uniformContinuous_continuousRep ε hε
  have hev : ∀ᶠ n in atTop, mesh n ∈ Ioo (-δ) δ :=
    hmesh (Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ)
  filter_upwards [hev] with n hn x
  apply huc
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hn.1, hn.2]

theorem tendstoUniformlyOn_interpolant_optimizer_of_nearMinimizer
    (L : ℝ) (hL : 0 < L) {mesh eps : ℕ → ℝ} {w : ℕ → Kernel}
    (hmesh : Tendsto mesh atTop (𝓝[>] 0)) (heps : Tendsto eps atTop (𝓝 0))
    (hw : ∀ n, IsAdmissible (mesh n) L (w n))
    (hnear : ∀ n, (mesh n)⁻¹ ^ 2 * rayleighQuotient (w n) ≤
      scaledDiscreteMinimum (mesh n) L + eps n) (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n => interpolant (mesh n) (w n))
      (optimizer L hL).continuousRep atTop K := by
  let K' : Set ℝ := (fun p : ℝ × ℝ => p.1 + p.2) '' (K ×ˢ Icc (-1 : ℝ) 1)
  have hK' : IsCompact K' := by
    apply (hK.prod isCompact_Icc).image
    exact continuous_fst.add continuous_snd
  have hshift := tendstoUniformlyOn_shiftedInterpolant_optimizer_of_nearMinimizer
    L hL hmesh heps hw hnear K' hK'
  have hopt := tendstoUniformly_optimizer_translate L hL
    ((tendsto_nhdsWithin_iff.mp hmesh).1)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hmesh0 : Tendsto mesh atTop (𝓝 0) := (tendsto_nhdsWithin_iff.mp hmesh).1
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    ((Metric.tendstoUniformlyOn_iff.mp hshift) (ε / 2) hε2)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    ((Metric.tendstoUniformly_iff.mp hopt) (ε / 2) hε2)
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1
    (hmesh0 (Icc_mem_nhds (a := (-1 : ℝ)) (b := 1) (x := 0)
      (by norm_num) (by norm_num)))
  filter_upwards [eventually_ge_atTop (max (max N₁ N₂) N₃)] with n hn x hx
  have hn1 := hN₁ n (le_trans (le_max_left N₁ N₂)
    (le_trans (le_max_left (max N₁ N₂) N₃) hn))
  have hn2 := hN₂ n (le_trans (le_max_right N₁ N₂)
    (le_trans (le_max_left (max N₁ N₂) N₃) hn))
  have hn3 := hN₃ n (le_trans (le_max_right (max N₁ N₂) N₃) hn)
  have hx' : x + mesh n ∈ K' := by
    refine ⟨(x, mesh n), ⟨hx, ?_⟩, rfl⟩
    exact hn3
  have hs := hn1 (x + mesh n) hx'
  have ho := hn2 x
  have hi : interpolant (mesh n) (w n) x =
      shiftedInterpolant (mesh n) (w n) (x + mesh n) := by
    simp [shiftedInterpolant]
  rw [hi]
  calc
    dist ((optimizer L hL).continuousRep x)
        (shiftedInterpolant (mesh n) (w n) (x + mesh n)) ≤
        dist ((optimizer L hL).continuousRep x)
          ((optimizer L hL).continuousRep (x + mesh n)) +
        dist ((optimizer L hL).continuousRep (x + mesh n))
          (shiftedInterpolant (mesh n) (w n) (x + mesh n)) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add ho hs
    _ = ε := by ring

end RayleighKernel.Discrete
