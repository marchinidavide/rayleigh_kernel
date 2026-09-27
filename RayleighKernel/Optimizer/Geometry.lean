import RayleighKernel.Compression.StrictMoment
import RayleighKernel.Variational.Existence
import RayleighKernel.Obstacle.Regularity

noncomputable section
open Set MeasureTheory
open RayleighKernel
namespace RayleighKernel.Analysis.HalfLineH1

theorem compressedProfile_isAdmissible_firstMoment
    {L : ℝ} {f : HalfLineH1} (hf : f.IsAdmissible L)
    (D : OpenIntervalDecomposition f.positivitySet) :
    (compressedProfile f D hf.nonnegative).IsAdmissible
      (compressedProfile f D hf.nonnegative).firstMoment := by
  let g := compressedProfile f D hf.nonnegative
  have hg_nonneg := compressedProfile_nonnegative f D hf.nonnegative
  have hg_int := integrableOn_continuousRep_compressedProfile f D hf.nonnegative hf.integrable
  have hg_moment := firstMoment_integrableOn_compressedProfile f D hf.nonnegative
    hf.integrable hf.firstMoment_integrable
  refine ⟨hg_nonneg, hg_int, hg_moment, ?_, rfl⟩
  rw [mass_compressedProfile f D hf.nonnegative hf.integrable, hf.mass_eq]

theorem rayleighQuotient_compressedProfile
    (f : HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet)
    (hnonneg : ∀ x ∈ Ici 0, 0 ≤ f.continuousRep x) :
    (compressedProfile f D hnonneg).rayleighQuotient = f.rayleighQuotient := by
  rw [HalfLineH1.rayleighQuotient, HalfLineH1.rayleighQuotient,
    dirichletEnergy_compressedProfile, squareEnergy_compressedProfile]

theorem firstMoment_compressedProfile_eq_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (D : OpenIntervalDecomposition f.positivitySet) :
    (compressedProfile f D hfmin.1.nonnegative).firstMoment = f.firstMoment := by
  let g := compressedProfile f D hfmin.1.nonnegative
  have hgadm : g.IsAdmissible g.firstMoment := compressedProfile_isAdmissible_firstMoment hfmin.1 D
  have hgpos : 0 < g.firstMoment := firstMoment_pos_of_mass_eq_one_of_nonnegative
    hgadm.nonnegative hgadm.mass_eq hgadm.firstMoment_integrable
  have hgle : g.firstMoment ≤ L := by
    have hgle' := firstMoment_compressedProfile_le f D hfmin.1.nonnegative
      hfmin.1.integrable hfmin.1.firstMoment_integrable
    change (compressedProfile f D hfmin.1.nonnegative).firstMoment ≤ L
    exact hgle'.trans_eq hfmin.1.firstMoment_eq
  have hgeq : g.firstMoment = L := by
    by_contra hne
    have hgl : g.firstMoment < L := lt_of_le_of_ne hgle hne
    let a : ℝ := g.firstMoment / L
    have ha : 0 < a := div_pos hgpos hL
    have ha1 : a < 1 := (div_lt_one hL).2 hgl
    have hscaled : (g.rescale a ha).IsAdmissible L := by
      have h := g.rescale_isAdmissible ha hgadm
      convert h using 1
      dsimp [a]
      field_simp [ne_of_gt hL]
    have hmin := hfmin.2 (g.rescale a ha) hscaled
    have hqcomp := rayleighQuotient_compressedProfile f D hfmin.1.nonnegative
    have hqscale := g.rayleighQuotient_rescale ha
    have hpos := rayleighQuotient_pos_of_mass_eq_one hfmin.1.mass_eq
    have hstrict : a ^ 2 * g.rayleighQuotient < f.rayleighQuotient := by
      have ha0 : 0 ≤ a := ha.le
      have hasq : a ^ 2 < 1 := by nlinarith
      change a ^ 2 * (compressedProfile f D hfmin.1.nonnegative).rayleighQuotient < _
      rw [hqcomp]
      nlinarith
    rw [hqscale] at hmin
    exact (not_lt_of_ge hmin) hstrict
  exact hgeq.trans hfmin.1.firstMoment_eq.symm

theorem integral_compressionMomentDefect_eq_zero_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (D : OpenIntervalDecomposition f.positivitySet) :
    (∫ x in f.positivitySet, f.compressionMomentDefect x * f.continuousRep x) = 0 := by
  have hident := firstMoment_sub_compressedProfile_eq_integral_compressionMomentDefect
    f D hfmin.1.nonnegative hfmin.1.integrable hfmin.1.firstMoment_integrable
  have heq := firstMoment_compressedProfile_eq_of_isMinimizer hL hfmin D
  rw [heq, sub_self] at hident
  exact hident.symm

theorem integral_continuousRep_pos_on_positivitySet_inter_Ioi
    {L : ℝ} {f : HalfLineH1} (hf : f.IsAdmissible L) {R : ℝ} (_hR : 0 ≤ R)
    (hposAbove : ∃ x ∈ f.positivitySet, R < x) :
    0 < ∫ x : ℝ in f.positivitySet ∩ Ioi R, f.continuousRep x := by
  let S : Set ℝ := f.positivitySet ∩ Ioi R
  have hSopen : IsOpen S := f.isOpen_positivitySet.inter isOpen_Ioi
  obtain ⟨z, hz, hzR⟩ := hposAbove
  have hSne : S.Nonempty := ⟨z, hz, hzR⟩
  have hSsub : S ⊆ halfLine := inter_subset_left.trans (positivitySet_subset_halfLine f)
  have hSint : IntegrableOn f.continuousRep S := hf.integrable.mono_set hSsub
  have hSnonneg : ∀ᵐ x ∂(volume.restrict S), 0 ≤ f.continuousRep x := by
    filter_upwards [ae_restrict_mem hSopen.measurableSet] with x hx
    exact hf.nonnegative x (hSsub hx)
  have hsupport : S ⊆ Function.support f.continuousRep := by
    intro x hx; exact ne_of_gt hx.1
  have hmeasure : 0 < volume (Function.support f.continuousRep ∩ S) := by
    exact lt_of_lt_of_le (hSopen.measure_pos (volume : Measure ℝ) hSne)
      (measure_mono (fun x hx => ⟨hsupport hx, hx⟩))
  exact (setIntegral_pos_iff_support_of_nonneg_ae hSnonneg hSint).2 hmeasure

theorem measureReal_compl_positivitySet_inter_Ioc_eq_zero_of_pos_above_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    {R : ℝ} (hR : 0 ≤ R) (hposAbove : ∃ x ∈ f.positivitySet, R < x) :
    volume.real (f.positivitySetᶜ ∩ Ioc 0 R) = 0 := by
  obtain ⟨D, hD⟩ := f.exists_positivityIntervalDecomposition
  have hmassAbove := integral_continuousRep_pos_on_positivitySet_inter_Ioi hfmin.1 hR hposAbove
  by_contra hgap
  have hgap' : 0 < volume.real (f.positivitySetᶜ ∩ Ioc 0 R) :=
    lt_of_le_of_ne (compressionMomentDefect_nonneg f R) (Ne.symm hgap)
  have hlt := firstMoment_compressedProfile_lt_of_gap_below_positive_mass f D
    hfmin.1.nonnegative hfmin.1.integrable hfmin.1.firstMoment_integrable hR hgap' hmassAbove
  have heq := firstMoment_compressedProfile_eq_of_isMinimizer hL hfmin D
  exact (lt_irrefl f.firstMoment) (heq ▸ hlt)

theorem exists_mem_positivitySet_lt_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    {R : ℝ} (hR : 0 < R) : ∃ x ∈ f.positivitySet, x < R := by
  obtain ⟨z, hz⟩ := f.positivitySet_nonempty hfmin.1
  by_contra hnone
  have hzR : R ≤ z := le_of_not_gt (fun h => hnone ⟨z, hz, h⟩)
  let r : ℝ := R / 2
  have hr : 0 ≤ r := le_of_lt (half_pos hR)
  have hzr : r < z := lt_of_lt_of_le (by dsimp [r]; linarith) hzR
  have hzero := measureReal_compl_positivitySet_inter_Ioc_eq_zero_of_pos_above_of_isMinimizer
    hL hfmin hr ⟨z, hz, hzr⟩
  have hsubset : Ioc 0 r ⊆ f.positivitySetᶜ ∩ Ioc 0 r := by
    intro x hx
    refine ⟨?_, hx⟩
    intro hxpos
    have hxR : x < R := by dsimp [r] at hx ⊢; linarith [hx.2, hR]
    exact hnone ⟨x, hxpos, hxR⟩
  have hpositive : 0 < volume.real (Ioc 0 r) := by
    have hrpos : 0 < r := by dsimp [r]; linarith
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    simpa using hrpos
  have hfinite : volume (f.positivitySetᶜ ∩ Ioc 0 r) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_Ioc_lt_top.ne (measure_mono inter_subset_right)
  have hmono := measureReal_mono hsubset hfinite
  linarith

theorem volume_compl_positivitySet_inter_Ioo_eq_zero_of_pos_above_of_isMinimizer
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hposAbove : ∃ x ∈ f.positivitySet, b < x) : volume (f.positivitySetᶜ ∩ Ioo a b) = 0 := by
  have hzero := measureReal_compl_positivitySet_inter_Ioc_eq_zero_of_pos_above_of_isMinimizer
    hL hfmin (le_trans ha (le_of_lt hab)) hposAbove
  have hsub : f.positivitySetᶜ ∩ Ioo a b ⊆ f.positivitySetᶜ ∩ Ioc 0 b := by
    intro x hx; exact ⟨hx.1, ⟨lt_of_le_of_lt ha hx.2.1, le_of_lt hx.2.2⟩⟩
  have hfinite : volume (f.positivitySetᶜ ∩ Ioc 0 b) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_Ioc_lt_top.ne (measure_mono inter_subset_right)
  have hreal : volume.real (f.positivitySetᶜ ∩ Ioo a b) = 0 := by
    have hle := measureReal_mono hsub hfinite
    exact le_antisymm (hle.trans_eq hzero) (measureReal_nonneg)
  rw [measureReal_def] at hreal
  have htop : volume (f.positivitySetᶜ ∩ Ioo a b) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_Ioc_lt_top.ne (measure_mono (show
      f.positivitySetᶜ ∩ Ioo a b ⊆ Ioc 0 b from by
       intro x hx; exact ⟨lt_of_le_of_lt ha hx.2.1, le_of_lt hx.2.2⟩))
  rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with hz | htop'
  · exact hz
  · exact (htop htop').elim

theorem CorrectionBumps.localReactionMeasure_restrict_Icc_eq_zero_of_pos_above
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps)
    {a b p q : ℝ} (ha : 0 < a) (hab : a < b)
    (hap : a < p) (hpq : p ≤ q) (hqb : q < b)
    (hposAbove : ∃ x ∈ f.positivitySet, q < x) :
    (B.localReactionMeasure hfmin a b).restrict (Icc p q) = 0 := by
  have hcutReal :=
    measureReal_compl_positivitySet_inter_Ioc_eq_zero_of_pos_above_of_isMinimizer
      hL hfmin (show 0 ≤ q by linarith [ha, hap, hpq]) hposAbove
  have hcut : volume (f.positivitySetᶜ ∩ Ioc 0 q) = 0 := by
    rw [measureReal_def] at hcutReal
    have hfinite : volume (f.positivitySetᶜ ∩ Ioc 0 q) ≠ ⊤ :=
      ne_top_of_le_ne_top measure_Ioc_lt_top.ne (measure_mono inter_subset_right)
    rcases (ENNReal.toReal_eq_zero_iff _).mp hcutReal with hz | htop
    · exact hz
    · exact (hfinite htop).elim
  have hcontactVolume : volume (f.positivitySetᶜ ∩ Icc p q) = 0 :=
    measure_mono_null
      (by
        intro x hx
        exact ⟨hx.1, ⟨lt_of_lt_of_le (lt_trans ha hap) hx.2.1, hx.2.2⟩⟩)
      hcut
  have hac := B.localReactionMeasure_restrict_absolutelyContinuous
    hfmin ha hab hap hpq hqb
  have hvolumePc : (volume.restrict (Icc p q)) f.positivitySetᶜ = 0 := by
    rw [Measure.restrict_apply f.isOpen_positivitySet.measurableSet.compl]
    exact hcontactVolume
  have hmuPc :
      ((B.localReactionMeasure hfmin a b).restrict (Icc p q)) f.positivitySetᶜ = 0 :=
    hac hvolumePc
  have hnuP : (B.localReactionMeasure hfmin a b) f.positivitySet = 0 := by
    let U : Set (Ioi (0 : ℝ)) := {z | (z : ℝ) ∈ f.positivitySet}
    have hUz : B.reactionMeasure hfmin U = 0 :=
      B.reactionMeasure_positivitySet_eq_zero hfmin
    rw [HalfLineH1.CorrectionBumps.localReactionMeasure,
      Measure.map_apply continuous_subtype_val.measurable
        f.isOpen_positivitySet.measurableSet,
      Measure.restrict_apply
        (f.isOpen_positivitySet.measurableSet.preimage continuous_subtype_val.measurable)]
    exact measure_mono_null inter_subset_left hUz
  have hmuP :
      ((B.localReactionMeasure hfmin a b).restrict (Icc p q)) f.positivitySet = 0 := by
    rw [Measure.restrict_apply f.isOpen_positivitySet.measurableSet]
    exact measure_mono_null inter_subset_left hnuP
  apply Measure.measure_univ_eq_zero.mp
  rw [← union_compl_self f.positivitySet,
    measure_union disjoint_compl_right f.isOpen_positivitySet.measurableSet.compl,
    hmuP, hmuPc, zero_add]

def positivityHullInterior (f : HalfLineH1) : Set ℝ :=
  {x | 0 < x ∧ ∃ y ∈ f.positivitySet, x < y}

theorem isOpen_positivityHullInterior (f : HalfLineH1) :
    IsOpen f.positivityHullInterior := by
  rw [show f.positivityHullInterior =
      Ioi 0 ∩ ⋃ y ∈ f.positivitySet, Iio y by
    ext x
    change (0 < x ∧ ∃ y ∈ f.positivitySet, x < y) ↔ _
    simp only [mem_inter_iff, mem_Ioi, mem_iUnion, mem_Iio]
    constructor
    · rintro ⟨hx0, y, hyP, hxy⟩
      exact ⟨hx0, y, hyP, hxy⟩
    · rintro ⟨hx0, y, hyP, hxy⟩
      exact ⟨hx0, y, hyP, hxy⟩]
  exact isOpen_Ioi.inter (isOpen_iUnion fun y => isOpen_iUnion fun _ => isOpen_Iio)

theorem positivitySet_subset_positivityHullInterior (f : HalfLineH1) :
    f.positivitySet ⊆ f.positivityHullInterior := by
  intro x hx
  have hxpos : 0 < x := lt_of_not_ge fun hx0 =>
    hx.ne' (f.continuousRep_eq_zero_of_nonpositive hx0)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp f.isOpen_positivitySet x hx
  let z : ℝ := x + ε / 2
  have hzdist : dist z x < ε := by
    change dist (x + ε / 2) x < ε
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  have hz : z ∈ f.positivitySet := hball hzdist
  change 0 < x ∧ ∃ y ∈ f.positivitySet, x < y
  refine ⟨hxpos, z, hz, ?_⟩
  change x < x + ε / 2
  linarith

theorem CorrectionBumps.reactionMeasure_positivityHullInterior_eq_zero
    {L : ℝ} (hL : 0 < L) {f : HalfLineH1} (hfmin : f.IsMinimizer L)
    (B : f.CorrectionBumps) :
    B.reactionMeasure hfmin
      {x : Ioi (0 : ℝ) | (x : ℝ) ∈ f.positivityHullInterior} = 0 := by
  let U : Set (Ioi (0 : ℝ)) :=
    {x | (x : ℝ) ∈ f.positivityHullInterior}
  have hU : IsOpen U :=
    (isOpen_positivityHullInterior f).preimage continuous_subtype_val
  let _ : (B.reactionMeasure hfmin).Regular := B.reactionMeasure_regular hfmin
  rw [show {x : Ioi (0 : ℝ) | (x : ℝ) ∈ f.positivityHullInterior} = U by rfl,
    hU.measure_eq_iSup_isCompact]
  apply le_antisymm
  · refine iSup_le fun K => iSup_le fun hKU => iSup_le fun hKcompact => ?_
    by_cases hKne : K.Nonempty
    · obtain ⟨xmin, hxmin, hmin⟩ :=
        hKcompact.exists_isMinOn hKne continuous_subtype_val.continuousOn
      obtain ⟨xmax, hxmax, hmax⟩ :=
        hKcompact.exists_isMaxOn hKne continuous_subtype_val.continuousOn
      let p : ℝ := xmin
      let q : ℝ := xmax
      have hp : 0 < p := by exact xmin.property
      have hpq : p ≤ q := by exact hmin hxmax
      obtain ⟨z, hz, hqz⟩ := (hKU hxmax).2
      let a : ℝ := p / 2
      let b : ℝ := (q + z) / 2
      have ha : 0 < a := by dsimp [a]; linarith
      have hap : a < p := by dsimp [a]; linarith
      have hqb : q < b := by dsimp [b]; linarith
      have hab : a < b := by dsimp [a, b]; linarith
      have hlocal := B.localReactionMeasure_restrict_Icc_eq_zero_of_pos_above
        hL hfmin ha hab hap hpq hqb ⟨z, hz, hqz⟩
      let Kreal : Set ℝ := (Subtype.val : Ioi (0 : ℝ) → ℝ) '' K
      have hKreal : IsCompact Kreal := hKcompact.image continuous_subtype_val
      have hKrealIcc : Kreal ⊆ Icc p q := by
        rintro y ⟨x, hx, rfl⟩
        exact ⟨hmin hx, hmax hx⟩
      have hIcczero : (B.localReactionMeasure hfmin a b) (Icc p q) = 0 := by
        have hzero := congrArg (fun m : Measure ℝ => m Set.univ) hlocal
        rw [Measure.restrict_apply MeasurableSet.univ] at hzero
        simpa using hzero
      have hKrealzero : (B.localReactionMeasure hfmin a b) Kreal = 0 :=
        measure_mono_null hKrealIcc hIcczero
      have hprezero :
          (B.reactionMeasure hfmin)
            ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Kreal ∩ localReactionSet a b) = 0 := by
        rw [HalfLineH1.CorrectionBumps.localReactionMeasure,
          Measure.map_apply continuous_subtype_val.measurable hKreal.measurableSet,
          Measure.restrict_apply
            (hKreal.measurableSet.preimage continuous_subtype_val.measurable)] at hKrealzero
        exact hKrealzero
      have hKzero : (B.reactionMeasure hfmin) K = 0 := by
        apply measure_mono_null ?_ hprezero
        intro x hx
        refine ⟨?_, ?_⟩
        · exact ⟨x, hx, rfl⟩
        · show a ≤ (x : ℝ) ∧ (x : ℝ) ≤ b
          exact ⟨le_trans hap.le (hmin hx), le_trans (hmax hx) hqb.le⟩
      exact le_of_eq hKzero
    · simp [not_nonempty_iff_eq_empty.mp hKne]
  · exact bot_le

end RayleighKernel.Analysis.HalfLineH1
