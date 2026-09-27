import RayleighKernel.Compression.Map

noncomputable section

namespace RayleighKernel

open Set MeasureTheory

def translatedComponent (f : Analysis.HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ) : Set ℝ :=
  f.compressionMap '' D.component n

@[simp] theorem mem_translatedComponent_iff (f : Analysis.HalfLineH1)
    (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ) (z : ℝ) :
    z ∈ translatedComponent f D n ↔
      ∃ x ∈ D.component n, f.compressionMap x = z := Iff.rfl

theorem image_ordConnected_of_continuousOn
    {F : ℝ → ℝ} {C : Set ℝ}
    (hC : OrdConnected C) (hcont : ContinuousOn F C) :
    OrdConnected (F '' C) :=
  (hC.isPreconnected.image F hcont).ordConnected

theorem compressionMap_image_component_ordConnected
    (f : Analysis.HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ) :
    OrdConnected (translatedComponent f D n) := by
  apply image_ordConnected_of_continuousOn (D.ordConnected_component n)
  intro x hx
  have hxI : x ∈ uIcc (x - 1) (x + 1) := by simp [uIcc]
  have hcont := f.compressionMap_continuousOn (x - 1) (x + 1)
  have hnh : uIcc (x - 1) (x + 1) ∈ nhds x := by
    rw [uIcc]
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    exact Icc_mem_nhds (by norm_num) (by norm_num)
  exact hcont.continuousAt hnh |>.continuousWithinAt

theorem compressionMap_image_component_isOpen
    (f : Analysis.HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ) :
    IsOpen (translatedComponent f D n) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨x, hx, rfl⟩
  obtain ⟨u, huSub, huOpen, hxu⟩ := mem_nhds_iff.1 ((D.isOpen_component n).mem_nhds hx)
  obtain ⟨δ, hδ, hδC⟩ := Metric.isOpen_iff.1 huOpen x hxu
  refine Metric.mem_nhds_iff.2 ⟨δ, hδ, ?_⟩
  intro y hy
  have hy' : y ∈ Ioo (f.compressionMap x - δ) (f.compressionMap x + δ) := by
    rw [Metric.mem_ball, Real.dist_eq] at hy
    constructor <;> rw [abs_lt] at hy <;> linarith
  let w : ℝ := x + (y - f.compressionMap x)
  have hw : w ∈ u := hδC (Metric.mem_ball.2 (by
    rw [Real.dist_eq]
    simp only [abs_lt]
    constructor <;> linarith [hy'.1, hy'.2]))
  have hw' : w ∈ D.component n := huSub hw
  refine ⟨w, hw', ?_⟩
  have htrans := f.compressionMap_sub_eq_sub_of_component D n hw' hx
  dsimp [w] at htrans
  linarith

theorem translatedComponent_isOpen_ordConnected
    (f : Analysis.HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ) :
    IsOpen (translatedComponent f D n) ∧
      OrdConnected (translatedComponent f D n) :=
  ⟨compressionMap_image_component_isOpen f D n,
    compressionMap_image_component_ordConnected f D n⟩

theorem compressionMap_strictMono_on_component
    (f : Analysis.HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) (n : ℕ)
    {x y : ℝ} (hx : x ∈ D.component n) (hxy : x < y)
    :
    f.compressionMap x < f.compressionMap y := by
  obtain ⟨u, huSub, huOpen, hxu⟩ := mem_nhds_iff.1 ((D.isOpen_component n).mem_nhds hx)
  obtain ⟨δ, hδ, hδC⟩ := Metric.isOpen_iff.1 huOpen x hxu
  let z : ℝ := x + min (δ / 2) ((y - x) / 2)
  have hzpos : 0 < min (δ / 2) ((y - x) / 2) := by positivity
  have hzy : z ≤ y := by
    dsimp [z]
    linarith [min_le_right (δ / 2) ((y - x) / 2)]
  have hzball : z ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [z]
    rw [show x + min (δ / 2) ((y - x) / 2) - x = min (δ / 2) ((y - x) / 2) by ring]
    rw [abs_of_nonneg (le_of_lt hzpos)]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hz : z ∈ D.component n := huSub (hδC hzball)
  have hstrict : f.compressionMap x < f.compressionMap z := by
    rw [← sub_pos, f.compressionMap_sub_eq_sub_of_component D n hx hz]
    linarith
  have hmono := f.compressionMap_monotone hzy
  linarith

theorem translatedComponent_pairwiseDisjoint
    (f : Analysis.HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) :
    ∀ ⦃m n : ℕ⦄, m ≠ n → Disjoint (translatedComponent f D m) (translatedComponent f D n) := by
  intro m n hmn
  rw [disjoint_left]
  rintro z ⟨x, hx, hzx⟩ ⟨y, hy, hzy⟩
  rcases le_total x y with hxy | hyx
  · by_cases hxy' : x = y
    · subst y
      exact (Set.disjoint_left.mp (D.pairwiseDisjoint hmn) hx hy).elim
    · have hxy'' : x < y := lt_of_le_of_ne hxy hxy'
      have hstrict := compressionMap_strictMono_on_component f D m hx hxy''
      linarith
  · by_cases hyx' : y = x
    · subst x
      exact (Set.disjoint_left.mp (D.pairwiseDisjoint hmn) hx hy).elim
    · have hyx'' : y < x := lt_of_le_of_ne hyx hyx'
      have hstrict := compressionMap_strictMono_on_component f D n hy hyx''
      linarith

theorem translatedComponent_iUnion
    (f : Analysis.HalfLineH1) (D : OpenIntervalDecomposition f.positivitySet) :
    (⋃ n, translatedComponent f D n) = f.compressionMap '' f.positivitySet := by
  change (⋃ n, f.compressionMap '' D.component n) = _
  rw [← image_iUnion, D.union_eq]

end RayleighKernel
