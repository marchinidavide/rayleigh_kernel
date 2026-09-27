import RayleighKernel.Discrete.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
namespace RayleighKernel.Discrete

open Set Filter Topology

/-- The full-domain piecewise-linear interpolant of a kernel at mesh size `h`. -/
def interpolant (h : ℝ) (w : Kernel) (x : ℝ) : ℝ :=
  if x ≤ -h then 0
  else if x ≤ 0 then (x + h) * (w 0 / h ^ 2)
  else
    let j : ℕ := ⌊x / h⌋₊
    w j / h + (x - (j : ℝ) * h) * (w (j + 1) - w j) / h ^ 2

/-- The interpolant vanishes on the left of the initial node. -/
@[simp] theorem interpolant_of_le_neg (h : ℝ) (w : Kernel) {x : ℝ} (hx : x ≤ -h) :
    interpolant h w x = 0 := by simp [interpolant, hx]

/-- The interpolant is zero at the initial node `-h`. -/
@[simp] theorem interpolant_neg_node (h : ℝ) (w : Kernel) :
    interpolant h w (-h) = 0 := interpolant_of_le_neg h w le_rfl

/-- Formula for the initial affine strip between `-h` and `0`. -/
theorem interpolant_neg_interval {h : ℝ} {w : Kernel} (_hh : 0 < h) {x : ℝ}
    (hx : x ∈ Ioc (-h) 0) : interpolant h w x = (x + h) * (w 0 / h ^ 2) := by
  rcases hx with ⟨hx₁, hx₂⟩
  simp only [interpolant, ite_eq_right (not_le.mpr hx₁), ite_eq_left hx₂]

/-- Exact value of the interpolant at every nonnegative mesh node. -/
theorem interpolant_node {h : ℝ} {w : Kernel} (hh : 0 < h) (j : ℕ) :
    interpolant h w ((j : ℝ) * h) = w j / h := by
  by_cases hj : j = 0
  · subst j
    have hn : ¬ h ≤ 0 := not_le.mpr hh
    simp [interpolant, hn]
    field_simp [ne_of_gt hh]
  have hjx : 0 < (j : ℝ) * h := mul_pos (by exact_mod_cast (Nat.zero_lt_of_ne_zero hj)) hh
  unfold interpolant
  rw [ite_eq_right (by linarith), ite_eq_right (by linarith)]
  have hq : ⌊((j : ℝ) * h) / h⌋₊ = j := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> field_simp <;> norm_num
  rw [hq]
  field_simp
  ring

/-- Exact value of the interpolant at the origin. -/
theorem interpolant_zero {h : ℝ} {w : Kernel} (hh : 0 < h) :
    interpolant h w 0 = w 0 / h := by simpa using interpolant_node hh 0

/-- Formula for the interpolant on a positive mesh cell. -/
theorem interpolant_cell {h : ℝ} {w : Kernel} (hh : 0 < h) (j : ℕ) {x : ℝ}
    (hx : x ∈ Ico ((j : ℝ) * h) ((j + 1 : ℕ) * h)) :
    interpolant h w x =
      w j / h + (x - (j : ℝ) * h) * (w (j + 1) - w j) / h ^ 2 := by
  rcases hx with ⟨hx₁, hx₂⟩
  by_cases hzero : x = 0
  · subst x
    have hj : j = 0 := by
      have : (0 : ℝ) ≤ (j : ℝ) * h := by positivity
      have : (j : ℝ) * h ≤ 0 := hx₁
      have : (j : ℝ) = 0 := by nlinarith
      exact_mod_cast this
    subst j
    simpa [interpolant, ne_of_gt hh] using interpolant_zero hh (w := w)
  have hx0 : 0 < x := lt_of_le_of_ne (le_trans (by positivity) hx₁) (Ne.symm hzero)
  have hf : ⌊x / h⌋₊ = j := by
    apply Nat.floor_eq_on_Ico
    constructor
    · exact (le_div_iff₀ hh).2 (by simpa [mul_comm] using hx₁)
    · exact (div_lt_iff₀ hh).2 (by
        simpa [Nat.cast_add, add_mul] using hx₂)
  unfold interpolant
  rw [ite_eq_right (by linarith), ite_eq_right (by linarith), hf]

/-- A nonnegative kernel has a nonnegative interpolant everywhere. -/
theorem interpolant_nonneg {h : ℝ} {w : Kernel} (hh : 0 < h) (hw : ∀ j, 0 ≤ w j) :
    ∀ x, 0 ≤ interpolant h w x := by
  intro x
  by_cases hx : x ≤ -h
  · rw [interpolant_of_le_neg h w hx]
  by_cases hx0 : x ≤ 0
  · rw [interpolant_neg_interval hh ⟨lt_of_not_ge hx, hx0⟩]
    exact mul_nonneg (by linarith) (div_nonneg (hw 0) (by positivity))
  let j : ℕ := ⌊x / h⌋₊
  have hxpos : 0 < x := lt_of_not_ge hx0
  have hmem : x ∈ Ico ((j : ℝ) * h) ((j + 1 : ℕ) * h) := by
    constructor
    · have hxph : 0 ≤ x / h := by positivity
      exact (le_div_iff₀ hh).mp (Nat.floor_le hxph)
    · have hf := Nat.lt_floor_add_one (x / h)
      norm_num [Nat.cast_add, add_mul] at hf ⊢
      simpa [j, Nat.cast_add, add_mul] using (div_lt_iff₀ hh).mp hf
  rw [interpolant_cell hh j hmem]
  have ht : 0 ≤ x - (j : ℝ) * h := sub_nonneg.mpr hmem.1
  have hth : x - (j : ℝ) * h ≤ h := by
    have := hmem.2
    norm_num [Nat.cast_add, add_mul] at this ⊢
    linarith
  have heq : w j / h + (x - (j : ℝ) * h) *
      (w (j + 1) - w j) / h ^ 2 =
      (((j + 1 : ℕ) * h - x) * w j +
        (x - (j : ℝ) * h) * w (j + 1)) / h ^ 2 := by
    field_simp
    norm_num [Nat.cast_add, add_mul]
    ring
  rw [heq]
  apply div_nonneg
  · apply add_nonneg
    · exact mul_nonneg (by linarith [hmem.2]) (hw j)
    · exact mul_nonneg ht (hw (j + 1))
  · positivity

theorem tendsto_atTop_zero_interpolant {h L : ℝ} {w : Kernel}
    (hw : IsAdmissible h L w) :
    Tendsto (interpolant h w) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hwt : Tendsto w atTop (𝓝 0) := hw.summable.tendsto_atTop_zero
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hwt ((ε / 2) * h)
    (mul_pos (by linarith) hw.h_pos)
  refine ⟨max 1 ((N : ℝ) * h), ?_⟩
  intro x hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hx)
  let j : ℕ := ⌊x / h⌋₊
  have hcell : x ∈ Ico ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) := by
    change x ∈ Ico ((↑⌊x / h⌋₊ : ℝ) * h) (((⌊x / h⌋₊ + 1 : ℕ) : ℝ) * h)
    constructor
    · have hxdiv : 0 ≤ x / h := div_nonneg hxpos.le hw.h_pos.le
      exact (le_div_iff₀ hw.h_pos).mp (Nat.floor_le hxdiv)
    · have hf := Nat.lt_floor_add_one (x / h)
      norm_num [Nat.cast_add, add_mul] at hf ⊢
      simpa [Nat.cast_add, add_mul] using (div_lt_iff₀ hw.h_pos).mp hf
  have hjN : N ≤ j := by
    apply Nat.le_floor
    change (N : ℝ) ≤ x / h
    apply (le_div_iff₀ hw.h_pos).2
    exact le_trans (le_max_right _ _) hx
  have hj1N : N ≤ j + 1 := hjN.trans (Nat.le_succ j)
  have hwj : w j / h < ε / 2 := by
    have hdist := hN j hjN
    have hdist' : w j < (ε / 2) * h := by
      simpa [Real.dist_eq, abs_of_nonneg (hw.nonnegative j)] using hdist
    exact (div_lt_iff₀ hw.h_pos).2 (by linarith)
  have hwj1 : w (j + 1) / h < ε / 2 := by
    have hdist := hN (j + 1) hj1N
    have hdist' : w (j + 1) < (ε / 2) * h := by
      simpa [Real.dist_eq, abs_of_nonneg (hw.nonnegative (j + 1))] using hdist
    exact (div_lt_iff₀ hw.h_pos).2 (by linarith)
  have hleft : 0 ≤ x - (j : ℝ) * h := sub_nonneg.mpr hcell.1
  have hright : x - (j : ℝ) * h ≤ h := by
    norm_num [Nat.cast_add, Nat.cast_one, add_mul] at hcell
    linarith
  have hbase : 0 ≤ w j / h := div_nonneg (hw.nonnegative j) hw.h_pos.le
  have hstep : 0 ≤ (x - (j : ℝ) * h) / h := div_nonneg hleft hw.h_pos.le
  have hstep_le : (x - (j : ℝ) * h) / h ≤ 1 := by
    exact (div_le_iff₀ hw.h_pos).2 (by linarith)
  have hform : interpolant h w x =
      (1 - (x - (j : ℝ) * h) / h) * (w j / h) +
        ((x - (j : ℝ) * h) / h) * (w (j + 1) / h) := by
    rw [interpolant_cell hw.h_pos j hcell]
    field_simp [ne_of_gt hw.h_pos]
    ring
  have hfirst : (1 - (x - (j : ℝ) * h) / h) * (w j / h) ≤
      (1 - (x - (j : ℝ) * h) / h) * (ε / 2) := by
    gcongr
  have hsecond : ((x - (j : ℝ) * h) / h) * (w (j + 1) / h) ≤
      ((x - (j : ℝ) * h) / h) * (ε / 2) := by
    gcongr
  have hsum :
      (1 - (x - (j : ℝ) * h) / h) * (w j / h) +
        ((x - (j : ℝ) * h) / h) * (w (j + 1) / h) < ε := by
    calc
      _ ≤ (1 - (x - (j : ℝ) * h) / h) * (ε / 2) +
          ((x - (j : ℝ) * h) / h) * (ε / 2) := add_le_add hfirst hsecond
      _ = ε / 2 := by ring
      _ < ε := by linarith
  rw [hform]
  rw [Real.dist_eq]
  have hnon : 0 ≤
      (1 - (x - (j : ℝ) * h) / h) * (w j / h) +
        ((x - (j : ℝ) * h) / h) * (w (j + 1) / h) := by
    apply add_nonneg
    · exact mul_nonneg (sub_nonneg.mpr hstep_le) hbase
    · exact mul_nonneg hstep (div_nonneg (hw.nonnegative (j + 1)) hw.h_pos.le)
  simpa [sub_zero, abs_of_nonneg hnon] using hsum

/-- Derivative of the interpolant on the initial open affine strip. -/
theorem hasDerivAt_interpolant_neg {h : ℝ} {w : Kernel} (hh : 0 < h)
    {x : ℝ} (hx : x ∈ Ioo (-h) 0) :
    HasDerivAt (interpolant h w) (w 0 / h ^ 2) x := by
  have hp : HasDerivAt (fun y : ℝ => (y + h) * (w 0 / h^2))
      (w 0 / h^2) x := by
    convert ((hasDerivAt_id x).add_const h).mul_const (w 0 / h^2) using 1 <;>
      simp
  refine hp.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact interpolant_neg_interval hh ⟨hy.1, le_of_lt hy.2⟩

/-- Derivative of the interpolant on a positive open mesh cell. -/
theorem hasDerivAt_interpolant_cell {h : ℝ} {w : Kernel} (hh : 0 < h) (j : ℕ)
    {x : ℝ} (hx : x ∈ Ioo ((j : ℝ) * h) ((j + 1 : ℕ) * h)) :
    HasDerivAt (interpolant h w)
      ((w (j + 1) - w j) / h^2) x := by
  have hp : HasDerivAt
      (fun y : ℝ => w j / h + (y - (j : ℝ) * h) *
        (w (j + 1) - w j) / h^2)
      ((w (j + 1) - w j) / h^2) x := by
    convert (((hasDerivAt_id x).sub_const ((j : ℝ) * h)).mul_const
      ((w (j + 1) - w j) / h^2)).add_const (w j / h) using 1 <;>
      simp; ring_nf
    ext y
    ring
  apply hp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact interpolant_cell hh j ⟨le_of_lt hy.1, hy.2⟩

private theorem cell_cont {h : ℝ} {w : Kernel} (hh : 0 < h) (j : ℕ) {x : ℝ}
    (hx : x ∈ Ioo ((j : ℝ) * h) ((j + 1 : ℕ) * h)) : ContinuousAt (interpolant h w) x := by
  have hc : ContinuousAt (fun y : ℝ => w j / h + (y - (j : ℝ) * h) *
      (w (j + 1) - w j) / h ^ 2) x := by fun_prop
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact interpolant_cell hh j ⟨le_of_lt hy.1, hy.2⟩

private theorem neg_cont {h : ℝ} {w : Kernel} (_hh : 0 < h) {x : ℝ}
    (hx : x < -h) : ContinuousAt (interpolant h w) x := by
  refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact interpolant_of_le_neg h w (le_of_lt hy)

private theorem neg_seam_cont {h : ℝ} {w : Kernel} (hh : 0 < h) :
    ContinuousAt (interpolant h w) (-h) := by
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) (-h)).continuousWithinAt
      |>.congr_of_eventuallyEq ?_ (by simp)
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact interpolant_of_le_neg h w hy
  · let f : ℝ → ℝ := fun y => (y + h) * (w 0 / h ^ 2)
    have hf : ContinuousAt f (-h) := by fun_prop
    have heq : interpolant h w (-h) = f (-h) := by simp [f]
    refine hf.continuousWithinAt.congr_of_eventuallyEq ?_ heq
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show -h < 0 by linarith))] with y hy hyo
    change -h ≤ y at hy
    rcases lt_or_eq_of_le hy with hlt | rfl
    · exact interpolant_neg_interval hh ⟨hlt, le_of_lt hyo⟩
    · simp [f]

private theorem zero_cont {h : ℝ} {w : Kernel} (hh : 0 < h) :
    ContinuousAt (interpolant h w) 0 := by
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · let f : ℝ → ℝ := fun y => (y + h) * (w 0 / h ^ 2)
    have hf : ContinuousAt f 0 := by fun_prop
    have heq : interpolant h w 0 = f 0 := by
      rw [interpolant_zero hh]
      dsimp [f]
      field_simp [ne_of_gt hh]
      ring
    refine hf.continuousWithinAt.congr_of_eventuallyEq ?_ heq
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show -h < 0 by linarith))] with y hy hyo
    change y ≤ 0 at hy
    rcases lt_or_eq_of_le hy with hlt | rfl
    · exact interpolant_neg_interval hh ⟨hyo, le_of_lt hlt⟩
    · rw [interpolant_zero hh]
      dsimp [f]
      field_simp [ne_of_gt hh]
      ring
  · let f : ℝ → ℝ := fun y => w 0 / h + y * (w 1 - w 0) / h ^ 2
    have hf : ContinuousAt f 0 := by fun_prop
    have heq : interpolant h w 0 = f 0 := by
      rw [interpolant_zero hh]
      dsimp [f]
      field_simp [ne_of_gt hh]
      ring
    refine hf.continuousWithinAt.congr_of_eventuallyEq ?_ heq
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hh)] with y hy hyo
    have he := interpolant_cell hh 0 (w := w) ⟨by simpa using hy,
      by simpa [Nat.cast_add, Nat.cast_one, add_mul] using hyo⟩
    simpa [f, Nat.cast_add, Nat.cast_one, add_mul] using he

private theorem node_cont {h : ℝ} {w : Kernel} (hh : 0 < h) (k : ℕ) :
    ContinuousAt (interpolant h w) ((k + 1 : ℕ) * h) := by
  let a : ℝ := ((k + 1 : ℕ) : ℝ) * h
  rw [continuousAt_iff_continuous_left_right]
  constructor
  · let f : ℝ → ℝ := fun y => w k / h + (y - (k : ℝ) * h) *
        (w (k + 1) - w k) / h ^ 2
    have hf : ContinuousAt f a := by fun_prop
    have heq : interpolant h w a = f a := by
      dsimp [a, f]
      rw [interpolant_node hh (k + 1)]
      field_simp [ne_of_gt hh]
      norm_num [Nat.cast_add, Nat.cast_one, add_mul]
    refine hf.continuousWithinAt.congr_of_eventuallyEq ?_ heq
    have hk : (k : ℝ) * h < a := by
      dsimp [a]
      norm_num [Nat.cast_add, Nat.cast_one, add_mul]
      linarith
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hk)] with y hy hyo
    change y ≤ a at hy
    rcases lt_or_eq_of_le hy with hlt | rfl
    · exact interpolant_cell hh k (w := w) ⟨le_of_lt hyo, hlt⟩
    · dsimp [f, a]
      rw [interpolant_node hh (k + 1)]
      field_simp [ne_of_gt hh]
      norm_num [Nat.cast_add, Nat.cast_one, add_mul]
  · let f : ℝ → ℝ := fun y => w (k + 1) / h +
        (y - ((k + 1 : ℕ) : ℝ) * h) * (w (k + 2) - w (k + 1)) / h ^ 2
    have hf : ContinuousAt f a := by fun_prop
    have heq : interpolant h w a = f a := by
      dsimp [a, f]
      rw [interpolant_node hh (k + 1)]
      field_simp [ne_of_gt hh]
      ring_nf
    refine hf.continuousWithinAt.congr_of_eventuallyEq ?_ heq
    have hk : a < ((k + 2 : ℕ) : ℝ) * h := by
      dsimp [a]
      norm_num [Nat.cast_add, Nat.cast_one, add_mul]
      linarith
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hk)] with y hy hyo
    exact interpolant_cell hh (k + 1) (w := w) ⟨hy, hyo⟩

/-- The full-domain piecewise-linear interpolant is globally continuous. -/
theorem continuous_interpolant {h : ℝ} {w : Kernel} (hh : 0 < h) :
    Continuous (interpolant h w) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hleft : x < -h
  · exact neg_cont hh hleft
  by_cases hneg : x = -h
  · simpa [hneg] using neg_seam_cont hh (w := w)
  by_cases hzero : x = 0
  · simpa [hzero] using zero_cont hh (w := w)
  by_cases hxpos : 0 < x
  · let j : ℕ := ⌊x / h⌋₊
    have hfloor : x ∈ Ico ((j : ℝ) * h) ((j + 1 : ℕ) * h) := by
      constructor
      · exact (le_div_iff₀ hh).mp (Nat.floor_le (by positivity))
      · have hf := Nat.lt_floor_add_one (x / h)
        norm_num [Nat.cast_add, add_mul] at hf ⊢
        simpa [j, Nat.cast_add, add_mul] using (div_lt_iff₀ hh).mp hf
    by_cases hnode : x = (j : ℝ) * h
    · have hj : 0 < j := by
        by_contra hz
        have hj0 : j = 0 := Nat.eq_zero_of_not_pos hz
        have : x = 0 := by simpa [hj0] using hnode
        exact (ne_of_gt hxpos) this
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
      have hxeq : x = ((k + 1 : ℕ) : ℝ) * h := by
        rw [hnode, hk]
      rw [hxeq]
      exact node_cont hh k (w := w)
    · exact cell_cont hh j (w := w)
        ⟨lt_of_le_of_ne hfloor.1 (Ne.symm hnode), hfloor.2⟩
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hzero
    have hxlower : -h < x := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hneg)
    let f : ℝ → ℝ := fun y => (y + h) * (w 0 / h ^ 2)
    have hf : ContinuousAt f x := by fun_prop
    refine hf.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hxlower hxneg] with y hy
    exact interpolant_neg_interval hh ⟨hy.1, le_of_lt hy.2⟩

end RayleighKernel.Discrete
