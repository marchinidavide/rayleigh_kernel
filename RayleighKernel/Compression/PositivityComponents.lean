import RayleighKernel.Obstacle.Variations
import Mathlib.Topology.Order.T5
import Mathlib.Topology.Bases

noncomputable section

namespace RayleighKernel

open Set
open scoped Topology

/-- A countable decomposition of an open subset of the real line into its open order
connected components.  Empty members are allowed in the enumeration, which makes the
indexing uniform also for the empty set. -/
structure OpenIntervalDecomposition (s : Set ℝ) where
  component : ℕ → Set ℝ
  isOpen_component : ∀ n, IsOpen (component n)
  ordConnected_component : ∀ n, OrdConnected (component n)
  subset : ∀ n, component n ⊆ s
  pairwiseDisjoint_component : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (component i) (component j)
  coverage : s ⊆ ⋃ n, component n
  maximal : ∀ n {x}, x ∈ component n → component n = ordConnectedComponent s x

namespace OpenIntervalDecomposition

variable {s : Set ℝ}

theorem component_is_interval (D : OpenIntervalDecomposition s) (n : ℕ) :
    IsOpen (D.component n) ∧ OrdConnected (D.component n) :=
  ⟨D.isOpen_component n, D.ordConnected_component n⟩

theorem component_subset (D : OpenIntervalDecomposition s) (n : ℕ) :
    D.component n ⊆ s := D.subset n

theorem pairwiseDisjoint (D : OpenIntervalDecomposition s) :
    ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (D.component i) (D.component j) :=
  D.pairwiseDisjoint_component

theorem coverage_subset (D : OpenIntervalDecomposition s) :
    s ⊆ ⋃ n, D.component n := D.coverage

theorem union_eq (D : OpenIntervalDecomposition s) :
    (⋃ n, D.component n) = s := by
  apply Set.Subset.antisymm
  · exact iUnion_subset fun n => D.component_subset n
  · exact D.coverage

theorem component_eq_ordConnectedComponent (D : OpenIntervalDecomposition s) (n : ℕ)
    {x : ℝ} (hx : x ∈ D.component n) :
    D.component n = ordConnectedComponent s x := D.maximal n hx

end OpenIntervalDecomposition

private lemma ordConnectedComponent_isOpen {s : Set ℝ} (hs : IsOpen s) (x : ℝ) :
    IsOpen (ordConnectedComponent s x) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rw [← ordConnectedComponent_eq (mem_ordConnectedComponent_comm.mp hy)]
  exact ordConnectedComponent_mem_nhds.2 (hs.mem_nhds (ordConnectedComponent_subset hy))

private lemma section_components_pairwiseDisjoint {s : Set ℝ} :
    ∀ ⦃x y : ℝ⦄, x ∈ ordConnectedSection s → y ∈ ordConnectedSection s →
      x ≠ y → Disjoint (ordConnectedComponent s x) (ordConnectedComponent s y) := by
  rintro x y hx hy hxy
  rw [disjoint_left]
  intro z hzx hzy
  apply hxy
  apply eq_of_mem_ordConnectedSection_of_uIcc_subset (s := s) hx hy
  exact uIcc_subset_uIcc_union_uIcc.trans (union_subset
    (mem_ordConnectedComponent.mp hzx)
    (by simpa [uIcc_comm] using (mem_ordConnectedComponent.mp hzy)))

private lemma section_components_nonempty {s : Set ℝ} {x : ℝ}
    (hx : x ∈ ordConnectedSection s) :
    (ordConnectedComponent s x).Nonempty := by
  exact ⟨x, self_mem_ordConnectedComponent.2 (ordConnectedSection_subset hx)⟩

private lemma section_countable {s : Set ℝ} (hs : IsOpen s) :
    (ordConnectedSection s).Countable := by
  let c : ordConnectedSection s → Set ℝ := fun x => ordConnectedComponent s x
  have hd : Pairwise (fun x y => Disjoint (c x) (c y)) := by
    intro x y hxy
    apply section_components_pairwiseDisjoint x.2 y.2
    exact fun h => hxy (Subtype.ext h)
  have ho : ∀ x, IsOpen (c x) := fun x => ordConnectedComponent_isOpen hs x
  have hn : ∀ x, (c x).Nonempty := fun x => section_components_nonempty x.2
  exact hd.countable_of_isOpen_disjoint ho hn

private lemma section_components_coverage {s : Set ℝ} (_hs : IsOpen s) :
    s ⊆ ⋃ x : ordConnectedSection s, ordConnectedComponent s x := by
  intro y hy
  let r : ℝ := ordConnectedProj s ⟨y, hy⟩
  have hr : r ∈ ordConnectedSection s := ⟨⟨y, hy⟩, rfl⟩
  exact mem_iUnion.2 ⟨⟨r, hr⟩, mem_ordConnectedComponent_ordConnectedProj s ⟨y, hy⟩⟩

/-- Every open subset of `ℝ` admits a countable disjoint decomposition into open
order-connected components.  The components are indexed by `ℕ`; empty entries are
used only when the set has fewer than countably many components. -/
theorem exists_openIntervalDecomposition {s : Set ℝ} (hs : IsOpen s) :
    Nonempty (OpenIntervalDecomposition s) := by
  classical
  by_cases hne : (ordConnectedSection s).Nonempty
  · obtain ⟨q, hq⟩ := (Set.countable_iff_exists_injective).mp (section_countable hs)
    let c : ℕ → Set ℝ := fun n =>
      if h : ∃ x : ordConnectedSection s, q x = n then
        ordConnectedComponent s (Classical.choose h : ordConnectedSection s)
      else ∅
    have hopen : ∀ n, IsOpen (c n) := by
      intro n
      dsimp [c]
      split <;> simp_all [ordConnectedComponent_isOpen hs]
    have hconn : ∀ n, OrdConnected (c n) := by
      intro n
      dsimp [c]
      split <;> infer_instance
    have hsub : ∀ n, c n ⊆ s := by
      intro n
      dsimp [c]
      split
      · exact ordConnectedComponent_subset
      · exact empty_subset _
    have hdisj : ∀ ⦃m n : ℕ⦄, m ≠ n → Disjoint (c m) (c n) := by
      intro m n hmn
      by_cases hm : ∃ x : ordConnectedSection s, q x = m
      · by_cases hn : ∃ x : ordConnectedSection s, q x = n
        · let xm : ordConnectedSection s := Classical.choose hm
          let xn : ordConnectedSection s := Classical.choose hn
          have hxm : q xm = m := Classical.choose_spec hm
          have hxn : q xn = n := Classical.choose_spec hn
          change Disjoint (if h : ∃ x : ordConnectedSection s, q x = m then
              ordConnectedComponent s (Classical.choose h : ordConnectedSection s) else ∅)
            (if h : ∃ x : ordConnectedSection s, q x = n then
              ordConnectedComponent s (Classical.choose h : ordConnectedSection s) else ∅)
          rw [dite_eq_left hm, dite_eq_left hn]
          apply section_components_pairwiseDisjoint xm.2 xn.2
          intro heq
          apply hmn
          calc
            m = q xm := hxm.symm
            _ = q xn := by rw [Subtype.ext heq]
            _ = n := hxn
        · dsimp [c]
          split <;> simp_all
      · dsimp [c]
        split <;> simp_all
    have hmax : ∀ n {x}, x ∈ c n → c n = ordConnectedComponent s x := by
      intro n x hx
      by_cases h : ∃ y : ordConnectedSection s, q y = n
      · change x ∈ (if h' : ∃ y : ordConnectedSection s, q y = n then
          ordConnectedComponent s (Classical.choose h' : ordConnectedSection s) else ∅) at hx
        rw [dite_eq_left h] at hx
        change (if h' : ∃ y : ordConnectedSection s, q y = n then
          ordConnectedComponent s (Classical.choose h' : ordConnectedSection s) else ∅) = _
        rw [dite_eq_left h]
        exact ordConnectedComponent_eq (mem_ordConnectedComponent.mp hx)
      · simp only [c, dite_eq_right h] at hx ⊢
        simp at hx
    refine ⟨⟨c, hopen, hconn, hsub, hdisj, ?_, hmax⟩⟩
    intro y hy
    have hcov := section_components_coverage hs hy
    rw [mem_iUnion] at hcov
    rcases hcov with ⟨x, hx⟩
    refine mem_iUnion.2 ⟨q x, ?_⟩
    have hqx : ∃ z : ordConnectedSection s, q z = q x := ⟨x, rfl⟩
    dsimp [c]
    split
    · rename_i h
      rw [show (Classical.choose h : ordConnectedSection s) = x by
        apply hq
        exact Classical.choose_spec h]
      exact hx
    · contradiction
  · have hs' : s = ∅ := by
      rw [← not_nonempty_iff_eq_empty]
      intro hsnon
      apply hne
      obtain ⟨y, hy⟩ := hsnon
      exact ⟨ordConnectedProj s ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩
    let c : ℕ → Set ℝ := fun _ => ∅
    refine ⟨⟨c, fun _ => isOpen_empty, fun _ => inferInstance, fun n => ?_,
       fun _ _ _ => by simp [c], ?_, ?_⟩⟩
    · rw [hs']
    · rw [hs']
      exact empty_subset _
    · intro n x hx
      simp [c] at hx

end RayleighKernel

namespace RayleighKernel.Analysis

open Set

/-- The positivity set of a half-line profile has the same countable
open interval decomposition, and every component lies in the open half-line. -/
theorem HalfLineH1.exists_positivityIntervalDecomposition {f : HalfLineH1} :
    ∃ D : OpenIntervalDecomposition f.positivitySet,
      ∀ n, D.component n ⊆ Ioi 0 := by
  obtain ⟨D⟩ := exists_openIntervalDecomposition f.isOpen_positivitySet
  refine ⟨D, fun n x hx ↦ ?_⟩
  exact (show f.positivitySet ⊆ Ioi 0 from by
    intro x hx
    exact lt_of_not_ge fun hx0 ↦ hx.ne' (f.continuousRep_eq_zero_of_nonpositive hx0))
    (D.subset n hx)

end RayleighKernel.Analysis
