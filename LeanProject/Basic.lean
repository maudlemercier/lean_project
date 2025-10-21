import Mathlib

lemma not_clusterPt_iff_exists_mem_nhds {X : Type*} [TopologicalSpace X] {x : X} {s : Set X} :
  ¬ClusterPt x (Filter.principal s) ↔ ∃ U ∈ nhds x, IsOpen U ∧ (U ∩ s) = ∅ := by
  rw [clusterPt_principal_iff]
  push_neg
  constructor
  · rintro ⟨U, hU_nhds, hU_disjoint⟩
    rcases mem_nhds_iff.1 hU_nhds with ⟨V, hV_sub, hV_open, hV_mem⟩
    use V
    exact ⟨hV_open.mem_nhds hV_mem, hV_open, Set.subset_eq_empty
          (Set.inter_subset_inter hV_sub fun _ a ↦ a) hU_disjoint⟩
  · rintro ⟨U, hU_nhds, _, hU_disjoint⟩
    exact ⟨U, hU_nhds, hU_disjoint⟩


theorem rudin {X : Type*} [TopologicalSpace X] (E : Set X) :
    IsOpen E ↔ IsClosed Eᶜ := by
  constructor
  · intro hop
    apply isClosed_iff_clusterPt.2
    intro x hx
    have hx' : x ∉ interior E := by
      intro hi
      rcases mem_interior.1 hi with ⟨U, hU, hop, hm⟩
      rw [clusterPt_principal_iff] at hx
      specialize hx U (IsOpen.mem_nhds hop hm )
      obtain ⟨y, hy⟩ := hx
      exact (absurd (hU (Set.mem_of_mem_diff hy)) (Set.mem_of_mem_inter_right hy))
    have hintc := Set.compl_subset_compl_of_subset (subset_interior_iff_isOpen.2 hop)
    exact hintc hx'
  · intro hc
    apply subset_interior_iff_isOpen.1
    intro x hx
    have hx' : x ∉ Eᶜ := Set.notMem_compl_iff.mpr hx
    have hnc : ¬ClusterPt x (Filter.principal Eᶜ) := by
      intro h
      exact hx' (isClosed_iff_clusterPt.1 hc x h)
    rcases not_clusterPt_iff_exists_mem_nhds.1 hnc with ⟨N, hN, hop, he⟩
    apply mem_interior.2
    use N, Set.diff_eq_empty.mp he, hop
    exact mem_of_mem_nhds hN
