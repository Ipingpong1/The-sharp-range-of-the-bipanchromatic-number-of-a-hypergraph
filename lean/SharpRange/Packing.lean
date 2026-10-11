import SharpRange.Definitions

namespace Bipanchromatic
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty collection of disjoint transversals of size at least r can be
completed to a coloring, keeping its number of classes and minimum class size. -/
theorem complete_packing (H : Hypergraph V) (P : Finset (Finset V)) (r : ℕ)
    (hP : P.Nonempty) (hne : ∀ C ∈ P, C.Nonempty)
    (hd : (↑P : Set (Finset V)).PairwiseDisjoint id)
    (ht : ∀ C ∈ P, Transversal H C) (hr : ∀ C ∈ P, r ≤ C.card) :
    ∃ Q : Finset (Finset V), Panchromatic H Q ∧ Q.card = P.card ∧
      (∀ C ∈ Q, r ≤ C.card) := by
  classical
  obtain ⟨C₀, hC₀⟩ := hP
  let W : Finset V := (P.biUnion id)ᶜ
  let D := C₀ ∪ W
  have hCsub : C₀ ⊆ D := subset_union_left
  have hDne : D.Nonempty := (hne C₀ hC₀).mono hCsub
  have hDC : ∀ C ∈ P, C ≠ C₀ → Disjoint D C := by
    intro C hC hCC₀
    apply disjoint_left.mpr
    intro v hvD hvC
    rcases mem_union.mp hvD with hv₀ | hvW
    · exact (disjoint_left.mp (hd hC₀ hC (Ne.symm hCC₀))) hv₀ hvC
    · have hvU : v ∈ P.biUnion id := mem_biUnion.mpr ⟨C, hC, hvC⟩
      exact (mem_compl.mp hvW) hvU
  have hDnot : D ∉ P.erase C₀ := by
    intro h
    have hh := hDC D (mem_erase.mp h).2 (mem_erase.mp h).1
    obtain ⟨v, hv⟩ := hDne
    exact (disjoint_left.mp hh) hv hv
  let Q := insert D (P.erase C₀)
  have hQne : ∀ C ∈ Q, C.Nonempty := by
    intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact hDne
    · exact hne C (mem_erase.mp hC).2
  have hQdis : (↑Q : Set (Finset V)).PairwiseDisjoint id := by
    intro C hC B hB hCB
    rcases mem_insert.mp hC with rfl | hC
    · rcases mem_insert.mp hB with rfl | hB
      · exact False.elim (hCB rfl)
      · exact hDC B (mem_erase.mp hB).2 (mem_erase.mp hB).1
    · rcases mem_insert.mp hB with rfl | hB
      · exact (hDC C (mem_erase.mp hC).2 (mem_erase.mp hC).1).symm
      · exact hd (mem_erase.mp hC).2 (mem_erase.mp hB).2 hCB
  have hQcover : Q.biUnion id = univ := by
    apply Finset.ext
    intro v
    simp only [mem_univ, iff_true]
    by_cases hv : v ∈ P.biUnion id
    · obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp hv
      by_cases heq : C = C₀
      · subst C
        exact mem_biUnion.mpr ⟨D, mem_insert_self _ _, hCsub hvC⟩
      · exact mem_biUnion.mpr ⟨C, mem_insert_of_mem (mem_erase.mpr ⟨heq, hC⟩), hvC⟩
    · exact mem_biUnion.mpr ⟨D, mem_insert_self _ _, mem_union_right _ (mem_compl.mpr hv)⟩
  have hQt : ∀ C ∈ Q, Transversal H C := by
    intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · intro e he
      obtain ⟨v, hv⟩ := ht C₀ hC₀ e he
      exact ⟨v, mem_inter.mpr ⟨hCsub (mem_inter.mp hv).1, (mem_inter.mp hv).2⟩⟩
    · exact ht C (mem_erase.mp hC).2
  refine ⟨Q, ⟨⟨hQne, hQdis, hQcover⟩, hQt⟩, ?_, ?_⟩
  · dsimp only [Q]
    rw [card_insert_of_notMem hDnot, card_erase_of_mem hC₀]
    have := card_pos.mpr ⟨C₀, hC₀⟩
    omega
  · intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact (hr C₀ hC₀).trans (card_le_card hCsub)
    · exact hr C (mem_erase.mp hC).2

end Bipanchromatic
