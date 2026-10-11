import SharpRange.Packing

namespace Bipanchromatic
open Finset
variable {V : Type*} [DecidableEq V]

structure PairPacking (C W : Finset V) (P : Finset (Finset V)) : Prop where
  disjoint : (↑P : Set (Finset V)).PairwiseDisjoint id
  size : ∀ B ∈ P, B.card = 2
  core : ∀ B ∈ P, (B ∩ C).Nonempty
  support : ∀ B ∈ P, B ⊆ C ∪ W

lemma pairPacking_empty (C W : Finset V) : PairPacking C W ∅ := by
  constructor <;> simp

lemma PairPacking.mono {C W C' W' : Finset V} {P : Finset (Finset V)}
    (h : PairPacking C W P) (hC : C ⊆ C') (hW : W ⊆ W') : PairPacking C' W' P := by
  refine ⟨h.disjoint, h.size, ?_, ?_⟩
  · intro B hB
    obtain ⟨v, hv⟩ := h.core B hB
    exact ⟨v, mem_inter.mpr ⟨(mem_inter.mp hv).1, hC (mem_inter.mp hv).2⟩⟩
  · intro B hB
    exact (h.support B hB).trans (union_subset_union hC hW)

lemma PairPacking.insert {C W : Finset V} {P : Finset (Finset V)} (h : PairPacking C W P)
    (R : Finset V) (hR : R.card = 2) (hRC : (R ∩ C).Nonempty) (hRS : R ⊆ C ∪ W)
    (hdis : ∀ B ∈ P, Disjoint R B) :
    PairPacking C W (insert R P) ∧ (insert R P).card = P.card + 1 := by
  have hn : R ∉ P := by
    intro hh
    have hd := hdis R hh
    have hne : R.Nonempty := card_pos.mp (by omega)
    obtain ⟨v, hv⟩ := hne
    exact (disjoint_left.mp hd) hv hv
  constructor
  · constructor
    · intro A hA B hB hAB
      rcases mem_insert.mp hA with hAR | hAP
      · subst A
        rcases mem_insert.mp hB with hBR | hBP
        · exact False.elim (hAB hBR.symm)
        · exact hdis B hBP
      · rcases mem_insert.mp hB with hBR | hBP
        · subst B
          exact (hdis A hAP).symm
        · exact h.disjoint hAP hBP hAB
    · intro B hB
      rcases mem_insert.mp hB with rfl | hB
      · exact hR
      · exact h.size B hB
    · intro B hB
      rcases mem_insert.mp hB with rfl | hB
      · exact hRC
      · exact h.core B hB
    · intro B hB
      rcases mem_insert.mp hB with rfl | hB
      · exact hRS
      · exact h.support B hB
  · exact card_insert_of_notMem hn

/-- Pair core vertices with available partners, then pair remaining core vertices.
The packing is constructed, not merely postulated from a counting inequality. -/
theorem exists_pairPacking (C W : Finset V) (hCW : Disjoint C W) :
    ∃ P, PairPacking C W P ∧ P.card = min C.card ((C.card + W.card) / 2) := by
  generalize hcard : C.card = m
  induction m using Nat.strong_induction_on generalizing C W with
  | h m ih =>
    by_cases hC : C.Nonempty
    · obtain ⟨c, hc⟩ := hC
      have hcW : c ∉ W := fun h => (disjoint_left.mp hCW) hc h
      by_cases hW : W.Nonempty
      · obtain ⟨w, hw⟩ := hW
        have hwC : w ∉ C := fun h => (disjoint_left.mp hCW) h hw
        have hcw : c ≠ w := fun h => hwC (h ▸ hc)
        have hsmall : (C.erase c).card < m := by
          rw [card_erase_of_mem hc]
          have := card_pos.mpr ⟨c, hc⟩
          omega
        obtain ⟨P, hP, hPc⟩ := ih _ hsmall (C.erase c) (W.erase w)
          (hCW.mono (erase_subset c C) (erase_subset w W)) rfl
        have hRdis : Disjoint ({c,w} : Finset V) (C.erase c ∪ W.erase w) := by
          simp [hcW, hwC, hcw]
        have hbig := hP.mono (erase_subset c C) (erase_subset w W)
        have hins := hbig.insert {c,w} (by simp [hcw])
          ⟨c, by simp [hc]⟩ (by intro v hv; simp only [mem_insert, mem_singleton] at hv
                                rcases hv with rfl | rfl
                                · exact mem_union_left _ hc
                                · exact mem_union_right _ hw)
          (fun B hB => hRdis.mono_right (hP.support B hB))
        refine ⟨insert {c,w} P, hins.1, ?_⟩
        rw [hins.2, hPc, card_erase_of_mem hc, card_erase_of_mem hw]
        have hcpos := card_pos.mpr ⟨c, hc⟩
        have hwpos := card_pos.mpr ⟨w, hw⟩
        omega
      · have hWe : W = ∅ := not_nonempty_iff_eq_empty.mp hW
        subst W
        by_cases hrest : (C.erase c).Nonempty
        · obtain ⟨w, hw⟩ := hrest
          have hwC := (mem_erase.mp hw).2
          have hwc := (mem_erase.mp hw).1
          have hcw : c ≠ w := Ne.symm hwc
          have hsmall : ((C.erase c).erase w).card < m := by
            rw [card_erase_of_mem hw, card_erase_of_mem hc]
            have := card_pos.mpr ⟨c, hc⟩
            omega
          obtain ⟨P, hP, hPc⟩ := ih _ hsmall ((C.erase c).erase w) ∅ (by simp) rfl
          have hsub : (C.erase c).erase w ⊆ C := (erase_subset w _).trans (erase_subset c C)
          have hRdis : Disjoint ({c,w} : Finset V) ((C.erase c).erase w ∪ ∅) := by
            simp [hcw]
          have hins := (hP.mono hsub (by rfl)).insert {c,w} (by simp [hcw])
            ⟨c, by simp [hc]⟩ (by simp only [union_empty, insert_subset_iff, singleton_subset_iff]; exact ⟨hc, hwC⟩)
            (fun B hB => hRdis.mono_right (hP.support B hB))
          refine ⟨insert {c,w} P, hins.1, ?_⟩
          rw [hins.2, hPc, card_erase_of_mem hw, card_erase_of_mem hc]
          have htw : 2 ≤ C.card := by
            have := card_pos.mpr ⟨w, hw⟩
            rw [card_erase_of_mem hc] at this
            omega
          simp only [card_empty, add_zero]
          omega
        · have he : C.erase c = ∅ := not_nonempty_iff_eq_empty.mp hrest
          have hc1 : C.card = 1 := by
            have hz := congrArg Finset.card he
            rw [card_erase_of_mem hc, card_empty] at hz
            have := card_pos.mpr ⟨c, hc⟩
            omega
          exact ⟨∅, pairPacking_empty _ _, by simp only [card_empty, add_zero]; omega⟩
    · have he : C = ∅ := not_nonempty_iff_eq_empty.mp hC
      subst C
      exact ⟨∅, pairPacking_empty _ _, by simp only [card_empty] at hcard ⊢; omega⟩

end Bipanchromatic
