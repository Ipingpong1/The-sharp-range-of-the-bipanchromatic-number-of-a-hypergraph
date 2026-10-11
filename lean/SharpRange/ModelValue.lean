import SharpRange.Construction
import SharpRange.Recoloring

namespace Bipanchromatic
namespace Model
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] in
lemma parts_disjoint (a : ℕ) (d : I → ℕ) : Pairwise (fun i j => Disjoint (part a d i) (part a d j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro v hv hw
  obtain ⟨x, rfl⟩ := (mem_part a d i v).mp hv
  obtain ⟨y, he⟩ := (mem_part a d j _).mp hw
  exact hij (congrArg Sigma.fst (Sum.inr_injective he))

omit [Fintype I] in
lemma core_part_disjoint (a : ℕ) (d : I → ℕ) (i : I) : Disjoint (core a d) (part a d i) := by
  apply disjoint_left.mpr
  intro v hv hw
  obtain ⟨u, rfl⟩ := (mem_core a d v).mp hv
  obtain ⟨x, hx⟩ := (mem_part a d i _).mp hw
  cases hx

theorem bicoloring_attains (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hq : 0 < Fintype.card I)
    (hd : ∀ i, 2 ≤ d i) :
    ∃ P, Bicoloring (hypergraph a d ha hd) P ∧ P.card = sizeValue a d := by
  have hcore : ∀ v ∈ core a d, Transversal (hypergraph a d ha hd) {v} := by
    intro v hv
    obtain ⟨u, rfl⟩ := (mem_core a d v).mp hv
    exact (transversal_iff a d ha hd _).mpr (Or.inl ⟨u, mem_singleton_self _⟩)
  have hAt : ∀ i, Transversal (hypergraph a d ha hd) (part a d i) := by
    intro i
    exact (transversal_iff a d ha hd _).mpr (Or.inr ⟨i, subset_rfl⟩)
  have hAs : ∀ i, 2 ≤ (part a d i).card := by simpa using hd
  have hC : (core a d).Nonempty := card_pos.mp (by simpa using ha)
  simpa only [card_core, card_part] using
    recolor_sizeValue (hypergraph a d ha hd) (core a d) (part a d)
      hC hq hcore (parts_disjoint a d) (core_part_disjoint a d) hAt hAs

/-- Counting every possible bipanchromatic coloring, including recolorings that
do not arise by keeping whole parts. -/
theorem bicoloring_le (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hd : ∀ i, 2 ≤ d i)
    (P : Finset (Finset (Vertex a d))) (hP : Bicoloring (hypergraph a d ha hd) P) :
    P.card ≤ sizeValue a d := by
  classical
  let L := P.filter (fun B => ∃ u : Fin a, Sum.inl u ∈ B)
  let K := P \ L
  have hLP : L ⊆ P := filter_subset _ _
  have hKP : K ⊆ P := sdiff_subset
  have hcore : ∀ B : L, ∃ u : Fin a, Sum.inl u ∈ B.val := by
    intro B
    exact (mem_filter.mp B.property).2
  choose g hg using hcore
  have hginj : Function.Injective g := by
    intro B D he
    by_contra hn
    have hne : B.val ≠ D.val := fun h => hn (Subtype.ext h)
    have hdis := hP.1.1.disjoint (hLP B.property) (hLP D.property) hne
    exact (disjoint_left.mp hdis) (hg B) (by simpa [he] using hg D)
  have hx : L.card ≤ a := by
    have h := Fintype.card_le_of_injective g hginj
    simpa using h
  have hres : ∀ B : K, ∃ i : I, part a d i ⊆ B.val := by
    intro B
    have hT := (transversal_iff a d ha hd B.val).mp (hP.1.2 B.val (hKP B.property))
    rcases hT with hcore | hpart
    · have hnot := (mem_sdiff.mp B.property).2
      exact False.elim (hnot (mem_filter.mpr ⟨hKP B.property, hcore⟩))
    · exact hpart
  choose f hf using hres
  have hfinj : Function.Injective f := by
    intro B D he
    by_contra hn
    have hne : B.val ≠ D.val := fun h => hn (Subtype.ext h)
    have hdis := hP.1.1.disjoint (hKP B.property) (hKP D.property) hne
    have hpartne : (part a d (f B)).Nonempty := card_pos.mp (by rw [card_part]; have := hd (f B); omega)
    obtain ⟨v, hv⟩ := hpartne
    exact (disjoint_left.mp hdis) (hf B hv) (hf D (by simpa [he] using hv))
  let J : Finset I := univ.image f
  have hJcard : J.card = K.card := by
    dsimp only [J]
    rw [card_image_of_injective _ hfinj]
    simp
  have hweight : (∑ i ∈ J, d i) ≤ ∑ B ∈ K, B.card := by
    have hh : ∀ B : K, d (f B) ≤ B.val.card := by
      intro B
      have h := card_le_card (hf B)
      simpa using h
    have hsum := Finset.sum_le_sum (fun B (_ : B ∈ (univ : Finset K)) => hh B)
    have hleft : (∑ i ∈ J, d i) = ∑ B : K, d (f B) := by
      exact sum_image (fun _ _ _ _ he => hfinj he)
    rw [← hleft] at hsum
    simpa only [Finset.sum_coe_sort] using hsum
  have htwo : 2 * L.card ≤ ∑ B ∈ L, B.card := by
    have hh := sum_le_sum (s := L) (f := fun _ => 2) (g := fun B => B.card)
      (fun B hB => hP.2 B (hLP hB))
    simpa [mul_comm] using hh
  have hsum := sum_sdiff (f := fun B : Finset (Vertex a d) => B.card) hLP
  change (∑ B ∈ K, B.card) + (∑ B ∈ L, B.card) = ∑ B ∈ P, B.card at hsum
  rw [partition_card_sum hP.1.1, card_vertices] at hsum
  have hpc : P.card = K.card + L.card := by
    have hh := card_sdiff_of_subset hLP
    have hle := card_le_card hLP
    change K.card = P.card - L.card at hh
    omega
  have hkc : K.card ≤ Fintype.card I := by
    have hh := card_le_card (subset_univ J)
    simpa [hJcard] using hh
  let S := Jᶜ
  have hSc : S.card = Fintype.card I - K.card := by simp [S, card_compl, hJcard]
  have hsumS := sum_add_sum_compl J d
  change (∑ i ∈ J, d i) + (∑ i ∈ S, d i) = ∑ i, d i at hsumS
  have htop := subset_sum_le_topSum d S
  have hcorecap : 2 * L.card ≤ a + topSum d S.card := by omega
  have hterm : P.card ≤ a + Fintype.card I - loss a S.card (topSum d S.card) := by
    unfold loss
    omega
  have ht : S.card ∈ range (Fintype.card I + 1) := mem_range.mpr (by omega)
  have hmax : a + Fintype.card I - loss a S.card (topSum d S.card) ≤ sizeValue a d :=
    Finset.le_sup (s := range (Fintype.card I + 1))
      (f := fun t => a + Fintype.card I - loss a t (topSum d t)) ht
  exact hterm.trans hmax

/-- Exact bipanchromatic number of the construction, with the nonempty residual
index set required by the range theorem. -/
theorem hasBipan (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hq : 0 < Fintype.card I)
    (hd : ∀ i, 2 ≤ d i) : HasBipan (hypergraph a d ha hd) (sizeValue a d) := by
  exact ⟨bicoloring_attains a d ha hq hd, fun P hP => bicoloring_le a d ha hd P hP⟩

end Model
end Bipanchromatic
