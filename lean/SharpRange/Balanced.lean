import SharpRange.Endpoints
import SharpRange.TransferPath

namespace Bipanchromatic
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem balanced_topSum (d : I → ℕ) (s r : ℕ)
    (hd : ∀ i, s ≤ d i ∧ d i ≤ s + 1)
    (hr : r < Fintype.card I) (htotal : ∑ i, d i = Fintype.card I * s + r)
    (t : ℕ) (ht : t ≤ Fintype.card I) : topSum d t = s * t + min t r := by
  apply Nat.le_antisymm
  · obtain ⟨S, hcard, heq⟩ := exists_topSum d t ht
    have hsplit : ∀ A : Finset I, (∑ i ∈ A, d i) = A.card * s + ∑ i ∈ A, (d i - s) := by
      intro A
      calc
        _ = ∑ i ∈ A, (s + (d i - s)) := sum_congr rfl (fun i _ => by have := (hd i).1; omega)
        _ = _ := by simp [sum_add_distrib]
    have hall : (∑ i, (d i - s)) = r := by
      have hh := hsplit univ
      simp only [card_univ] at hh
      omega
    have hsub : (∑ i ∈ S, (d i - s)) ≤ r := by
      rw [← hall]
      exact sum_le_sum_of_subset (subset_univ S)
    have hone : (∑ i ∈ S, (d i - s)) ≤ t := by
      have hh := sum_le_sum (s := S) (f := fun i => d i - s) (g := fun _ => 1)
        (fun i _ => by have := hd i; omega)
      simpa [hcard] using hh
    have hS := hsplit S
    rw [hcard] at hS
    rw [heq]
    nlinarith [Nat.le_min.mpr ⟨hone, hsub⟩]
  · exact topSum_balanced_bound d s r t ht hr htotal

theorem balanced_sizeValue (a : ℕ) (d : I → ℕ) (s r : ℕ)
    (hd : ∀ i, s ≤ d i ∧ d i ≤ s + 1)
    (hr : r < Fintype.card I) (htotal : ∑ i, d i = Fintype.card I * s + r) :
    sizeValue a d = balancedLower a (Fintype.card I) s r := by
  unfold sizeValue balancedLower
  apply Finset.sup_congr rfl
  intro t ht
  have ht' : t ≤ Fintype.card I := by have := mem_range.mp ht; omega
  rw [balanced_topSum d s r hd hr htotal t ht']

theorem exists_balanced (s r : ℕ) (hr : r < Fintype.card I) :
    ∃ d : I → ℕ, (∀ i, s ≤ d i ∧ d i ≤ s + 1) ∧
      (∑ i, d i) = Fintype.card I * s + r := by
  obtain ⟨S, _, hcard⟩ := exists_subset_card_eq
    (show r ≤ (univ : Finset I).card by simp; omega)
  let d := fun i : I => s + if i ∈ S then 1 else 0
  refine ⟨d, ?_, ?_⟩
  · intro i
    dsimp only [d]
    split_ifs <;> omega
  · simp [d, sum_add_distrib, hcard]

/-- Every value from the balanced objective to the concentrated endpoint occurs
for an admissible size vector with the prescribed total. This is a numerical
spectrum theorem, used by the hypergraph theorem in Full.lean. -/
theorem size_vector_interval (a s r : ℕ) (ha : 0 < a) (hs : 2 ≤ s)
    (hr : r < Fintype.card I) :
    ∀ b, balancedLower a (Fintype.card I) s r ≤ b →
      b ≤ min (a + Fintype.card I - 1) ((a + Fintype.card I * s + r) / 2) →
      ∃ d : I → ℕ, (∀ i, 2 ≤ d i) ∧
        (∑ i, d i) = Fintype.card I * s + r ∧ sizeValue a d = b := by
  obtain ⟨d, hd, htotal⟩ := exists_balanced (I := I) s r hr
  have hd2 : ∀ i, 2 ≤ d i := fun i => hs.trans (hd i).1
  have hne : (univ : Finset I).Nonempty := card_pos.mp (by simp; omega)
  obtain ⟨i, _, hi⟩ := exists_max_image univ d hne
  have hi' : ∀ j, d j ≤ d i := fun j => hi j (mem_univ j)
  obtain ⟨e, hpath, he2, _, hetotal, hecon⟩ := reaches_concentrated i d hd2 hi'
  have hstart := balanced_sizeValue a d s r hd hr htotal
  have hend := concentrated_sizeValue a e i ha he2 hecon
  rw [hetotal, htotal] at hend
  intro b hlo hhi
  obtain ⟨f, hfpath, hfval⟩ := transfer_path_intermediate a hpath b
    (by simpa [hstart] using hlo) (by simpa [hend, Nat.add_assoc] using hhi)
  have hf := transfer_path_invariants hfpath hd2
  exact ⟨f, hf.1, hf.2.trans htotal, hfval⟩


/-- Complete spectrum for the numerical size-vector objective. This theorem
has no hypergraph hypotheses; ModelValue.lean supplies the coloring connection. -/
theorem size_vector_spectrum (a s r b : ℕ) (ha : 0 < a) (hs : 2 ≤ s)
    (hr : r < Fintype.card I) :
    (∃ d : I → ℕ, (∀ i, 2 ≤ d i) ∧ (∑ i, d i) = Fintype.card I * s + r ∧ sizeValue a d = b) ↔
    balancedLower a (Fintype.card I) s r ≤ b ∧
      b ≤ min (a + Fintype.card I - 1) ((a + Fintype.card I * s + r) / 2) := by
  constructor
  · rintro ⟨d, hd, htotal, rfl⟩
    refine ⟨sizeValue_ge_balanced a d s r hr htotal, ?_⟩
    simpa [htotal, Nat.add_assoc] using sizeValue_upper a d ha hd
  · rintro ⟨hlo, hhi⟩
    exact size_vector_interval a s r ha hs hr b hlo hhi

end Bipanchromatic
