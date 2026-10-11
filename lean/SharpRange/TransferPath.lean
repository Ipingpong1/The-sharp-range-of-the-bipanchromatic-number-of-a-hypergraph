import SharpRange.SizeVectors

namespace Bipanchromatic
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A permitted transfer to the distinguished largest part. -/
def TransferStep (i : I) (d e : I → ℕ) : Prop :=
  ∃ j, i ≠ j ∧ 2 < d j ∧ (∀ k, d k ≤ d i) ∧ e = transfer d i j

theorem transferStep_value (a : ℕ) {i : I} {d e : I → ℕ} (h : TransferStep i d e) :
    sizeValue a d ≤ sizeValue a e ∧ sizeValue a e ≤ sizeValue a d + 1 := by
  obtain ⟨j, hij, hj, hi, rfl⟩ := h
  exact sizeValue_transfer a d i j hij (by omega) hi

theorem reaches_concentrated (i : I) (d : I → ℕ)
    (hd : ∀ k, 2 ≤ d k) (hi : ∀ k, d k ≤ d i) :
    ∃ e : I → ℕ,
      Relation.ReflTransGen (TransferStep i) d e ∧
      (∀ k, 2 ≤ e k) ∧ (∀ k, e k ≤ e i) ∧
      (∑ k, e k) = ∑ k, d k ∧ (∀ j, j ≠ i → e j = 2) := by
  generalize hm : (∑ k ∈ univ.erase i, d k) = m
  induction m using Nat.strong_induction_on generalizing d with
  | h m ih =>
    by_cases hdone : ∀ j, j ≠ i → d j = 2
    · exact ⟨d, .refl, hd, hi, rfl, hdone⟩
    · have hw : ∃ j, i ≠ j ∧ 2 < d j := by
        push Not at hdone
        obtain ⟨j, hji, hj⟩ := hdone
        exact ⟨j, Ne.symm hji, by have := hd j; omega⟩
      obtain ⟨j, hij, hj⟩ := hw
      let d' := transfer d i j
      have had := transfer_admissible d i j hij hd hj hi
      have hmeasure := transfer_sum_identity d i j hij (by omega) (univ.erase i)
      have hji : j ≠ i := Ne.symm hij
      simp [hji] at hmeasure
      have hlt : (∑ k ∈ univ.erase i, d' k) < m := by
        dsimp only [d']
        omega
      obtain ⟨e, hpath, hed, hei, htotal, hend⟩ :=
        ih _ hlt d' had.1 had.2 rfl
      have hstep : TransferStep i d d' := ⟨j, hij, hj, hi, rfl⟩
      refine ⟨e, hpath.head hstep, hed, hei, ?_, hend⟩
      exact htotal.trans (transfer_total d i j hij (by omega))

/-- Every intermediate numerical value is realized along the actual transfer
relation; the existence of a suitable sequence is not assumed. -/
theorem transfer_path_intermediate (a : ℕ) {i : I} {d e : I → ℕ}
    (hpath : Relation.ReflTransGen (TransferStep i) d e) (b : ℕ)
    (hlo : sizeValue a d ≤ b) (hhi : b ≤ sizeValue a e) :
    ∃ f : I → ℕ, Relation.ReflTransGen (TransferStep i) d f ∧ sizeValue a f = b := by
  induction hpath with
  | refl => exact ⟨d, .refl, by omega⟩
  | @tail e f hpath hstep ih =>
    by_cases hb : b ≤ sizeValue a e
    · exact ih hb
    · have hv := transferStep_value a hstep
      exact ⟨f, hpath.tail hstep, by omega⟩

/-- Admissibility and total size are preserved along the whole path. -/
theorem transfer_path_invariants {i : I} {d e : I → ℕ}
    (hpath : Relation.ReflTransGen (TransferStep i) d e) (hd : ∀ k, 2 ≤ d k) :
    (∀ k, 2 ≤ e k) ∧ (∑ k, e k) = ∑ k, d k := by
  induction hpath with
  | refl => exact ⟨hd, rfl⟩
  | @tail e f hpath hstep ih =>
    obtain ⟨j, hij, hj, hi, rfl⟩ := hstep
    exact ⟨(transfer_admissible e i j hij ih.1 hj hi).1,
      (transfer_total e i j hij (by omega)).trans ih.2⟩

/-- A fully proved numerical no-gaps statement for size vectors. Connecting
sizeValue to hypergraph bipanchromatic numbers is a separate obligation. -/
theorem numerical_no_gaps (a : ℕ) (i : I) (d : I → ℕ)
    (hd : ∀ k, 2 ≤ d k) (hi : ∀ k, d k ≤ d i) :
    ∃ e : I → ℕ, (∀ j, j ≠ i → e j = 2) ∧
      (∀ b, sizeValue a d ≤ b → b ≤ sizeValue a e →
        ∃ f : I → ℕ, (∀ k, 2 ≤ f k) ∧ (∑ k, f k) = ∑ k, d k ∧ sizeValue a f = b) := by
  obtain ⟨e, hpath, _, _, _, hend⟩ := reaches_concentrated i d hd hi
  refine ⟨e, hend, ?_⟩
  intro b hlo hhi
  obtain ⟨f, hfpath, hfval⟩ := transfer_path_intermediate a hpath b hlo hhi
  have hinv := transfer_path_invariants hfpath hd
  exact ⟨f, hinv.1, hinv.2, hfval⟩

end Bipanchromatic
