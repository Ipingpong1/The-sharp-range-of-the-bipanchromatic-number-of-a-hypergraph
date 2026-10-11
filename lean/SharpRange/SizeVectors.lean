import Mathlib
import Arithmetic

namespace Bipanchromatic
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The sum of the t largest entries, specified without sorting. -/
def topSum (d : I → ℕ) (t : ℕ) : ℕ :=
  (univ.powersetCard t).sup (fun S => ∑ i ∈ S, d i)

/-- Being a set of largest entries, in the order-theoretic sense. -/
def Largest (d : I → ℕ) (S : Finset I) : Prop :=
  ∀ i ∈ S, ∀ j ∉ S, d j ≤ d i

omit [DecidableEq I] in
theorem subset_sum_le_topSum (d : I → ℕ) (S : Finset I) :
    ∑ i ∈ S, d i ≤ topSum d S.card := by
  exact Finset.le_sup (s := univ.powersetCard S.card)
    (f := fun T => ∑ i ∈ T, d i) (mem_powersetCard.mpr ⟨subset_univ S, rfl⟩)

omit [DecidableEq I] in
theorem exists_topSum (d : I → ℕ) (t : ℕ) (ht : t ≤ Fintype.card I) :
    ∃ S : Finset I, S.card = t ∧ topSum d t = ∑ i ∈ S, d i := by
  have hne : (univ.powersetCard t : Finset (Finset I)).Nonempty := by
    obtain ⟨S, hS, hcard⟩ := exists_subset_card_eq (show t ≤ (univ : Finset I).card by simpa using ht)
    exact ⟨S, mem_powersetCard.mpr ⟨hS, hcard⟩⟩
  obtain ⟨S, hS, heq⟩ := exists_mem_eq_sup _ hne (fun S => ∑ i ∈ S, d i)
  exact ⟨S, (mem_powersetCard.mp hS).2, heq⟩

omit [Fintype I] in
theorem maximizing_is_largest (d : I → ℕ) (S : Finset I)
    (hmax : ∀ T : Finset I, T.card = S.card → (∑ i ∈ T, d i) ≤ ∑ i ∈ S, d i) :
    Largest d S := by
  intro i hi j hj
  have hj' : j ∉ S.erase i := fun h => hj (mem_of_mem_erase h)
  have hcard : (insert j (S.erase i)).card = S.card := by
    rw [card_insert_of_notMem hj', card_erase_of_mem hi]
    have := card_pos.mpr ⟨i, hi⟩
    omega
  have hm := hmax (insert j (S.erase i)) hcard
  rw [sum_insert hj'] at hm
  have hs := sum_erase_add S d hi
  omega

theorem topSum_largest (d : I → ℕ) (S : Finset I)
    (heq : topSum d S.card = ∑ i ∈ S, d i) : Largest d S := by
  apply maximizing_is_largest
  intro T hT
  have hh := subset_sum_le_topSum d T
  simpa [hT, heq] using hh

/-- Integer majorization: balanced entries minimize all largest-part sums. -/
theorem balanced_sum_bound (d : I → ℕ) (S : Finset I) (s r : ℕ)
    (hlarge : Largest d S) (_hr : r < Fintype.card I)
    (htotal : ∑ i, d i = Fintype.card I * s + r) :
    s * S.card + min S.card r ≤ ∑ i ∈ S, d i := by
  by_contra hbad
  have hbad' : (∑ i ∈ S, d i) < s * S.card + min S.card r := by omega
  have hw : ∃ i ∈ S, d i ≤ s := by
    by_contra hh
    have hsmall : ∀ i ∈ S, s + 1 ≤ d i := by
      intro i hi
      by_contra hn
      exact hh ⟨i, hi, by omega⟩
    have hs := sum_le_sum hsmall
    simp only [sum_const, smul_eq_mul] at hs
    have hm := min_le_left S.card r
    nlinarith
  obtain ⟨i, hi, hdi⟩ := hw
  have hout : ∑ j ∈ Sᶜ, d j ≤ (Fintype.card I - S.card) * s := by
    have h := sum_le_sum (s := Sᶜ) (f := d) (g := fun _ => s) (fun j hj =>
      (hlarge i hi j (mem_compl.mp hj)).trans hdi)
    simpa [Finset.card_compl] using h
  have hsum := sum_add_sum_compl S d
  have hc : S.card ≤ Fintype.card I := by simpa using card_le_card (subset_univ S)
  have hdecomp : Fintype.card I = S.card + (Fintype.card I - S.card) := by omega
  rw [htotal, hdecomp] at hsum
  have hm := min_le_right S.card r
  nlinarith

theorem topSum_balanced_bound (d : I → ℕ) (s r t : ℕ)
    (ht : t ≤ Fintype.card I) (hr : r < Fintype.card I)
    (htotal : ∑ i, d i = Fintype.card I * s + r) :
    s * t + min t r ≤ topSum d t := by
  obtain ⟨S, hcard, heq⟩ := exists_topSum d t ht
  have hlarge := topSum_largest d S (by simpa [hcard] using heq)
  have hh := balanced_sum_bound d S s r hlarge hr htotal
  simpa [hcard, ← heq] using hh

/-- Numerical objective for an arbitrary size vector, with a singleton core. -/
def sizeValue (a : ℕ) (d : I → ℕ) : ℕ :=
  (range (Fintype.card I + 1)).sup (fun t => a + Fintype.card I - loss a t (topSum d t))

omit [DecidableEq I] in
theorem sizeValue_step (a : ℕ) (d d' : I → ℕ)
    (h : ∀ t ≤ Fintype.card I, topSum d t ≤ topSum d' t ∧ topSum d' t ≤ topSum d t + 1) :
    sizeValue a d ≤ sizeValue a d' ∧ sizeValue a d' ≤ sizeValue a d + 1 := by
  constructor
  · unfold sizeValue
    apply Finset.sup_le
    intro t ht
    have ht' : t ≤ Fintype.card I := by simpa using Nat.le_of_lt_succ (mem_range.mp ht)
    have hl := (loss_step a t _ _ (h t ht').1 (h t ht').2).1
    have hs : a + Fintype.card I - loss a t (topSum d' t) ≤ sizeValue a d' := Finset.le_sup (s := range (Fintype.card I + 1)) (f := fun t => a + Fintype.card I - loss a t (topSum d' t)) ht
    unfold sizeValue at hs
    omega
  · unfold sizeValue
    apply Finset.sup_le
    intro t ht
    have ht' : t ≤ Fintype.card I := by simpa using Nat.le_of_lt_succ (mem_range.mp ht)
    have hl := (loss_step a t _ _ (h t ht').1 (h t ht').2).2
    have hs : a + Fintype.card I - loss a t (topSum d t) ≤ sizeValue a d := Finset.le_sup (s := range (Fintype.card I + 1)) (f := fun t => a + Fintype.card I - loss a t (topSum d t)) ht
    unfold sizeValue at hs
    omega


/-- Transfer a single unit from donor j to recipient i. -/
def transfer (d : I → ℕ) (i j : I) : I → ℕ :=
  Function.update (Function.update d i (d i + 1)) j (d j - 1)

omit [Fintype I] in
theorem transfer_sum_identity (d : I → ℕ) (i j : I) (hij : i ≠ j)
    (hj : 1 ≤ d j) (S : Finset I) :
    (∑ k ∈ S, transfer d i j k) + (if j ∈ S then 1 else 0) =
    (∑ k ∈ S, d k) + (if i ∈ S then 1 else 0) := by
  have hp : ∀ k, transfer d i j k + (if k = j then 1 else 0) =
      d k + (if k = i then 1 else 0) := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [transfer, Function.update, hij]
    · by_cases hkj : k = j
      · subst k
        simp [transfer, Function.update, hki]
        omega
      · simp [transfer, Function.update, hki, hkj]
  have hs := Finset.sum_congr (s₁ := S) rfl (fun k _ => hp k)
  simpa [sum_add_distrib] using hs

theorem exists_topSum_containing (d : I → ℕ) (t : ℕ) (i : I)
    (ht0 : 0 < t) (ht : t ≤ Fintype.card I) (hi : ∀ j, d j ≤ d i) :
    ∃ S : Finset I, S.card = t ∧ i ∈ S ∧ topSum d t = ∑ k ∈ S, d k := by
  obtain ⟨S, hcard, hsum⟩ := exists_topSum d t ht
  by_cases hiS : i ∈ S
  · exact ⟨S, hcard, hiS, hsum⟩
  obtain ⟨j, hj⟩ := card_pos.mp (show 0 < S.card by omega)
  have hlarge := topSum_largest d S (by simpa [hcard] using hsum)
  have hji : d j = d i := Nat.le_antisymm (hi j) (hlarge j hj i hiS)
  have hiE : i ∉ S.erase j := fun h => hiS (mem_of_mem_erase h)
  refine ⟨insert i (S.erase j), ?_, mem_insert_self _ _, ?_⟩
  · rw [card_insert_of_notMem hiE, card_erase_of_mem hj, hcard]
    omega
  · rw [sum_insert hiE]
    have hs := sum_erase_add S d hj
    omega

/-- The genuine combinatorial transfer lemma for largest-part sums. -/
theorem topSum_transfer (d : I → ℕ) (i j : I) (hij : i ≠ j)
    (hj : 1 ≤ d j) (hi : ∀ k, d k ≤ d i) (t : ℕ) (ht : t ≤ Fintype.card I) :
    topSum d t ≤ topSum (transfer d i j) t ∧
    topSum (transfer d i j) t ≤ topSum d t + 1 := by
  constructor
  · by_cases ht0 : t = 0
    · subst t
      simp [topSum]
    obtain ⟨S, hcard, hiS, hsum⟩ := exists_topSum_containing d t i (by omega) ht hi
    have hs := transfer_sum_identity d i j hij hj S
    have hb := subset_sum_le_topSum (transfer d i j) S
    rw [hcard] at hb
    simp only [hiS, ite_true] at hs
    split_ifs at hs <;> omega
  · unfold topSum
    apply Finset.sup_le
    intro S hS
    have hcard := (mem_powersetCard.mp hS).2
    have hs := transfer_sum_identity d i j hij hj S
    have hb := subset_sum_le_topSum d S
    rw [hcard] at hb
    unfold topSum at hb
    split_ifs at hs <;> omega

theorem sizeValue_transfer (a : ℕ) (d : I → ℕ) (i j : I) (hij : i ≠ j)
    (hj : 1 ≤ d j) (hi : ∀ k, d k ≤ d i) :
    sizeValue a d ≤ sizeValue a (transfer d i j) ∧
    sizeValue a (transfer d i j) ≤ sizeValue a d + 1 :=
  sizeValue_step a d _ (fun t ht => topSum_transfer d i j hij hj hi t ht)

theorem transfer_total (d : I → ℕ) (i j : I) (hij : i ≠ j) (hj : 1 ≤ d j) :
    ∑ k, transfer d i j k = ∑ k, d k := by
  have h := transfer_sum_identity d i j hij hj univ
  simp at h
  exact h

omit [Fintype I] in
theorem transfer_admissible (d : I → ℕ) (i j : I) (hij : i ≠ j)
    (hd : ∀ k, 2 ≤ d k) (hj : 2 < d j) (hi : ∀ k, d k ≤ d i) :
    (∀ k, 2 ≤ transfer d i j k) ∧
    (∀ k, transfer d i j k ≤ transfer d i j i) := by
  have hi' : transfer d i j i = d i + 1 := by simp [transfer, Function.update, hij]
  constructor
  · intro k
    have hk := hd k
    by_cases hki : k = i
    · subst k
      rw [hi']
      omega
    · by_cases hkj : k = j
      · subst k
        simp [transfer, Function.update]
        omega
      · simpa [transfer, Function.update, hki, hkj] using hk
  · intro k
    rw [hi']
    have hk := hi k
    by_cases hki : k = i
    · subst k
      rw [hi']
    · by_cases hkj : k = j
      · subst k
        simp [transfer, Function.update]
        omega
      · simpa [transfer, Function.update, hki, hkj] using (show d k ≤ d i + 1 by omega)

end Bipanchromatic
