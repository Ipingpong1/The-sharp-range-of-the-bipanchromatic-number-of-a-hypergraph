import SharpRange.SizeVectors

namespace Bipanchromatic
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
@[simp] theorem topSum_zero (d : I → ℕ) : topSum d 0 = 0 := by simp [topSum]

theorem concentrated_topSum (d : I → ℕ) (i : I) (hd : ∀ k, 2 ≤ d k)
    (he : ∀ j, j ≠ i → d j = 2) (t : ℕ) (ht0 : 0 < t) (ht : t ≤ Fintype.card I) :
    topSum d t = d i + 2 * (t - 1) := by
  have hi : ∀ j, d j ≤ d i := by
    intro j
    by_cases hji : j = i
    · simp [hji]
    · rw [he j hji]
      exact hd i
  obtain ⟨S, hcard, hiS, hsum⟩ := exists_topSum_containing d t i ht0 ht hi
  have hrest : ∑ k ∈ S.erase i, d k = (S.card - 1) * 2 := by
    calc
      _ = ∑ k ∈ S.erase i, 2 := sum_congr rfl (fun k hk => he k (mem_erase.mp hk).1)
      _ = _ := by simp [card_erase_of_mem hiS]
  have hs := sum_erase_add S d hiS
  rw [hrest, hcard] at hs
  omega

theorem concentrated_total (d : I → ℕ) (i : I) (he : ∀ j, j ≠ i → d j = 2) :
    ∑ k, d k = d i + 2 * (Fintype.card I - 1) := by
  have hrest : ∑ k ∈ univ.erase i, d k = (Fintype.card I - 1) * 2 := by
    calc
      _ = ∑ k ∈ univ.erase i, 2 := sum_congr rfl (fun k hk => he k (mem_erase.mp hk).1)
      _ = _ := by simp
  have hs := sum_erase_add univ d (mem_univ i)
  rw [hrest] at hs
  omega

/-- The concentrated endpoint, now derived from the actual largest-part sums. -/
theorem concentrated_sizeValue (a : ℕ) (d : I → ℕ) (i : I) (ha : 0 < a)
    (hd : ∀ k, 2 ≤ d k) (he : ∀ j, j ≠ i → d j = 2) :
    sizeValue a d = min (a + Fintype.card I - 1) ((a + ∑ k, d k) / 2) := by
  have hq : 1 ≤ Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  have hmin : sizeValue a d = a + Fintype.card I - loss a 1 (d i) := by
    apply Nat.le_antisymm
    · unfold sizeValue
      apply Finset.sup_le
      intro t ht
      have ht' : t ≤ Fintype.card I := by have := mem_range.mp ht; omega
      have hl : loss a 1 (d i) ≤ loss a t (topSum d t) := by
        by_cases ht0 : t = 0
        · subst t
          rw [topSum_zero]
          exact concentrated_beats_pairing a (d i) ha (hd i)
        · rw [concentrated_topSum d i hd he t (by omega) ht']
          exact concentrated_positive_min a (d i) t (by omega)
      omega
    · have hs := Finset.le_sup (s := range (Fintype.card I + 1))
        (f := fun t => a + Fintype.card I - loss a t (topSum d t))
        (b := 1) (mem_range.mpr (by omega))
      have ht1 := concentrated_topSum d i hd he 1 (by omega) hq
      simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at ht1
      simpa only [ht1, sizeValue] using hs
  rw [hmin]
  exact concentrated_endpoint a (Fintype.card I) (d i) _ ha hq (hd i)
    (by rw [concentrated_total d i he]; omega)

/-- The balanced numerical guarantee for any size vector. -/
def balancedLower (a q s r : ℕ) : ℕ :=
  (range (q + 1)).sup (fun t => a + q - loss a t (s * t + min t r))

theorem sizeValue_ge_balanced (a : ℕ) (d : I → ℕ) (s r : ℕ)
    (hr : r < Fintype.card I) (htotal : ∑ i, d i = Fintype.card I * s + r) :
    balancedLower a (Fintype.card I) s r ≤ sizeValue a d := by
  unfold balancedLower
  apply Finset.sup_le
  intro t ht
  have ht' : t ≤ Fintype.card I := by have := mem_range.mp ht; omega
  have hmajor := topSum_balanced_bound d s r t ht' hr htotal
  have hl := loss_antitone a t _ _ hmajor
  have hs : a + Fintype.card I - loss a t (topSum d t) ≤ sizeValue a d :=
    Finset.le_sup (s := range (Fintype.card I + 1))
      (f := fun t => a + Fintype.card I - loss a t (topSum d t)) ht
  omega


/-- Both universal upper bounds for the numerical objective. -/
theorem sizeValue_upper (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hd : ∀ k, 2 ≤ d k) :
    sizeValue a d ≤ min (a + Fintype.card I - 1) ((a + ∑ k, d k) / 2) := by
  unfold sizeValue
  apply Finset.sup_le
  intro t ht
  have ht' : t ≤ Fintype.card I := by have := mem_range.mp ht; omega
  obtain ⟨S, hcard, heq⟩ := exists_topSum d t ht'
  have hrest : 2 * (Fintype.card I - t) ≤ ∑ k ∈ Sᶜ, d k := by
    have hh := sum_le_sum (s := Sᶜ) (f := fun _ => 2) (g := d) (fun k _ => hd k)
    simpa [card_compl, hcard, mul_comm] using hh
  have hsum := sum_add_sum_compl S d
  have hcount := dissolution_count a (Fintype.card I) t (topSum d t) ht'
  have hloss : 1 ≤ loss a t (topSum d t) := by
    by_cases hz : t = 0
    · rw [hz, topSum_zero]
      unfold loss
      omega
    · unfold loss
      omega
  apply le_min
  · omega
  · omega

end Bipanchromatic
