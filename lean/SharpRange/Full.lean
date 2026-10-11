import SharpRange.UniversalLower
import SharpRange.ModelValue
import SharpRange.Relabel

namespace Bipanchromatic
open Finset

/-- The corrected model-value target, in the q ≥ 1 regime of the range theorem. -/
theorem model_value : ModelValueStatement := by
  intro a q d hq ha hd
  exact Model.hasBipan a d ha (by simpa using hq) hd

/-- Every value has a p-uniform witness with common core of exactly a vertices. -/
theorem sharp_range_witness (n p a b : ℕ) (_hp : 2 ≤ p) (ha : 1 ≤ a)
    (hap : a < p) (hn : 2 * p ≤ n + a)
    (hlo : sharpLower n p a ≤ b) (hhi : b ≤ sharpUpper n p) :
    ∃ H : Hypergraph (Fin n), HasPan H p ∧ HasAlpha H p a ∧ HasBipan H b ∧
      (∀ D ∈ H.edges, D.card = p) ∧ (commonCore H).card = a := by
  classical
  let q := p - a
  let s := (n - a) / q
  let r := (n - a) % q
  have hq : 0 < q := by dsimp only [q]; omega
  have hpa : a + q = p := by dsimp only [q]; omega
  have hna : a ≤ n := by omega
  have hdiv : r + q * s = n - a := Nat.mod_add_div (n - a) q
  have htotal : a + q * s + r = n := by omega
  have hs : 2 ≤ s := by
    apply (Nat.le_div_iff_mul_le hq).mpr
    omega
  have hr : r < q := Nat.mod_lt _ hq
  have hlow : balancedLower a (Fintype.card (Fin q)) s r = sharpLower n p a := by
    rw [Fintype.card_fin, balancedLower_eq_sub_minLoss, hpa]
    rfl
  have hupp : min (a + Fintype.card (Fin q) - 1)
      ((a + Fintype.card (Fin q) * s + r) / 2) = sharpUpper n p := by
    simp only [Fintype.card_fin, hpa, htotal, sharpUpper]
  obtain ⟨d, hd, hdsum, hdval⟩ := size_vector_interval (I := Fin q) a s r ha hs
    (by simpa using hr) b (hlow.le.trans hlo) (hhi.trans hupp.ge)
  let H := Model.hypergraph a d ha hd
  have hV : Fintype.card (Model.Vertex a d) = n := by
    rw [Model.card_vertices, hdsum, Fintype.card_fin]
    omega
  let e : Model.Vertex a d ≃ Fin n := Fintype.equivFinOfCardEq hV
  have hpan : HasPan H p := by
    have hh := Model.hasPan a d ha hd
    simpa only [Fintype.card_fin, hpa] using hh
  have halpha : HasAlpha H p a := by
    have hh := Model.hasAlpha a d ha hd
    simpa only [Fintype.card_fin, hpa] using hh
  have hb : HasBipan H b := by
    have hh := Model.hasBipan a d ha (by simpa using hq) hd
    simpa only [hdval] using hh
  refine ⟨relabel H e, relabel_hasPan H e p hpan,
    relabel_hasAlpha H e p a halpha, relabel_hasBipan H e b hb, ?_, ?_⟩
  · apply relabel_uniform H e p
    intro D hD
    have hh := Model.uniform a d ha hd D hD
    simpa only [Fintype.card_fin, hpa] using hh
  · rw [relabel_commonCore, card_image_of_injective _ e.injective]
    have hcore : commonCore H = Model.core a d := by
      ext v
      change v ∈ commonCore (Model.hypergraph a d ha hd) ↔ v ∈ Model.core a d
      rw [mem_commonCore, Model.common_core]
    rw [hcore, Model.card_core]

/-- Full sharp interval theorem for arbitrary hypergraphs on n labelled vertices. -/
theorem sharp_range : SharpRangeStatement := by
  intro n p a hp ha hap hn b
  constructor
  · rintro ⟨H, hpan, halpha, hb⟩
    obtain ⟨Q, hQ, hQc⟩ := universal_lower n p a H hp ha hap hpan halpha
    have hQb := hb.2 Q hQ
    have hu := range_upper hpan halpha hb ha
    exact ⟨hQc.trans hQb, by simpa [sharpUpper] using hu⟩
  · rintro ⟨hlo, hhi⟩
    obtain ⟨H, hpan, halpha, hb, _hu, _hc⟩ := sharp_range_witness n p a b hp ha hap hn hlo hhi
    exact ⟨H, hpan, halpha, hb⟩

end Bipanchromatic
