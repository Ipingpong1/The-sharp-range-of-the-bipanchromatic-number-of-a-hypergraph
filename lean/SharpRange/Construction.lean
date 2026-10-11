import SharpRange.Definitions

namespace Bipanchromatic
namespace Model
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Vertex (a : ℕ) (d : I → ℕ) := Fin a ⊕ ((i : I) × Fin (d i))

def core (a : ℕ) (d : I → ℕ) : Finset (Vertex a d) :=
  univ.image Sum.inl

def part (a : ℕ) (d : I → ℕ) (i : I) : Finset (Vertex a d) :=
  univ.image (fun x => Sum.inr ⟨i, x⟩)

def edge (a : ℕ) (d : I → ℕ) (f : (i : I) → Fin (d i)) : Finset (Vertex a d) :=
  core a d ∪ univ.image (fun i => Sum.inr ⟨i, f i⟩)

omit [Fintype I] in
theorem mem_core (a : ℕ) (d : I → ℕ) (v : Vertex a d) :
    v ∈ core a d ↔ ∃ u, v = Sum.inl u := by
  simp [core, eq_comm]

omit [Fintype I] in
theorem mem_part (a : ℕ) (d : I → ℕ) (i : I) (v : Vertex a d) :
    v ∈ part a d i ↔ ∃ x, v = Sum.inr ⟨i, x⟩ := by
  simp [part, eq_comm]

omit [Fintype I] in
@[simp] theorem card_core (a : ℕ) (d : I → ℕ) : (core a d).card = a := by
  rw [core, card_image_of_injective _ Sum.inl_injective]
  simp

omit [Fintype I] in
@[simp] theorem card_part (a : ℕ) (d : I → ℕ) (i : I) : (part a d i).card = d i := by
  have hinj : Function.Injective (fun x : Fin (d i) => (Sum.inr ⟨i, x⟩ : Vertex a d)) := by
    intro x y h
    simpa using h
  rw [part, card_image_of_injective _ hinj]
  simp

omit [DecidableEq I] in
@[simp] theorem card_vertices (a : ℕ) (d : I → ℕ) :
    Fintype.card (Vertex a d) = a + ∑ i, d i := by
  simp [Vertex, Fintype.card_sigma]

@[simp] theorem card_edge (a : ℕ) (d : I → ℕ) (f : (i : I) → Fin (d i)) :
    (edge a d f).card = a + Fintype.card I := by
  have hinj : Function.Injective (fun i => (Sum.inr ⟨i, f i⟩ : Vertex a d)) := by
    intro i j h
    exact congrArg Sigma.fst (Sum.inr_injective h)
  have hd : Disjoint (core a d) (univ.image (fun i => (Sum.inr ⟨i, f i⟩ : Vertex a d))) := by
    apply disjoint_left.mpr
    intro v hv hw
    obtain ⟨u, rfl⟩ := (mem_core a d v).mp hv
    simp at hw
  rw [edge, card_union_of_disjoint hd, card_core, card_image_of_injective _ hinj]
  simp

/-- Exactly the complete choice edges, with a nonempty core. -/
def hypergraph (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hd : ∀ i, 2 ≤ d i) :
    Hypergraph (Vertex a d) where
  edges := univ.image (edge a d)
  nonempty_edges := by
    let f : (i : I) → Fin (d i) := fun i => ⟨0, by have := hd i; omega⟩
    exact ⟨edge a d f, mem_image.mpr ⟨f, mem_univ f, rfl⟩⟩
  nonempty_edge := by
    intro e he
    obtain ⟨f, _, rfl⟩ := mem_image.mp he
    apply card_pos.mp
    rw [card_edge]
    omega

/-- The key combinatorial description: a transversal either contains a core
vertex or contains an entire residual part. -/
theorem transversal_iff (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hd : ∀ i, 2 ≤ d i)
    (T : Finset (Vertex a d)) :
    Transversal (hypergraph a d ha hd) T ↔
      (∃ u : Fin a, Sum.inl u ∈ T) ∨ (∃ i : I, part a d i ⊆ T) := by
  classical
  constructor
  · intro hT
    by_contra hn
    have hncore : ∀ u : Fin a, Sum.inl u ∉ T := by
      intro u hu
      exact hn (Or.inl ⟨u, hu⟩)
    have hmissing : ∀ i : I, ∃ x : Fin (d i), Sum.inr ⟨i, x⟩ ∉ T := by
      intro i
      by_contra hh
      push Not at hh
      apply hn
      right
      refine ⟨i, ?_⟩
      intro v hv
      obtain ⟨x, rfl⟩ := (mem_part a d i v).mp hv
      exact hh x
    choose f hf using hmissing
    have he : edge a d f ∈ (hypergraph a d ha hd).edges :=
      mem_image.mpr ⟨f, mem_univ f, rfl⟩
    obtain ⟨v, hv⟩ := hT (edge a d f) he
    obtain ⟨hvT, hve⟩ := mem_inter.mp hv
    rcases mem_union.mp hve with hvcore | hvrest
    · obtain ⟨u, rfl⟩ := (mem_core a d v).mp hvcore
      exact hncore u hvT
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hvrest
      exact hf i hvT
  · intro hT e he
    obtain ⟨f, _, rfl⟩ := mem_image.mp he
    rcases hT with ⟨u, hu⟩ | ⟨i, hi⟩
    · refine ⟨Sum.inl u, mem_inter.mpr ⟨hu, ?_⟩⟩
      exact mem_union_left _ (mem_image.mpr ⟨u, mem_univ u, rfl⟩)
    · refine ⟨Sum.inr ⟨i, f i⟩, mem_inter.mpr ⟨?_, ?_⟩⟩
      · exact hi (mem_image.mpr ⟨f i, mem_univ _, rfl⟩)
      · exact mem_union_right _ (mem_image.mpr ⟨i, mem_univ i, rfl⟩)

/-- All edges have the promised size p = a + q. -/
theorem uniform (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hd : ∀ i, 2 ≤ d i)
    (e : Finset (Vertex a d)) (he : e ∈ (hypergraph a d ha hd).edges) :
    e.card = a + Fintype.card I := by
  obtain ⟨f, _, rfl⟩ := mem_image.mp he
  exact card_edge a d f


def naturalColor (a : ℕ) (d : I → ℕ) : Vertex a d → Fin a ⊕ I
  | Sum.inl u => Sum.inl u
  | Sum.inr ⟨i, _⟩ => Sum.inr i

omit [Fintype I] [DecidableEq I] in
theorem naturalColor_surjective (a : ℕ) (d : I → ℕ) (hd : ∀ i, 2 ≤ d i) :
    Function.Surjective (naturalColor a d) := by
  intro k
  cases k with
  | inl u => exact ⟨Sum.inl u, rfl⟩
  | inr i => exact ⟨Sum.inr ⟨i, ⟨0, by have := hd i; omega⟩⟩, rfl⟩

@[simp] theorem fiber_core (a : ℕ) (d : I → ℕ) (u : Fin a) :
    fiber (naturalColor a d) (Sum.inl u) = {Sum.inl u} := by
  ext v
  cases v with
  | inl w => simp [naturalColor]
  | inr w => simp [naturalColor]

@[simp] theorem fiber_part (a : ℕ) (d : I → ℕ) (i : I) :
    fiber (naturalColor a d) (Sum.inr i) = part a d i := by
  ext v
  cases v with
  | inl u => simp [naturalColor, part]
  | inr w =>
    obtain ⟨j, x⟩ := w
    simp only [mem_fiber, naturalColor, Sum.inr.injEq]
    rw [mem_part]
    constructor
    · intro h
      subst j
      exact ⟨x, rfl⟩
    · rintro ⟨y, h⟩
      exact congrArg Sigma.fst (Sum.inr_injective h)

theorem natural_panchromatic (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hd : ∀ i, 2 ≤ d i) :
    Panchromatic (hypergraph a d ha hd) (colorPartition (naturalColor a d)) := by
  refine ⟨colorPartition_partition _ (naturalColor_surjective a d hd), ?_⟩
  intro C hC
  obtain ⟨k, _, rfl⟩ := mem_image.mp hC
  apply (transversal_iff a d ha hd _).mpr
  cases k with
  | inl u => exact Or.inl ⟨u, by simp⟩
  | inr i => exact Or.inr ⟨i, by simp⟩

theorem natural_card (a : ℕ) (d : I → ℕ) (hd : ∀ i, 2 ≤ d i) :
    (colorPartition (naturalColor a d)).card = a + Fintype.card I := by
  rw [colorPartition_card _ (naturalColor_surjective a d hd)]
  simp

theorem hasPan (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hd : ∀ i, 2 ≤ d i) :
    HasPan (hypergraph a d ha hd) (a + Fintype.card I) := by
  constructor
  · exact ⟨_, natural_panchromatic a d ha hd, natural_card a d hd⟩
  · intro P hP
    obtain ⟨e, he⟩ := (hypergraph a d ha hd).nonempty_edges
    have hh := pan_card_le_edge hP he
    simpa [uniform a d ha hd e he] using hh

theorem natural_singletons (a : ℕ) (d : I → ℕ) (hd : ∀ i, 2 ≤ d i) :
    singletonCount (colorPartition (naturalColor a d)) = a := by
  have hset : (colorPartition (naturalColor a d)).filter (fun C => C.card = 1) =
      (univ : Finset (Fin a)).image (fun u => ({Sum.inl u} : Finset (Vertex a d))) := by
    ext C
    constructor
    · intro hC
      obtain ⟨hC, hcard⟩ := mem_filter.mp hC
      obtain ⟨k, _, rfl⟩ := mem_image.mp hC
      cases k with
      | inl u => exact mem_image.mpr ⟨u, mem_univ u, by simp⟩
      | inr i =>
        have hh := hd i
        simp only [fiber_part, card_part] at hcard
        omega
    · intro hC
      obtain ⟨u, _, rfl⟩ := mem_image.mp hC
      apply mem_filter.mpr
      refine ⟨mem_image.mpr ⟨Sum.inl u, mem_univ _, by simp⟩, by simp⟩
  unfold singletonCount
  rw [hset]
  have hinj : Function.Injective (fun u : Fin a => ({Sum.inl u} : Finset (Vertex a d))) := by
    intro u v h
    simpa using h
  rw [card_image_of_injective _ hinj]
  simp

/-- Every core vertex co-occurs with each vertex in some choice edge. -/
theorem core_cooccurs (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hd : ∀ i, 2 ≤ d i)
    (u : Fin a) (v : Vertex a d) :
    ∃ e ∈ (hypergraph a d ha hd).edges, Sum.inl u ∈ e ∧ v ∈ e := by
  let f₀ : (i : I) → Fin (d i) := fun i => ⟨0, by have := hd i; omega⟩
  have hcore : ∀ f : (i : I) → Fin (d i), Sum.inl u ∈ edge a d f := by
    intro f
    exact mem_union_left _ (mem_image.mpr ⟨u, mem_univ u, rfl⟩)
  cases v with
  | inl w =>
    refine ⟨edge a d f₀, mem_image.mpr ⟨f₀, mem_univ _, rfl⟩, hcore _, ?_⟩
    exact mem_union_left _ (mem_image.mpr ⟨w, mem_univ w, rfl⟩)
  | inr w =>
    obtain ⟨i, x⟩ := w
    let f := Function.update f₀ i x
    refine ⟨edge a d f, mem_image.mpr ⟨f, mem_univ _, rfl⟩, hcore _, ?_⟩
    apply mem_union_right
    exact mem_image.mpr ⟨i, mem_univ i, by simp [f]⟩

theorem optimal_core_singletons (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hd : ∀ i, 2 ≤ d i)
    (P : Finset (Finset (Vertex a d))) (hP : Panchromatic (hypergraph a d ha hd) P)
    (hcard : P.card = a + Fintype.card I) (u : Fin a) : {Sum.inl u} ∈ P := by
  apply forced_singleton hP (fun e he => hcard.trans (uniform a d ha hd e he).symm)
  exact core_cooccurs a d ha hd u

/-- The singleton parameter of the construction is proved from its definition. -/
theorem hasAlpha (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hd : ∀ i, 2 ≤ d i) :
    HasAlpha (hypergraph a d ha hd) (a + Fintype.card I) a := by
  constructor
  · exact ⟨_, natural_panchromatic a d ha hd, natural_card a d hd, natural_singletons a d hd⟩
  · intro P hP hcard
    let S : Finset (Finset (Vertex a d)) :=
      (univ : Finset (Fin a)).image (fun u => {Sum.inl u})
    have hsub : S ⊆ P.filter (fun C => C.card = 1) := by
      intro C hC
      obtain ⟨u, _, rfl⟩ := mem_image.mp hC
      exact mem_filter.mpr ⟨optimal_core_singletons a d ha hd P hP hcard u, by simp⟩
    have hinj : Function.Injective (fun u : Fin a => ({Sum.inl u} : Finset (Vertex a d))) := by
      intro u v h
      simpa using h
    have hs : S.card = a := by
      dsimp only [S]
      rw [card_image_of_injective _ hinj]
      simp
    have hh := card_le_card hsub
    simpa [hs, singletonCount] using hh


/-- The common core is exactly the a distinguished vertices. -/
theorem common_core (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hd : ∀ i, 2 ≤ d i)
    (v : Vertex a d) :
    (∀ e ∈ (hypergraph a d ha hd).edges, v ∈ e) ↔ v ∈ core a d := by
  rw [← singleton_transversal_iff, transversal_iff]
  constructor
  · intro h
    rcases h with ⟨u, hu⟩ | ⟨i, hi⟩
    · have hv := mem_singleton.mp hu
      exact (mem_core a d v).mpr ⟨u, hv.symm⟩
    · have hh := card_le_card hi
      have hdi := hd i
      simp only [card_part, card_singleton] at hh
      omega
  · intro hv
    obtain ⟨u, rfl⟩ := (mem_core a d v).mp hv
    exact Or.inl ⟨u, mem_singleton_self _⟩

/-- All prescribed parameters except the bipanchromatic number, without assumptions
about the construction's coloring behavior. -/
theorem parameters (a : ℕ) (d : I → ℕ) (ha : 0 < a) (hd : ∀ i, 2 ≤ d i) :
    Fintype.card (Vertex a d) = a + ∑ i, d i ∧
    HasPan (hypergraph a d ha hd) (a + Fintype.card I) ∧
    HasAlpha (hypergraph a d ha hd) (a + Fintype.card I) a ∧
    (∀ e ∈ (hypergraph a d ha hd).edges, e.card = a + Fintype.card I) := by
  exact ⟨card_vertices a d, hasPan a d ha hd, hasAlpha a d ha hd,
    fun e he => uniform a d ha hd e he⟩

end Model
end Bipanchromatic
