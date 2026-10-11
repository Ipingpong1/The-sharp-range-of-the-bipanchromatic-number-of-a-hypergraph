import SharpRange.Definitions

namespace Bipanchromatic
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def mapBlocks (e : V ≃ W) (P : Finset (Finset V)) : Finset (Finset W) := P.image (fun C => C.image e)

omit [Fintype V] [Fintype W] [DecidableEq V] in
lemma image_set_injective (e : V ≃ W) : Function.Injective (fun C : Finset V => C.image e) :=
  Finset.image_injective e.injective

omit [Fintype V] [Fintype W] [DecidableEq V] in
@[simp] lemma mapBlocks_card (e : V ≃ W) (P : Finset (Finset V)) : (mapBlocks e P).card = P.card :=
  card_image_of_injective _ (image_set_injective e)

omit [Fintype V] [Fintype W] in
@[simp] lemma mapBlocks_inverse (e : V ≃ W) (P : Finset (Finset V)) :
    mapBlocks e.symm (mapBlocks e P) = P := by
  simp [mapBlocks, image_image, Function.comp_def]

def relabel (H : Hypergraph V) (e : V ≃ W) : Hypergraph W where
  edges := mapBlocks e H.edges
  nonempty_edges := H.nonempty_edges.image _
  nonempty_edge := by
    intro D hD
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
    exact (H.nonempty_edge C hC).image _

lemma hypergraph_ext {H G : Hypergraph V} (h : H.edges = G.edges) : H = G := by
  cases H
  cases G
  cases h
  rfl

@[simp] lemma relabel_inverse (H : Hypergraph V) (e : V ≃ W) : relabel (relabel H e) e.symm = H := by
  apply hypergraph_ext
  exact mapBlocks_inverse e H.edges

lemma map_partition (e : V ≃ W) (P : Finset (Finset V)) (hP : Partition P) : Partition (mapBlocks e P) := by
  constructor
  · intro D hD
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
    exact (hP.nonempty C hC).image _
  · intro D hD F hF hDF
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hD
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hF
    have hBC : B ≠ C := fun h => hDF (congrArg (fun C : Finset V => C.image e) h)
    apply disjoint_left.mpr
    intro w hwB hwC
    obtain ⟨v, hvB, rfl⟩ := mem_image.mp hwB
    obtain ⟨u, huC, huv⟩ := mem_image.mp hwC
    have huve := e.injective huv
    exact (disjoint_left.mp (hP.disjoint hB hC hBC)) hvB (huve ▸ huC)
  · apply Finset.ext
    intro w
    simp only [mem_univ, iff_true]
    have hv : e.symm w ∈ P.biUnion id := by rw [hP.cover]; exact mem_univ _
    obtain ⟨C, hC, hvC⟩ := mem_biUnion.mp hv
    exact mem_biUnion.mpr ⟨C.image e, mem_image.mpr ⟨C, hC, rfl⟩,
      mem_image.mpr ⟨e.symm w, hvC, e.apply_symm_apply w⟩⟩

lemma map_transversal (H : Hypergraph V) (e : V ≃ W) (C : Finset V) (hC : Transversal H C) :
    Transversal (relabel H e) (C.image e) := by
  intro D hD
  obtain ⟨B, hB, rfl⟩ := mem_image.mp hD
  obtain ⟨v, hv⟩ := hC B hB
  obtain ⟨hvC, hvB⟩ := mem_inter.mp hv
  exact ⟨e v, mem_inter.mpr ⟨mem_image.mpr ⟨v, hvC, rfl⟩, mem_image.mpr ⟨v, hvB, rfl⟩⟩⟩

lemma map_panchromatic (H : Hypergraph V) (e : V ≃ W) (P : Finset (Finset V))
    (hP : Panchromatic H P) : Panchromatic (relabel H e) (mapBlocks e P) := by
  refine ⟨map_partition e P hP.1, ?_⟩
  intro D hD
  obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
  exact map_transversal H e C (hP.2 C hC)

lemma pull_panchromatic (H : Hypergraph V) (e : V ≃ W) (Q : Finset (Finset W))
    (hQ : Panchromatic (relabel H e) Q) : Panchromatic H (mapBlocks e.symm Q) := by
  simpa using map_panchromatic (relabel H e) e.symm Q hQ

lemma map_bicoloring (H : Hypergraph V) (e : V ≃ W) (P : Finset (Finset V))
    (hP : Bicoloring H P) : Bicoloring (relabel H e) (mapBlocks e P) := by
  refine ⟨map_panchromatic H e P hP.1, ?_⟩
  intro D hD
  obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
  rw [card_image_of_injective _ e.injective]
  exact hP.2 C hC

lemma pull_bicoloring (H : Hypergraph V) (e : V ≃ W) (Q : Finset (Finset W))
    (hQ : Bicoloring (relabel H e) Q) : Bicoloring H (mapBlocks e.symm Q) := by
  simpa using map_bicoloring (relabel H e) e.symm Q hQ

omit [Fintype V] [Fintype W] [DecidableEq V] in
@[simp] lemma map_singletonCount (e : V ≃ W) (P : Finset (Finset V)) :
    singletonCount (mapBlocks e P) = singletonCount P := by
  unfold singletonCount mapBlocks
  rw [filter_image]
  simp only [card_image_of_injective _ e.injective]
  rw [card_image_of_injective _ (image_set_injective e)]

lemma relabel_hasPan (H : Hypergraph V) (e : V ≃ W) (p : ℕ) (hp : HasPan H p) : HasPan (relabel H e) p := by
  constructor
  · obtain ⟨P, hP, hc⟩ := hp.1
    exact ⟨mapBlocks e P, map_panchromatic H e P hP, (mapBlocks_card e P).trans hc⟩
  · intro Q hQ
    have hh := hp.2 _ (pull_panchromatic H e Q hQ)
    simpa using hh

lemma relabel_hasAlpha (H : Hypergraph V) (e : V ≃ W) (p a : ℕ) (ha : HasAlpha H p a) :
    HasAlpha (relabel H e) p a := by
  constructor
  · obtain ⟨P, hP, hc, hs⟩ := ha.1
    exact ⟨mapBlocks e P, map_panchromatic H e P hP, (mapBlocks_card e P).trans hc,
      (map_singletonCount e P).trans hs⟩
  · intro Q hQ hc
    have hh := ha.2 _ (pull_panchromatic H e Q hQ) (by simpa using hc)
    simpa using hh

lemma relabel_hasBipan (H : Hypergraph V) (e : V ≃ W) (b : ℕ) (hb : HasBipan H b) : HasBipan (relabel H e) b := by
  constructor
  · obtain ⟨P, hP, hc⟩ := hb.1
    exact ⟨mapBlocks e P, map_bicoloring H e P hP, (mapBlocks_card e P).trans hc⟩
  · intro Q hQ
    have hh := hb.2 _ (pull_bicoloring H e Q hQ)
    simpa using hh

end Bipanchromatic

namespace Bipanchromatic
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

noncomputable def commonCore (H : Hypergraph V) : Finset V := by
  classical
  exact univ.filter (fun v => ∀ e ∈ H.edges, v ∈ e)

@[simp] lemma mem_commonCore (H : Hypergraph V) (v : V) :
    v ∈ commonCore H ↔ ∀ e ∈ H.edges, v ∈ e := by
  classical
  simp [commonCore]

lemma relabel_commonCore (H : Hypergraph V) (e : V ≃ W) :
    commonCore (relabel H e) = (commonCore H).image e := by
  classical
  apply Finset.ext
  intro w
  constructor
  · intro hw
    have hw' := (mem_commonCore (relabel H e) w).mp hw
    refine mem_image.mpr ⟨e.symm w, (mem_commonCore H _).mpr ?_, e.apply_symm_apply w⟩
    intro D hD
    have hh := hw' (D.image e) (mem_image.mpr ⟨D, hD, rfl⟩)
    obtain ⟨v, hv, hvw⟩ := mem_image.mp hh
    have hv' : v = e.symm w := by simpa using congrArg e.symm hvw
    exact hv' ▸ hv
  · intro hw
    obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
    apply (mem_commonCore _ _).mpr
    intro D hD
    obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
    exact mem_image.mpr ⟨v, (mem_commonCore H v).mp hv C hC, rfl⟩

lemma relabel_uniform (H : Hypergraph V) (e : V ≃ W) (p : ℕ)
    (hu : ∀ D ∈ H.edges, D.card = p) : ∀ D ∈ (relabel H e).edges, D.card = p := by
  intro D hD
  obtain ⟨C, hC, rfl⟩ := mem_image.mp hD
  rw [card_image_of_injective _ e.injective]
  exact hu C hC

end Bipanchromatic
