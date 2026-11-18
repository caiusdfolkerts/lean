module

public import Papers.GraphicalZonotopes.BookPrincipal
public import Papers.GraphicalZonotopes.SmallCliqueDimension
public import Papers.GraphicalZonotopes.PartialThreeTreeSupport
public import Papers.GraphicalZonotopes.SetFunctionEmbeddingDirections

/-! # The full dimension spectrum and prescribed supports of clique books

This file proves both assertions of Corollary 7.11. The coordinate-support
predicate means literal constancy of every outside coordinate. It does not
require every allowed edge inside the support to be an actual direction.

The key bridge restricts any such polytope to the induced coordinate graph.
It is proved from lower-support reconstruction and exposed edges; it is not
an additional hypothesis on the summand.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical BigOperators Pointwise

namespace GraphicalZonotopes.BookSpectrum
open Finset SetFunctionEmbedding

section CoordinateSupport

variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]

/-- Every coordinate outside `U` is constant on the actual polytope. The
constant can depend on the coordinate and need not be zero. -/
def FixesOutside (Q : Set (V → ℝ)) (U : Finset V) : Prop :=
  ∀ u, u ∉ U → ∃ c : ℝ, ∀ x ∈ Q, x u = c

/-- Ordinary polytopal indecomposability, dimension `|U| - 1`, and literal
fixed outside coordinates, all in the original ambient coordinate space. -/
def HasFullSupportedSummand (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∃ Q : Set (V → ℝ), IsFinitePolytope Q ∧
    PolytopalMinkowskiIndecomposable Q ∧
    IsWeakMinkowskiSummand Q (graphicalZonotope G) ∧
    Module.finrank ℝ (vectorSpan ℝ Q) = U.card - 1 ∧ FixesOutside Q U

theorem FixesOutside.no_root_edge {Q : Set (V → ℝ)} {U : Finset V}
    (hfix : FixesOutside Q U) {u v : V} (hu : u ∉ U) :
    ¬ ActualRootEdge Q u v := by
  rintro ⟨huv, p, q, ⟨hpq, l, a, hl, hface⟩, c, hc, hdir⟩
  obtain ⟨b, hb⟩ := hfix u hu
  have hp : p ∈ Q := by
    have hm := left_mem_segment ℝ p q
    rw [← hface] at hm
    exact hm.1
  have hq : q ∈ Q := by
    have hm := right_mem_segment ℝ p q
    rw [← hface] at hm
    exact hm.1
  have he := congrFun hdir u
  apply hc
  simpa [Pi.sub_apply, Pi.smul_apply, basisVector, Pi.single_apply,
    huv, Ne.symm huv, hb p hp, hb q hq] using he.symm

theorem card_eq_of_embedding_range (e : W ↪ V) {U : Finset V}
    (hrange : ∀ v, v ∈ U ↔ v ∈ Set.range e) : U.card = Fintype.card W := by
  have he : univ.map e = U := by
    ext v
    simpa only [mem_map, mem_univ, true_and, Set.mem_range] using (hrange v).symm
  rw [← he, card_map, card_univ]

/-- Removing the constant coordinates gives precisely the ordinary
full-dimensional summand problem on the induced coordinate graph. -/
theorem supported_iff_embedding (e : W ↪ V) {G : SimpleGraph V} {U : Finset V}
    (hU : 2 ≤ U.card) (hrange : ∀ v, v ∈ U ↔ v ∈ Set.range e) :
    HasFullSupportedSummand G U ↔ SupportsFullIndecomposable (G.comap e) := by
  have hcard := card_eq_of_embedding_range e hrange
  constructor
  · rintro ⟨Q, hQ, hi, hw, hd, hfix⟩
    have hic := (weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi
    obtain ⟨z, hzs, hze, hdim, hactual⟩ := weak_summand_normalized_function hQ hic hw
    have hext : ExtremeSupermodular z.1 := by
      rcases hze with hz | hz
      · rw [hz, basePolytope_zero, _root_.vectorSpan_singleton, finrank_bot] at hdim
        omega
      · exact hz
    have hrec : extend e (restrict e z.1) = z.1 := by
      apply reconstruct_of_insert_absent e z.1
      intro u hu
      apply insert_absent_of_zero_deltas z.2.1 u
      intro v huv S huS hvS
      by_contra hdelta
      have hedge := (actualRootEdge_iff_nonzero_delta z.2.1.1 hzs u v).mpr
        ⟨huv, S, huS, hvS, hdelta⟩
      have hedgeQ : ActualRootEdge Q u v := by
        change (actualDirectionGraph Q).Adj u v
        rw [hactual]
        exact hedge
      exact hfix.no_root_edge (fun hm => hu ((hrange u).mp hm)) hedgeQ
    have hf := extreme_restrict_of_reconstruction e hext hrec
    have hgp : IsGeneralizedPermutahedron (basePolytope (restrict e z.1)) :=
      ⟨restrict e z.1, hf.1.1, hf.2.1, rfl⟩
    refine ⟨basePolytope (restrict e z.1), hgp.finitePolytope,
      hf.minkowskiIndecomposable, ?_, ?_⟩
    · have he := finrank_vectorSpan_extend e (restrict_translationNormalized e z.2.1)
      rw [hrec] at he
      change Module.finrank ℝ (vectorSpan ℝ (basePolytope (restrict e z.1))) =
        Fintype.card W - 1
      rw [← hcard]
      exact he.symm.trans (hdim.symm.trans hd)
    · exact (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr
        (restrict_graphical e z.2.2)
  · rintro ⟨Q, hQ, hi, hd, hw⟩
    obtain ⟨z, hzs, hze, hdim⟩ := weak_summand_extreme_or_zero hQ hi hw
    have hd' : Module.finrank ℝ (vectorSpan ℝ Q) = U.card - 1 := by
      simpa only [FullDimension, ← hcard] using hd
    have hext : ExtremeSupermodular z.1 := by
      rcases hze with hz | hz
      · rw [hz, basePolytope_zero, _root_.vectorSpan_singleton, finrank_bot] at hdim
        omega
      · exact hz
    have hf := extend_extreme e hext
    have hgp : IsGeneralizedPermutahedron (basePolytope (extend e z.1)) :=
      ⟨extend e z.1, hf.1.1, hf.2.1, rfl⟩
    refine ⟨basePolytope (extend e z.1), hgp.finitePolytope,
      (minkowskiIndecomposable_iff_polytopal hgp).mp hf.minkowskiIndecomposable,
      (isWeakMinkowskiSummand_graphical_iff hf.1.1 hf.2.1).mpr
        (extend_graphical e z.2.2), ?_, ?_⟩
    · rw [finrank_vectorSpan_extend e z.2.1]
      exact hdim.symm.trans hd'
    · intro u hu
      refine ⟨0, ?_⟩
      intro x hx
      rw [basePolytope_extend e z.2.1] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact pushVector_outside e y u (fun hm => hu ((hrange u).mpr hm))

end CoordinateSupport

abbrev Vertex (s k : ℕ) := Fin s ⊕ Fin k

local instance vertexOrder (s k : ℕ) : LinearOrder (Vertex s k) :=
  inferInstanceAs (LinearOrder (Fin s ⊕ₗ Fin k))

local instance vertexDecidableEq (s k : ℕ) : DecidableEq (Vertex s k) :=
  (vertexOrder s k).toDecidableEq

/-- The prescribed hubs, counted in the original book. -/
def hubs {s k : ℕ} (U : Finset (Vertex s k)) : Finset (Fin s) :=
  univ.filter (fun i => Sum.inl i ∈ U)

/-- The prescribed outer vertices, counted in the original book. -/
def outers {s k : ℕ} (U : Finset (Vertex s k)) : Finset (Fin k) :=
  univ.filter (fun j => Sum.inr j ∈ U)

private def enumerate {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    Fin S.card ≃ S :=
  (finCongr (Fintype.card_coe S).symm).trans (Fintype.equivFin S).symm

private def prescribedEmbedding {s k : ℕ} (U : Finset (Vertex s k)) :
    Vertex (hubs U).card (outers U).card ↪ Vertex s k :=
  Function.Embedding.sumMap
    ((enumerate (hubs U)).toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩)
    ((enumerate (outers U)).toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩)

private theorem prescribedEmbedding_range {s k : ℕ} (U : Finset (Vertex s k))
    (v : Vertex s k) : v ∈ U ↔ v ∈ Set.range (prescribedEmbedding U) := by
  cases v with
  | inl i =>
    constructor
    · intro hi
      have hm : i ∈ hubs U := by simpa [hubs] using hi
      refine ⟨Sum.inl ((enumerate (hubs U)).symm ⟨i, hm⟩), ?_⟩
      simp [prescribedEmbedding]
    · rintro ⟨v, hv⟩
      cases v with
      | inl a =>
        have he : ((enumerate (hubs U)) a).1 = i := Sum.inl_injective hv
        have hm := ((enumerate (hubs U)) a).2
        rw [he] at hm
        simpa [hubs] using hm
      | inr b => exact (Sum.inr_ne_inl hv).elim
  | inr j =>
    constructor
    · intro hj
      have hm : j ∈ outers U := by simpa [outers] using hj
      refine ⟨Sum.inr ((enumerate (outers U)).symm ⟨j, hm⟩), ?_⟩
      simp [prescribedEmbedding]
    · rintro ⟨v, hv⟩
      cases v with
      | inl a => exact (Sum.inl_ne_inr hv).elim
      | inr b =>
        have he : ((enumerate (outers U)) b).1 = j := Sum.inr_injective hv
        have hm := ((enumerate (outers U)) b).2
        rw [he] at hm
        simpa [outers] using hm

private theorem prescribedEmbedding_graph {s k : ℕ} (U : Finset (Vertex s k)) :
    (cliqueBook s k).comap (prescribedEmbedding U) =
      cliqueBook (hubs U).card (outers U).card := by
  ext u v
  change (prescribedEmbedding U u ≠ prescribedEmbedding U v ∧
    ((prescribedEmbedding U u).isLeft ∨ (prescribedEmbedding U v).isLeft)) ↔
    (u ≠ v ∧ (u.isLeft ∨ v.isLeft))
  rw [(prescribedEmbedding U).injective.ne_iff]
  cases u <;> cases v <;> rfl

theorem prescribed_card {s k : ℕ} (U : Finset (Vertex s k)) :
    U.card = (hubs U).card + (outers U).card := by
  simpa only [Fintype.card_sum, Fintype.card_fin] using
    card_eq_of_embedding_range (prescribedEmbedding U) (prescribedEmbedding_range U)

private theorem book_complete_support {h t : ℕ} (hcard : 2 ≤ h + t) (ht : t ≤ 1) :
    SupportsFullIndecomposable (cliqueBook h t) := by
  have hcl : (cliqueBook h t).IsClique (univ : Finset (Vertex h t)) := by
    intro u hu v hv huv
    refine ⟨huv, ?_⟩
    cases u with
    | inl i => exact Or.inl rfl
    | inr i =>
      cases v with
      | inl j => exact Or.inr rfl
      | inr j =>
        have he : i = j := Fin.ext (by omega)
        exact (huv (congrArg Sum.inr he)).elim
  obtain ⟨Q, hQ, hi, hw, hd⟩ := clique_simplex_witness
    (G := cliqueBook h t) (C := univ)
    (by simpa only [card_univ, Fintype.card_sum, Fintype.card_fin] using hcard) hcl
  exact ⟨Q, hQ.finitePolytope, hi, by simpa only [FullDimension, card_univ] using hd, hw⟩

private theorem one_hub_triangleFree (t : ℕ) : (cliqueBook 1 t).CliqueFree 3 := by
  have unique : ∀ u v : Vertex 1 t, u.isLeft → v.isLeft → u = v := by
    intro u v hu hv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact congrArg Sum.inl (Subsingleton.elim i j)
      | inr j => simp at hv
    | inr i => simp at hu
  intro C hC
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := card_eq_three.mp hC.card_eq
  have hab := hC.isClique (by simp) (by simp) huv
  have hac := hC.isClique (by simp) (by simp) huw
  have hbc := hC.isClique (by simp) (by simp) hvw
  have hnab : ¬ (u.isLeft ∧ v.isLeft) := fun hh => huv (unique u v hh.1 hh.2)
  have hnac : ¬ (u.isLeft ∧ w.isLeft) := fun hh => huw (unique u w hh.1 hh.2)
  have hnbc : ¬ (v.isLeft ∧ w.isLeft) := fun hh => hvw (unique v w hh.1 hh.2)
  have hab' := hab.2
  have hac' := hac.2
  have hbc' := hbc.2
  tauto

/-- The exact full-dimensional classification also at zero and one hub.
Only the nontrivial-coordinate assumption is imposed. -/
theorem book_full_criterion (h t : ℕ) (hcard : 2 ≤ h + t) :
    SupportsFullIndecomposable (cliqueBook h t) ↔
      t = 0 ∨ (h = 1 ∧ t = 1) ∨ (2 ≤ h ∧ 1 ≤ t ∧ t ≤ cliqueCapacity h) := by
  constructor
  · intro hsupp
    by_cases ht : t = 0
    · exact Or.inl ht
    have htpos : 1 ≤ t := by omega
    by_cases hh : h = 0
    · subst h
      obtain ⟨Q, hQ, hi, hd, hw⟩ := hsupp
      have hz : maximumIndecomposableDimension (cliqueBook 0 t) = 0 :=
        edgeless_maximum_dimension (by
          intro u v hadj
          cases u with
          | inl i => exact Fin.elim0 i
          | inr i =>
            cases v with
            | inl j => exact Fin.elim0 j
            | inr j => simpa [cliqueBook] using hadj)
      have hb := dimension_le_maximum hQ hi hw
      rw [hz] at hb
      simp only [FullDimension, Fintype.card_sum, Fintype.card_fin] at hd
      omega
    by_cases hh1 : h = 1
    · subst h
      obtain ⟨Q, hQ, hi, hd, hw⟩ := hsupp
      have hb := triangleFree_summand_dimension_le_one (one_hub_triangleFree t) hQ hi hw
      simp only [FullDimension, Fintype.card_sum, Fintype.card_fin] at hd
      exact Or.inr (Or.inl ⟨rfl, by omega⟩)
    · have hh2 : 2 ≤ h := by omega
      exact Or.inr (Or.inr ⟨hh2, htpos,
        (clique_book_classification h t hh2 htpos).2.1.mp hsupp⟩)
  · rintro (ht | ⟨hh, ht⟩ | ⟨hh, ht, hcap⟩)
    · exact book_complete_support hcard (by omega)
    · exact book_complete_support hcard (by omega)
    · exact (clique_book_classification h t hh ht).2.1.mpr hcap

/-- Corollary 7.11, prescribed-coordinate form. The set is arbitrary, its
size may be two or three, and all zero-hub and one-hub cases are retained. -/
theorem prescribed_coordinate_criterion {s k : ℕ} (U : Finset (Vertex s k))
    (hU : 2 ≤ U.card) :
    HasFullSupportedSummand (cliqueBook s k) U ↔
      (outers U).card = 0 ∨
      ((hubs U).card = 1 ∧ (outers U).card = 1) ∨
      (2 ≤ (hubs U).card ∧ 1 ≤ (outers U).card ∧
        (outers U).card ≤ cliqueCapacity (hubs U).card) := by
  rw [supported_iff_embedding (prescribedEmbedding U) hU (prescribedEmbedding_range U),
    prescribedEmbedding_graph]
  exact book_full_criterion _ _ (by rwa [← prescribed_card U])

/-- Every positive dimension through the sharp bound has a lattice witness. -/
theorem lattice_dimension_spectrum (s k d : ℕ) (hs : 2 ≤ s) (hk : 1 ≤ k)
    (hd : 1 ≤ d) (hmax : d ≤ min (s + k - 1) (s + cliqueCapacity s - 1)) :
    ∃ Q : Set (Vertex s k → ℝ), LatticePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d := by
  by_cases hds : d ≤ s
  · let j : Fin k := ⟨0, by omega⟩
    let C : Finset (Vertex s k) := insert (Sum.inr j) (univ.image Sum.inl)
    have hC : C.card = s + 1 := by
      simp [C, card_image_of_injective _ Sum.inl_injective]
    have hcl : (cliqueBook s k).IsClique C := by
      intro u hu v hv huv
      refine ⟨huv, ?_⟩
      rcases mem_insert.mp hu with rfl | hu
      · rcases mem_insert.mp hv with rfl | hv
        · exact (huv rfl).elim
        · obtain ⟨i, _, rfl⟩ := mem_image.mp hv
          exact Or.inr rfl
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hu
        exact Or.inl rfl
    obtain ⟨D, hDC, hD⟩ := exists_subset_card_eq (s := C) (n := d + 1) (by omega)
    obtain ⟨Q, hQ, hi, hw, hdim⟩ := clique_simplex_witness (by omega : 2 ≤ D.card)
      (fun u hu v hv huv => hcl (hDC hu) (hDC hv) huv)
    exact ⟨Q, hQ, (weakSummand_indecomposable_iff_polytopal hQ.finitePolytope hw).mp hi,
      hw, by omega⟩
  · let t := d - s + 1
    have hst : s + t - 1 = d := by
      change s + (d - s + 1) - 1 = d
      omega
    have ht : 1 ≤ t := by omega
    have htk : t ≤ k := by omega
    have htcap : t ≤ cliqueCapacity s := by omega
    have hatt := (book_lattice_full s t hs ht htcap).embed
      (bookOuterEmbedding s htk) (bookOuterEmbedding_edges s htk)
    obtain ⟨f, hn, hint, hext, hg, hdim, hb⟩ := hatt
    have hgp : IsGeneralizedPermutahedron (basePolytope f) := ⟨f, hn.1, hext.2.1, rfl⟩
    exact ⟨basePolytope f, hint.basePolytope hn.1 hext.2.1,
      (minkowskiIndecomposable_iff_polytopal hgp).mp hext.minkowskiIndecomposable,
      (isWeakMinkowskiSummand_graphical_iff hn.1 hext.2.1).mpr hg, hdim.trans hst⟩

/-- Corollary 7.11, full positive spectrum, with necessity for every ordinary
polytopal weak summand and sufficiency for every integer in the interval. -/
theorem positive_dimension_spectrum (s k d : ℕ) (hs : 2 ≤ s) (hk : 1 ≤ k)
    (hd : 1 ≤ d) :
    (∃ Q : Set (Vertex s k → ℝ), IsFinitePolytope Q ∧
      PolytopalMinkowskiIndecomposable Q ∧
      IsWeakMinkowskiSummand Q (graphicalZonotope (cliqueBook s k)) ∧
      Module.finrank ℝ (vectorSpan ℝ Q) = d) ↔
      d ≤ min (s + k - 1) (s + cliqueCapacity s - 1) := by
  constructor
  · rintro ⟨Q, hQ, hi, hw, hdim⟩
    rw [← hdim]
    exact BookDimension.actual_summand_dimension_bound s k hs hQ
      ((weakSummand_indecomposable_iff_polytopal hQ hw).mpr hi) hw
  · intro hmax
    obtain ⟨Q, hQ, hi, hw, hdim⟩ := lattice_dimension_spectrum s k d hs hk hd hmax
    exact ⟨Q, hQ.finitePolytope, hi, hw, hdim⟩

end GraphicalZonotopes.BookSpectrum
