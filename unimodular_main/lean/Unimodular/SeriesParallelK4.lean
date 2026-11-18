module

public import Unimodular.SeriesParallelNecessity

@[expose] public section

open scoped BigOperators Matroid
open Set

namespace Unimodular.SeriesParallel

noncomputable section

/-- The six directed edges of the genuine complete graph on the four vertices
`none, some 0, some 1, some 2`. -/
def K4Network : RootedNetwork 3 6 where
  source := ![some 0, some 1, some 2, some 0, some 0, some 1]
  target := ![none, none, none, some 1, some 2, some 2]

/-- Every pair of distinct vertices is joined by one of the displayed edges. -/
theorem K4Network_complete : ∀ p q : Option (Fin 3), p ≠ q →
    ∃ e : Fin 6, (K4Network.source e = p ∧ K4Network.target e = q) ∨
      (K4Network.source e = q ∧ K4Network.target e = p) := by decide

theorem K4Network_loopless : ∀ e, K4Network.source e ≠ K4Network.target e := by decide

/-- The ordinary cycle matroid of this complete graph, represented by its
actual six directed incidence columns. -/
def K4Matroid : Matroid (Fin 6) :=
  VectorMatroid.ofFamily (K := ℝ) (fun e => embed (RankThree.baseRoot e))

theorem K4Matroid_eq_cycleMatroid : K4Matroid = K4Network.cycleMatroid := by
  unfold K4Matroid RootedNetwork.cycleMatroid
  congr 1
  funext e
  fin_cases e <;> ext i <;> fin_cases i <;>
    simp [K4Matroid, RootedNetwork.cycleMatroid, K4Network, Graphic.vertex,
      RankThree.baseRoot, embed, Pi.basisFun_apply, Pi.single_apply]

@[simp] theorem K4Matroid_ground : K4Matroid.E = Set.univ := rfl

private theorem pair_completing_basis : ∀ i j : Fin 6, i ≠ j → ∃ k : Fin 6,
    detThree (RankThree.baseRoot i) (RankThree.baseRoot j) (RankThree.baseRoot k) ≠ 0 := by
  decide

set_option maxHeartbeats 0 in
private theorem pair_complement_basis : ∀ i j : Fin 6, ∃ a b c : Fin 6,
    (a ≠ i ∧ a ≠ j) ∧ (b ≠ i ∧ b ≠ j) ∧ (c ≠ i ∧ c ≠ j) ∧
      detThree (RankThree.baseRoot a) (RankThree.baseRoot b) (RankThree.baseRoot c) ≠ 0 := by
  decide

private theorem root_triple_is_basis (a : Fin 3 → Fin 6)
    (hd : detThree (RankThree.baseRoot (a 0)) (RankThree.baseRoot (a 1))
      (RankThree.baseRoot (a 2)) ≠ 0) :
    LinearIndependent ℝ (fun i => embed (RankThree.baseRoot (a i))) ∧
      Submodule.span ℝ (Set.range (fun i => embed (RankThree.baseRoot (a i)))) = ⊤ := by
  have hdet : (Pi.basisFun ℝ (Fin 3)).det (fun i => embed (RankThree.baseRoot (a i))) ≠ 0 := by
    have heq : (Pi.basisFun ℝ (Fin 3)).det (fun i => embed (RankThree.baseRoot (a i))) =
        (detThree (RankThree.baseRoot (a 0)) (RankThree.baseRoot (a 1))
          (RankThree.baseRoot (a 2)) : ℝ) := by
      have hcoord : (Pi.basisFun ℝ (Fin 3)).det
          (fun i => embed (RankThree.baseRoot (a i))) =
          (Matrix.of (fun i => embed (RankThree.baseRoot (a i)))).det := by
        rw [Module.Basis.det_apply, ← Matrix.det_transpose]
        congr 1 <;> ext i j <;> simp [Module.Basis.toMatrix_apply]
      rw [hcoord]
      simp [Matrix.det_fin_three, detThree, embed]
      <;> ring
    rw [heq]
    exact_mod_cast hd
  exact (Pi.basisFun ℝ (Fin 3)).is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr hdet)

theorem K4Matroid_pair_indep (i j : Fin 6) (hij : i ≠ j) : K4Matroid.Indep {i, j} := by
  obtain ⟨k, hk⟩ := pair_completing_basis i j hij
  let a : Fin 3 → Fin 6 := ![i, j, k]
  have hli := (root_triple_is_basis a hk).1
  have hai : Function.Injective a := by
    intro r s h
    apply hli.injective
    exact congrArg (fun t => embed (RankThree.baseRoot t)) h
  have hlinear : LinearIndepOn ℝ (fun t => embed (RankThree.baseRoot t)) (Set.range a) :=
    (linearIndepOn_range_iff hai _).mpr hli
  apply (VectorMatroid.ofFamily_indep _ _).mpr
  apply hlinear.mono
  intro t ht
  rcases ht with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- Removing any two edges of K4 leaves a spanning configuration. The finite
certificate supplies an actual nonsingular three-column basis. -/
theorem K4Matroid_pair_complement_span (i j : Fin 6) :
    Submodule.span ℝ ((fun t => embed (RankThree.baseRoot t)) '' ({i, j} : Set (Fin 6))ᶜ) = ⊤ := by
  obtain ⟨a, b, c, ha, hb, hc, hd⟩ := pair_complement_basis i j
  have hspan := (root_triple_is_basis (![a, b, c]) hd).2
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro x ⟨k, rfl⟩
  refine ⟨![a, b, c] k, ?_, rfl⟩
  fin_cases k <;> simp [ha, hb, hc]

theorem K4Matroid_pair_complement_spanning (i j : Fin 6) :
    K4Matroid.Spanning ({i, j} : Set (Fin 6))ᶜ := by
  apply (VectorMatroid.ofFamily_spanning_iff _ _).mpr
  have hspan := K4Matroid_pair_complement_span i j
  have hfull : Submodule.span ℝ (Set.range (fun t => embed (RankThree.baseRoot t))) = ⊤ := by
    apply top_unique
    rw [← hspan]
    exact Submodule.span_mono (Set.image_subset_range _ _)
  rw [hspan, hfull]

theorem K4Matroid_not_loop (i : Fin 6) : ¬K4Matroid.IsLoop i := by
  rw [K4Matroid, VectorMatroid.ofFamily_isLoop_iff]
  intro hz
  have hbase : RankThree.baseRoot i = 0 := by
    funext j
    have hj := congrFun hz j
    change (RankThree.baseRoot i j : ℝ) = 0 at hj
    exact Int.cast_eq_zero.mp hj
  have h := RankThree.root_ne_zero (i, false)
  apply h
  simpa [RankThree.root] using hbase

theorem K4Matroid_not_coloop (i : Fin 6) : ¬K4Matroid.IsColoop i := by
  rw [K4Matroid, VectorMatroid.ofFamily_isColoop_iff, not_not]
  have hspan : Submodule.span ℝ ((fun t => embed (RankThree.baseRoot t)) ''
      ({i} : Set (Fin 6))ᶜ) = ⊤ := by
    simpa using K4Matroid_pair_complement_span i i
  rw [hspan]
  trivial

theorem K4Matroid_not_pair_circuit (i j : Fin 6) (hij : i ≠ j) :
    ¬K4Matroid.IsCircuit {i, j} := fun h => h.not_indep (K4Matroid_pair_indep i j hij)

theorem K4Matroid_not_pair_cocircuit (i j : Fin 6) : ¬K4Matroid.IsCocircuit {i, j} := by
  intro h
  have hn := (Matroid.isCocircuit_iff_minimal_compl_nonspanning.mp h).prop
  rw [K4Matroid_ground, ← Set.compl_eq_univ_sdiff] at hn
  exact hn (K4Matroid_pair_complement_spanning i j)

/-- Every nonempty ordinary series--parallel matroid has a final elementary
reduction, with the usual circuit and cocircuit meanings. -/
theorem GroundSeriesParallel.exists_reduction {E : Type*} {M : Matroid E}
    (h : GroundSeriesParallel M) (hne : M.E.Nonempty) :
    (∃ e, M.IsLoop e) ∨ (∃ e, M.IsColoop e) ∨
      ∃ e f, e ≠ f ∧ (M.IsCircuit {e, f} ∨ M.IsCocircuit {e, f}) := by
  cases h with
  | empty M hE => exact False.elim (by simpa [hE] using hne)
  | @addLoop M e h he => exact Or.inl ⟨e, he⟩
  | @addColoop M e h he => exact Or.inr (Or.inl ⟨e, he⟩)
  | @parallel M e f h hef hp => exact Or.inr (Or.inr ⟨e, f, hef, Or.inl hp⟩)
  | @series M e f h hef hp => exact Or.inr (Or.inr ⟨e, f, hef, Or.inr hp⟩)

/-- No injective relabeling of the ordinary K4 cycle matroid is series--parallel.
The argument uses its actual independent sets and cocircuits. -/
theorem K4Matroid_not_seriesParallel_map {E : Type*} (f : Fin 6 ↪ E) :
    ¬GroundSeriesParallel (K4Matroid.mapEmbedding f) := by
  intro h
  have hground : (K4Matroid.mapEmbedding f).E = Set.range f := by simp
  have hne : (K4Matroid.mapEmbedding f).E.Nonempty := by
    rw [hground]
    exact ⟨f 0, 0, rfl⟩
  rcases h.exists_reduction hne with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, g, heg, hpair⟩
  · obtain ⟨i, rfl⟩ := hground ▸ he.mem_ground
    exact K4Matroid_not_loop i ((EmbeddingTransport.map_isLoop K4Matroid f i).mp he)
  · obtain ⟨i, rfl⟩ := hground ▸ he.mem_ground
    exact K4Matroid_not_coloop i ((EmbeddingTransport.map_isColoop K4Matroid f i).mp he)
  · have hpground : ({e, g} : Set E) ⊆ (K4Matroid.mapEmbedding f).E := by
      rcases hpair with hp | hp
      · exact hp.subset_ground
      · exact hp.subset_ground
    obtain ⟨i, rfl⟩ := hground ▸ hpground (by simp : e ∈ ({e, g} : Set E))
    obtain ⟨j, rfl⟩ := hground ▸ hpground (by simp : g ∈ ({f i, g} : Set E))
    have hij : i ≠ j := fun h => heg (congrArg f h)
    rcases hpair with hp | hp
    · exact K4Matroid_not_pair_circuit i j hij
        ((EmbeddingTransport.map_image_circuit K4Matroid f {i, j}).mp
          (by simpa only [Set.image_pair] using hp))
    · exact K4Matroid_not_pair_cocircuit i j
        ((EmbeddingTransport.map_image_cocircuit K4Matroid f {i, j}).mp
          (by simpa only [Set.image_pair] using hp))

/-- The usual labeled meaning of an M(K4) minor: an injective labeling of the
six edges realizes that actual cycle matroid as an ordinary matroid minor. -/
def HasK4Minor {E : Type*} (M : Matroid E) : Prop :=
  ∃ f : Fin 6 ↪ E, K4Matroid.mapEmbedding f ≤m M

/-- Standard series--parallel matroids exclude M(K4) in all ranks. This follows
from ordinary minor closure and the proved exact K4 obstruction. -/
theorem GroundSeriesParallel.no_K4_minor {E : Type*} {M : Matroid E}
    (h : GroundSeriesParallel M) : ¬HasK4Minor M := by
  rintro ⟨f, hf⟩
  exact K4Matroid_not_seriesParallel_map f (h.minor hf)

/-- The excluded ordinary M(K4)-minor conclusion for the actual primitive-ray
matroid of a complete regular deeply monotone fan, in every dimension. -/
theorem fan_rayMatroid_no_K4_minor {N V : Type*} [AddCommGroup N]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : TauCeti.Toric.Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ) :
    ¬HasK4Minor (VectorMatroid.ofFamily (K := ℝ)
      (fun u : {u : N // ConeBases.IsRay Φ u} => ι u.val)) :=
  (fan_rayMatroid_seriesParallel Φ hc hr hp).groundConstruction.no_K4_minor

/-- The same exact excluded-minor assertion on the primitive-ray subset of
the original integral lattice, matching the constructive minor witness API. -/
theorem fan_onSet_rayMatroid_no_K4_minor {N V : Type*} [AddCommGroup N]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {ι : N →+ V} (Φ : TauCeti.Toric.Fan ι) (hc : Φ.IsComplete) (hr : Φ.IsRegular)
    (hp : ConeBases.PositiveCriterion Φ) :
    ¬HasK4Minor (VectorMatroid.onSet (K := ℝ) (fun u : N => ι u)
      {u | ConeBases.IsRay Φ u}) :=
  (fan_onSet_rayMatroid_seriesParallel Φ hc hr hp).no_K4_minor

#print axioms Unimodular.SeriesParallel.K4Matroid_eq_cycleMatroid
#print axioms Unimodular.SeriesParallel.K4Matroid_not_seriesParallel_map
#print axioms Unimodular.SeriesParallel.GroundSeriesParallel.no_K4_minor
#print axioms Unimodular.SeriesParallel.fan_rayMatroid_no_K4_minor

end
end Unimodular.SeriesParallel
