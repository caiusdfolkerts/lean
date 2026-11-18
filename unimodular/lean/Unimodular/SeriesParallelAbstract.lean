module

public import Unimodular.SeriesParallelExtensionSemantics
public import Unimodular.SeriesParallelMatroidMinor

@[expose] public section

open Set
open scoped Matroid

namespace Matroid

variable {α : Type*} {M N : Matroid α} {e f : α}

/-- Parallel elements belong to exactly the same closed sets. This is obtained
from the actual two-element circuit by the circuit closure theorem. -/
theorem pair_circuit_mem_closure_iff (hC : M.IsCircuit {e, f}) (hef : e ≠ f)
    (X : Set α) : e ∈ M.closure X ↔ f ∈ M.closure X := by
  have hfe : f ∈ M.closure ({e} : Set α) := by
    have h := hC.mem_closure_sdiff_singleton_of_mem (show f ∈ ({e, f} : Set α) by simp)
    simpa only [pair_sdiff_right hef] using h
  have hef' : e ∈ M.closure ({f} : Set α) := by
    have h := hC.mem_closure_sdiff_singleton_of_mem (show e ∈ ({e, f} : Set α) by simp)
    simpa only [pair_sdiff_left hef] using h
  constructor
  · intro h
    exact (closure_subset_closure_of_subset_closure (singleton_subset_iff.2 h)) hfe
  · intro h
    exact (closure_subset_closure_of_subset_closure (singleton_subset_iff.2 h)) hef'

/-- Replacing one of two parallel elements by the other preserves independence
when neither is already in the remainder of the set. -/
theorem pair_circuit_insert_indep_iff (hC : M.IsCircuit {e, f}) (hef : e ≠ f)
    (I : Set α) (heI : e ∉ I) (hfI : f ∉ I) :
    M.Indep (insert e I) ↔ M.Indep (insert f I) := by
  have heE : e ∈ M.E := hC.subset_ground (by simp)
  have hfE : f ∈ M.E := hC.subset_ground (by simp)
  simp only [insert_indep_iff, heI, hfI, not_false_eq_true, true_implies,
    Set.mem_sdiff, heE, hfE, true_and]
  exact and_congr Iff.rfl (not_congr (Matroid.pair_circuit_mem_closure_iff hC hef I))

/-- Deleting a new loop uniquely determines the extension once its ground set is
fixed. No representability or finite-rank assumption is used. -/
theorem loop_extension_unique (hE : M.E = N.E) (hM : M.IsLoop f) (hN : N.IsLoop f)
    (hdel : M ＼ ({f} : Set α) = N ＼ ({f} : Set α)) : M = N := by
  apply ext_indep hE
  intro I hI
  by_cases hfI : f ∈ I
  · exact iff_of_false (hM.not_indep_of_mem hfI) (hN.not_indep_of_mem hfI)
  · have hd : Disjoint I ({f} : Set α) := disjoint_singleton_right.2 hfI
    have he := congrArg (fun L : Matroid α => L.Indep I) hdel
    simpa only [delete_indep_iff, hd, and_true] using Iff.of_eq he

/-- A parallel extension is unique: the deletion, ground set, and specified
ordinary two-element circuit determine the entire matroid. -/
theorem parallel_extension_unique (hE : M.E = N.E) (hef : e ≠ f)
    (hM : M.IsCircuit {e, f}) (hN : N.IsCircuit {e, f})
    (hdel : M ＼ ({f} : Set α) = N ＼ ({f} : Set α)) : M = N := by
  have houtside : ∀ I : Set α, f ∉ I → (M.Indep I ↔ N.Indep I) := by
    intro I hfI
    have hd : Disjoint I ({f} : Set α) := disjoint_singleton_right.2 hfI
    have he := congrArg (fun L : Matroid α => L.Indep I) hdel
    simpa only [delete_indep_iff, hd, and_true] using Iff.of_eq he
  apply ext_indep hE
  intro I hI
  by_cases hfI : f ∈ I
  · by_cases heI : e ∈ I
    · have hpair : ({e, f} : Set α) ⊆ I :=
        Set.insert_subset_iff.2 ⟨heI, Set.singleton_subset_iff.2 hfI⟩
      exact iff_of_false (fun h => hM.not_indep (h.subset hpair))
        (fun h => hN.not_indep (h.subset hpair))
    · have heJ : e ∉ I \ {f} := fun h => heI h.1
      have hfJ : f ∉ I \ {f} := by simp
      have hrecover : insert f (I \ {f}) = I := by simp [hfI]
      have hswapM : M.Indep I ↔ M.Indep (insert e (I \ {f})) := by
        nth_rw 1 [← hrecover]
        exact (Matroid.pair_circuit_insert_indep_iff hM hef _ heJ hfJ).symm
      have hswapN : N.Indep I ↔ N.Indep (insert e (I \ {f})) := by
        nth_rw 1 [← hrecover]
        exact (Matroid.pair_circuit_insert_indep_iff hN hef _ heJ hfJ).symm
      exact hswapM.trans ((houtside _ (by simp [hef.symm])).trans hswapN.symm)
  · exact houtside I hfI

/-- The dual uniqueness theorem for an arbitrary ordinary series extension. -/
theorem series_extension_unique (hE : M.E = N.E) (hef : e ≠ f)
    (hM : M.IsCocircuit {e, f}) (hN : N.IsCocircuit {e, f})
    (hcon : M ／ ({f} : Set α) = N ／ ({f} : Set α)) : M = N := by
  have hdual : M✶ = N✶ := parallel_extension_unique (by simpa using hE) hef hM hN (by
    simpa only [dual_contract] using congrArg Matroid.dual hcon)
  simpa only [dual_dual] using congrArg Matroid.dual hdual

/-- A coloop extension is also fixed by its deletion. The proof reduces to loop
uniqueness by actual matroid duality and the coloop deletion/contraction identity. -/
theorem coloop_extension_unique (hE : M.E = N.E)
    (hM : M.IsColoop f) (hN : N.IsColoop f)
    (hdel : M ＼ ({f} : Set α) = N ＼ ({f} : Set α)) : M = N := by
  have hcM : M ／ ({f} : Set α) = M ＼ ({f} : Set α) :=
    contract_eq_delete_of_subset_coloops (singleton_subset_iff.2 hM)
  have hcN : N ／ ({f} : Set α) = N ＼ ({f} : Set α) :=
    contract_eq_delete_of_subset_coloops (singleton_subset_iff.2 hN)
  have hcon : M ／ ({f} : Set α) = N ／ ({f} : Set α) := hcM.trans (hdel.trans hcN.symm)
  have hdual : M✶ = N✶ := loop_extension_unique (by simpa using hE)
    hM.dual_isLoop hN.dual_isLoop (by
      simpa only [dual_contract] using congrArg Matroid.dual hcon)
  simpa only [dual_dual] using congrArg Matroid.dual hdual

end Matroid

namespace Unimodular.SeriesParallel

noncomputable section

attribute [local instance] Classical.propDecidable

namespace SPProgram

@[simp] theorem matroid_ground {m : ℕ} (P : SPProgram m) : P.matroid.E = Set.univ := rfl

/-- Precomposing a program's columns is the ordinary inverse relabeling of the
actual Matroid. The equality compares every independent subset. -/
theorem matroid_relabel {m : ℕ} (P : SPProgram m) (e : Equiv.Perm (Fin m)) :
    (P.relabel e).matroid = P.matroid.mapEquiv e.symm := by
  have hm := VectorMatroid.ofFamily_mapEmbedding_eq_onSet
    (K := ℝ) (fun j => embed (P.columns j))
    (fun j => embed (P.columns (e j))) e.symm.toEmbedding (by intro j; simp)
  have hr : Set.range e.symm.toEmbedding = Set.univ :=
    Set.range_eq_univ.2 e.symm.surjective
  rw [hr] at hm
  simpa only [matroid, columns, Matroid.mapEquiv, VectorMatroid.ofFamily, Function.comp_def] using hm.symm

end SPProgram

/-- The standard abstract finite series--parallel construction class. Extensions
are arbitrary Mathlib matroids characterized by their ordinary two-element
circuits/cocircuits and exact deletion/contraction, not by a chosen representation.
The first label is newly adjoined; unrestricted relabeling makes this convention
immaterial. Singleton loop and coloop summands include disconnected matroids. -/
inductive HasSeriesParallelConstruction : {m : ℕ} → Matroid (Fin m) → Prop
  | empty (M : Matroid (Fin 0)) : HasSeriesParallelConstruction M
  | addLoop {m : ℕ} {M : Matroid (Fin m)} {N : Matroid (Fin (m + 1))} :
      HasSeriesParallelConstruction M → N.E = Set.univ → N.IsLoop 0 →
      N ＼ ({0} : Set _) = M.mapEmbedding (oldLabels m) →
      HasSeriesParallelConstruction N
  | addColoop {m : ℕ} {M : Matroid (Fin m)} {N : Matroid (Fin (m + 1))} :
      HasSeriesParallelConstruction M → N.E = Set.univ → N.IsColoop 0 →
      N ＼ ({0} : Set _) = M.mapEmbedding (oldLabels m) →
      HasSeriesParallelConstruction N
  | parallel {m : ℕ} {M : Matroid (Fin m)} {N : Matroid (Fin (m + 1))}
      (e : Fin m) : HasSeriesParallelConstruction M → N.E = Set.univ →
      M.IsNonloop e → N.IsCircuit {0, e.succ} →
      N ＼ ({0} : Set _) = M.mapEmbedding (oldLabels m) →
      HasSeriesParallelConstruction N
  | series {m : ℕ} {M : Matroid (Fin m)} {N : Matroid (Fin (m + 1))}
      (e : Fin m) : HasSeriesParallelConstruction M → N.E = Set.univ →
      ¬M.IsColoop e → N.IsCocircuit {0, e.succ} →
      N ／ ({0} : Set _) = M.mapEmbedding (oldLabels m) →
      HasSeriesParallelConstruction N
  | relabel {m : ℕ} {M : Matroid (Fin m)} (e : Equiv.Perm (Fin m)) :
      HasSeriesParallelConstruction M → HasSeriesParallelConstruction (M.mapEquiv e)

/-- Every abstract construction uses exactly its displayed finite label type. -/
theorem HasSeriesParallelConstruction.ground_eq_univ {m : ℕ} {M : Matroid (Fin m)}
    (h : HasSeriesParallelConstruction M) : M.E = Set.univ := by
  induction h with
  | empty M =>
    ext x
    exact Fin.elim0 x
  | @addLoop m M N h hg he hd ih => exact hg
  | @addColoop m M N h hg he hd ih => exact hg
  | @parallel m M N e h hg he hp hd ih => exact hg
  | @series m M N e h hg he hp hc ih => exact hg
  | relabel e h ih => simp only [Matroid.mapEquiv_ground_eq, ih, Set.image_univ,
      Equiv.range_eq_univ]

private theorem fin_zero_matroid_eq (M N : Matroid (Fin 0)) : M = N := by
  apply Matroid.ext_indep
  · ext i
    exact Fin.elim0 i
  · intro I hI
    have he : I = ∅ := by ext i; exact Fin.elim0 i
    simp [he]

/-- Every abstract eligible extension construction is represented by an
admissible program. The four uniqueness theorems above close the gap between a
concrete column operation and an arbitrary matroid extension. -/
theorem abstract_construction_has_program {m : ℕ} {M : Matroid (Fin m)}
    (h : HasSeriesParallelConstruction M) :
    ∃ P : SPProgram m, P.Admissible ∧ M = P.matroid := by
  induction h with
  | empty M => exact ⟨SPProgram.empty, trivial, fin_zero_matroid_eq _ _⟩
  | @addLoop m M N h hground hloop hdel ih =>
    obtain ⟨P, hP, rfl⟩ := ih
    refine ⟨P.addLoop, hP, ?_⟩
    exact Matroid.loop_extension_unique (hground.trans (P.addLoop.matroid_ground).symm)
      hloop P.addLoop_isLoop (hdel.trans P.addLoop_delete.symm)
  | @addColoop m M N h hground hcoloop hdel ih =>
    obtain ⟨P, hP, rfl⟩ := ih
    refine ⟨P.addColoop, hP, ?_⟩
    exact Matroid.coloop_extension_unique (hground.trans (P.addColoop.matroid_ground).symm)
      hcoloop P.addColoop_isColoop (hdel.trans P.addColoop_delete.symm)
  | @parallel m M N e h hground he hpair hdel ih =>
    obtain ⟨P, hP, rfl⟩ := ih
    have he' : P.columns e ≠ 0 := (P.matroid_isNonloop_iff e).1 he
    refine ⟨P.parallel e, ⟨hP, he'⟩, ?_⟩
    apply Matroid.parallel_extension_unique
      (hground.trans ((P.parallel e).matroid_ground).symm) (by simp : e.succ ≠ 0)
    · simpa only [Set.pair_comm] using hpair
    · simpa only [Set.pair_comm] using P.parallel_isCircuit e he'
    · exact hdel.trans (P.parallel_delete e).symm
  | @series m M N e h hground he hpair hcon ih =>
    obtain ⟨P, hP, rfl⟩ := ih
    have he' := (P.matroid_not_isColoop_iff e).1 he
    refine ⟨P.series e, ⟨hP, he'⟩, ?_⟩
    apply Matroid.series_extension_unique
      (hground.trans ((P.series e).matroid_ground).symm) (by simp : e.succ ≠ 0)
    · simpa only [Set.pair_comm] using hpair
    · simpa only [Set.pair_comm] using P.series_isCocircuit e he'
    · exact hcon.trans (P.series_contract e).symm
  | relabel e h ih =>
    obtain ⟨P, hP, rfl⟩ := ih
    exact ⟨P.relabel e.symm, hP, by rw [P.matroid_relabel]; simp⟩

/-- Conversely, admissible programs use precisely the ordinary eligible abstract
extension operations, including all singleton and relabeling cases. -/
theorem SPProgram.abstract_construction {m : ℕ} (P : SPProgram m) (hP : P.Admissible) :
    HasSeriesParallelConstruction P.matroid := by
  induction P with
  | empty => exact .empty _
  | addLoop P ih =>
    exact .addLoop (ih hP) P.addLoop.matroid_ground P.addLoop_isLoop P.addLoop_delete
  | addColoop P ih =>
    exact .addColoop (ih hP) P.addColoop.matroid_ground
      P.addColoop_isColoop P.addColoop_delete
  | parallel P e ih =>
    exact .parallel e (ih hP.1) (P.parallel e).matroid_ground
      ((P.matroid_isNonloop_iff e).2 hP.2) (P.parallel_isCircuit e hP.2)
      (P.parallel_delete e)
  | series P e ih =>
    exact .series e (ih hP.1) (P.series e).matroid_ground
      ((P.matroid_not_isColoop_iff e).2 hP.2) (P.series_isCocircuit e hP.2)
      (P.series_contract e)
  | relabel P e ih =>
    rw [P.matroid_relabel]
    exact .relabel e.symm (ih hP)

/-- Exact equivalence with the standard abstract construction class, preserving
the complete Matroid rather than only rank, bases of a chosen size, or finite tests. -/
theorem abstract_construction_iff_program {m : ℕ} (M : Matroid (Fin m)) :
    HasSeriesParallelConstruction M ↔ ∃ P : SPProgram m, P.Admissible ∧ M = P.matroid :=
  ⟨abstract_construction_has_program, by
    rintro ⟨P, hP, rfl⟩
    exact P.abstract_construction hP⟩

/-- The graph construction formulation and the abstract extension formulation
are rigorously equivalent. This prevents a concrete representation class from
silently replacing the paper's series--parallel matroid class. -/
theorem abstract_construction_iff_seriesParallel {m : ℕ} (M : Matroid (Fin m)) :
    HasSeriesParallelConstruction M ↔ IsSeriesParallelMatroid M := by
  rw [abstract_construction_iff_program, isSeriesParallelMatroid_iff_program]

/-- The full constructive direction of Proposition 6.7 for the abstract standard
series--parallel class. The minor is a literal Mathlib contraction/deletion minor
of the genuine primitive facet-normal matroid, after an explicit injective relabeling.
The dimension is exactly m, hence in particular at most m. -/
theorem abstract_seriesParallel_cubical_realization {m : ℕ} (M : Matroid (Fin m))
    (hM : HasSeriesParallelConstruction M) :
    ∃ (σ : SmoothCompleteFan m) (Q : SmoothReflexivePresentation m)
      (f : Fin m ↪ Lattice m),
      σ.PositiveCoordinateCriterion ∧ Q.DeeplyMonotone ∧ Q.IsCombinatorialCube ∧
      (Q.normals : Set (Lattice m)) = σ.rays ∧
      M.mapEmbedding f ≤m
        VectorMatroid.onSet (K := ℝ) (embed : Lattice m → Ambient m) (Q.normals : Set _) ∧
      σ.rays.ncard = 2 * m ∧ (σ.maximal.image basisCone).card = 2 ^ m ∧
      Q.normals.card = 2 * m ∧ Q.vertices.card = 2 ^ m := by
  obtain ⟨P, hP, rfl⟩ := abstract_construction_has_program hM
  obtain ⟨R⟩ := program_has_realization P
  have hnorm : ((R.fan.polarPresentation R.criterion).normals : Set (Lattice m)) =
      R.fan.rays := by
    ext u
    exact R.fan.mem_rayFinset u
  refine ⟨R.fan, R.fan.polarPresentation R.criterion, R.witness.chosen,
    R.criterion, R.fan.polarPresentation_deeplyMonotone R.criterion,
    R.cubical.polar_isCombinatorialCube R.criterion, hnorm, ?_, R.ray_count,
    R.cone_count, R.cubical.polar_normals_card R.criterion,
    R.cubical.polar_vertices_card R.criterion⟩
  rw [hnorm]
  exact R.witness.matroid_isMinor

/-- The graph/network statement used elsewhere in the formalization has the
same full constructive conclusion, by the proved abstract-class equivalence. -/
theorem seriesParallel_cubical_realization {m : ℕ} (M : Matroid (Fin m))
    (hM : IsSeriesParallelMatroid M) :
    ∃ (σ : SmoothCompleteFan m) (Q : SmoothReflexivePresentation m)
      (f : Fin m ↪ Lattice m),
      σ.PositiveCoordinateCriterion ∧ Q.DeeplyMonotone ∧ Q.IsCombinatorialCube ∧
      (Q.normals : Set (Lattice m)) = σ.rays ∧
      M.mapEmbedding f ≤m
        VectorMatroid.onSet (K := ℝ) (embed : Lattice m → Ambient m) (Q.normals : Set _) ∧
      σ.rays.ncard = 2 * m ∧ (σ.maximal.image basisCone).card = 2 ^ m ∧
      Q.normals.card = 2 * m ∧ Q.vertices.card = 2 ^ m :=
  abstract_seriesParallel_cubical_realization M
    ((abstract_construction_iff_seriesParallel M).2 hM)

end
end Unimodular.SeriesParallel
