module

public import Unimodular.VectorMatroid
public import Unimodular.SeriesParallelNetworks
public import Unimodular.RankThree

@[expose] public section

open Set
open scoped Matroid

namespace Unimodular.VectorMatroid

noncomputable section

variable {K α V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Vector-matroid closure is exactly membership in the span of the indicated
labelled vectors, for every set of labels. -/
theorem ofFamily_mem_closure (v : α → V) (X : Set α) (e : α) :
    e ∈ (ofFamily (K := K) v).closure X ↔ v e ∈ Submodule.span K (v '' X) := by
  let M := ofFamily (K := K) v
  obtain ⟨B, hB⟩ := M.exists_isBasis X (by simp [M])
  have hspan : Submodule.span K (v '' B) = Submodule.span K (v '' X) :=
    isBasis_span_eq v hB
  rw [← hB.closure_eq_closure, ← hspan]
  by_cases heB : e ∈ B
  · have hecl : e ∈ M.closure B := M.mem_closure_of_mem' heB (by simp [M])
    have hesp : v e ∈ Submodule.span K (v '' B) :=
      Submodule.subset_span ⟨e, heB, rfl⟩
    exact iff_of_true hecl hesp
  · have hli : LinearIndepOn K v B := (ofFamily_indep v B).mp hB.indep
    have hn : e ∉ M.closure B ↔ v e ∉ Submodule.span K (v '' B) := by
      rw [hB.indep.notMem_closure_iff_of_notMem heB (by simp [M])]
      rw [ofFamily_indep, linearIndepOn_insert heB]
      exact and_iff_right hli
    exact not_iff_not.mp hn

/-- A represented element is a coloop exactly when its vector is outside the
span of all the other labelled vectors. -/
theorem ofFamily_isColoop_iff (v : α → V) (e : α) :
    (ofFamily (K := K) v).IsColoop e ↔
      v e ∉ Submodule.span K (v '' {e}ᶜ) := by
  rw [Matroid.isColoop_iff_notMem_closure_compl (by simp), ofFamily_ground,
    ← Set.compl_eq_univ_sdiff, ofFamily_mem_closure]

/-- The spanning predicate agrees with equality of the full represented spans. -/
theorem ofFamily_spanning_iff (v : α → V) (X : Set α) :
    (ofFamily (K := K) v).Spanning X ↔
      Submodule.span K (v '' X) = Submodule.span K (Set.range v) := by
  rw [Matroid.spanning_iff_closure_eq, ofFamily_ground]
  constructor
  · intro h
    apply le_antisymm (Submodule.span_mono (Set.image_subset_range _ _))
    apply Submodule.span_le.mpr
    rintro _ ⟨e, rfl⟩
    exact (ofFamily_mem_closure v X e).mp (by rw [h]; trivial)
  · intro h
    apply Set.eq_univ_of_forall
    intro e
    rw [ofFamily_mem_closure, h]
    exact Submodule.subset_span ⟨e, rfl⟩

end
end Unimodular.VectorMatroid

namespace Unimodular.SeriesParallel

noncomputable section

private lemma embed_injective {n : ℕ} : Function.Injective (@embed n) := by
  intro x y h
  ext i
  have hi := congrFun h i
  change (x i : ℝ) = (y i : ℝ) at hi
  exact_mod_cast hi

private lemma embed_eq_zero_iff {n : ℕ} (x : Lattice n) : embed x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    change (x i : ℝ) = 0 at hi
    exact Int.cast_eq_zero.mp hi
  · rintro rfl
    funext i
    change ((0 : ℤ) : ℝ) = 0
    exact Int.cast_zero

namespace RootedNetwork

/-- The actual Mathlib cycle matroid of the directed incidence representation.
Every edge label is retained, including loops and parallel edges. -/
def cycleMatroid {n m : ℕ} (G : RootedNetwork n m) : Matroid (Fin m) :=
  VectorMatroid.ofFamily (K := ℝ) (fun e =>
    embed (Graphic.vertex (Pi.basisFun ℤ (Fin n)) (G.source e) -
      Graphic.vertex (Pi.basisFun ℤ (Fin n)) (G.target e)))

/-- The standard eligible network construction: singleton loop/bridge summands,
parallel duplication of a nonloop, subdivision of a noncoloop, and relabeling.
Eligibility uses the ordinary Mathlib matroid predicates. -/
inductive HasEligibleConstruction : {m : ℕ} → RootedNetwork m m → Prop
  | empty : HasEligibleConstruction empty
  | addLoop {m : ℕ} {G : RootedNetwork m m} : HasEligibleConstruction G →
      HasEligibleConstruction G.addLoop
  | addBridge {m : ℕ} {G : RootedNetwork m m} : HasEligibleConstruction G →
      HasEligibleConstruction G.addBridge
  | parallel {m : ℕ} {G : RootedNetwork m m} : HasEligibleConstruction G →
      (e : Fin m) → G.cycleMatroid.IsNonloop e → HasEligibleConstruction (G.parallel e)
  | subdivide {m : ℕ} {G : RootedNetwork m m} : HasEligibleConstruction G →
      (e : Fin m) → ¬G.cycleMatroid.IsColoop e → HasEligibleConstruction (G.subdivide e)
  | relabel {m : ℕ} {G : RootedNetwork m m} : HasEligibleConstruction G →
      (e : Equiv.Perm (Fin m)) → HasEligibleConstruction (G.relabel e)

end RootedNetwork

/-- Incidence in an arbitrary integral basis has exactly the standard cycle
matroid. The proof transports every independent subset through the actual real
coordinate equivalence. -/
theorem incidence_matroid_basis_invariant {n : ℕ} {E : Type*}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (s t : E → Option (Fin n)) :
    VectorMatroid.ofFamily (K := ℝ) (fun e =>
      embed (Graphic.vertex b (s e) - Graphic.vertex b (t e))) =
    VectorMatroid.ofFamily (K := ℝ) (fun e =>
      embed (Graphic.vertex (Pi.basisFun ℤ (Fin n)) (s e) -
        Graphic.vertex (Pi.basisFun ℤ (Fin n)) (t e))) := by
  let f := realCoordinateEquiv b
  have hvec (e : E) :
      f (embed (Graphic.vertex b (s e) - Graphic.vertex b (t e))) =
      embed (Graphic.vertex (Pi.basisFun ℤ (Fin n)) (s e) -
        Graphic.vertex (Pi.basisFun ℤ (Fin n)) (t e)) := by
    ext i
    rw [realCoordinateEquiv_embed]
    simp only [Module.Basis.equivFun_apply, map_sub, Finsupp.sub_apply,
      Graphic.repr_vertex]
    cases hs : s e <;> cases ht : t e <;>
      simp [Graphic.vertex, Graphic.endpoint, embed, Pi.basisFun_apply,
        Pi.single_apply, Finsupp.single_apply, eq_comm, hs, ht]
  apply (VectorMatroid.ofFamily_eq_iff _ _).mpr
  intro S
  have he : (fun j : S =>
      embed (Graphic.vertex (Pi.basisFun ℤ (Fin n)) (s j.val) -
        Graphic.vertex (Pi.basisFun ℤ (Fin n)) (t j.val))) =
      f.toLinearMap ∘ (fun j : S => embed (Graphic.vertex b (s j.val) -
        Graphic.vertex b (t j.val))) := by
    funext j
    exact (hvec j.val).symm
  change LinearIndependent ℝ _ ↔ LinearIndependent ℝ _
  rw [he]
  exact (f.toLinearMap.linearIndependent_iff (LinearMap.ker_eq_bot.mpr f.injective)).symm

namespace SPProgram

/-- The actual Mathlib matroid represented by all program columns. -/
def matroid {m : ℕ} (P : SPProgram m) : Matroid (Fin m) :=
  VectorMatroid.ofFamily (K := ℝ) (fun e => embed (P.columns e))

/-- Programs represent the ordinary cycle matroids of their explicit networks. -/
theorem matroid_eq_cycleMatroid {m : ℕ} (P : SPProgram m) :
    P.matroid = P.network.cycleMatroid := by
  rw [matroid, show (fun e => embed (P.columns e)) =
      (fun e => embed (Graphic.vertex P.networkBasis (P.network.source e) -
        Graphic.vertex P.networkBasis (P.network.target e))) from
      funext (fun e => congrArg embed (P.columns_eq_incidence e))]
  exact incidence_matroid_basis_invariant P.networkBasis P.network.source P.network.target

@[simp] theorem matroid_isNonloop_iff {m : ℕ} (P : SPProgram m) (e : Fin m) :
    P.matroid.IsNonloop e ↔ P.columns e ≠ 0 := by
  rw [← Matroid.not_isLoop_iff (by simp [matroid]), matroid,
    VectorMatroid.ofFamily_isLoop_iff, embed_eq_zero_iff]

@[simp] theorem matroid_not_isColoop_iff {m : ℕ} (P : SPProgram m) (e : Fin m) :
    ¬P.matroid.IsColoop e ↔ embed (P.columns e) ∈ Submodule.span ℝ
      {v | ∃ j, j ≠ e ∧ embed (P.columns j) = v} := by
  rw [matroid, VectorMatroid.ofFamily_isColoop_iff, not_not]
  have he : (fun j => embed (P.columns j)) '' ({e}ᶜ : Set (Fin m)) =
      {v | ∃ j, j ≠ e ∧ embed (P.columns j) = v} := by
    ext v
    simp
  rw [he]

/-- Program admissibility is precisely the standard matroid eligibility of its
actual graph operations. -/
theorem network_eligible {m : ℕ} (P : SPProgram m) (hP : P.Admissible) :
    P.network.HasEligibleConstruction := by
  induction P with
  | empty => exact .empty
  | addLoop P ih => exact .addLoop (ih hP)
  | addColoop P ih => exact .addBridge (ih hP)
  | parallel P e ih =>
    exact .parallel (ih hP.1) e (by
      rw [← P.matroid_eq_cycleMatroid, matroid_isNonloop_iff]
      exact hP.2)
  | series P e ih =>
    exact .subdivide (ih hP.1) e (by
      rw [← P.matroid_eq_cycleMatroid, matroid_not_isColoop_iff]
      exact hP.2)
  | relabel P e ih => exact .relabel (ih hP) e

end SPProgram

namespace RootedNetwork

/-- Conversely every eligible construction of an actual network is represented
by an admissible program, with exactly the same labelled graph endpoints. -/
theorem eligible_iff_program {m : ℕ} (G : RootedNetwork m m) :
    G.HasEligibleConstruction ↔ ∃ P : SPProgram m, P.Admissible ∧ P.network = G := by
  constructor
  · intro h
    induction h with
    | empty => exact ⟨.empty, trivial, rfl⟩
    | addLoop h ih =>
      obtain ⟨P, hP, rfl⟩ := ih
      exact ⟨P.addLoop, hP, rfl⟩
    | addBridge h ih =>
      obtain ⟨P, hP, rfl⟩ := ih
      exact ⟨P.addColoop, hP, rfl⟩
    | parallel h e he ih =>
      obtain ⟨P, hP, rfl⟩ := ih
      refine ⟨P.parallel e, ⟨hP, ?_⟩, rfl⟩
      rwa [← P.matroid_eq_cycleMatroid, P.matroid_isNonloop_iff] at he
    | subdivide h e he ih =>
      obtain ⟨P, hP, rfl⟩ := ih
      refine ⟨P.series e, ⟨hP, ?_⟩, rfl⟩
      rwa [← P.matroid_eq_cycleMatroid, P.matroid_not_isColoop_iff] at he
    | relabel h e ih =>
      obtain ⟨P, hP, rfl⟩ := ih
      exact ⟨P.relabel e, hP, rfl⟩
  · rintro ⟨P, hP, rfl⟩
    exact P.network_eligible hP

end RootedNetwork

/-- The constructive series--parallel matroid class stated with actual Mathlib
cycle matroids of networks and ordinary matroid eligibility predicates. -/
def IsSeriesParallelMatroid {m : ℕ} (M : Matroid (Fin m)) : Prop :=
  ∃ G : RootedNetwork m m, G.HasEligibleConstruction ∧ M = G.cycleMatroid

/-- Exact correspondence between the network construction class and admissible
programs. This equivalence preserves the entire actual Mathlib matroid. -/
theorem isSeriesParallelMatroid_iff_program {m : ℕ} (M : Matroid (Fin m)) :
    IsSeriesParallelMatroid M ↔ ∃ P : SPProgram m, P.Admissible ∧ M = P.matroid := by
  constructor
  · rintro ⟨G, hG, hM⟩
    obtain ⟨P, hP, rfl⟩ := (G.eligible_iff_program).mp hG
    exact ⟨P, hP, hM.trans P.matroid_eq_cycleMatroid.symm⟩
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P.network, P.network_eligible hP, P.matroid_eq_cycleMatroid⟩

#print axioms Unimodular.VectorMatroid.ofFamily_mem_closure
#print axioms Unimodular.VectorMatroid.ofFamily_isColoop_iff
#print axioms Unimodular.SeriesParallel.SPProgram.matroid_eq_cycleMatroid
#print axioms Unimodular.SeriesParallel.isSeriesParallelMatroid_iff_program

end
end Unimodular.SeriesParallel
