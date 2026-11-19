module

public import Unimodular.SeriesParallelMatroidSemantics
public import Unimodular.SeriesParallelRealization

@[expose] public section

open Set
open scoped Matroid

namespace Unimodular.VectorMatroid

noncomputable section

variable {K α V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Distinct labels carrying the same nonzero vector form an ordinary
Mathlib two-element circuit. -/
theorem pair_isCircuit_of_eq (v : α → V) {e f : α} (hef : e ≠ f)
    (hne : v e ≠ 0) (heq : v e = v f) :
    (ofFamily (K := K) v).IsCircuit {e, f} := by
  have he : (ofFamily (K := K) v).IsNonloop e := by
    rw [← Matroid.not_isLoop_iff (by simp), ofFamily_isLoop_iff]
    exact hne
  apply (he.closure_eq_closure_iff_isCircuit_of_ne hef).mp
  ext x
  rw [ofFamily_mem_closure, ofFamily_mem_closure, Set.image_singleton,
    Set.image_singleton, heq]

/-- A two-element cocircuit test in a represented matroid. A functional is
nonzero precisely on the pair, and their sum lies in the span of the other
columns. The proof checks ordinary matroid spanning and its minimal failure. -/
theorem pair_isCocircuit_of_functional (v : α → V) {e f : α} (hef : e ≠ f)
    (g : V →ₗ[K] K) (he : g (v e) = 1) (hf : g (v f) = -1)
    (hz : ∀ a, a ≠ e → a ≠ f → g (v a) = 0)
    (hsum : v e + v f ∈ Submodule.span K (v '' ({e, f} : Set α)ᶜ)) :
    (ofFamily (K := K) v).IsCocircuit {e, f} := by
  let M := ofFamily (K := K) v
  have hker : Submodule.span K (v '' ({e, f} : Set α)ᶜ) ≤ LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact hz a (by simpa using fun h => ha (Or.inl h))
      (by simpa using fun h => ha (Or.inr h))
  have hnot : ¬M.Spanning ({e, f} : Set α)ᶜ := by
    intro h
    have hsp := (ofFamily_spanning_iff v _).mp h
    have hve : v e ∈ Submodule.span K (v '' ({e, f} : Set α)ᶜ) := by
      rw [hsp]
      exact Submodule.subset_span ⟨e, rfl⟩
    have hzero : g (v e) = 0 := hker hve
    rw [he] at hzero
    exact one_ne_zero hzero
  have hspe : M.Spanning ({e} : Set α)ᶜ := by
    apply (ofFamily_spanning_iff v _).mpr
    apply le_antisymm (Submodule.span_mono (Set.image_subset_range _ _))
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    by_cases hae : a = e
    · subst a
      have hs : v e + v f ∈ Submodule.span K (v '' ({e} : Set α)ᶜ) :=
        Submodule.span_mono (Set.image_mono (by intro a ha h; exact ha (Or.inl h))) hsum
      have hvf : v f ∈ Submodule.span K (v '' ({e} : Set α)ᶜ) :=
        Submodule.subset_span ⟨f, by simpa using hef.symm, rfl⟩
      simpa using (Submodule.sub_mem _ hs hvf)
    · exact Submodule.subset_span ⟨a, by simpa using hae, rfl⟩
  have hspf : M.Spanning ({f} : Set α)ᶜ := by
    apply (ofFamily_spanning_iff v _).mpr
    apply le_antisymm (Submodule.span_mono (Set.image_subset_range _ _))
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    by_cases haf : a = f
    · subst a
      have hs : v e + v f ∈ Submodule.span K (v '' ({f} : Set α)ᶜ) :=
        Submodule.span_mono (Set.image_mono (by intro a ha h; exact ha (Or.inr h))) hsum
      have hve : v e ∈ Submodule.span K (v '' ({f} : Set α)ᶜ) :=
        Submodule.subset_span ⟨e, by simpa using hef, rfl⟩
      simpa using (Submodule.sub_mem _ hs hve)
    · exact Submodule.subset_span ⟨a, by simpa using haf, rfl⟩
  rw [Matroid.isCocircuit_iff_minimal_compl_nonspanning, minimal_iff_forall_ssubset]
  refine ⟨by simpa [M, ← Set.compl_eq_univ_sdiff] using hnot, ?_⟩
  intro D hD
  simp only [not_not]
  rcases Set.subset_pair_iff_eq.mp hD.subset with rfl | rfl | rfl | hlast
  · simpa [M] using M.ground_spanning
  · simpa [M, ← Set.compl_eq_univ_sdiff] using hspe
  · simpa [M, ← Set.compl_eq_univ_sdiff] using hspf
  · exact False.elim (hD.ne hlast)

end
end Unimodular.VectorMatroid

namespace Unimodular.SeriesParallel

noncomputable section

open FanRealization

/-- The old edge-label inclusion after adjoining a new first label. -/
def oldLabels (m : ℕ) : Fin m ↪ Fin (m + 1) := ⟨Fin.succ, Fin.succ_injective m⟩

private theorem range_oldLabels (m : ℕ) :
    Set.range (oldLabels m) = ({0} : Set (Fin (m + 1)))ᶜ := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [oldLabels]
  · simp [oldLabels]

private theorem matroid_realLift {m : ℕ} (v : Fin m → Ambient m) :
    VectorMatroid.ofFamily (K := ℝ) (realLift ∘ v) = VectorMatroid.ofFamily (K := ℝ) v := by
  apply (VectorMatroid.ofFamily_eq_iff (K := ℝ) _ _).mpr
  intro S
  exact (realLift : Ambient m →ₗ[ℝ] Ambient (m + 1)).linearIndependent_iff
    (LinearMap.ker_eq_bot.mpr realLift_injective)

private theorem old_lift_delete {m : ℕ} (P : SPProgram m)
    (v : Fin (m + 1) → Lattice (m + 1))
    (hv : ∀ j, v j.succ = liftColumn (P.columns j)) :
    (VectorMatroid.ofFamily (K := ℝ) (fun j => embed (v j))) ＼ ({0} : Set _) =
      P.matroid.mapEmbedding (oldLabels m) := by
  have himage := VectorMatroid.ofFamily_mapEmbedding_eq_onSet (K := ℝ)
    (realLift ∘ (fun j => embed (P.columns j))) (fun j => embed (v j)) (oldLabels m)
    (by
      intro j
      change embed (v j.succ) = realLift (embed (P.columns j))
      rw [hv j]
      exact embed_lift (P.columns j))
  rw [matroid_realLift, range_oldLabels] at himage
  rw [SPProgram.matroid, VectorMatroid.ofFamily, VectorMatroid.delete_onSet]
  simpa only [← Set.compl_eq_univ_sdiff] using himage.symm

private theorem ker_realTail {m : ℕ} :
    LinearMap.ker (realTail : Ambient (m + 1) →ₗ[ℝ] Ambient m) =
      Submodule.span ℝ ({embed (Fin.cons (-1) (0 : Lattice m))} : Set (Ambient (m + 1))) := by
  apply le_antisymm
  · intro x hx
    have ht : Fin.tail x = 0 := hx
    have he : x = (-x 0) • embed (Fin.cons (-1) (0 : Lattice m)) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [embed, Pi.smul_apply, smul_eq_mul]
      · have hj := congrFun ht j
        simpa [embed, Pi.smul_apply, smul_eq_mul, Fin.tail] using hj
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro x (rfl : x = embed (Fin.cons (-1) (0 : Lattice m)))
    change Fin.tail (embed (Fin.cons (-1) (0 : Lattice m))) = 0
    ext j
    simp [embed, Fin.tail]

namespace SPProgram

/-- Adding the zero column is exactly adjoining an ordinary matroid loop. -/
theorem addLoop_isLoop {m : ℕ} (P : SPProgram m) : P.addLoop.matroid.IsLoop 0 := by
  rw [matroid, VectorMatroid.ofFamily_isLoop_iff]
  simp [columns, embed]

theorem addLoop_delete {m : ℕ} (P : SPProgram m) :
    P.addLoop.matroid ＼ ({0} : Set _) = P.matroid.mapEmbedding (oldLabels m) :=
  old_lift_delete P P.addLoop.columns (by intro j; rfl)

theorem addColoop_delete {m : ℕ} (P : SPProgram m) :
    P.addColoop.matroid ＼ ({0} : Set _) = P.matroid.mapEmbedding (oldLabels m) :=
  old_lift_delete P P.addColoop.columns (by intro j; rfl)

/-- The independent new coordinate is exactly a matroid coloop. -/
theorem addColoop_isColoop {m : ℕ} (P : SPProgram m) : P.addColoop.matroid.IsColoop 0 := by
  rw [matroid, VectorMatroid.ofFamily_isColoop_iff]
  have hz : Submodule.span ℝ ((fun j => embed (P.addColoop.columns j)) ''
      ({0} : Set (Fin (m + 1)))ᶜ) ≤ LinearMap.ker (LinearMap.proj 0) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, hj, rfl⟩
    cases j using Fin.cases with
    | zero => exact False.elim (hj (Set.mem_singleton _))
    | succ j => simp [columns, liftColumn, embed]
  intro h
  have hh : (embed (P.addColoop.columns 0)) 0 = 0 := hz h
  norm_num [columns, newColumn, embed] at hh

/-- The pair created by a parallel step is an actual two-element circuit. -/
theorem parallel_isCircuit {m : ℕ} (P : SPProgram m) (e : Fin m)
    (he : P.columns e ≠ 0) : (P.parallel e).matroid.IsCircuit {0, e.succ} := by
  apply VectorMatroid.pair_isCircuit_of_eq (fun j => embed ((P.parallel e).columns j))
    (Ne.symm (Fin.succ_ne_zero e))
  · intro hz
    apply he
    ext i
    have hi : (P.columns e i : ℝ) = 0 := by
      simpa [columns, liftColumn, embed] using congrFun hz i.succ
    change P.columns e i = 0
    exact_mod_cast hi
  · rfl

theorem parallel_delete {m : ℕ} (P : SPProgram m) (e : Fin m) :
    (P.parallel e).matroid ＼ ({0} : Set _) = P.matroid.mapEmbedding (oldLabels m) :=
  old_lift_delete P (P.parallel e).columns (by intro j; rfl)

/-- Contracting either new series coordinate as displayed recovers precisely
the old labelled matroid, not just its rank. -/
theorem series_contract {m : ℕ} (P : SPProgram m) (e : Fin m) :
    (P.series e).matroid ／ ({0} : Set _) = P.matroid.mapEmbedding (oldLabels m) := by
  let v := fun j => embed ((P.series e).columns j)
  have hker : LinearMap.ker (realTail : Ambient (m + 1) →ₗ[ℝ] Ambient m) =
      Submodule.span ℝ (v '' ({0} : Set (Fin (m + 1)))) := by
    simpa [v, columns] using (ker_realTail (m := m))
  have hc := VectorMatroid.contract_onSet (K := ℝ) v (Set.subset_univ ({0} : Set _)) realTail hker
  have hm := VectorMatroid.ofFamily_mapEmbedding_eq_onSet (K := ℝ)
    (fun j => embed (P.columns j)) (realTail ∘ v) (oldLabels m) (by
      intro j
      change Fin.tail (embed ((P.series e).columns j.succ)) = embed (P.columns j)
      ext i
      by_cases hje : j = e
      · simp [columns, hje, embed, Fin.tail]
      · simp [columns, hje, liftColumn, embed, Fin.tail])
  rw [range_oldLabels] at hm
  change (VectorMatroid.onSet (K := ℝ) v Set.univ) ／ {0} =
    P.matroid.mapEmbedding (oldLabels m)
  exact hc.trans (by simpa only [← Set.compl_eq_univ_sdiff, matroid] using hm.symm)

/-- The eligible series step creates an actual two-element cocircuit. -/
theorem series_isCocircuit {m : ℕ} (P : SPProgram m) (e : Fin m)
    (he : embed (P.columns e) ∈ Submodule.span ℝ
      {v | ∃ j, j ≠ e ∧ embed (P.columns j) = v}) :
    (P.series e).matroid.IsCocircuit {0, e.succ} := by
  let v := fun j => embed ((P.series e).columns j)
  apply VectorMatroid.pair_isCocircuit_of_functional v (Ne.symm (Fin.succ_ne_zero e))
    (-LinearMap.proj 0)
  · norm_num [v, columns, embed]
  · norm_num [v, columns, embed]
  · intro a ha₀ hae
    cases a using Fin.cases with
    | zero => exact False.elim (ha₀ rfl)
    | succ j =>
      have hje : j ≠ e := fun h => hae (congrArg Fin.succ h)
      simp [v, columns, hje, liftColumn, embed]
  · have hm : realLift (embed (P.columns e)) ∈ Submodule.span ℝ
        (v '' ({0, e.succ} : Set (Fin (m + 1)))ᶜ) := by
      have hmap : Submodule.span ℝ
          {w | ∃ j, j ≠ e ∧ embed (P.columns j) = w} ≤
          (Submodule.span ℝ (v '' ({0, e.succ} : Set (Fin (m + 1)))ᶜ)).comap
            (realLift : Ambient m →ₗ[ℝ] Ambient (m + 1)) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, hje, rfl⟩
        change realLift (embed (P.columns j)) ∈
          Submodule.span ℝ (v '' ({0, e.succ} : Set (Fin (m + 1)))ᶜ)
        refine Submodule.subset_span ⟨j.succ, by simp [hje], ?_⟩
        change embed ((P.series e).columns j.succ) = realLift (embed (P.columns j))
        simp only [columns, Fin.cons_succ, if_neg hje]
        exact embed_lift (P.columns j)
      exact hmap he
    have hsum : v 0 + v e.succ = realLift (embed (P.columns e)) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [v, columns, embed, realLift]
    rwa [hsum]

end SPProgram

#print axioms Unimodular.SeriesParallel.SPProgram.parallel_isCircuit
#print axioms Unimodular.SeriesParallel.SPProgram.series_isCocircuit
#print axioms Unimodular.SeriesParallel.SPProgram.series_contract

end
end Unimodular.SeriesParallel
