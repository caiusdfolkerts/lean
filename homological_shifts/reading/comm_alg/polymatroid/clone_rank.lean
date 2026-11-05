import CommAlg.Polymatroid.CloneMatroid
import CommAlg.Polymatroid.RankFunction

/-! # Canonical rank inequalities from the integer exchange axiom

The clone matroid proves both submodularity of the canonical rank and the
integer saturation of its base polytope.  In particular no linear-resolution
theorem or homological characterization is used in this direction.
-/

noncomputable section

namespace CommAlg.Polymatroid

open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def upperRank (B : Family V) (U : Finset V) : ℕ :=
  B.sup (fun a => subsetSum a U)

theorem le_upperRank {B : Family V} {a : Exponent V} (ha : a ∈ B) (U : Finset V) :
    subsetSum a U ≤ upperRank B U := by
  exact Finset.le_sup (f := fun b => subsetSum b U) ha

theorem upperRank_attained {B : Family V} (hB : B.Nonempty) (U : Finset V) :
    ∃ a ∈ B, subsetSum a U = upperRank B U := by
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup B hB (fun a => subsetSum a U)
  exact ⟨a, ha, he.symm⟩

def cloneGroup {d : ℕ} (U : Finset V) : Set (Clone V d) := {x | x.1 ∈ U}

theorem encard_clonesOfSet {d : ℕ} (S : Set (Clone V d)) :
    S.encard = (clonesOfSet S).card := by
  have h : (clonesOfSet S : Set (Clone V d)) = S := by ext x; simp
  calc
    S.encard = (clonesOfSet S : Set (Clone V d)).encard := congrArg Set.encard h.symm
    _ = _ := Set.encard_coe_eq_coe_finsetCard _

theorem cloneGroup_inter {d : ℕ} (U W : Finset V) :
    (cloneGroup (d := d) (U ∩ W)) = cloneGroup U ∩ cloneGroup W := by
  ext x; simp [cloneGroup]

theorem cloneGroup_union {d : ℕ} (U W : Finset V) :
    (cloneGroup (d := d) (U ∪ W)) = cloneGroup U ∪ cloneGroup W := by
  ext x; simp [cloneGroup]

section Family

variable (B : Family V) (hBne : B.Nonempty) (d : ℕ)
  (hdeg : Equigenerated B d) (hB : IsPolymatroidal B)

local notation "M" => cloneMatroid B hBne d hdeg hB

theorem cloneGroup_rank (U : Finset V) : (M).eRk (cloneGroup U) = upperRank B U := by
  apply le_antisymm
  · apply Matroid.eRk_le_iff.mpr
    intro I hIU hI
    obtain ⟨T, hT, hIT⟩ := hI.exists_isBase_superset
    have hT' : cloneCount (clonesOfSet T) ∈ B := hT
    have hsub : clonesOfSet I ⊆ (clonesOfSet T).filter (fun x => x.1 ∈ U) := by
      intro x hx
      have hxI : x ∈ I := mem_clonesOfSet I x |>.mp hx
      exact Finset.mem_filter.mpr ⟨mem_clonesOfSet T x |>.mpr (hIT hxI), hIU hxI⟩
    have hcard : (clonesOfSet I).card ≤ upperRank B U := calc
      _ ≤ ((clonesOfSet T).filter (fun x => x.1 ∈ U)).card := Finset.card_le_card hsub
      _ = subsetSum (cloneCount (clonesOfSet T)) U := (cloneCount_subsetSum _ _).symm
      _ ≤ upperRank B U := le_upperRank hT' U
    rw [encard_clonesOfSet]
    exact_mod_cast hcard
  · obtain ⟨a, ha, he⟩ := upperRank_attained hBne U
    let S := canonicalClones d a
    have hc : cloneCount S = a := cloneCount_canonical d a
      (fun i => (coordinate_le_degree a i).trans (by rw [hdeg a ha]; omega))
    have hS : (M).IsBase (S : Set (Clone V d)) := by
      change cloneCount (clonesOfSet (S : Set (Clone V d))) ∈ B
      rwa [clonesOfSet_coe, hc]
    let T := S.filter (fun x => x.1 ∈ U)
    have hT : (M).Indep (T : Set (Clone V d)) := hS.indep.subset (by
      intro x hx
      exact (Finset.mem_filter.mp hx).1)
    have hTU : (T : Set (Clone V d)) ⊆ cloneGroup U := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    have hcard : T.card = upperRank B U := by
      rw [← cloneCount_subsetSum, hc, he]
    simpa only [Set.encard_coe_eq_coe_finsetCard, hcard] using hT.encard_le_eRk_of_subset hTU

/-- The canonical upper rank of an exchange family is genuinely submodular. -/
def canonicalRank : RankFunction V where
  toFun := upperRank B
  empty := by simp [upperRank]
  monotone := by
    intro U W hUW
    apply Finset.sup_le
    intro a ha
    exact (subsetSum_mono a hUW).trans (le_upperRank ha W)
  submodular := by
    intro U W
    have h := (M).eRk_inter_add_eRk_union_le (cloneGroup U) (cloneGroup W)
    rw [← cloneGroup_inter, ← cloneGroup_union,
      cloneGroup_rank B hBne d hdeg hB, cloneGroup_rank B hBne d hdeg hB,
      cloneGroup_rank B hBne d hdeg hB, cloneGroup_rank B hBne d hdeg hB] at h
    exact_mod_cast (show (upperRank B (U ∪ W) : ℕ∞) + upperRank B (U ∩ W) ≤
      upperRank B U + upperRank B W by simpa only [add_comm] using h)

@[simp] theorem canonicalRank_apply (U : Finset V) :
    canonicalRank B hBne d hdeg hB U = upperRank B U := rfl

theorem cloneCount_map (σ : Clone V d ≃ Clone V d)
    (hσ : ∀ x, (σ x).1 = x.1) (S : Finset (Clone V d)) :
    cloneCount (S.map σ.toEmbedding) = cloneCount S := by
  simp only [cloneCount, Finset.sum_map, Equiv.toEmbedding_apply, hσ]

theorem clonesOfSet_image (σ : Clone V d ≃ Clone V d) (S : Set (Clone V d)) :
    clonesOfSet (σ '' S) = (clonesOfSet S).map σ.toEmbedding := by
  ext x
  simp

theorem clone_indep_image (σ : Clone V d ≃ Clone V d)
    (hσ : ∀ x, (σ x).1 = x.1) {I : Set (Clone V d)} (hI : (M).Indep I) :
    (M).Indep (σ '' I) := by
  obtain ⟨T, hT, hIT⟩ := hI.exists_isBase_superset
  apply Matroid.indep_iff.mpr
  refine ⟨σ '' T, ?_, Set.image_mono hIT⟩
  change cloneCount (clonesOfSet (σ '' T)) ∈ B
  rw [clonesOfSet_image, cloneCount_map d σ hσ]
  exact hT

theorem clone_indep_image_iff (σ : Clone V d ≃ Clone V d)
    (hσ : ∀ x, (σ x).1 = x.1) (I : Set (Clone V d)) :
    (M).Indep (σ '' I) ↔ (M).Indep I := by
  refine ⟨?_, clone_indep_image B hBne d hdeg hB σ hσ⟩
  intro h
  have hσ' : ∀ x, (σ.symm x).1 = x.1 := by
    intro x
    simpa only [Equiv.apply_symm_apply] using (hσ (σ.symm x)).symm
  have hi := clone_indep_image B hBne d hdeg hB σ.symm hσ' h
  simpa using hi

/-- Every clone of an element in a circuit lies in that circuit's closure. -/
theorem circuit_clone_mem_closure {C : Set (Clone V d)} (hC : (M).IsCircuit C)
    {e f : Clone V d} (he : e ∈ C) (hfe : f.1 = e.1) : f ∈ (M).closure C := by
  by_cases hf : f ∈ C
  · exact (M).subset_closure C (by simp) hf
  have hne : e ≠ f := fun h => hf (h ▸ he)
  have hswap : ∀ x : Clone V d, (Equiv.swap e f x).1 = x.1 := by
    intro x
    by_cases hxe : x = e
    · subst x; simpa using hfe
    by_cases hxf : x = f
    · subst x; simpa using hfe.symm
    simp [Equiv.swap_apply_of_ne_of_ne hxe hxf]
  have hn : ¬ (M).Indep ((Equiv.swap e f) '' C) := by
    intro h
    exact hC.not_indep ((clone_indep_image_iff B hBne d hdeg hB _ hswap C).mp h)
  have him : ((Equiv.swap e f) '' C) = insert f (C \ {e}) := by
    rw [Equiv.image_swap_of_mem_of_notMem he hf]
    ext x
    simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  rw [him] at hn
  have hdep : (M).Dep (insert f (C \ {e})) := (Matroid.not_indep_iff (by simp)).mp hn
  have hf' : f ∉ C \ {e} := fun h => hf h.1
  have hc := (hC.sdiff_singleton_indep he).mem_closure_iff_of_notMem hf'
  exact (M).closure_subset_closure Set.sdiff_subset (hc.mpr hdep)

include hBne hdeg hB in
/-- Exact integral base-polytope description, proved from exchange alone. -/
theorem mem_iff_canonical_rank (a : Exponent V) :
    a ∈ B ↔ a.degree = d ∧ ∀ U, subsetSum a U ≤ upperRank B U := by
  refine ⟨fun ha => ⟨hdeg a ha, fun U => le_upperRank ha U⟩, ?_⟩
  rintro ⟨hadeg, haU⟩
  let S := canonicalClones d a
  have hc : cloneCount S = a := cloneCount_canonical d a
    (fun i => (coordinate_le_degree a i).trans (by rw [hadeg]; omega))
  have hS : (M).Indep (S : Set (Clone V d)) := by
    by_contra hn
    have hdep : (M).Dep (S : Set (Clone V d)) :=
      (Matroid.not_indep_iff (by simp)).mp hn
    obtain ⟨C, hCS, hC⟩ := hdep.exists_isCircuit_subset
    let U := (clonesOfSet C).image Prod.fst
    have hCG : C ⊆ cloneGroup U := by
      intro x hx
      exact Finset.mem_image.mpr ⟨x, (mem_clonesOfSet C x).mpr hx, rfl⟩
    have hGC : cloneGroup U ⊆ (M).closure C := by
      intro x hx
      obtain ⟨e, he, hex⟩ := Finset.mem_image.mp hx
      exact circuit_clone_mem_closure B hBne d hdeg hB hC
        ((mem_clonesOfSet C e).mp he) hex.symm
    have hr : (M).eRk (cloneGroup U) ≤ (M).eRk C := by
      simpa only [(M).eRk_closure_eq] using (M).eRk_mono hGC
    have hlt := Matroid.eRk_lt_encard_of_dep_of_finite (Set.toFinite C) hC.dep
    have hcount : C.encard ≤ (subsetSum a U : ℕ∞) := by
      have hsub : clonesOfSet C ⊆ S.filter (fun x => x.1 ∈ U) := by
        intro x hx
        have hxC := (mem_clonesOfSet C x).mp hx
        exact Finset.mem_filter.mpr ⟨hCS hxC, hCG hxC⟩
      have hcard := Finset.card_le_card hsub
      rw [← cloneCount_subsetSum, hc] at hcard
      rw [encard_clonesOfSet]
      exact_mod_cast hcard
    have haR : (subsetSum a U : ℕ∞) ≤ (M).eRk (cloneGroup U) := by
      rw [cloneGroup_rank]
      exact_mod_cast haU U
    exact (not_lt_of_ge haR) (hr.trans_lt (hlt.trans_le hcount))
  obtain ⟨T, hT, hST⟩ := hS.exists_isBase_superset
  have hmem : cloneCount (clonesOfSet T) ∈ B := hT
  have hle : a ≤ cloneCount (clonesOfSet T) := by
    rw [← hc]
    apply cloneCount_mono
    intro x hx
    exact (mem_clonesOfSet T x).mpr (hST hx)
  have heq := eq_of_le_of_degree_eq hle (hadeg.trans (hdeg _ hmem).symm)
  rwa [heq]

end Family

end CommAlg.Polymatroid
