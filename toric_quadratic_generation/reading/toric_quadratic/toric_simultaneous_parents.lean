module

public import PaperVerification.ToricSimultaneousCombinatorics
public import PaperVerification.ToricFiberWalls

@[expose] public section

/-! # Full-cone and wall parents in the simultaneous subdivision

These are incidence consequences of the constructed finite fan.  In
particular an exceptional endpoint has an actual old adjacent cone, and
its vector is the old endpoint ray plus a sum of common wall rays.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)
variable {ι : Type*} [Fintype ι] (T : ι → Finset (Lattice n))
variable (hT : ∀ i,T i ∈ «Σ».cones) (hne : ∀ i,(T i).Nonempty)
variable (hdisj : «Σ».PairwiseDisjointFoci T)

/-- A full cone is one of the actual generating charts, without any
unproved maximal-cone or refinement assumption. -/
theorem full_simultaneous_cone_parent {s : Finset (Lattice n)}
    (hs : s ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones) (hscard : s.card=n) :
    (s ∈ «Σ».cones ∧ ∀ i,¬T i⊆s) ∨
      ∃ i : ι, ∃ U ∈ «Σ».cones,U.card=n ∧ T i⊆U ∧
        ∃ p ∈ T i,s=starRaySet U (T i) p := by
  obtain ⟨C,hC,hsC⟩ := (mem_finiteConeFamilyClosure («Σ».simultaneousCandidates T) s).mp hs
  obtain ⟨b,hb⟩ := «Σ».simultaneousCandidates_smooth T C hC
  have hCle : C.card≤n := by
    have h := Finset.card_le_card hb
    simpa only [Finset.card_image_of_injective _ b.injective,Finset.card_fin] using h
  have hsCeq : s=C := Finset.eq_of_subset_of_card_le hsC (by omega)
  rcases («Σ».mem_simultaneousCandidates T C).mp hC with ⟨hCold,hnone⟩ |
    ⟨i,U,hU,p,hp,hTU,hCeq⟩
  · exact Or.inl ⟨hsCeq.symm ▸ hCold,fun i ↦ hsCeq.symm ▸ hnone i⟩
  · have hseq : s=starRaySet U (T i) p := hsCeq.trans hCeq
    have hUcard : U.card=n := by
      rw [hseq,«Σ».starRaySet_card hU hTU hp] at hscard
      exact hscard
    exact Or.inr ⟨i,U,hU,hUcard,hTU,p,hp,hseq⟩

variable (hcard : ∀ i,2≤(T i).card)

include hcard in
/-- A wall opposite one exceptional ray contains only old rays and is an
actual old cone. Pairwise disjointness excludes every other exceptional ray. -/
theorem simultaneous_wall_below_sum_old (i : ι) (W : Finset (Lattice n))
    (hs : insert (∑ v ∈ T i,v) W ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones)
    (heW : (∑ v ∈ T i,v) ∉ W) :
    W ∈ «Σ».cones ∧ W⊆«Σ».rays ∧ ∀ k : ι,(∑ v ∈ T k,v) ∉ W := by
  have hnone (k : ι) : (∑ v ∈ T k,v) ∉ W := by
    by_cases hki : k=i
    · simpa only [hki] using heW
    · have hk := «Σ».simultaneous_no_common_sums T hT hne hdisj hcard i k (fun hik => hki hik.symm)
        hs (Finset.mem_insert_self _ _)
      exact fun hm ↦ hk (Finset.mem_insert_of_mem hm)
  have hWnew : W ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones :=
    («Σ».simultaneousSubdivision T hT hne hdisj).downward _ hs W (Finset.subset_insert _ _)
  have hWold := ((«Σ».simultaneous_cone_without_sums_iff T hT hne hdisj hnone).mp hWnew).1
  exact ⟨hWold,fun _ hu ↦ «Σ».ray_mem_of_mem_cone hWold hu,hnone⟩

include hcard in
/-- Removing the exceptional endpoint from a full chart recovers its exact
old wall. The missing old focus ray is the old endpoint. -/
theorem full_simultaneous_sum_endpoint_parent (i : ι) (W : Finset (Lattice n))
    (hs : insert (∑ v ∈ T i,v) W ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones)
    (hscard : (insert (∑ v ∈ T i,v) W).card=n)
    (heW : (∑ v ∈ T i,v) ∉ W) :
    ∃ p ∈ T i,p ∉ W ∧ insert p W ∈ «Σ».cones ∧ (insert p W).card=n ∧
      T i⊆insert p W ∧ (T i).erase p⊆W ∧
      (∑ v ∈ T i,v)=p+∑ v ∈ (T i).erase p,v := by
  have hsingle := («Σ».simultaneous_cone_over_sum_iff T hT hne hdisj hcard i
    (Finset.mem_insert_self _ _)).mp hs
  obtain ⟨U,hU,hUcard,hTU,p,hp,hseq⟩ :=
    «Σ».full_star_cone_parent (T i) (hT i) (hne i) (hcard i) hsingle hscard
      (Finset.mem_insert_self _ _)
  have heU : (∑ v ∈ T i,v) ∉ U := fun h ↦
    «Σ».sum_rays_not_mem_rays (hT i) (hcard i) («Σ».ray_mem_of_mem_cone hU h)
  have heUp : (∑ v ∈ T i,v) ∉ U.erase p := fun h ↦ heU (Finset.mem_of_mem_erase h)
  have hstar : starRaySet U (T i) p = insert (∑ v ∈ T i,v) (U.erase p) := by
    ext v
    simp only [mem_starRaySet, Finset.mem_insert, Finset.mem_erase]
  have hwall : W=U.erase p := by
    have h := congrArg (fun s : Finset (Lattice n) ↦ s.erase (∑ v ∈ T i,v))
      (hseq.trans hstar)
    simpa only [Finset.erase_insert_eq_erase,
      Finset.erase_eq_of_notMem heW,Finset.erase_eq_of_notMem heUp] using h
  have hparent : U=insert p W := by rw [hwall,Finset.insert_erase (hTU hp)]
  have hpW : p ∉ W := by rw [hwall]; exact Finset.notMem_erase p U
  have hrest : (T i).erase p⊆W := by
    rw [hwall]
    exact Finset.erase_subset_erase p hTU
  refine ⟨p,hp,hpW,hparent ▸ hU,hparent ▸ hUcard,hparent ▸ hTU,hrest,?_⟩
  exact (Finset.add_sum_erase (T i) (fun v ↦ v) hp).symm

include hcard in
/-- Each endpoint of a full wall has a genuine old endpoint parent.
The last disjunction records whether the endpoint was changed, and gives
the exact focus needed to compute its pulled-back support coefficient. -/
theorem full_simultaneous_endpoint_parent (W : Finset (Lattice n)) (x : Lattice n)
    (hW : ∀ i : ι,(∑ v ∈ T i,v) ∉ W)
    (hs : insert x W ∈ («Σ».simultaneousSubdivision T hT hne hdisj).cones)
    (hscard : (insert x W).card=n) :
    ∃ q : Lattice n, ∃ D : Finset (Lattice n),
      insert q W ∈ «Σ».cones ∧ (insert q W).card=n ∧ D⊆W ∧ x=q+∑ u ∈ D,u ∧
      ((x ∈ «Σ».rays ∧ q=x ∧ D=∅) ∨
        ∃ i : ι,x=(∑ v ∈ T i,v) ∧ q ∈ T i ∧ D=(T i).erase q) := by
  by_cases hex : ∃ i : ι,x=∑ v ∈ T i,v
  · obtain ⟨i,rfl⟩ := hex
    obtain ⟨q,hq,hqW,hqcone,hqcard,hTq,hD,hx⟩ :=
      «Σ».full_simultaneous_sum_endpoint_parent T hT hne hdisj hcard i W hs hscard (hW i)
    exact ⟨q,(T i).erase q,hqcone,hqcard,hD,hx,Or.inr ⟨i,rfl,hq,rfl⟩⟩
  · have hnone (i : ι) : (∑ v ∈ T i,v) ∉ insert x W := by
      intro hm
      rcases Finset.mem_insert.mp hm with heq | hm
      · exact hex ⟨i,heq.symm⟩
      · exact hW i hm
    have hold := ((«Σ».simultaneous_cone_without_sums_iff T hT hne hdisj hnone).mp hs).1
    refine ⟨x,∅,hold,hscard,Finset.empty_subset W,by simp,Or.inl ?_⟩
    exact ⟨«Σ».ray_mem_of_mem_cone hold (Finset.mem_insert_self _ _),rfl,rfl⟩

end SmoothCompleteFan

end PaperVerification.ToricGeometry
