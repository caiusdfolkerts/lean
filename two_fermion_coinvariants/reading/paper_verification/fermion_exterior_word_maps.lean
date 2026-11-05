module

public import PaperVerification.FermionExteriorWordGrading

/-!
# Exterior word maps preserve their original weighted degrees

Extracted without mathematical changes from
FermionExteriorGradedMaps; no local-coordinate or coefficient-transport
construction is needed for these statements.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion

section WordMaps

variable {A B ι Γ : Type*} [CommRing A] [Ring B]
  [Algebra A B] [Fintype ι] [LinearOrder ι]
  [AddCommMonoid Γ] [DecidableEq Γ]

theorem graded_list_prod_mem (part : Γ → Submodule A B)
    [GradedAlgebra part] (w : ι → Γ) (g : ι → B)
    (hg : ∀ i,g i∈part (w i)) (l : List ι) :
    (l.map g).prod∈part (l.map w).sum := by
  induction l with
  | nil => simpa only [List.map_nil,List.prod_nil,List.sum_nil] using
      (SetLike.one_mem_graded part)
  | cons i l ih =>
      simpa only [List.map_cons,List.prod_cons,List.sum_cons] using
        SetLike.mul_mem_graded (hg i) ih

theorem exteriorWeighted_map_mem
    (w : ι → Γ) (part : Γ → Submodule A B) [GradedAlgebra part]
    (f : ExteriorAlgebra A (ι → A) →ₐ[A] B)
    (hg : ∀ i,f (exteriorGenerator i)∈part (w i))
    {d : Γ} {x : ExteriorAlgebra A (ι → A)}
    (hx : x∈exteriorWeightedPart w d) : f x∈part d := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨T,hT,rfl⟩ := hx
      rw [←hT,Module.Basis.exteriorAlgebra_eq_prod_map_sort,map_list_prod]
      have hs : (T.sort.map w).sum=exteriorWordDegree w T := by
        simpa only [Finset.sort_toFinset,exteriorWordDegree] using
          (List.sum_toFinset w (Finset.sort_nodup T (· ≤ ·))).symm
      have hgen (i : ι) : ExteriorAlgebra.ι A ((Pi.basisFun A ι) i)=
          exteriorGenerator i := by
        unfold exteriorGenerator
        apply congrArg (ExteriorAlgebra.ι A)
        funext j
        by_cases hji : j=i
        · subst j
          simp only [Pi.basisFun_apply,Pi.single_eq_same]
        · simp only [Pi.basisFun_apply,Pi.single_apply,hji,ite_false]
      have h := graded_list_prod_mem part w (fun i ↦ f (exteriorGenerator i)) hg T.sort
      simpa only [List.map_map,Function.comp_def,hgen,hs] using h
  | zero => simpa only [map_zero] using (part d).zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ a ih

end WordMaps

section Diagonal

variable {A ι Γ : Type*} [CommRing A] [Fintype ι] [LinearOrder ι]
  [AddCommMonoid Γ] [DecidableEq Γ]

theorem exteriorDiagonalUnitEquiv_weighted_mem (w : ι → Γ) (units : ι → Aˣ)
    {d : Γ} {x : ExteriorAlgebra A (ι → A)}
    (hx : x∈exteriorWeightedPart w d) :
    exteriorDiagonalUnitEquiv units x∈exteriorWeightedPart w d := by
  letI := exteriorWeightedGrading (A := A) w
  exact exteriorWeighted_map_mem w (exteriorWeightedPart w)
    (exteriorDiagonalUnitEquiv units).toAlgHom
    (fun i ↦ by
      change exteriorDiagonalUnitEquiv units (exteriorGenerator i)∈exteriorWeightedPart w (w i)
      rw [exteriorDiagonalUnitEquiv_generator]
      exact Submodule.smul_mem _ _ (exteriorGenerator_weighted_mem w i)) hx

theorem exteriorDiagonalUnitEquiv_symm_weighted_mem (w : ι → Γ) (units : ι → Aˣ)
    {d : Γ} {x : ExteriorAlgebra A (ι → A)}
    (hx : x∈exteriorWeightedPart w d) :
    (exteriorDiagonalUnitEquiv units).symm x∈exteriorWeightedPart w d := by
  letI := exteriorWeightedGrading (A := A) w
  exact exteriorWeighted_map_mem w (exteriorWeightedPart w)
    (exteriorDiagonalUnitEquiv units).symm.toAlgHom
    (fun i ↦ by
      change (exteriorDiagonalUnitEquiv units).symm (exteriorGenerator i)∈exteriorWeightedPart w (w i)
      rw [exteriorDiagonalUnitEquiv_symm_generator]
      exact Submodule.smul_mem _ _ (exteriorGenerator_weighted_mem w i)) hx

end Diagonal

end PaperVerification.Fermion
