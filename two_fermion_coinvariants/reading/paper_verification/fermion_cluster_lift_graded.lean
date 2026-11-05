module

public import PaperVerification.FermionClusterUniversal
public import PaperVerification.FermionExteriorGradedMaps

/-!
# The cluster evaluation maps preserve the actual total exterior grading

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.Fermion
namespace ClusterRepresentation

variable {F C ι κ : Type*} [Field F] [CharZero F] [Ring C] [Algebra F C]
  [Fintype ι] [Fintype κ] [LinearOrder (ι⊕ι)]
  {part : ℕ → Submodule F C} [GradedAlgebra part]
  {beta : ι → F} {cluster : ι → κ} {r u v : ι → ℕ} {s : κ → ℕ}
  (rep : ClusterRepresentation part beta cluster r s u v) (hC : IsSupercommutative part)

theorem exteriorMap_degree {degree : ℕ}
    {x : ClusterExterior (ClusterOrdinary beta cluster r s) ι}
    (hx : x∈exteriorTotalPart degree) :
    rep.exteriorMap hC x∈part degree := by
  letI := rep.coefficientAlgebra hC
  letI := rep.coefficientTower hC
  let w := fun _ : ι⊕ι ↦ (1:ℕ)
  let gen := Sum.elim rep.theta rep.xi
  have hgen (i : ι⊕ι) : gen i∈part 1 := by
    cases i with
    | inl i => exact rep.theta_degree i
    | inr i => exact rep.xi_degree i
  have hegen (i : ι⊕ι) : rep.exteriorMap hC (exteriorGenerator i)=gen i := by
    cases i with
    | inl i => exact rep.exteriorMap_theta hC i
    | inr i => exact rep.exteriorMap_xi hC i
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨T,hT,rfl⟩ := hx
      rw [←hT,Module.Basis.exteriorAlgebra_eq_prod_map_sort,map_list_prod]
      have hs : (T.sort.map w).sum=exteriorWordDegree w T := by
        simpa only [Finset.sort_toFinset,exteriorWordDegree] using
          (List.sum_toFinset w (Finset.sort_nodup T (· ≤ ·))).symm
      have hiota (i : ι⊕ι) :
          ExteriorAlgebra.ι (ClusterOrdinary beta cluster r s)
            ((Pi.basisFun (ClusterOrdinary beta cluster r s) (ι⊕ι)) i)=
          exteriorGenerator i := by
        unfold exteriorGenerator
        apply congrArg (ExteriorAlgebra.ι (ClusterOrdinary beta cluster r s))
        funext j
        by_cases hji : j=i
        · subst j
          simp only [Pi.basisFun_apply,Pi.single_eq_same]
        · simp only [Pi.basisFun_apply,Pi.single_apply,hji,ite_false]
      have h := graded_list_prod_mem part w gen hgen T.sort
      simpa only [List.map_map,Function.comp_def,hiota,hegen,hs,w] using h
  | zero => simpa only [map_zero] using (part degree).zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      rw [rep.exteriorMap_smul]
      simpa only [Nat.zero_add] using
        SetLike.mul_mem_graded (rep.coefficientMap_degree hC a) ih

theorem lift_degree {degree : ℕ}
    {x : HomogeneousClusterAlgebra beta cluster r s u v}
    (hx : x∈homogeneousClusterPart beta cluster r s u v degree) :
    rep.lift hC x∈part degree := by
  obtain ⟨y,hy,rfl⟩ := hx
  exact rep.exteriorMap_degree hC hy

end ClusterRepresentation
end PaperVerification.Fermion

