module

public import PaperVerification.FermionExteriorWordMaps
public import PaperVerification.FermionMultiplicityBlocks

/-!
# Literal block-coefficient ideals and homogeneous linear maps

All blocks here are defined from a fixed, independently supplied basis.
The result proves that a polynomial-linear map preserving those genuine
blocks preserves the corresponding coefficient-ideal relations.

-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Fermion

section Coefficients
variable {P M J Γ : Type*} [CommRing P] [AddCommGroup M] [Module P M]
  [Fintype J] [DecidableEq Γ]

theorem basisDegreePart_coefficient_zero (b : Module.Basis J P M) (degree : J → Γ)
    {g : Γ} {x : M} (hx : x∈basisDegreePart b degree g)
    (j : J) (hj : degree j≠g) : b.repr x j=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i,hi,rfl⟩ := hx
      have hji : j≠i := by
        intro h
        subst i
        exact hj hi
      simp only [Module.Basis.repr_self,Finsupp.single_eq_of_ne hji]
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | add x y hx hy ihx ihy => simp only [map_add,Finsupp.add_apply,ihx,ihy,add_zero]
  | smul c x hx ih => simp only [map_smul,Finsupp.smul_apply,ih,smul_zero]

theorem map_preserves_coefficientIdeals (b : Module.Basis J P M) (degree : J → Γ)
    (ideals : Γ → Ideal P) (f : M →ₗ[P] M)
    (hf : ∀ j,f (b j)∈basisDegreePart b degree (degree j))
    {x : M} (hx : ∀ j,b.repr x j∈ideals (degree j)) :
    ∀ j,b.repr (f x) j∈ideals (degree j) := by
  intro j
  rw [←b.sum_repr x,map_sum,map_sum]
  simp only [map_smul,Finset.sum_apply,Finsupp.finsetSum_apply,Finsupp.sum_apply,
    Finsupp.smul_apply,smul_eq_mul]
  apply Ideal.sum_mem
  intro i hi
  by_cases h : degree j=degree i
  · rw [h]
    exact (ideals (degree i)).mul_mem_right _ (hx i)
  · rw [basisDegreePart_coefficient_zero b degree (hf i) j h,mul_zero]
    exact (ideals (degree j)).zero_mem

end Coefficients

open Exterior

def indexDegree {n : ℕ} (j : OddIndex n) : Fin n → ℕ :=
  Pi.single (modeIndex j) 1

theorem exteriorWordDegree_indexDegree {n : ℕ} (T : Finset (OddIndex n)) (i : Fin n) :
    exteriorWordDegree indexDegree T i=(wordMultiplicityVector T i).val := by
  have h (j : OddIndex n) : indexDegree j i=
      (if j=Sum.inl i then 1 else 0)+(if j=Sum.inr i then 1 else 0) := by
    cases j with
    | inl j => simp [indexDegree,modeIndex,Pi.single_apply,eq_comm]
    | inr j => simp [indexDegree,modeIndex,Pi.single_apply,eq_comm]
  change (∑ j∈T,indexDegree j) i=wordMultiplicity T i
  simp only [Finset.sum_apply]
  simp_rw [h]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',wordMultiplicity]
  split_ifs <;> rfl

theorem wordMultiplicityVector_eq_of_indexDegree_eq {n : ℕ}
    {S T : Finset (OddIndex n)}
    (h : exteriorWordDegree indexDegree S=exteriorWordDegree indexDegree T) :
    wordMultiplicityVector S=wordMultiplicityVector T := by
  funext i
  apply Fin.ext
  simpa only [exteriorWordDegree_indexDegree] using congrFun h i

end PaperVerification.Fermion
