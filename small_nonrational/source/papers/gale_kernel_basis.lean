module
public import Papers.RationalityTenSupportBasics
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Lean.Elab.Tactic.Omega

@[expose] public section
noncomputable section
open Matrix Module Set
open scoped BigOperators
namespace Papers.RationalityTen.ChirotopeDensity

/-- A Gale matrix is built from a basis of the actual kernel. No abstract
duality or representability assumption is inserted. -/
theorem exists_gale_matrix {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℝ) (hA : LinearIndependent ℝ A.row) :
    ∃ k : ℕ, ∃ B : Matrix (Fin n) (Fin k) ℝ,
      k+r=n ∧ Spans B ∧ A*B=0 ∧ B.mulVecLin.range=A.mulVecLin.ker := by
  classical
  let K := A.mulVecLin.ker
  let k := finrank ℝ K
  let E : Basis (Fin k) ℝ K := Module.finBasis ℝ K
  let B : Matrix (Fin n) (Fin k) ℝ := fun i j => (E j : Fin n → ℝ) i
  have hBmap : B.mulVecLin = K.subtype.comp E.equivFun.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    funext i
    have hx : ∀ j, E.repr (E.equivFun.symm x) j = x j := by
      intro j
      change (E.equivFun (E.equivFun.symm x)) j = x j
      exact congrFun (E.equivFun.apply_symm_apply x) j
    have hsum : (∑ j, x j • E j) = E.equivFun.symm x := by
      simpa only [hx] using E.sum_repr (E.equivFun.symm x)
    have h := congrArg (fun z : K => (z : Fin n → ℝ) i) hsum
    change ∑ j, B i j * x j = (E.equivFun.symm x : Fin n → ℝ) i
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, mul_comm] using h
  have hinj : Function.Injective B.mulVecLin := by
    rw [hBmap]
    exact Subtype.val_injective.comp E.equivFun.symm.injective
  have hrange : B.mulVecLin.range = K := by
    rw [hBmap,LinearMap.range_comp,LinearEquiv.range,Submodule.map_top,
      Submodule.range_subtype]
  have hrank : B.rank=k := by
    change finrank ℝ B.mulVecLin.range = k
    rw [LinearMap.finrank_range_of_inj hinj]
    simp
  have hdim : k+r=n := by
    have h := A.mulVecLin.finrank_range_add_finrank_ker
    have hArank := hA.rank_matrix
    have h' : A.rank+k=n := by
      simpa [k,K,Matrix.rank] using h
    simp only [Fintype.card_fin] at hArank
    omega
  refine ⟨k,B,hdim,(spans_iff_matrix_rank B).mpr hrank,?_,hrange⟩
  ext i j
  have hmem := (E j).2
  change (A.mulVec (B.col j)) i = 0
  exact congrFun hmem i

end Papers.RationalityTen.ChirotopeDensity
