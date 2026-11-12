module

public import ToricPower.ArrangementPowerIncidence

/-! # Literal integer coordinates of the power-incidence functor -/

@[expose] public noncomputable section

open CategoryTheory

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (ell : ℕ) (positive : 0 < ell)

/-- The geometric incidence proof does not change its specified carry. -/
theorem powerBranchFunctor_map_val
    {c d : PowerIncidenceObject A ell positive} (f : c ⟶ d) :
    ((powerBranchFunctor A ell positive).map f).val =
      latticeResidueCarry ell positive f.hom.val c.val := rfl

end ToricPower.IntegralArrangement

end
