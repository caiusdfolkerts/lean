module

public import ToricPower.DualDiagonalAllWeightAction

/-!
# Compatibility with the actual product-chart ring action

The full weight decomposition intertwines multiplication in the actual
ring-linear dual complex with the original cellular monomial maps.
Thus the coherent top classes can be assembled over the product-chart
coordinate ring, not only over its coefficient field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (k : Type) [Field k] (A : Fin s → Fin n → ℤ)
  (S T : Set (Fin s))
  (a : rayCharacterMonoid A S) (b : rayCharacterMonoid A T)

namespace DiagonalCellFrames

variable {S T} {q : ℕ} (F : DiagonalCellFrames A S T q)

/-- Ordinary monomial multiplication in the dual frame is exactly the
actual Laurent shift on the two characters. -/
theorem dualCell_monomial (j : NormalizedCell A q)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) :
    F.dualCell j ((a,b)+p) =
      dualDiagonalAllWeightMonomialIndex A S T a b q (F.dualCell j p) := by
  apply dualDiagonalAllWeightIndex_ext
  · change (F.left j + (a.val+p.1.val)) + (F.right j + (b.val+p.2.val)) =
      (F.left j+p.1.val)+(F.right j+p.2.val)+a.val+b.val
    abel
  · rfl
  · change F.left j + (a.val+p.1.val) = (F.left j+p.1.val)+a.val
    abel

/-- Exact basis formula for the actual ring scalar action. -/
theorem dualCoefficientEquiv_monomial_generator (j : NormalizedCell A q)
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (r : k) :
    F.dualCoefficientEquiv k
      (AddMonoidAlgebra.single (a,b) (1:k) •
        (Finsupp.single j (AddMonoidAlgebra.single p r) :
          NormalizedCell A q →₀ DiagonalChartRing k A S T)) =
      Finsupp.single
        (dualDiagonalAllWeightMonomialIndex A S T a b q (F.dualCell j p)) r := by
  rw [Finsupp.smul_single, smul_eq_mul, AddMonoidAlgebra.single_mul_single,
    one_mul, F.dualCoefficientEquiv_single, F.dualCell_monomial A a b]

end DiagonalCellFrames

variable (frames : ∀ q, DiagonalCellFrames A S T q)

local notation "R" => DiagonalChartRing k A S T

/-- The scalar restriction of literal multiplication in the actual
ring-linear dual complex. Its chain-map property is automatic from
`R`-linearity of that complex, rather than assumed weight compatibility. -/
def diagonalFramedDualMonomialMap :
    diagonalFramedDualScalarComplex k A S T frames ⟶
      diagonalFramedDualScalarComplex k A S T frames :=
  ((ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (AddMonoidAlgebra.single (a,b) (1:k) •
        𝟙 (diagonalFramedDualComplex k A S T frames))

/-- The actual scalar multiplication map has the exact Laurent basis
shift of the already constructed cellular monomial map. -/
theorem diagonalFramedDualMonomialMap_generator (q : ℕ)
    (x : DualDiagonalAllWeightIndex A S T q) (r : k) :
    diagonalFramedDualScalarCoordinates k A S T frames q
      ((diagonalFramedDualMonomialMap k A S T a b frames).f q
        ((diagonalFramedDualScalarCoordinates k A S T frames q).symm
          (Finsupp.single x r))) =
      Finsupp.single (dualDiagonalAllWeightMonomialIndex A S T a b q x) r := by
  obtain ⟨⟨j,p⟩,rfl⟩ := (frames q).dualCellEquiv.surjective x
  change diagonalFramedDualScalarCoordinates k A S T frames q
    ((diagonalFramedDualMonomialMap k A S T a b frames).f q
      ((diagonalFramedDualScalarCoordinates k A S T frames q).symm
        (Finsupp.single ((frames q).dualCell j p) r))) = _
  rw [diagonalFramedDualScalarCoordinates_symm_single]
  change (frames q).dualCoefficientEquiv k
    (diagonalFramedDualCoordinates k A S T frames q
      (AddMonoidAlgebra.single (a,b) (1:k) •
        ((diagonalFramedDualCoordinates k A S T frames q).symm
          (Finsupp.single j (AddMonoidAlgebra.single p r))))) = _
  rw [map_smul, LinearEquiv.apply_symm_apply]
  exact (frames q).dualCoefficientEquiv_monomial_generator k A a b j p r

/-- The complete actual ring scalar action commutes with the full
unrestricted Laurent complex isomorphism. -/
theorem diagonalFramedDualAllWeightIso_monomial :
    diagonalFramedDualMonomialMap k A S T a b frames ≫
        (diagonalFramedDualAllWeightIso k A S T frames).hom =
      (diagonalFramedDualAllWeightIso k A S T frames).hom ≫
        dualDiagonalAllWeightMonomialMap k A S T a b := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  let actual := (dualDiagonalAllWeightCoordinates k A S T q).toLinearMap.comp
    ((((diagonalFramedDualMonomialMap k A S T a b frames ≫
      (diagonalFramedDualAllWeightIso k A S T frames).hom).f q).hom).comp
        (diagonalFramedDualScalarCoordinates k A S T frames q).symm.toLinearMap)
  let weighted := (dualDiagonalAllWeightCoordinates k A S T q).toLinearMap.comp
    ((((diagonalFramedDualAllWeightIso k A S T frames).hom ≫
      dualDiagonalAllWeightMonomialMap k A S T a b).f q).hom.comp
        (diagonalFramedDualScalarCoordinates k A S T frames q).symm.toLinearMap)
  have equal : actual = weighted := by
    apply Finsupp.lhom_ext
    intro x r
    change dualDiagonalAllWeightCoordinates k A S T q
        ((dualDiagonalAllWeightCoordinates k A S T q).symm
          (diagonalFramedDualScalarCoordinates k A S T frames q
            ((diagonalFramedDualMonomialMap k A S T a b frames).f q
              ((diagonalFramedDualScalarCoordinates k A S T frames q).symm
                (Finsupp.single x r))))) =
      dualDiagonalAllWeightCoordinates k A S T q
        ((dualDiagonalAllWeightMonomialMap k A S T a b).f q
          ((dualDiagonalAllWeightCoordinates k A S T q).symm
            (diagonalFramedDualScalarCoordinates k A S T frames q
              ((diagonalFramedDualScalarCoordinates k A S T frames q).symm
                (Finsupp.single x r)))))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      diagonalFramedDualMonomialMap_generator, dualDiagonalAllWeightMonomialMap_generator]
  apply LinearMap.ext
  intro v
  apply (dualDiagonalAllWeightCoordinates k A S T q).injective
  have value := DFunLike.congr_fun equal
    (diagonalFramedDualScalarCoordinates k A S T frames q v)
  simpa only [actual, weighted, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using value

end ToricPower.IntegralArrangement
