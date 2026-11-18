module

public import ToricPower.DualDiagonalFramedWeightDecomposition
public import ToricPower.DualDiagonalMonomialMaps

/-!
# Genuine monomial maps on the unrestricted weight sum

The map is obtained from the actual monomial maps of the original
cellular coefficient complexes and the coproduct universal property.
Its complete coordinate formula retains every character and every cell.
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

/-- The total-character and actual first-character shift of a monomial. -/
def dualDiagonalAllWeightMonomialIndex (q : ℕ) :
    DualDiagonalAllWeightIndex A S T q → DualDiagonalAllWeightIndex A S T q :=
  fun x => ⟨x.1 + a.val + b.val, dualDiagonalWeightMonomialIndex A S T x.1 a b q x.2⟩

/-- A cocone into the full sum, using the actual chain maps in every
weight and the genuine target weight inclusions. -/
def dualDiagonalAllWeightMonomialCocone :
    Cocone (Discrete.functor (fun u => dualDiagonalWeightComplex A S T u k)) where
  pt := dualDiagonalAllWeightComplex k A S T
  ι := Discrete.natTrans (fun u => dualDiagonalWeightMonomialMap A S T u.as a b k ≫
    ModuleDirectSum.complexInclusion k (fun v => dualDiagonalWeightComplex A S T v k)
      (u.as + a.val + b.val))

/-- The actual monomial map of the complete unrestricted complex. -/
def dualDiagonalAllWeightMonomialMap :
    dualDiagonalAllWeightComplex k A S T ⟶ dualDiagonalAllWeightComplex k A S T :=
  (ModuleDirectSum.complexCoconeIsColimit k
    (fun u => dualDiagonalWeightComplex A S T u k)).desc
      (dualDiagonalAllWeightMonomialCocone k A S T a b)

@[reassoc]
theorem dualDiagonalAllWeightMonomialMap_inclusion (u : Fin n → ℤ) :
    ModuleDirectSum.complexInclusion k (fun v => dualDiagonalWeightComplex A S T v k) u ≫
        dualDiagonalAllWeightMonomialMap k A S T a b =
      dualDiagonalWeightMonomialMap A S T u a b k ≫
        ModuleDirectSum.complexInclusion k (fun v => dualDiagonalWeightComplex A S T v k)
          (u + a.val + b.val) :=
  (ModuleDirectSum.complexCoconeIsColimit k
    (fun u => dualDiagonalWeightComplex A S T u k)).fac
      (dualDiagonalAllWeightMonomialCocone k A S T a b) ⟨u⟩

/-- Its action on each original full Laurent generator is precisely the
actual monomial shift, with unchanged coefficient. -/
theorem dualDiagonalAllWeightMonomialMap_generator (q : ℕ)
    (x : DualDiagonalAllWeightIndex A S T q) (r : k) :
    dualDiagonalAllWeightCoordinates k A S T q
      ((dualDiagonalAllWeightMonomialMap k A S T a b).f q
        ((dualDiagonalAllWeightCoordinates k A S T q).symm (Finsupp.single x r))) =
      Finsupp.single (dualDiagonalAllWeightMonomialIndex A S T a b q x) r := by
  rcases x with ⟨u, i⟩
  let sourceCoordinates := translatedWeightCellularCoordinates A
    (dualDiagonalWeightAllowed A S T u) (dualDiagonalWeightAllowed_map A S T u) k q
  let targetCoordinates := translatedWeightCellularCoordinates A
    (dualDiagonalWeightAllowed A S T (u+a.val+b.val))
    (dualDiagonalWeightAllowed_map A S T (u+a.val+b.val)) k q
  have inclusion := ModuleDirectSum.complexCoordinates_symm_single k
    (fun u => dualDiagonalWeightComplex A S T u k)
    (fun u q => DualDiagonalWeightIndex A S T u q)
    (fun u q => translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
      (dualDiagonalWeightAllowed_map A S T u) k q) q u i r
  change (dualDiagonalAllWeightCoordinates k A S T q).symm
      (Finsupp.single (⟨u, i⟩ : DualDiagonalAllWeightIndex A S T q) r) =
    (ModuleDirectSum.complexInclusion k (fun v => dualDiagonalWeightComplex A S T v k) u).f q
      (sourceCoordinates.symm (Finsupp.single i r)) at inclusion
  rw [inclusion]
  have component := congrArg (fun f => f.f q)
    (dualDiagonalAllWeightMonomialMap_inclusion k A S T a b u)
  have value := ConcreteCategory.congr_hom component (sourceCoordinates.symm (Finsupp.single i r))
  change (dualDiagonalAllWeightMonomialMap k A S T a b).f q
      ((ModuleDirectSum.complexInclusion k (fun v => dualDiagonalWeightComplex A S T v k) u).f q
        (sourceCoordinates.symm (Finsupp.single i r))) =
    (ModuleDirectSum.complexInclusion k (fun v => dualDiagonalWeightComplex A S T v k)
      (u+a.val+b.val)).f q
        ((dualDiagonalWeightMonomialMap A S T u a b k).f q
          (sourceCoordinates.symm (Finsupp.single i r))) at value
  rw [value]
  have image : (dualDiagonalWeightMonomialMap A S T u a b k).f q
      (sourceCoordinates.symm (Finsupp.single i r)) =
    targetCoordinates.symm
      (Finsupp.single (dualDiagonalWeightMonomialIndex A S T u a b q i) r) := by
    apply targetCoordinates.injective
    rw [LinearEquiv.apply_symm_apply]
    exact translatedCoefficientComplexMap_generator A
      (dualDiagonalWeightAllowed A S T u) (dualDiagonalWeightAllowed A S T (u+a.val+b.val))
      (dualDiagonalWeightAllowed_map A S T u)
      (dualDiagonalWeightAllowed_map A S T (u+a.val+b.val)) a.val
      (dualDiagonalWeightMonomial_permitted A S T u a b) k q i r
  rw [image]
  exact ModuleDirectSum.complexCoordinates_inclusion_generator k
    (fun u => dualDiagonalWeightComplex A S T u k)
    (fun u q => DualDiagonalWeightIndex A S T u q)
    (fun u q => translatedWeightCellularCoordinates A (dualDiagonalWeightAllowed A S T u)
      (dualDiagonalWeightAllowed_map A S T u) k q) q (u+a.val+b.val) _ r

end ToricPower.IntegralArrangement
