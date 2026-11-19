module

public import ToricPower.DualDiagonalSupportedSheaf
public import ToricPower.DiagonalExteriorDualLabels
public import ToricPower.DiagonalPullbackExteriorIso
public import ToricPower.DiagonalTopCellLabels

/-!
# The actual global diagonal top quotient and its boundary-labelled maps

The map in this file is the genuine quotient to the actual top homology
of the internal-dual diagonal complex. Pulling this map back gives maps
from the actual top-cell labels to the actual line `J = δ*H`.

Every top cell restricts to the literal boundary Cartier line, so each
gives a specified global morphism from that line to `J`. The assertion
that such a morphism is an isomorphism requires the additional local
top-class calculation; it is not part of these definitions.

Ordinary pullback along the diagonal is not asserted to preserve the
quasi-isomorphism of the original dual complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "X" => fan.algebraicRealization
local notation "Y" => toricDiagonalProduct fan
local notation "K" => diagonalGlobalInternalDualComplex fan nonempty regular basis rays
local notation "H" => dualDiagonalTopSheaf fan nonempty regular basis rays
local notation "J" => dualDiagonalLineSheaf fan nonempty regular basis rays
local notation "P" => Scheme.Modules.pullback (toricDiagonal fan)

local instance diagonalTopQuotientCellsFintype (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _
local instance diagonalTopQuotientBiproducts : HasFiniteBiproducts (Y).Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- The original cochain quotient to actual top homology. -/
def dualDiagonalTopQuotient : (K).X n ⟶ H :=
  (K).pOpcycles n ≫
    ((K).isoHomologyι n (n+1) (by simp)
      (diagonalGlobalInternalDual_top_differential fan nonempty regular basis rays)).inv

@[reassoc]
theorem dualDiagonalTopQuotient_boundary (q : ℕ) :
    (K).d q n ≫ dualDiagonalTopQuotient fan nonempty regular basis rays = 0 := by
  rw [dualDiagonalTopQuotient, ← Category.assoc,
    HomologicalComplex.d_pOpcycles, zero_comp]

/-- The original top-cell inclusion, its actual inverse-label
identification, and the genuine top quotient. -/
def diagonalInverseCellTopQuotient (c : NormalizedCell A n) :
    diagonalInverseProductSheaf fan nonempty regular basis rays c ⟶ H :=
  biproduct.ι
      (fun d : NormalizedCell A n =>
        diagonalInverseProductSheaf fan nonempty regular basis rays d) c ≫
    (diagonalExteriorDualTermIso fan nonempty regular basis rays n).hom ≫
      dualDiagonalTopQuotient fan nonempty regular basis rays

/-- Actual pullback gives a top-quotient chain map. No exactness of
diagonal pullback, or of its mapped dual complex, is presumed. -/
def dualDiagonalPulledTopAugmentation :
    (((P).mapHomologicalComplex (.up ℕ)).obj K) ⟶
      (HomologicalComplex.single (X).Modules (.up ℕ) n).obj J :=
  HomologicalComplex.mkHomToSingle
    ((P).map (dualDiagonalTopQuotient fan nonempty regular basis rays)) (by
      intro q relation
      change (P).map ((K).d q n) ≫ (P).map
        (dualDiagonalTopQuotient fan nonempty regular basis rays) = 0
      rw [← Functor.map_comp, dualDiagonalTopQuotient_boundary, Functor.map_zero])

/-- The literal boundary line used in the paper's normalization. -/
def diagonalBoundaryLine : (X).Modules := by
  letI := toricSchemeIntegral fan nonempty
  exact (invariantCartierDivisor fan nonempty regular (fun _ => 1)).sheaf

/-- Every top-cell inverse exterior label restricts to this actual
boundary line, by actual pullback, Cartier multiplication, and the exact
top-cell coefficient identity. -/
def diagonalTopCellBoundaryIso (c : NormalizedCell A n) :
    (P).obj (diagonalInverseProductSheaf fan nonempty regular basis rays c) ≅
      diagonalBoundaryLine fan nonempty regular := by
  letI := toricSchemeIntegral fan nonempty
  letI (D : CartierDivisor X) : D.sheaf.IsQuasicoherent := by
    letI := D.isInvertible_sheaf
    infer_instance
  exact diagonalPullbackExternalIso fan
      (-(invariantCartierDivisor fan nonempty regular
        (diagonalLeftCoefficients fan basis rays c))).sheaf
      (-(invariantCartierDivisor fan nonempty regular
        (diagonalRightCoefficients fan basis rays c))).sheaf ≪≫
    tensorIso
      (eqToIso (congrArg CartierDivisor.sheaf
        (invariantCartierDivisor_neg fan nonempty regular
          (diagonalLeftCoefficients fan basis rays c))).symm)
      (eqToIso (congrArg CartierDivisor.sheaf
        (invariantCartierDivisor_neg fan nonempty regular
          (diagonalRightCoefficients fan basis rays c))).symm) ≪≫
    invariantCartierTensorIso fan nonempty regular
      (-diagonalLeftCoefficients fan basis rays c)
      (-diagonalRightCoefficients fan basis rays c) ≪≫
    eqToIso (congrArg (fun b : fan.Ray → ℤ =>
      (invariantCartierDivisor fan nonempty regular b).sheaf)
      (diagonalInverseCoefficient_sum_top fan basis rays c))

/-- This specified global morphism is the candidate boundary
identification whose invertibility is tested by the actual local top
classes. Its definition makes no such invertibility assumption. -/
def diagonalBoundaryToTopLine (c : NormalizedCell A n) :
    diagonalBoundaryLine fan nonempty regular ⟶ J :=
  (diagonalTopCellBoundaryIso fan nonempty regular basis rays c).inv ≫
    (P).map (diagonalInverseCellTopQuotient fan nonempty regular basis rays c)

end ToricPower

end
