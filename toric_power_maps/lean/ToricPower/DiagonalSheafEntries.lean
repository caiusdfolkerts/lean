module

public import ToricPower.DiagonalGlobalColumns
public import ToricPower.DiagonalFanLabels
public import ToricPower.DivisorWeightMonomialMaps
public import ToricPower.SheafTensor
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Actual global sheaf entries of the cellular diagonal

The matrix of ray pairings is obtained from an integral character basis
and an enumeration of the actual fan rays.  The two labels are the actual
Cartier sheaves with coefficients `-ceil(-Ax)` and `-ceil(Ax)`.

Every supported term of the genuine universal-cover cellular boundary
gives actual monomial morphisms of both Cartier factors.  Pulling these
morphisms to the actual product over `Spec ℂ` and tensoring gives the
global diagonal matrix entry.  The finite boundary column is then a sum
of these actual morphisms, with its actual incidence coefficients.

No complex or exactness property is assumed in this construction.  The
square-zero and local-resolution comparisons are separate obligations.
This is development source until checked by the pinned Lean compiler.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric
open scoped Classical BigOperators

namespace ToricPower

open IntegralArrangement

local instance diagonalSchemeFiniteBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones)
  (regular : fan.IsRegular)

variable {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ))
  (rays : Fin s ≃ fan.Ray)

def diagonalLeftSheaf {d : ℕ}
    (c : NormalizedCell (fanArrangementMatrix fan basis rays) d) :
    fan.algebraicRealization.Modules :=
  letI := toricSchemeIntegral fan nonempty
  (invariantCartierDivisor fan nonempty regular
    (diagonalLeftCoefficients fan basis rays c)).sheaf

def diagonalRightSheaf {d : ℕ}
    (c : NormalizedCell (fanArrangementMatrix fan basis rays) d) :
    fan.algebraicRealization.Modules :=
  letI := toricSchemeIntegral fan nonempty
  (invariantCartierDivisor fan nonempty regular
    (diagonalRightCoefficients fan basis rays c)).sheaf

variable (d : ℕ)
  (j : NormalizedCell (fanArrangementMatrix fan basis rays) (d+1))
  (p : DiagonalGlobalColumnTerm ℂ (fanArrangementMatrix fan basis rays) d j)

/-- Every supported left factor has a globally regular actual character
map; its inequality is proved from genuine cellular incidence. -/
def diagonalLeftMonomialEntry :
    diagonalLeftSheaf fan nonempty regular basis rays j ⟶
      diagonalLeftSheaf fan nonempty regular basis rays p.val.1 := by
  letI := toricSchemeIntegral fan nonempty
  apply toricCartierMonomialMap fan nonempty regular
    (diagonalLeftCoefficients fan basis rays j)
    (diagonalLeftCoefficients fan basis rays p.val.1)
    (basis.equivFun.symm p.val.2)
  intro ρ
  have hp := (diagonalGlobalColumnTerm_regular ℂ
    (fanArrangementMatrix fan basis rays) d j p (rays.symm ρ)).1
  rw [fanArrangementMatrix_character] at hp
  unfold diagonalLeftCoefficients
  omega

/-- The right factor uses the opposite character.  Both maps exist on
the whole fan, including all nonmaximal and non-full-dimensional cones. -/
def diagonalRightMonomialEntry :
    diagonalRightSheaf fan nonempty regular basis rays j ⟶
      diagonalRightSheaf fan nonempty regular basis rays p.val.1 := by
  letI := toricSchemeIntegral fan nonempty
  apply toricCartierMonomialMap fan nonempty regular
    (diagonalRightCoefficients fan basis rays j)
    (diagonalRightCoefficients fan basis rays p.val.1)
    (-(basis.equivFun.symm p.val.2))
  intro ρ
  have hp := (diagonalGlobalColumnTerm_regular ℂ
    (fanArrangementMatrix fan basis rays) d j p (rays.symm ρ)).2
  rw [fanArrangementMatrix_character] at hp
  unfold diagonalRightCoefficients
  simp only [AddMonoidHom.neg_apply]
  omega

/-- The line-bundle term on the literal product, formed by the actual
scheme-module pullbacks and tensor product. -/
def diagonalProductSheaf {d : ℕ}
    (c : NormalizedCell (fanArrangementMatrix fan basis rays) d) :
    (toricDiagonalProduct fan).Modules :=
  (Scheme.Modules.pullback (toricDiagonalFirst fan)).obj
      (diagonalLeftSheaf fan nonempty regular basis rays c) ⊗
    (Scheme.Modules.pullback (toricDiagonalSecond fan)).obj
      (diagonalRightSheaf fan nonempty regular basis rays c)

/-- The actual monomial map with character pair `(a,-a)`. -/
def diagonalProductMonomialEntry :
    diagonalProductSheaf fan nonempty regular basis rays j ⟶
      diagonalProductSheaf fan nonempty regular basis rays p.val.1 :=
  (Scheme.Modules.pullback (toricDiagonalFirst fan)).map
      (diagonalLeftMonomialEntry fan nonempty regular basis rays d j p) ⊗ₘ
    (Scheme.Modules.pullback (toricDiagonalSecond fan)).map
      (diagonalRightMonomialEntry fan nonempty regular basis rays d j p)

local instance normalizedCellsFintype (e : ℕ) :
    Fintype (NormalizedCell (fanArrangementMatrix fan basis rays) e) := Fintype.ofFinite _

local instance supportedTermsFintype :
    Fintype (DiagonalGlobalColumnTerm ℂ (fanArrangementMatrix fan basis rays) d j) :=
  Fintype.ofFinite _

/-- The actual finite sum of labelled line bundles in one homological
degree of the proposed diagonal resolution. -/
def diagonalGlobalSheafTerm (e : ℕ) : (toricDiagonalProduct fan).Modules :=
  ⨁ (fun c : NormalizedCell (fanArrangementMatrix fan basis rays) e =>
    diagonalProductSheaf fan nonempty regular basis rays c)

/-- A finite column of actual sheaf morphisms, with the actual complex
cellular incidence coefficient acting through the structure map. -/
def diagonalGlobalSheafColumn :
    diagonalProductSheaf fan nonempty regular basis rays j ⟶
      diagonalGlobalSheafTerm fan nonempty regular basis rays d :=
  ∑ p : DiagonalGlobalColumnTerm ℂ (fanArrangementMatrix fan basis rays) d j,
    diagonalProductMonomialEntry fan nonempty regular basis rays d j p ≫
      Scheme.Modules.globalSectionsSmul
        (diagonalProductSheaf fan nonempty regular basis rays p.val.1)
        (Scheme.Modules.baseRingToGlobalSections ℂ (toricDiagonalProduct fan)
          (diagonalGlobalColumn ℂ (fanArrangementMatrix fan basis rays) d j p.val)) ≫
      biproduct.ι
        (fun c : NormalizedCell (fanArrangementMatrix fan basis rays) d =>
          diagonalProductSheaf fan nonempty regular basis rays c) p.val.1

/-- The global matrix, assembled by the actual finite biproduct universal
property.  Its chain and exactness laws are not built into its definition. -/
def diagonalGlobalSheafBoundary :
    diagonalGlobalSheafTerm fan nonempty regular basis rays (d+1) ⟶
      diagonalGlobalSheafTerm fan nonempty regular basis rays d :=
  biproduct.desc (fun j =>
    diagonalGlobalSheafColumn fan nonempty regular basis rays d j)

theorem diagonalGlobalSheafBoundary_column :
    biproduct.ι
        (fun c : NormalizedCell (fanArrangementMatrix fan basis rays) (d+1) =>
          diagonalProductSheaf fan nonempty regular basis rays c) j ≫
      diagonalGlobalSheafBoundary fan nonempty regular basis rays d =
        diagonalGlobalSheafColumn fan nonempty regular basis rays d j := by
  simp only [diagonalGlobalSheafBoundary, biproduct.ι_desc]

end ToricPower
