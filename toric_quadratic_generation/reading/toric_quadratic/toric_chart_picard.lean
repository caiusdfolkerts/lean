module

public import PaperVerification.ToricChartFactorization
public import PaperVerification.ToricAffinePicard

@[expose] public section

/-! # Triviality of the actual Picard group on every smooth fan chart -/

noncomputable section

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open AlgebraicGeometry CategoryTheory

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type*) [Field k]

theorem chartPic_subsingleton (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones) :
    Subsingleton (CommRing.Pic (monoidChartAlgebra k (dualConeMonoid s))) := by
  letI := «Σ».chartRing_isDomain k s hs
  letI := «Σ».chartRing_uniqueFactorization k s hs
  infer_instance

/-- Every actual invertible sheaf on a smooth cone chart is trivial.
The assertion is for the genuine structure sheaf, not a character module. -/
def chartInvertibleSheafIso (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones)
    (M : (Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s)))).Modules)
    (hM : IsInvertibleModule M) :
    M ≅ SheafOfModules.unit
      (Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s)))).ringCatSheaf := by
  letI := «Σ».chartPic_subsingleton k s hs
  exact affineInvertibleSheafIso M hM

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.chartInvertibleSheafIso
