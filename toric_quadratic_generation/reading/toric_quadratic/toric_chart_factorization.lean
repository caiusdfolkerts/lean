module

public import PaperVerification.ToricLaurentPicard
public import PaperVerification.ToricCartierCharacterModules

@[expose] public section

/-! # Unique factorization on every actual smooth affine chart -/

noncomputable section

namespace PaperVerification.ToricCharacters

variable (k : Type*) [Field k]

def finiteLatticeCoordinates (J : Type*) [Fintype J] :
    (J → ℤ) ≃+ (Fin (Fintype.card J) → ℤ) where
  toFun x i := x ((Fintype.equivFin J).symm i)
  invFun x j := x (Fintype.equivFin J j)
  left_inv x := by funext j; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl

def finiteCharacterRingEquiv (J : Type*) [Fintype J] :
    AddMonoidAlgebra k (J → ℤ) ≃ₐ[k] torusCoordinateRing k (Fintype.card J) :=
  AddMonoidAlgebra.domCongr k k (finiteLatticeCoordinates J)

theorem finiteCharacterRing_isDomain (J : Type*) [Fintype J] :
    IsDomain (AddMonoidAlgebra k (J → ℤ)) := by
  letI := torusCoordinateRing_isDomain k (Fintype.card J)
  exact MulEquiv.isDomain _ (finiteCharacterRingEquiv k J).toMulEquiv

theorem finiteCharacterRing_uniqueFactorization (J : Type*) [Fintype J] :
    UniqueFactorizationMonoid (AddMonoidAlgebra k (J → ℤ)) :=
  (finiteCharacterRingEquiv k J).symm.toMulEquiv.uniqueFactorizationMonoid
    (torusCoordinateRing_uniqueFactorization k (Fintype.card J))

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type*) [Field k]

theorem chartRing_isDomain (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones) :
    IsDomain (monoidChartAlgebra k (dualConeMonoid s)) := by
  obtain ⟨b, I, hI, ⟨e⟩⟩ := «Σ».smooth_chart_algebra k s hs
  letI := finiteCharacterRing_isDomain k (FreeCoordinate I)
  exact MulEquiv.isDomain _ e.toMulEquiv

/-- Factoriality is proved from the actual chart algebra equivalence;
it is not an extra hypothesis on a smooth fan. -/
theorem chartRing_uniqueFactorization (s : Finset (Lattice n)) (hs : s ∈ «Σ».cones) :
    UniqueFactorizationMonoid (monoidChartAlgebra k (dualConeMonoid s)) := by
  obtain ⟨b, I, hI, ⟨e⟩⟩ := «Σ».smooth_chart_algebra k s hs
  letI := finiteCharacterRing_isDomain k (FreeCoordinate I)
  letI := finiteCharacterRing_uniqueFactorization k (FreeCoordinate I)
  exact e.symm.toMulEquiv.uniqueFactorizationMonoid inferInstance

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.chartRing_uniqueFactorization
