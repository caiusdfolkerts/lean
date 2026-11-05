module

public import PaperVerification.ToricChartFactorization
public import PaperVerification.ToricFanSchemeIntegral
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

/-!
# Noetherianity of the actual fan scheme

The coordinate rings are actual polynomial rings over iterated Laurent
extensions, up to the previously constructed algebra equivalences. Hilbert's
basis theorem and localization prove that they are Noetherian. The actual
finite affine open cover then proves that the glued scheme is Noetherian.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

variable (k : Type*) [Field k]

theorem laurent_isNoetherianRing (A : Type*) [CommRing A]
    [IsNoetherianRing A] : IsNoetherianRing (AddMonoidAlgebra A ℤ) :=
  IsLocalization.isNoetherianRing
    (Submonoid.powers (Polynomial.X : Polynomial A))
    (AddMonoidAlgebra A ℤ) inferInstance

theorem torusCoordinateRing_isNoetherianRing (n : ℕ) :
    IsNoetherianRing (torusCoordinateRing k n) := by
  induction n with
  | zero =>
      exact isNoetherianRing_of_ringEquiv k
        (AddMonoidAlgebra.uniqueAlgEquiv k (Fin 0 → ℤ)).symm.toRingEquiv
  | succ n ih =>
      letI := ih
      letI := laurent_isNoetherianRing (torusCoordinateRing k n)
      exact isNoetherianRing_of_ringEquiv
        (AddMonoidAlgebra (torusCoordinateRing k n) ℤ)
        (torusCoordinateRingSucc k n).symm.toRingEquiv

theorem finiteCharacterRing_isNoetherianRing (J : Type*) [Fintype J] :
    IsNoetherianRing (AddMonoidAlgebra k (J → ℤ)) := by
  letI := torusCoordinateRing_isNoetherianRing k (Fintype.card J)
  exact isNoetherianRing_of_ringEquiv _ (finiteCharacterRingEquiv k J).symm.toRingEquiv

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open PaperVerification.ToricCharacters
open AlgebraicGeometry CategoryTheory

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type*) [Field k]

theorem chartRing_isNoetherianRing (s : Finset (Lattice n)) (hs : s∈«Σ».cones) :
    IsNoetherianRing (monoidChartAlgebra k (dualConeMonoid s)) := by
  obtain ⟨b,I,hI,⟨e⟩⟩ := «Σ».smooth_chart_algebra k s hs
  letI := finiteCharacterRing_isNoetherianRing k (FreeCoordinate I)
  exact isNoetherianRing_of_ringEquiv _ e.symm.toRingEquiv

instance fanScheme_isLocallyNoetherian : IsLocallyNoetherian («Σ».fanScheme k) := by
  apply (isLocallyNoetherian_iff_openCover («Σ».fanSchemeOpenCover k)).mpr
  intro s
  letI := «Σ».chartRing_isNoetherianRing k s.val s.property
  change IsLocallyNoetherian (Spec (CommRingCat.of
    (monoidChartAlgebra k (dualConeMonoid s.val))))
  infer_instance

instance fanScheme_isNoetherian : IsNoetherian («Σ».fanScheme k) where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace := by
    letI : Finite («Σ».fanSchemeOpenCover k).I₀ :=
      inferInstanceAs (Finite «Σ».ConeIndex)
    letI : ∀ s : («Σ».fanSchemeOpenCover k).I₀,
        CompactSpace ((«Σ».fanSchemeOpenCover k).X s) := fun s => by
      change CompactSpace (Spec (CommRingCat.of
        (monoidChartAlgebra k (dualConeMonoid s.val))))
      infer_instance
    exact Scheme.OpenCover.compactSpace («Σ».fanSchemeOpenCover k)

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanScheme_isNoetherian
