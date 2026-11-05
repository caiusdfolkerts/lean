module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Ideal
public import paper_verification.toric022
public import paper_verification.toric025
public import paper_verification.toric026

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricPolynomialBoundary
section Source_ToricPolynomialBoundary

-- original header: module

-- original header: public import PaperVerification.ToricAffineBoundaryOrders
-- original header: public import PaperVerification.ToricCartierOrders
-- original header: public import PaperVerification.ToricRationalPointDegrees
-- original header: public import Mathlib.RingTheory.Polynomial.Ideal

-- original header: @[expose] public section

/-!
# Boundary orders on an actual affine-line chart

The origin is the prime defined by evaluation at zero. Its ideal is
literally `(X)`, and its local ring is the actual DVR at that prime.
The coordinate has order one there and zero at every other point of
the affine chart. Arbitrary integral powers are treated without a
positivity restriction on the exponent.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical

variable (k : Type u) [Field k]

def polynomialOrigin : PrimeSpectrum (Polynomial k) :=
  ⟨RingHom.ker (Polynomial.evalRingHom (0 : k)),RingHom.ker_isPrime _⟩

theorem polynomialOrigin_ideal :
    (polynomialOrigin k).asIdeal = Ideal.span {Polynomial.X} := by
  change RingHom.ker (Polynomial.evalRingHom (0 : k)) = _
  simpa using Polynomial.ker_evalRingHom (0 : k)

instance polynomialOrigin_isMaximal : (polynomialOrigin k).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (Polynomial.evalRingHom (0 : k))
    (fun a => ⟨Polynomial.C a,by simp⟩)

theorem polynomial_X_mem_iff (p : PrimeSpectrum (Polynomial k)) :
    Polynomial.X ∈ p.asIdeal ↔ p = polynomialOrigin k := by
  constructor
  · intro h
    apply PrimeSpectrum.ext
    symm
    apply (polynomialOrigin_isMaximal k).eq_of_le p.isPrime.ne_top
    rw [polynomialOrigin_ideal]
    apply Ideal.span_le.mpr
    intro q hq
    obtain rfl := Set.mem_singleton_iff.mp hq
    exact h
  · rintro rfl
    rw [polynomialOrigin_ideal]
    exact Ideal.subset_span (Set.mem_singleton _)

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- A regular germ outside the affine prime is a unit even if no DVR
structure is specified. At other codimensions the order is zero by its
ordinary definition. -/
theorem affineOpen_order_zero_of_not_mem (R : CommRingCat.{u})
    [IsDomain R] (j : Spec R ⟶ X) [IsOpenImmersion j]
    (p : PrimeSpectrum R) (r : R) (hr : r ∉ p.asIdeal) :
    X.ord (affineOpenCoordinateMap R j r) (j p) = 0 := by
  by_cases hc : Order.coheight (j p) = 1
  · letI : Ring.KrullDimLE 1 (X.presheaf.stalk (j p)) :=
      krullDimLE_of_coheight_le hc.le
    have hu : IsUnit (algebraMap R (Localization.AtPrime p.asIdeal) r) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff
        (S := Localization.AtPrime p.asIdeal) (I := p.asIdeal) r).mpr hr
    have hr0 : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
    have hr' : affineOpenCoordinateMap R j r ≠ 0 :=
      (map_ne_zero_iff _ (affineOpenCoordinateMap_injective R j)).mpr hr0
    rw [X.ord_eq_iff hc hr']
    change Ring.ordFrac (X.presheaf.stalk (j p))
      (affineOpenCoordinateMap R j r) = WithZero.exp (0 : ℤ)
    rw [← affineOpenStalkEquiv_functionField R j p r]
    have hu' : IsUnit ((affineOpenStalkEquiv R j p)
        (algebraMap R (Localization.AtPrime p.asIdeal) r)) :=
      hu.map (affineOpenStalkEquiv R j p).toRingHom
    simpa only [WithZero.exp_zero] using Ring.ordFrac_of_isUnit hu'
  · exact X.ord_eq_zero_of_coheight_neq_one hc _

variable (j : Spec (.of (Polynomial k)) ⟶ X) [IsOpenImmersion j]

/-- The order of the literal affine coordinate is supported precisely
at the actual origin of that chart. -/
theorem affineLine_coordinate_order (p : PrimeSpectrum (Polynomial k)) :
    X.ord (affineOpenCoordinateMap (.of (Polynomial k)) j Polynomial.X) (j p) =
      if p = polynomialOrigin k then 1 else 0 := by
  by_cases hp : p=polynomialOrigin k
  · subst p
    rw [if_pos rfl]
    exact affineOpen_order_principalPrime (.of (Polynomial k)) j
      (polynomialOrigin k) Polynomial.X Polynomial.X_ne_zero (polynomialOrigin_ideal k)
  · rw [if_neg hp]
    exact affineOpen_order_zero_of_not_mem (.of (Polynomial k)) j p Polynomial.X
      (fun h => hp ((polynomial_X_mem_iff k p).mp h))

theorem affineLine_coordinate_zpow_order (m : ℤ)
    (p : PrimeSpectrum (Polynomial k)) :
    X.ord ((affineOpenCoordinateMap (.of (Polynomial k)) j Polynomial.X)^m) (j p) =
      if p=polynomialOrigin k then m else 0 := by
  have hX : affineOpenCoordinateMap (.of (Polynomial k)) j Polynomial.X ≠ 0 :=
    (map_ne_zero_iff _ (affineOpenCoordinateMap_injective _ j)).mpr Polynomial.X_ne_zero
  rw [rationalOrder_zpow hX,affineLine_coordinate_order]
  split_ifs <;> simp

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineLine_coordinate_zpow_order
end
end Source_ToricPolynomialBoundary
-- END ORIGINAL PaperVerification.ToricPolynomialBoundary


-- BEGIN ORIGINAL PaperVerification.ToricFanNoetherian
section Source_ToricFanNoetherian

-- original header: module

-- original header: public import PaperVerification.ToricChartFactorization
-- original header: public import PaperVerification.ToricFanSchemeIntegral
-- original header: public import Mathlib.RingTheory.Localization.Submodule
-- original header: public import Mathlib.RingTheory.Polynomial.Basic
-- original header: public import Mathlib.AlgebraicGeometry.Noetherian

-- original header: @[expose] public section

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
end
end Source_ToricFanNoetherian
-- END ORIGINAL PaperVerification.ToricFanNoetherian


