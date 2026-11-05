module

public import Continuation.Runtime.RealValuativeCharts
public import Continuation.Runtime.ValuativeAffineCover

/-!
# Valuative tests of the actual affine scheme charts

These maps are spectra of the literal character evaluations and the
literal inclusions into the Laurent ring. Full faithfulness of `Spec`
turns an arbitrary geometric lift back into the ring factorization that
detects its real cone. Universal closedness then proves that the cones of
any actual covering family of these charts cover every real cocharacter.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open AlgebraicGeometry CategoryTheory Opposite
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k]

/-- The generic-point map of the actual Hahn valuation ring. -/
def realValuationGeneric :
    Spec (CommRingCat.of (HahnSeries ℝ k)) ⟶
      Spec (CommRingCat.of (RealCharacterValuationRing k)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (RealCharacterValuationRing k) (HahnSeries ℝ k)))

instance realValuationGeneric_isDominant : IsDominant (realValuationGeneric k) := by
  constructor
  change DenseRange (PrimeSpectrum.comap
    (algebraMap (RealCharacterValuationRing k) (HahnSeries ℝ k)))
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
  rw [(RingHom.injective_iff_ker_eq_bot _).mp
    (IsFractionRing.injective (RealCharacterValuationRing k) (HahnSeries ℝ k))]
  exact bot_le

variable {M : Type} [AddCommGroup M] (w : M →+ ℝ) (S : AddSubmonoid M)

/-- The original Hahn-valued point of the character torus. -/
def realWeightTorusPoint :
    Spec (CommRingCat.of (HahnSeries ℝ k)) ⟶
      Spec (CommRingCat.of (AddMonoidAlgebra k M)) :=
  Spec.map (CommRingCat.ofHom (realCharacterEvaluation k w).toRingHom)

/-- The torus morphism of a literal character chart. -/
def characterChartTorusMap :
    Spec (CommRingCat.of (AddMonoidAlgebra k M)) ⟶ monoidChartScheme k S :=
  Spec.map (CommRingCat.ofHom (monoidChartAlgebra k S).val.toRingHom)

/-- All face maps preserve the original Laurent characters literally. -/
@[reassoc] theorem characterChartTorusMap_comp_face {S U : AddSubmonoid M} (hSU : S ≤ U) :
    characterChartTorusMap k U ≫ monoidChartSpecMap k hSU =
      characterChartTorusMap k S := by
  rw [characterChartTorusMap, monoidChartSpecMap, ← Spec.map_comp]
  rfl

/-- A nonnegative character weight gives an actual lift to the chart. -/
def realCharacterChartLift (hS : ∀ m ∈ S, 0 ≤ w m) :
    Spec (CommRingCat.of (RealCharacterValuationRing k)) ⟶ monoidChartScheme k S :=
  Spec.map (CommRingCat.ofHom (realChartCharacterEvaluation k w S hS).toRingHom)

theorem realCharacterChartLift_generic (hS : ∀ m ∈ S, 0 ≤ w m) :
    realValuationGeneric k ≫ realCharacterChartLift k w S hS =
      realWeightTorusPoint k w ≫ characterChartTorusMap k S := by
  have h := congrArg (fun φ : monoidChartAlgebra k S →ₐ[k] HahnSeries ℝ k =>
    Spec.map (CommRingCat.ofHom φ.toRingHom))
      (realChartCharacterEvaluation_generic k w S hS)
  change Spec.map (CommRingCat.ofHom
      ((algebraMap (RealCharacterValuationRing k) (HahnSeries ℝ k)).comp
        (realChartCharacterEvaluation k w S hS).toRingHom)) =
    Spec.map (CommRingCat.ofHom ((realCharacterEvaluation k w).toRingHom.comp
      (monoidChartAlgebra k S).val.toRingHom)) at h
  simpa only [realValuationGeneric, realCharacterChartLift, realWeightTorusPoint,
    characterChartTorusMap, ← Spec.map_comp, CommRingCat.ofHom_comp] using h

theorem realCharacterChartLift_base (hS : ∀ m ∈ S, 0 ≤ w m) :
    realCharacterChartLift k w S hS ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (monoidChartAlgebra k S))) =
        Spec.map (CommRingCat.ofHom (algebraMap k (RealCharacterValuationRing k))) := by
  rw [realCharacterChartLift, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (realChartCharacterEvaluation k w S hS).commutes c

/-- Every geometric lift, with no chosen algebra-homomorphism encoding,
forces the exact nonnegative character inequalities. -/
theorem nonnegative_of_realCharacterChartLift
    (l : Spec (CommRingCat.of (RealCharacterValuationRing k)) ⟶ monoidChartScheme k S)
    (hl : realValuationGeneric k ≫ l =
      realWeightTorusPoint k w ≫ characterChartTorusMap k S) :
    ∀ m ∈ S, 0 ≤ w m := by
  let φ : CommRingCat.of (monoidChartAlgebra k S) ⟶
      CommRingCat.of (RealCharacterValuationRing k) :=
    (Spec.fullyFaithful.preimage l).unop
  have hφ : Spec.map φ = l := Spec.fullyFaithful.map_preimage l
  apply nonnegative_of_realChart_ringFactorization k w S φ.hom
  have he : φ ≫ CommRingCat.ofHom
        (algebraMap (RealCharacterValuationRing k) (HahnSeries ℝ k)) =
      CommRingCat.ofHom (monoidChartAlgebra k S).val.toRingHom ≫
        CommRingCat.ofHom (realCharacterEvaluation k w).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hφ]
    exact hl
  exact congrArg CommRingCat.Hom.hom he

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (j : Spec (CommRingCat.of (AddMonoidAlgebra k M)) ⟶ X)
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k M))))

/-- The actual valuative square associated to an arbitrary real weight. -/
def realWeightValuativeSquare : ValuativeCommSq f where
  R := RealCharacterValuationRing k
  K := HahnSeries ℝ k
  i₁ := realWeightTorusPoint k w ≫ j
  i₂ := Spec.map (CommRingCat.ofHom (algebraMap k (RealCharacterValuationRing k)))
  commSq := ⟨by
    rw [Category.assoc, hj]
    simp only [realWeightTorusPoint, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact (realCharacterEvaluation k w).commutes c⟩

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricSchemes

variable (k : Type u) [Field k] {n : ℕ}
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f]
    (j : Spec (CommRingCat.of (AddMonoidAlgebra k (Lattice n))) ⟶ X)
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Lattice n)))))
    {J : Type v} (b : J → Module.Basis (Fin n) ℤ (Lattice n)) (I : J → Finset (Fin n))
    (a : ∀ i, monoidChartScheme k (coordinateConeMonoid (b i) (I i)) ⟶ X)
    [∀ i, IsOpenImmersion (a i)]
    (hT : ∀ i, characterChartTorusMap k (coordinateConeMonoid (b i) (I i)) ≫ a i = j)

include f j hj hT

/-- Universal closedness of the original scheme forces the real cones
of an actual covering family of smooth character charts to be complete.
There is no rational-direction restriction in this conclusion. -/
theorem realCones_cover_of_actual_chartCover
    (hcover : ∀ x : X, ∃ i z, a i z = x) (x : Ambient n) :
    ∃ i, x ∈ latticeRayCone ((I i).image (integralDualBasis (b i))) := by
  let C : X.OpenCover := Scheme.Cover.mkOfCovers J
    (fun i => monoidChartScheme k (coordinateConeMonoid (b i) (I i))) a hcover
  let V := realWeightValuativeSquare k (latticeRealWeight x) f j hj
  obtain ⟨i, l, hl, hbase⟩ := exists_valuativeLift_into_openCover f V C
  refine ⟨i, (mem_dualBasisCone_iff_nonnegative_characters (b i) (I i) x).mpr ?_⟩
  apply nonnegative_of_realCharacterChartLift k (latticeRealWeight x)
    (coordinateConeMonoid (b i) (I i)) l
  apply (cancel_mono (a i)).mp
  change realValuationGeneric k ≫ l ≫ a i =
    realWeightTorusPoint k (latticeRealWeight x) ≫ j at hl
  simpa only [Category.assoc, hT] using hl

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.nonnegative_of_realCharacterChartLift
#print axioms PaperVerification.ToricSchemes.realCones_cover_of_actual_chartCover
