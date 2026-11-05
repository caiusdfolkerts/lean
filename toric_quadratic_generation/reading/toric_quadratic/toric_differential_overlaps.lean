module

public import PaperVerification.ToricCanonicalDifferentialGluing

@[expose] public section

/-!
# Natural differential localization on actual fan overlaps

The maps below are induced by the literal inclusions of character
algebras. Every cone chart has a free Kähler module, obtained by
localizing a full chart. Its top differential module injects into the
actual generic differential module. Consequently agreement on an
intersection chart is exactly agreement of the actual generic forms.
This supplies the overlap compatibility of the differential-volume
sheaf, independently of its later Cartier description.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u

namespace PaperVerification.ToricCharacters

open KaehlerDifferential

/-- Coefficients after the genuine differential map to a coefficient
ring. Keeping this composition over abstract rings fixes the native
restricted exterior-module structure before applying it to a chart. -/
def topDifferentialCoefficient (k R K : Type*)
    [CommRing k] [CommRing R] [CommRing K]
    [Algebra k R] [Algebra k K] [Algebra R K] [IsScalarTower k R K]
    (n : ℕ) (b : Module.Basis (Fin n) K Ω[K⁄k]) :
    (⋀[R]^n Ω[R⁄k]) →ₗ[R] K :=
  ((basisTopExteriorEquiv b).toLinearMap.restrictScalars R).comp
    (topDifferentialMap k R K n)

/-- Equal actual structure homomorphisms induce the same coefficient
function. The scalar-tower witnesses are propositions; no definitional
identification of unequal chosen algebra structures is assumed. -/
theorem topDifferentialCoefficient_algebra_eq (k R K : Type*)
    [CommRing k] [CommRing R] [CommRing K] [Algebra k R] [Algebra k K]
    (A B : Algebra R K) (hAB : A=B)
    (hA : letI := A; IsScalarTower k R K)
    (hB : letI := B; IsScalarTower k R K)
    (n : ℕ) (b : Module.Basis (Fin n) K Ω[K⁄k]) (ω : ⋀[R]^n Ω[R⁄k]) :
    (letI := A; letI := hA; topDifferentialCoefficient k R K n b ω)=
      (letI := B; letI := hB; topDifferentialCoefficient k R K n b ω) := by
  subst B
  rfl

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory KaehlerDifferential
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

attribute [local instance] fanFunctionFieldAlgebra torusFunctionFieldAlgebra
  chartFunctionFieldAlgebra torusFunctionField_isFractionRing

/-- Here the scalar action is the action of the actual chart map to the
function field. Its agreement with the Laurent action is proved by the
chart/torus coordinate compatibility, rather than inferred by definitional
conversion between the two module structures. -/
local instance chartGenericFunctionFieldSMul (s : «Σ».ConeIndex) :
    SMul (monoidChartAlgebra k (dualConeMonoid s.val)) («Σ».fanScheme k).functionField :=
  («Σ».chartFunctionFieldAlgebra k s).toSMul

local instance chartGenericFunctionFieldModule (s : «Σ».ConeIndex) :
    Module (monoidChartAlgebra k (dualConeMonoid s.val)) («Σ».fanScheme k).functionField :=
  @Algebra.toModule _ _ _ _ («Σ».chartFunctionFieldAlgebra k s)

local instance chartGenericFunctionField_scalarTower (s : «Σ».ConeIndex) :
    IsScalarTower k (monoidChartAlgebra k (dualConeMonoid s.val))
      («Σ».fanScheme k).functionField := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap k («Σ».fanScheme k).functionField r=
    «Σ».chartRationalMap k s (algebraMap k (monoidChartAlgebra k (dualConeMonoid s.val)) r)
  exact (IsScalarTower.algebraMap_apply k (AddMonoidAlgebra k (Lattice n))
    («Σ».fanScheme k).functionField r).trans
      («Σ».chartRationalMap_eq_torusRationalMap k s
        (algebraMap k (monoidChartAlgebra k (dualConeMonoid s.val)) r)).symm

def chartFaceAlgebra {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    Algebra (monoidChartAlgebra k (dualConeMonoid s))
      (monoidChartAlgebra k (dualConeMonoid t)) :=
  (monoidChartInclusion k (dualConeMonoid_antitone hts)).toRingHom.toAlgebra

def chartFace_scalarTower {s t : Finset (Lattice n)} (hts : t ⊆ s) :
    letI := chartFaceAlgebra k hts
    IsScalarTower k (monoidChartAlgebra k (dualConeMonoid s))
      (monoidChartAlgebra k (dualConeMonoid t)) := by
  letI := chartFaceAlgebra k hts
  exact IsScalarTower.of_algebraMap_eq fun r =>
    ((monoidChartInclusion k (dualConeMonoid_antitone hts)).commutes r).symm

def chartFaceFunctionField_scalarTower {s t : «Σ».ConeIndex} (hts : t.val ⊆ s.val) :
    letI := chartFaceAlgebra k hts
    IsScalarTower (monoidChartAlgebra k (dualConeMonoid s.val))
      (monoidChartAlgebra k (dualConeMonoid t.val)) («Σ».fanScheme k).functionField := by
  letI := chartFaceAlgebra k hts
  exact IsScalarTower.of_algebraMap_eq fun r =>
    («Σ».chartRationalMap_restrict k (s := t) (t := s) hts r).symm

theorem chartFunctionField_isFractionRing (s : «Σ».ConeIndex) :
    IsFractionRing (monoidChartAlgebra k (dualConeMonoid s.val))
      («Σ».fanScheme k).functionField := by
  letI := «Σ».chartRing_isDomain k s.val s.property
  letI : IsOpenImmersion («Σ».fanChartMap k s) := «Σ».fanChartMap_isOpenImmersion k s
  exact affineOpenCoordinate_isFractionRing
    (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val)))
    («Σ».fanChartMap k s)

theorem exists_chartDifferentialBasis (hpure : «Σ».IsPure) (s : «Σ».ConeIndex) :
    Nonempty (Module.Basis (Fin n) (monoidChartAlgebra k (dualConeMonoid s.val))
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) := by
  obtain ⟨t, ht, hst, hcard⟩ := hpure s.val s.property
  let t' : «Σ».fullCones := ⟨t, Finset.mem_filter.mpr ⟨ht, hcard⟩⟩
  obtain ⟨v, hv, hloc⟩ := «Σ».chart_face_isLocalizationMap k t s.val ht hst
  letI : Algebra (monoidChartAlgebra k (dualConeMonoid t))
      (monoidChartAlgebra k (dualConeMonoid s.val)) := chartFaceAlgebra k hst
  letI : IsScalarTower k (monoidChartAlgebra k (dualConeMonoid t))
      (monoidChartAlgebra k (dualConeMonoid s.val)) := chartFace_scalarTower k hst
  letI : IsLocalization (Submonoid.powers (chartCharacter k _ v hv))
      (monoidChartAlgebra k (dualConeMonoid s.val)) :=
    (isLocalization_iff_isLocalizationMap _ _).mpr hloc
  exact ⟨localizedDifferentialBasis k _ _
    (Submonoid.powers (chartCharacter k _ v hv))
    («Σ».actualFullChartDifferentialBasis k t')⟩

theorem chartTopDifferentialMap_injective (hpure : «Σ».IsPure) (s : «Σ».ConeIndex) :
    Function.Injective (topDifferentialMap k
      (monoidChartAlgebra k (dualConeMonoid s.val)) («Σ».fanScheme k).functionField n) := by
  letI := «Σ».chartFunctionField_isFractionRing k s
  obtain ⟨b⟩ := «Σ».exists_chartDifferentialBasis k hpure s
  exact topDifferentialMap_injective_of_localization k _ _
    (nonZeroDivisors (monoidChartAlgebra k (dualConeMonoid s.val))) b
    («Σ».chartRationalMap_injective k s)

/-- The coefficient of a genuine top differential on any actual chart. -/
def chartGenericTopCoefficient (b₀ : Module.Basis (Fin n) ℤ (Lattice n))
    (s : «Σ».ConeIndex) :
    (⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) →ₗ[
        monoidChartAlgebra k (dualConeMonoid s.val)] («Σ».fanScheme k).functionField :=
  topDifferentialCoefficient k (monoidChartAlgebra k (dualConeMonoid s.val))
    («Σ».fanScheme k).functionField n («Σ».genericLogDifferentialBasis k b₀)

theorem chartGenericTopCoefficient_injective (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».ConeIndex) :
    Function.Injective («Σ».chartGenericTopCoefficient k b₀ s) :=
  (basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀)).injective.comp
    («Σ».chartTopDifferentialMap_injective k hpure s)

theorem chartGenericTopCoefficient_restrict
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) {s t : «Σ».ConeIndex}
    (hts : t.val ⊆ s.val)
    (ω : ⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) :
    letI := chartFaceAlgebra k hts
    letI := chartFace_scalarTower k hts
    «Σ».chartGenericTopCoefficient k b₀ t
        (topDifferentialMap k (monoidChartAlgebra k (dualConeMonoid s.val))
          (monoidChartAlgebra k (dualConeMonoid t.val)) n ω) =
      «Σ».chartGenericTopCoefficient k b₀ s ω := by
  letI := chartFaceAlgebra k hts
  letI := chartFace_scalarTower k hts
  letI := «Σ».chartFaceFunctionField_scalarTower k hts
  exact congrArg (fun f =>
    basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀) (f ω))
      (topDifferentialMap_comp k
        (monoidChartAlgebra k (dualConeMonoid s.val))
        (monoidChartAlgebra k (dualConeMonoid t.val)) («Σ».fanScheme k).functionField n)

set_option maxHeartbeats 2000000 in
/-- On a full chart this is the already constructed actual differential
coefficient. The explicit chart scalar action changes no generic form. -/
theorem chartGenericTopCoefficient_fullCone
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    (ω : ⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k]) :
    «Σ».chartGenericTopCoefficient k b₀ («Σ».fullConeIndex s) ω=
      «Σ».actualChartTopCoefficient k b₀ s ω := by
  let R := monoidChartAlgebra k (dualConeMonoid s.val)
  let K := («Σ».fanScheme k).functionField
  let A : Algebra R K := «Σ».chartFunctionFieldAlgebra k («Σ».fullConeIndex s)
  let B : Algebra R K := (monoidChartAlgebra k (dualConeMonoid s.val)).toAlgebra
  have hAB : A=B := Algebra.algebra_ext A B fun r =>
    «Σ».chartRationalMap_eq_torusRationalMap k («Σ».fullConeIndex s) r
  exact topDifferentialCoefficient_algebra_eq k R K A B hAB
    («Σ».chartGenericFunctionField_scalarTower k («Σ».fullConeIndex s))
    (by
      letI : Algebra R K := B
      exact IsScalarTower.of_algebraMap_eq (R := k) (S := R) (A := K) fun r =>
        IsScalarTower.algebraMap_apply k (AddMonoidAlgebra k (Lattice n)) K r)
    n («Σ».genericLogDifferentialBasis k b₀) ω

/-- The actual localized differential forms agree on the actual common
face precisely when they give the same generic form. Thus the computed
volume transition is the natural differential transition, not an
independently prescribed line-bundle cocycle. -/
theorem fullChart_differentials_agree_on_overlap_iff (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s t : «Σ».fullCones)
    (ω : ⋀[monoidChartAlgebra k (dualConeMonoid s.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid s.val)⁄k])
    (η : ⋀[monoidChartAlgebra k (dualConeMonoid t.val)]^n
      Ω[monoidChartAlgebra k (dualConeMonoid t.val)⁄k]) :
    let l : «Σ».ConeIndex :=
      ⟨s.val ∩ t.val, «Σ».downward s.val («Σ».fullCones_mem s) _ Finset.inter_subset_left⟩
    letI := chartFaceAlgebra k (Finset.inter_subset_left : l.val ⊆ s.val)
    letI := chartFaceAlgebra k (Finset.inter_subset_right : l.val ⊆ t.val)
    letI := chartFace_scalarTower k (Finset.inter_subset_left : l.val ⊆ s.val)
    letI := chartFace_scalarTower k (Finset.inter_subset_right : l.val ⊆ t.val)
    topDifferentialMap k (monoidChartAlgebra k (dualConeMonoid s.val))
        (monoidChartAlgebra k (dualConeMonoid l.val)) n ω =
      topDifferentialMap k (monoidChartAlgebra k (dualConeMonoid t.val))
        (monoidChartAlgebra k (dualConeMonoid l.val)) n η ↔
      «Σ».actualChartTopCoefficient k b₀ s ω = «Σ».actualChartTopCoefficient k b₀ t η := by
  dsimp only
  let l : «Σ».ConeIndex :=
    ⟨s.val ∩ t.val, «Σ».downward s.val («Σ».fullCones_mem s) _ Finset.inter_subset_left⟩
  letI := chartFaceAlgebra k (Finset.inter_subset_left : l.val ⊆ s.val)
  letI := chartFaceAlgebra k (Finset.inter_subset_right : l.val ⊆ t.val)
  letI := chartFace_scalarTower k (Finset.inter_subset_left : l.val ⊆ s.val)
  letI := chartFace_scalarTower k (Finset.inter_subset_right : l.val ⊆ t.val)
  have hω := («Σ».chartGenericTopCoefficient_restrict k b₀
    (s := «Σ».fullConeIndex s) (t := l)
    (Finset.inter_subset_left : l.val ⊆ s.val) ω).trans
      («Σ».chartGenericTopCoefficient_fullCone k b₀ s ω)
  have hη := («Σ».chartGenericTopCoefficient_restrict k b₀
    (s := «Σ».fullConeIndex t) (t := l)
    (Finset.inter_subset_right : l.val ⊆ t.val) η).trans
      («Σ».chartGenericTopCoefficient_fullCone k b₀ t η)
  exact («Σ».chartGenericTopCoefficient_injective k hpure b₀ l).eq_iff.symm.trans
    (congrArg₂ (fun x y : («Σ».fanScheme k).functionField => x=y) hω hη).to_iff

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fullChart_differentials_agree_on_overlap_iff
