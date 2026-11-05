module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import paper_verification.toric022
public import paper_verification.toric024
public import paper_verification.toric031
public import paper_verification.toric037
public import paper_verification.toric039

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricCanonicalDifferentialGluing
section Source_ToricCanonicalDifferentialGluing

-- original header: module

-- original header: public import PaperVerification.ToricCanonicalDifferentialCocycle
-- original header: public import PaperVerification.ToricInvertibleRestriction
-- original header: public import Mathlib.LinearAlgebra.TensorProduct.Tower

-- original header: @[expose] public section

/-!
# The differential gluing maps are actual localization maps

Kähler functoriality and exterior functoriality give compatibility on
chains of actual ring maps. Localizing a free differential module
localizes its top exterior power; the resulting base-change equivalence
is computed on its genuine wedge generator. The global differential
volume sheaf restricts to the actual tilde of each chart's top Ω module.
-/

noncomputable section

universe u

namespace PaperVerification.ToricCharacters

open KaehlerDifferential
open scoped BigOperators Classical TensorProduct

section Naturality

variable (k R S T : Type*) [CommRing k] [CommRing R] [CommRing S] [CommRing T]
    [Algebra k R] [Algebra k S] [Algebra k T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower k R S] [IsScalarTower k S T] [IsScalarTower k R T]
    [IsScalarTower R S T]

theorem kahler_map_comp :
    (KaehlerDifferential.map k k S T).restrictScalars R ∘ₗ
        KaehlerDifferential.map k k R S = KaehlerDifferential.map k k R T := by
  rw [Submodule.linearMap_eq_iff_of_span_eq_top _ _
    (KaehlerDifferential.span_range_derivation k R)]
  rintro ⟨_, ⟨r, rfl⟩⟩
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    KaehlerDifferential.map_D, IsScalarTower.algebraMap_apply R S T]

def topDifferentialMap (n : ℕ) :
    (⋀[R]^n Ω[R⁄k]) →ₗ[R] (⋀[S]^n Ω[S⁄k]) :=
  exteriorScalarExtensionMap (S := S) (KaehlerDifferential.map k k R S)

@[simp] theorem topDifferentialMap_wedge (n : ℕ) (v : Fin n → Ω[R⁄k]) :
    topDifferentialMap k R S n (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun i => KaehlerDifferential.map k k R S (v i)) :=
  exteriorScalarExtensionMap_wedge _ _

theorem topDifferentialMap_comp (n : ℕ) :
    (topDifferentialMap k S T n).restrictScalars R ∘ₗ
        topDifferentialMap k R S n = topDifferentialMap k R T n := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, topDifferentialMap_wedge]
  apply congrArg (fun w : Fin n → Ω[T⁄k] => exteriorPower.ιMulti T n w)
  funext i
  exact congrArg (fun f => f (v i)) (kahler_map_comp k R S T)

end Naturality

section Localization

variable (k R S : Type*) [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
    {n : ℕ} (M : Submonoid R) [IsLocalization M S]
    (b : Module.Basis (Fin n) R Ω[R⁄k])

def localizedDifferentialBasis : Module.Basis (Fin n) S Ω[S⁄k] :=
  b.ofIsLocalizedModule S M (KaehlerDifferential.map k k R S)

theorem localized_topDifferential_coefficient (ω : ⋀[R]^n Ω[R⁄k]) :
    basisTopExteriorEquiv (localizedDifferentialBasis k R S M b)
        (topDifferentialMap k R S n ω) =
      algebraMap R S (basisTopExteriorEquiv b ω) := by
  conv_lhs => rw [topExterior_eq_smul_basis b ω]
  rw [map_smul, topDifferentialMap_wedge]
  have hb : (fun i => KaehlerDifferential.map k k R S (b i)) =
      localizedDifferentialBasis k R S M b := by
    funext i
    exact (b.ofIsLocalizedModule_apply S M
      (KaehlerDifferential.map k k R S) i).symm
  rw [hb, ← IsScalarTower.algebraMap_smul S, map_smul,
    basisTopExteriorEquiv_basis, smul_eq_mul, mul_one]

include M b in
/-- A free top differential module embeds in its localization whenever
the underlying coordinate-ring map is injective. -/
theorem topDifferentialMap_injective_of_localization
    (hinj : Function.Injective (algebraMap R S)) :
    Function.Injective (topDifferentialMap k R S n) := by
  intro ω η h
  apply (basisTopExteriorEquiv b).injective
  apply hinj
  simpa only [localized_topDifferential_coefficient] using
    congrArg (basisTopExteriorEquiv (localizedDifferentialBasis k R S M b)) h

/-- The actual top differential modules before and after localization
satisfy the ordinary tensor-product base-change property. -/
def topDifferentialLocalizationEquiv :
    S ⊗[R] (⋀[R]^n Ω[R⁄k]) ≃ₗ[S] (⋀[S]^n Ω[S⁄k]) :=
  ((basisTopExteriorEquiv b).baseChange R S (⋀[R]^n Ω[R⁄k]) R).trans
    ((TensorProduct.AlgebraTensorModule.rid R S S).trans
      (basisTopExteriorEquiv (localizedDifferentialBasis k R S M b)).symm)

theorem topDifferentialLocalizationEquiv_tmul (s : S) (ω : ⋀[R]^n Ω[R⁄k]) :
    topDifferentialLocalizationEquiv k R S M b (s ⊗ₜ[R] ω) =
      s • topDifferentialMap k R S n ω := by
  apply (basisTopExteriorEquiv (localizedDifferentialBasis k R S M b)).injective
  simp only [topDifferentialLocalizationEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul,
    LinearEquiv.apply_symm_apply, map_smul, localized_topDifferential_coefficient,
    smul_eq_mul, Algebra.smul_def]
  exact mul_comm _ _

end Localization

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

variable {X Y : Scheme.{u}} [IsIntegral X]
    (C : RationalCartierCocycle X) (i : C.index)
    (j : Y ⟶ X) [IsOpenImmersion j] (hj : j.opensRange ≤ C.openSet i)

/-- The proved cocycle frame transported to an actual open chart, with
the actual section isomorphism supplying the scalar change. -/
def cocycleOpenFrameCoordinates (U : Y.Opens) :
    Γ(C.sheaf.restrict j,U) ≃ₗ[Γ(Y,U)] Γ(Y,U) := by
  let hU : j ''ᵁ U ≤ C.openSet i := by
    rintro x ⟨y, hy, rfl⟩
    exact hj ⟨y, rfl⟩
  let eM := (C.sheaf.restrictAppIso j U).addCommGroupIsoToAddEquiv
  let eX := C.localCoordinates i (j ''ᵁ U) hU
  let eR := (j.appIso U).commRingCatIsoToRingEquiv
  refine
    { toFun := fun s => eR (eX (eM s))
      invFun := fun a => eM.symm (eX.symm (eR.symm a))
      left_inv := by intro s; simp
      right_inv := by intro a; simp
      map_add' := by intro s t; simp
      map_smul' := ?_ }
  intro a s
  change eR (eX (eR.symm a • eM s)) = a * eR (eX (eM s))
  rw [eX.map_smul]
  change eR (eR.symm a * eX (eM s)) = _
  rw [map_mul, RingEquiv.apply_symm_apply]

theorem cocycleOpenFrameCoordinates_restrict
    {U V : Y.Opens} (f : V ⟶ U) (s : Γ(C.sheaf.restrict j,U)) :
    cocycleOpenFrameCoordinates C i j hj V
      ((C.sheaf.restrict j).presheaf.map f.op s) =
      Y.presheaf.map f.op (cocycleOpenFrameCoordinates C i j hj U s) := by
  let f' : j ''ᵁ V ⟶ j ''ᵁ U := homOfLE (j.image_mono f.le)
  let t : Γ(C.sheaf,j ''ᵁ U) := (C.sheaf.restrictAppIso j U).hom s
  have hU : j ''ᵁ U ≤ C.openSet i := by
    rintro x ⟨y, hy, rfl⟩
    exact hj ⟨y, rfl⟩
  have hV : j ''ᵁ V ≤ C.openSet i := (j.image_mono f.le).trans hU
  change (j.appIso V).hom
      (C.localCoordinates i (j ''ᵁ V) hV
        (C.sheaf.presheaf.map f'.op t)) =
    Y.presheaf.map f.op ((j.appIso U).hom (C.localCoordinates i (j ''ᵁ U) hU t))
  have hn : X.presheaf.map f'.op ≫ (j.appIso V).hom =
      (j.appIso U).hom ≫ Y.presheaf.map f.op := by
    simp [Scheme.Hom.appIso_hom']
  calc
    _ = (j.appIso V).hom (X.presheaf.map f'.op
        (C.localCoordinates i (j ''ᵁ U) hU t)) :=
      congrArg (fun a : Γ(X,j ''ᵁ V) => (j.appIso V).hom a)
        (C.localCoordinates_restrict i f' hU hV t)
    _ = _ := congrArg (fun h : Γ(X,j ''ᵁ U) ⟶ Γ(Y,V) =>
      h (C.localCoordinates i (j ''ᵁ U) hU t)) hn

def cocycleOpenFrame :
    C.sheaf.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun U => (cocycleOpenFrameCoordinates C i j hj U.unop).toModuleIso)
      (by
        intro U V f
        ext s
        exact cocycleOpenFrameCoordinates_restrict C i j hj f.unop s)

theorem cocycleOpenFrameCoordinates_value (U : Y.Opens) [Nonempty U]
    (s : Γ(C.sheaf.restrict j,U)) :
    letI : Nonempty (j ''ᵁ U) := by
      obtain ⟨y⟩ := (inferInstance : Nonempty U)
      exact ⟨⟨j y.val,⟨y.val,y.property,rfl⟩⟩⟩
    X.germToFunctionField (j ''ᵁ U)
      ((j.appIso U).inv (cocycleOpenFrameCoordinates C i j hj U s)) =
        rationalValue X (j ''ᵁ U)
          ((C.sheaf.restrictAppIso j U).hom s).val / (C.generator i : X.functionField) := by
  letI : Nonempty (j ''ᵁ U) := by
    obtain ⟨y⟩ := (inferInstance : Nonempty U)
    exact ⟨⟨j y.val,⟨y.val,y.property,rfl⟩⟩⟩
  let t : Γ(C.sheaf,j ''ᵁ U) := (C.sheaf.restrictAppIso j U).hom s
  have hU : j ''ᵁ U ≤ C.openSet i := by
    rintro x ⟨y, hy, rfl⟩
    exact hj ⟨y, rfl⟩
  change X.germToFunctionField (j ''ᵁ U)
      ((j.appIso U).inv ((j.appIso U).hom
        (C.localCoordinates i (j ''ᵁ U) hU t))) =
    rationalValue X (j ''ᵁ U) t.val / (C.generator i : X.functionField)
  rw [Iso.hom_inv_id_apply]
  exact C.localCoordinates_value i (j ''ᵁ U) hU t

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

attribute [local instance] fanFunctionFieldAlgebra torusFunctionFieldAlgebra
  chartFunctionFieldAlgebra torusFunctionField_isFractionRing

/-- The global differential sheaf restricts to the actual affine sheaf
associated to the actual top Kähler module of every full smooth chart.
The coordinate maps divide by the genuine generic differential image. -/
def differentialVolumeData_chartIso (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones) :
    («Σ».differentialVolumeData k hpure b₀).sheaf.restrict
        («Σ».fanChartMap k («Σ».fullConeIndex s)) ≅
      «Σ».fullChartTopDifferentialSheaf k s :=
  cocycleOpenFrame («Σ».differentialVolumeCocycle k hpure b₀) ⟨s⟩
      («Σ».fanChartMap k («Σ».fullConeIndex s)) le_rfl ≪≫
    («Σ».fullChartTopDifferentialFrame k s).symm

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricCharacters.topDifferentialMap_comp
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.differentialVolumeData_chartIso

end
end Source_ToricCanonicalDifferentialGluing
-- END ORIGINAL PaperVerification.ToricCanonicalDifferentialGluing


-- BEGIN ORIGINAL PaperVerification.ToricDifferentialOverlaps
section Source_ToricDifferentialOverlaps

-- original header: module

-- original header: public import PaperVerification.ToricCanonicalDifferentialGluing

-- original header: @[expose] public section

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
end
end Source_ToricDifferentialOverlaps
-- END ORIGINAL PaperVerification.ToricDifferentialOverlaps


-- BEGIN ORIGINAL PaperVerification.ToricFanIntrinsicCanonical
section Source_ToricFanIntrinsicCanonical

-- original header: module

-- original header: public import PaperVerification.ToricAffineDifferentialWedges
-- original header: public import PaperVerification.ToricOpenModuleFrames
-- original header: public import PaperVerification.ToricDifferentialOverlaps
-- original header: public import PaperVerification.ToricRationalFrameComparison

-- original header: @[expose] public section

/-!
# The intrinsic canonical sheaf of the actual fan scheme

The left-hand side below is the ordinary top exterior power of the
intrinsic Kähler sheaf. Its actual polynomial-chart frames map to the
previously computed genuine generic differential volumes. This proves
the global sheaf comparison, and only then identifies the canonical
Cartier coefficients with minus one on every ray.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace KaehlerDifferential
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical BaseSections

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

attribute [local instance] fanFunctionFieldAlgebra torusFunctionFieldAlgebra
  chartFunctionFieldAlgebra torusFunctionField_isFractionRing

local notation "X" => «Σ».fanScheme k
local notation "M" => topDifferentialSheaf k X n

def fullChartIntrinsicTopFrame (s : «Σ».fullCones) :
    topDifferentialSheaf k (coneChart k s.val) n≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf :=
  affineTopDifferentialSheafIso k (monoidChartAlgebra k (dualConeMonoid s.val))
      («Σ».actualFullChartDifferentialBasis k s) ≪≫
    «Σ».fullChartTopDifferentialFrame k s

def intrinsicTopChartFrame (s : «Σ».fullCones) :
    (M).restrict («Σ».fanChartMap k («Σ».fullConeIndex s))≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf :=
  topDifferentialSheafRestrictIso («Σ».fanChartMap k («Σ».fullConeIndex s)) n k ≪≫
    «Σ».fullChartIntrinsicTopFrame k s

/-- Actual local freeness on the actual image open. -/
def intrinsicTopOpenFrame (s : «Σ».fullCones) : ModuleFrame M («Σ».fullChartOpen k s) :=
  ModuleFrame.ofOpenImmersionIso («Σ».fanChartMap k («Σ».fullConeIndex s))
    («Σ».intrinsicTopChartFrame k s)

set_option maxHeartbeats 2000000 in
theorem fullChartIntrinsicTopFrame_wedge (s : «Σ».fullCones) :
    («Σ».fullChartIntrinsicTopFrame k s).hom.app ⊤
      (differentialWedgeSection (coneChart k s.val) k ⊤
        (fun i=>(Scheme.ΓSpecIso (CommRingCat.of
          (monoidChartAlgebra k (dualConeMonoid s.val)))).inv
            («Σ».fullChartCoordinate k s i)))=(1 : Γ(coneChart k s.val,⊤)) := by
  let R := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val))
  let b := «Σ».actualFullChartDifferentialBasis k s
  have hw := affineTopDifferentialSheafIso_differentialWedge_top k R b
    («Σ».fullChartCoordinate k s)
  have hb : (fun i : Fin n => D k R («Σ».fullChartCoordinate k s i))=b := by
    funext i
    exact («Σ».actualFullChartDifferentialBasis_apply k s i).symm
  have hw' := hw.trans (congrArg
    (fun v : Fin n → KaehlerDifferential k R =>
      tilde.toOpen (R := R) (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R))) ⊤
        (exteriorPower.ιMulti R n v)) hb)
  have hc : tildeTopBasisCoordinates R (ModuleCat.of R (KaehlerDifferential k R)) b ⊤
      (tilde.toOpen (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R))) ⊤
        (exteriorPower.ιMulti R n b))=(1 : Γ(Spec R,⊤)) :=
    (tildeTopBasisCoordinates_toOpen R (ModuleCat.of R (KaehlerDifferential k R)) b ⊤
      (exteriorPower.ιMulti R n b)).trans (by
        rw [basisTopExteriorEquiv_basis,map_one])
  exact (congrArg ((«Σ».fullChartTopDifferentialFrame k s).hom.app ⊤) hw').trans hc

/-- The chart coordinate, now as an actual regular function on the
actual image open of the chart. -/
def fullChartGlobalCoordinate (s : «Σ».fullCones) (i : Fin n) :
    Γ(X,«Σ».fullChartOpen k s) :=
  let j := «Σ».fanChartMap k («Σ».fullConeIndex s)
  (X).presheaf.map (eqToHom (j.image_top_eq_opensRange).symm).op
    ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of
      (monoidChartAlgebra k (dualConeMonoid s.val)))).inv
        («Σ».fullChartCoordinate k s i)))

theorem intrinsicTopChartFrame_inv_one (s : «Σ».fullCones) :
    («Σ».intrinsicTopChartFrame k s).inv.app ⊤ (1 : Γ(coneChart k s.val,⊤)) =
      ((M).restrictAppIso («Σ».fanChartMap k («Σ».fullConeIndex s)) ⊤).inv
        (differentialWedgeSection X k
          ((«Σ».fanChartMap k («Σ».fullConeIndex s)) ''ᵁ ⊤)
          (fun i=>((«Σ».fanChartMap k («Σ».fullConeIndex s)).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of
              (monoidChartAlgebra k (dualConeMonoid s.val)))).inv
                («Σ».fullChartCoordinate k s i)))) := by
  letI : IsIso ((«Σ».intrinsicTopChartFrame k s).hom.app ⊤) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.mp
      (inferInstance : IsIso («Σ».intrinsicTopChartFrame k s).hom) ⊤
  apply (ConcreteCategory.bijective_of_isIso
    ((«Σ».intrinsicTopChartFrame k s).hom.app ⊤)).injective
  have hc := congrArg (fun f=>f.app ⊤ (1 : Γ(coneChart k s.val,⊤)))
    («Σ».intrinsicTopChartFrame k s).inv_hom_id
  rw [show («Σ».intrinsicTopChartFrame k s).hom.app ⊤
      ((«Σ».intrinsicTopChartFrame k s).inv.app ⊤ (1 : Γ(coneChart k s.val,⊤)))=(1 : Γ(coneChart k s.val,⊤)) from by
        simpa only [Scheme.Modules.Hom.comp_app,Scheme.Modules.Hom.id_app,
          ConcreteCategory.comp_apply,ConcreteCategory.id_apply] using hc]
  simp only [intrinsicTopChartFrame,Iso.trans_hom,Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply,differentialWedgeSection_openRestriction,
    Iso.inv_hom_id_apply]
  exact («Σ».fullChartIntrinsicTopFrame_wedge k s).symm

/-- The local basis of the intrinsic top sheaf is the actual wedge of
the actual affine coordinate differentials. -/
theorem intrinsicTopOpenFrame_generator (s : «Σ».fullCones) :
    («Σ».intrinsicTopOpenFrame k s).generator («Σ».fullChartOpen k s) le_rfl=
      differentialWedgeSection X k («Σ».fullChartOpen k s)
        («Σ».fullChartGlobalCoordinate k s) := by
  let j := «Σ».fanChartMap k («Σ».fullConeIndex s)
  let e : (M).restrict j ≅
      SheafOfModules.unit (coneChart k («Σ».fullConeIndex s).val).ringCatSheaf :=
    «Σ».intrinsicTopChartFrame k s
  let a : Fin n → Γ(X,j ''ᵁ (⊤ : (coneChart k («Σ».fullConeIndex s).val).Opens)) :=
    fun i => (j.appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of
        (monoidChartAlgebra k (dualConeMonoid s.val)))).inv
          («Σ».fullChartCoordinate k s i))
  let ω := differentialWedgeSection X k (j ''ᵁ ⊤) a
  have he : e.inv.app ⊤
      (1 : Γ(coneChart k («Σ».fullConeIndex s).val,⊤)) =
      ((M).restrictAppIso j ⊤).inv ω :=
    «Σ».intrinsicTopChartFrame_inv_one k s
  have hv : ((M).restrictAppIso j ⊤).hom
      (e.inv.app ⊤ (1 : Γ(coneChart k («Σ».fullConeIndex s).val,⊤))) = ω :=
    (congrArg ((M).restrictAppIso j ⊤).hom he).trans
      (((M).restrictAppIso j ⊤).inv_hom_id_apply ω)
  have himage : ModuleFrame.imageFrameGenerator j e =
      (M).presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op ω :=
    congrArg (fun v : Γ(M,j ''ᵁ (⊤ : (coneChart k («Σ».fullConeIndex s).val).Opens)) =>
      (M).presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op v) hv
  have hres : (M).presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op ω =
      differentialWedgeSection X k j.opensRange
        (fun i => (X).presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op (a i)) :=
    differentialWedgeSection_restrict X k j.image_top_eq_opensRange.symm.le a
  exact (ModuleFrame.ofOpenImmersionIso_generator j e).trans (himage.trans hres)

theorem fullChartGlobalCoordinate_germ (s : «Σ».fullCones)
    [Nonempty («Σ».fullChartOpen k s)] (i : Fin n) :
    (X).germToFunctionField («Σ».fullChartOpen k s) («Σ».fullChartGlobalCoordinate k s i)=
      «Σ».chartRationalMap k («Σ».fullConeIndex s) («Σ».fullChartCoordinate k s i) := by
  let R := CommRingCat.of
    (monoidChartAlgebra k (dualConeMonoid («Σ».fullConeIndex s).val))
  let j : coneChart k («Σ».fullConeIndex s).val ⟶ X :=
    «Σ».fanChartMap k («Σ».fullConeIndex s)
  letI : IsIntegral (coneChart k («Σ».fullConeIndex s).val) :=
    «Σ».coneChart_isIntegral k («Σ».fullConeIndex s)
  letI : IsOpenImmersion j :=
    «Σ».fanChartMap_isOpenImmersion k («Σ».fullConeIndex s)
  let a : Γ(coneChart k («Σ».fullConeIndex s).val,⊤) :=
    (Scheme.ΓSpecIso R).inv («Σ».fullChartCoordinate k s i)
  let U : (X).Opens := j ''ᵁ (⊤ : (coneChart k («Σ».fullConeIndex s).val).Opens)
  letI : Nonempty U := by
    rw [show U=«Σ».fullChartOpen k s from j.image_top_eq_opensRange]
    infer_instance
  let b : Γ(X,U) := (j.appIso ⊤).inv a
  let f : «Σ».fullChartOpen k s ⟶ U :=
    eqToHom (j.image_top_eq_opensRange).symm
  change (X).germToFunctionField («Σ».fullChartOpen k s)
    ((X).presheaf.map f.op b) = _
  calc
    _ = (X).germToFunctionField U b :=
      germToFunctionField_restrict X f b
    _ = openImmersionRegularToFunctionField j ⊤ a :=
      (openImmersionRegularToFunctionField_eq_germ_image j ⊤ a).symm
    _ = _ := rfl


/-- The generic coefficient of the intrinsic local basis is exactly
the coefficient already obtained from actual chart Kähler modules. -/
theorem intrinsicTopOpenFrame_value
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    [Nonempty («Σ».fullChartOpen k s)] :
    rationalValue X («Σ».fullChartOpen k s)
      ((topDifferentialRationalMap X k («Σ».genericLogDifferentialBasis k b₀)).app
        («Σ».fullChartOpen k s)
          ((«Σ».intrinsicTopOpenFrame k s).generator («Σ».fullChartOpen k s) le_rfl))=
      («Σ».differentialVolumeUnit k b₀ s : (X).functionField) := by
  rw [«Σ».intrinsicTopOpenFrame_generator,
    topDifferentialRationalMap_differentialWedge]
  simp_rw [«Σ».fullChartGlobalCoordinate_germ]
  change _=«Σ».actualChartTopCoefficient k b₀ s
    (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
      («Σ».actualFullChartDifferentialBasis k s))
  unfold actualChartTopCoefficient
  rw [LinearMap.comp_apply,exteriorScalarExtensionMap_wedge]
  change basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀) _ =
    basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀) _
  apply congrArg (fun ω :
    ⋀[(«Σ».fanScheme k).functionField]^n
      (KaehlerDifferential k («Σ».fanScheme k).functionField) =>
        basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀) ω)
  apply congrArg (fun v : Fin n → KaehlerDifferential k («Σ».fanScheme k).functionField =>
    exteriorPower.ιMulti («Σ».fanScheme k).functionField n v)
  funext i
  rw [«Σ».actualFullChartDifferentialBasis_apply,KaehlerDifferential.map_D]
  exact congrArg (D k («Σ».fanScheme k).functionField)
    («Σ».chartRationalMap_eq_torusRationalMap k («Σ».fullConeIndex s)
      («Σ».fullChartCoordinate k s i))

theorem intrinsicTopFrameValues (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    («Σ».differentialVolumeCocycle k hpure b₀).FrameValues M
      (topDifferentialRationalMap X k («Σ».genericLogDifferentialBasis k b₀))
      (fun s=>«Σ».intrinsicTopOpenFrame k s.down) := by
  intro s h
  letI : Nonempty («Σ».fullChartOpen k s.down) := h
  exact «Σ».intrinsicTopOpenFrame_value k b₀ s.down

/-- The genuine intrinsic canonical sheaf is the fractional sheaf
obtained from its genuine generic differential volume. -/
def intrinsicTopDifferentialVolumeIso (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    topDifferentialSheaf k («Σ».fanScheme k) n≅
      («Σ».differentialVolumeData k hpure b₀).sheaf :=
  («Σ».differentialVolumeCocycle k hpure b₀).sheafIsoOfFrames M
    (topDifferentialRationalMap X k («Σ».genericLogDifferentialBasis k b₀))
    (fun s=>«Σ».intrinsicTopOpenFrame k s.down)
    («Σ».intrinsicTopFrameValues k hpure b₀)

/-- The minus-one ray coefficients are a consequence of the actual
Kähler/top-exterior computation, not the definition of the canonical sheaf. -/
def intrinsicCanonicalFanIso (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    topDifferentialSheaf k («Σ».fanScheme k) n≅
      («Σ».fanCartierData k hpure (fun _=>-1)).sheaf :=
  «Σ».intrinsicTopDifferentialVolumeIso k hpure b₀ ≪≫
    («Σ».differentialVolumeData_equivalent_canonical k hpure b₀).choose

theorem intrinsicTopDifferential_isInvertible (hpure : «Σ».IsPure) :
    IsInvertibleModule (topDifferentialSheaf k («Σ».fanScheme k) n) := by
  intro x
  obtain ⟨s,hs⟩ := «Σ».fullChartOpen_cover k hpure x
  exact ⟨«Σ».fullChartOpen k s,hs,⟨«Σ».intrinsicTopOpenFrame k s⟩⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.intrinsicTopDifferentialVolumeIso
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.intrinsicCanonicalFanIso
end
end Source_ToricFanIntrinsicCanonical
-- END ORIGINAL PaperVerification.ToricFanIntrinsicCanonical


-- BEGIN ORIGINAL PaperVerification.ToricFanDimension
section Source_ToricFanDimension

-- original header: module

-- original header: public import PaperVerification.ToricFanDifferentials
-- original header: public import Mathlib.RingTheory.KrullDimension.Polynomial
-- original header: public import Mathlib.RingTheory.KrullDimension.Field

-- original header: @[expose] public section

/-!
# The actual dimension of a smooth complete fan scheme

Full cones give actual open affine charts with polynomial coordinate
rings in `n` variables. Their union is the whole scheme. The upper
dimension bound follows from preservation of point coheight under open
immersions; the lower bound follows from any one of those open charts.
Thus the rank parameter is identified with ordinary topological Krull
dimension, including rank zero.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry TopologicalSpace

theorem scheme_topologicalKrullDim_eq_orderKrullDim (X : Scheme) :
    topologicalKrullDim X = Order.krullDim X := by
  change Order.krullDim (IrreducibleCloseds X) = Order.krullDim X
  exact Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

theorem fullChart_ringKrullDim (s : «Σ».fullCones) :
    ringKrullDim (monoidChartAlgebra k (dualConeMonoid s.val)) = n := by
  rw [← ringKrullDim_eq_of_ringEquiv
    («Σ».fullChartPolynomialPresentation k s).toRingEquiv]
  simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
    Fintype.card_fin, zero_add]

theorem fullChart_topologicalKrullDim (s : «Σ».fullCones) :
    topologicalKrullDim (coneChart k s.val) = n := by
  change topologicalKrullDim
    (PrimeSpectrum (monoidChartAlgebra k (dualConeMonoid s.val))) = n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    «Σ».fullChart_ringKrullDim k s]

theorem fanScheme_orderKrullDim_le (hpure : «Σ».IsPure) :
    Order.krullDim («Σ».fanScheme k) ≤ n := by
  rw [Order.krullDim_eq_iSup_coheight]
  apply iSup_le
  intro x
  obtain ⟨s, y, rfl⟩ := «Σ».fullChartOpen_cover k hpure x
  rw [coheight_eq_of_isOpenImmersion]
  erw [← idealHeight_eq_coheight (CommRingCat.of
    (monoidChartAlgebra k (dualConeMonoid s.val)))
      (show Spec (CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val))) from y)]
  have h := Ideal.height_le_ringKrullDim_of_ne_top y.isPrime.ne_top
  have hd : ringKrullDim
      (monoidChartAlgebra k (dualConeMonoid («Σ».fullConeIndex s).val)) = n :=
    «Σ».fullChart_ringKrullDim k s
  rw [hd] at h
  exact h

/-- Dimension means chains of actual irreducible closed subsets of the
glued scheme, rather than a separately assigned lattice-rank invariant. -/
theorem fanScheme_topologicalKrullDim (hpure : «Σ».IsPure) :
    topologicalKrullDim («Σ».fanScheme k) = n := by
  apply le_antisymm
  · rw [scheme_topologicalKrullDim_eq_orderKrullDim]
    exact «Σ».fanScheme_orderKrullDim_le k hpure
  · obtain ⟨s, hs⟩ := «Σ».fullCones_nonempty hpure
    let s' : «Σ».fullCones := ⟨s, hs⟩
    have h := ((«Σ».fanChartMap k («Σ».fullConeIndex s')).isOpenEmbedding.isEmbedding.isInducing).topologicalKrullDim_le
    change topologicalKrullDim (coneChart k s'.val) ≤
      topologicalKrullDim («Σ».fanScheme k) at h
    simpa only [«Σ».fullChart_topologicalKrullDim k s'] using h

theorem fanScheme_orderKrullDim (hpure : «Σ».IsPure) :
    Order.krullDim («Σ».fanScheme k) = n := by
  rw [← scheme_topologicalKrullDim_eq_orderKrullDim,
    «Σ».fanScheme_topologicalKrullDim k hpure]

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.fanScheme_topologicalKrullDim
end
end Source_ToricFanDimension
-- END ORIGINAL PaperVerification.ToricFanDimension


