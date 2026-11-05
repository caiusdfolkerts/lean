module

public import PaperVerification.ToricCanonicalDifferentialCocycle
public import PaperVerification.ToricInvertibleRestriction
public import Mathlib.LinearAlgebra.TensorProduct.Tower

@[expose] public section

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

