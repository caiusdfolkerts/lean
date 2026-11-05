module
public import SegreVerified.Stage027.CriticalCoordinates
public import SegreVerified.Stage027.WeightedComplex
import all Lean.Util.CollectAxioms

set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section ProbeLayer391



/-!
# Singular-vector geometry and all-format spanning theorems

The named sections preserve the original proof stages and local scopes.
-/

@[expose] public section

-- Emit compilation progress immediately while checking this large unit.
set_option stderrAsMessages false
-- Style linting is separate from elaboration, kernel checking, and the axiom audit.
set_option linter.all false
noncomputable section
set_option autoImplicit false


section SegreCriticalBundleGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage027.Resolution"
  out.flush

/-!
# The actual critical bundle and its weighted Koszul complex

The named sections preserve the original proof stages and local scopes.
-/

set_option autoImplicit false

section SegreActualWeightedExactness

/-!
# Exactness of the actual product critical Koszul complex

The polynomial equations are the literal coefficients of the original
functional in the canonical source and line frames, transported through
the actual product-chart coordinate-ring isomorphism. Finiteness of these
actual quotients supplies local regularity. All source and line frames,
all coefficient multiplication comparisons, and the local-to-global
comparison are constructed, so no resolution or Koszul exactness is
assumed.
-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.ActualWeightedExactness

open scoped ProjectiveChartSections ProductChartSections
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open ActualProductKoszulTerms ActualProductChartFrames ActualProductSheafFrames
open ProductWeightedKoszul ProductSheafMultiplication ProductChartSections

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k + 1) → Type u)
variable [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- Actual coefficients of the complete functional, in the original
canonical source and line frames on a chart. -/
def coefficient (d : ℤ) (φ : source K I ⟶ line K I d)
    (p : ∀ i, I i) (q : FrameIndex I p) : Γ(X, chart K I p) :=
  lineFrame K I p d
    (φ.app (chart K I p) (sourceFrame K I p (Pi.single q 1)))

/-- The genuine polynomial model of the actual product-chart ring. -/
def coordinateEquiv (p : ∀ i, I i) :
    Γ(X, chart K I p) ≃ₐ[K] MvPolynomial (FrameIndex I p) K :=
  projectiveProductChartSectionsEquiv I p

/-- The actual coefficient polynomials, without replacing the functional
by a chosen polynomial system. -/
def coefficientPolynomial (d : ℤ) (φ : source K I ⟶ line K I d)
    (p : ∀ i, I i) (q : FrameIndex I p) : MvPolynomial (FrameIndex I p) K :=
  coordinateEquiv K I p (coefficient K I d φ p q)

def equationIdeal (d : ℤ) (φ : source K I ⟶ line K I d) (p : ∀ i, I i) :
    Ideal (MvPolynomial (FrameIndex I p) K) :=
  Ideal.span (Set.range (coefficientPolynomial K I d φ p))

/-- Linearity identifies the entire actual functional with its complete
coefficient family; this is not merely a calculation on a selected subset. -/
theorem functional_coefficients (d : ℤ) (φ : source K I ⟶ line K I d)
    (p : ∀ i, I i) (v : FrameIndex I p → Γ(X, chart K I p)) :
    lineFrame K I p d (φ.app (chart K I p) (sourceFrame K I p v)) =
      Fintype.linearCombination Γ(X, chart K I p) (coefficient K I d φ p) v := by
  let a : (FrameIndex I p → Γ(X, chart K I p)) →ₗ[Γ(X, chart K I p)]
      Γ(X, chart K I p) :=
    (lineFrame K I p d).toLinearMap.comp
      ((φ.val.app (Opposite.op (chart K I p))).hom.comp
        (sourceFrame K I p).toLinearMap)
  have ha : a = Fintype.linearCombination Γ(X, chart K I p) (coefficient K I d φ p) := by
    apply (Pi.basisFun Γ(X, chart K I p) (FrameIndex I p)).ext
    intro q
    rw [Pi.basisFun_apply, Fintype.linearCombination_apply_single, one_smul]
    rfl
  exact LinearMap.congr_fun ha v

/-- A finite actual coefficient quotient makes the genuine restricted
weighted complex exact in every positive degree. -/
theorem chart_exact (d : ℤ) (φ : source K I ⟶ line K I d)
    (p : ∀ i, I i)
    [Module.Finite K (MvPolynomial (FrameIndex I p) K ⧸ equationIdeal K I d φ p)]
    (r : ℕ) :
    ((ProductWeightedKoszul.shortComplex K I d φ r).map
      (restrictFunctor (chart_affine K I p).fromSpec)).Exact := by
  let j := (chart_affine K I p).fromSpec
  let A := Γ(X, chart K I p)
  let e := (coordinateEquiv K I p).symm.toRingEquiv
  let f := coefficientPolynomial K I d φ p
  letI : Module.Finite K (MvPolynomial (FrameIndex I p) K ⧸ Ideal.span (Set.range f)) :=
    inferInstanceAs (Module.Finite K
      (MvPolynomial (FrameIndex I p) K ⧸ equationIdeal K I d φ p))
  have hf (q : FrameIndex I p) : e (f q) = coefficient K I d φ p q :=
    (coordinateEquiv K I p).symm_apply_apply _
  have hφ : (sourceSheafFrame K I p).inv ≫
      RegularSheafKoszul.tildeFunctional (ModuleCat.of A (FrameIndex I p → A))
        (Fintype.linearCombination A (fun q => e (f q))) =
      (restrictFunctor j).map φ ≫ (lineUnitFrame K I p d).hom := by
    apply functional_under_unit_frames K I p d φ
      (Fintype.linearCombination A (fun q => e (f q)))
    intro v
    simp only [hf]
    exact functional_coefficients K I d φ p v
  have hl := WeightedKoszulAffineExactness.indexed_coordinate_weighted_exact
    (K := K) A ((source K I).restrict j) ((line K I d).restrict j)
    (fun n => (coefficientFamily K I d n).restrict j)
    ((restrictFunctor j).map φ)
    (WeightedKoszulRestriction.restrictMultiplication j
      (line K I d) (coefficientFamily K I d) (coefficientMultiplication K I d))
    (lineUnitFrame K I p d)
    (fun n => lineUnitFrame K I p (d * (1 - (n : ℤ))))
    (coefficientMultiplication_compatible K I p d) e f
    (sourceSheafFrame K I p).symm hφ r
  exact WeightedKoszulRestriction.exact_restrict_of_local j
    (source K I) (line K I d) (coefficientFamily K I d) φ
    (coefficientMultiplication K I d) (coefficientsCommute K I d) r hl

/-- Full exactness of the original global weighted Koszul complex from
finiteness of its actual coefficient schemes in all genuine affine charts. -/
theorem exact_of_finite_charts (d : ℤ) (φ : source K I ⟶ line K I d)
    (hfinite : ∀ p : ∀ i, I i,
      Module.Finite K (MvPolynomial (FrameIndex I p) K ⧸ equationIdeal K I d φ p))
    (r : ℕ) : (ProductWeightedKoszul.shortComplex K I d φ r).Exact := by
  apply SchemeKoszulLocalExactness.exact_of_openImmersion_cover _
    (fun p : ∀ i, I i => (chart_affine K I p).fromSpec)
  · simpa only [IsAffineOpen.opensRange_fromSpec] using chart_cover K I
  · intro p
    letI := hfinite p
    exact chart_exact K I d φ p r

/-- The full critical coefficient is precisely the already computed
actual full coordinate equation. -/
theorem full_coefficient (T : (∀ i, I i) → K) (p : ∀ i, I i)
    (q : FrameIndex I p) :
    coefficient K I 1 (GlobalCriticalMap.criticalMap I (factorProjection K I) T) p q =
      ActualCriticalFrame.fullCoefficient K I T p q := by
  unfold coefficient ActualCriticalFrame.fullCoefficient
  exact congrArg (lineFrame K I p 1)
    (ActualCriticalFrame.full_sourceFrame_single K I T p q)

/-- The graph critical coefficient is precisely the already computed
actual quadratic graph coordinate equation. -/
theorem graph_coefficient {J : Type u} [Fintype J]
    (T : J → (∀ i, I i) → K) (p : ∀ i, I i) (q : FrameIndex I p) :
    coefficient K I 2 (GraphCriticalMap.graphCriticalMap I (factorProjection K I) T) p q =
      ActualCriticalFrame.graphCoefficient K I T p q := by
  unfold coefficient ActualCriticalFrame.graphCoefficient
  exact congrArg (lineFrame K I p 2)
    (ActualCriticalFrame.graph_sourceFrame_single K I T p q)

end PaperVerification.Segre.ActualWeightedExactness

end SegreActualWeightedExactness

section SegreWeightedKoszulDegreeOne

/-!
# The weighted augmentation is the original coefficient functional

The entire first differential is identified with the original functional
and coefficient multiplication under the canonical zeroth and first
exterior isomorphisms. For the actual product line family its coefficient
map is the actual unit action, so the transported augmentation is exactly
the critical functional, with no scalar or invertibility premise.
-/

open scoped Classical TensorProduct BigOperators

namespace PaperVerification.Segre.WeightedKoszulDegreeOne

open CategoryTheory MonoidalCategory
open TauCeti.SheafOfModules (ringCatSheaf)
open SheafCoefficientContraction SheafCoefficientComplex
open WeightedSheafKoszul WeightedKoszulLocalFormula FiniteTensorSections

universe u
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})

set_option hygiene false in
set_option quotPrecheck false in local notation "Sh" => SheafOfModules.{u} (ringCatSheaf R)
set_option hygiene false in
set_option quotPrecheck false in local notation "F" => PresheafOfModules.sheafification.{u} (𝟙 (ringCatSheaf R).obj)
local notation "G" => SheafOfModules.forget (ringCatSheaf R)
local notation "A" => TauCeti.SheafOfModules.sheafificationForgetAdjunction R

variable (M L : Sh) (Q : ℕ → Sh)

@[reassoc] theorem exteriorUnit_zero :
    exteriorUnit R M 0 ≫ (G).map ((SheafOfModules.exteriorPowerZeroIso R).hom.app M) =
      (PresheafOfModulesOfCommRing.exteriorPowerZeroIso R.obj).hom.app M.val := by
  let U : Sh := SheafOfModules.unit (ringCatSheaf R)
  have hU :
      (A).unit.app U.val ≫
          (G).map (TauCeti.SheafOfModules.sheafificationIso _ U).hom =
        𝟙 U.val := by
    rw [← TauCeti.SheafOfModules.sheafificationForgetAdjunction_counit_app R U]
    exact (A).right_triangle_components U
  simp only [exteriorUnit, SheafOfModules.exteriorPowerZeroIso_hom_app,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  let e := (PresheafOfModulesOfCommRing.exteriorPowerZeroIso R.obj).hom.app M.val
  have hn := (A).unit.naturality e
  change e ≫ (A).unit.app U.val =
    (A).unit.app _ ≫ (G).map ((F).map e) at hn
  erw [← Category.assoc, ← hn, Category.assoc, hU]
  exact Category.comp_id _

/-- The degree-one identification agrees with the actual sheafification unit. -/
@[reassoc] theorem exteriorUnit_one :
    exteriorUnit R M 1 ≫ (G).map ((SheafOfModules.exteriorPowerOneIso R).hom.app M) =
      (PresheafOfModulesOfCommRing.exteriorPowerOneIso R.obj).hom.app M.val := by
  let U : Sh := M
  have hU :
      (A).unit.app U.val ≫
          (G).map (TauCeti.SheafOfModules.sheafificationIso _ U).hom =
        𝟙 U.val := by
    rw [← TauCeti.SheafOfModules.sheafificationForgetAdjunction_counit_app R U]
    exact (A).right_triangle_components U
  simp only [exteriorUnit, SheafOfModules.exteriorPowerOneIso_hom_app,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  let e := (PresheafOfModulesOfCommRing.exteriorPowerOneIso R.obj).hom.app M.val
  have hn := (A).unit.naturality e
  change e ≫ (A).unit.app U.val =
    (A).unit.app _ ≫ (G).map ((F).map e) at hn
  erw [← Category.assoc, ← hn, Category.assoc, hU]
  exact Category.comp_id _

@[simp] theorem exteriorZeroIso_wedge (U : Cᵒᵖ) (v : Fin 0 → M.val.obj U) :
    ((SheafOfModules.exteriorPowerZeroIso R).hom.app M).val.app U
      (wedgeSection R M 0 U v) = (1 : R.obj.obj U) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.app U) (exteriorUnit_zero R M))
    (exteriorPower.ιMulti (R.obj.obj U) 0 v)
  simp only [PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    PresheafOfModulesOfCommRing.exteriorPowerZeroIso_hom_app_app] at h
  change ((SheafOfModules.exteriorPowerZeroIso R).hom.app M).val.app U
    (wedgeSection R M 0 U v) = _ at h
  exact h.trans (ModuleCat.exteriorPower.iso₀_hom_apply (R := R.obj.obj U) v)

@[simp] theorem exteriorOneIso_wedge (U : Cᵒᵖ) (v : Fin 1 → M.val.obj U) :
    ((SheafOfModules.exteriorPowerOneIso R).hom.app M).val.app U
      (wedgeSection R M 1 U v) = v 0 := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun f => f.app U)
      (exteriorUnit_one R M))
    (exteriorPower.ιMulti (R.obj.obj U) 1 v)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply,
    PresheafOfModulesOfCommRing.exteriorPowerOneIso_hom_app_app] at h
  change ((SheafOfModules.exteriorPowerOneIso R).hom.app M).val.app U
    (wedgeSection R M 1 U v) = _ at h
  exact h.trans (ModuleCat.exteriorPower.iso₁_hom_apply (R := R.obj.obj U) v)

/-- The canonical zeroth-term identification with the original coefficient
sheaf, retaining the actual left unitor. -/
def termZeroIso : term R M Q 0 ≅ Q 0 :=
  ((SheafOfModules.exteriorPowerZeroIso R).app M ⊗ᵢ Iso.refl (Q 0)) ≪≫ λ_ (Q 0)

/-- The canonical first-term identification with the source tensor the
degree-one coefficient line. -/
def termOneIso : term R M Q 1 ≅ M ⊗ Q 1 :=
  (SheafOfModules.exteriorPowerOneIso R).app M ⊗ᵢ Iso.refl (Q 1)

@[simp] theorem termZeroIso_wedge_tensor (U : Cᵒᵖ)
    (v : Fin 0 → M.val.obj U) (q : (Q 0).val.obj U) :
    (termZeroIso R M Q).hom.val.app U
      (tensorSection R ((SheafOfModules.exteriorPower R 0).obj M) (Q 0) U
        (wedgeSection R M 0 U v) q) = q := by
  simp only [termZeroIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    tensorSection_map, Iso.app_hom, exteriorZeroIso_wedge,
    SheafOfModules.id_val, PresheafOfModules.id_app, ConcreteCategory.id_apply,
    tensorSection_leftUnitor, one_smul]
  erw [tensorSection_map R]
  simp only [exteriorZeroIso_wedge, SheafOfModules.id_val,
    PresheafOfModules.id_app, ConcreteCategory.id_apply]
  exact (tensorSection_leftUnitor R (Q 0) U (1 : R.obj.obj U) q).trans (one_smul _ _)

@[simp] theorem termOneIso_wedge_tensor (U : Cᵒᵖ)
    (v : Fin 1 → M.val.obj U) (q : (Q 1).val.obj U) :
    (termOneIso R M Q).hom.val.app U
      (tensorSection R ((SheafOfModules.exteriorPower R 1).obj M) (Q 1) U
        (wedgeSection R M 1 U v) q) = tensorSection R M (Q 1) U (v 0) q := by
  simp only [termOneIso, tensorIso_hom, Iso.refl_hom, Iso.app_hom]
  erw [tensorSection_map R]
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ConcreteCategory.id_apply]
  exact congrArg (fun m => tensorSection R M (Q 1) U m q)
    (exteriorOneIso_wedge R M U v)

/-- Equality of the complete first weighted differential with the actual
coefficient-valued map, not merely equality of its image or its rank. -/
@[reassoc] theorem differential_degree_one (φ : M ⟶ L)
    (μ : ∀ n, L ⊗ Q (n + 1) ⟶ Q n) :
    differential R M L Q φ μ 0 ≫ (termZeroIso R M Q).hom =
      (termOneIso R M Q).hom ≫ (φ ⊗ₘ 𝟙 (Q 1)) ≫ μ 0 := by
  apply WeightedKoszulLocalFormula.hom_ext R M Q 1
  intro U v q
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply, differential_wedge_tensor, map_sum, map_zsmul, Fin.sum_univ_one,
    Fin.val_zero, pow_zero, one_zsmul, termZeroIso_wedge_tensor,
    termOneIso_wedge_tensor, tensorSection_map, PresheafOfModules.id_app,
    ConcreteCategory.id_apply, multiplicationAt_apply]
  simp only [Nat.zero_add, Fin.sum_univ_one, Fin.val_zero, pow_zero, one_zsmul,
    SheafOfModules.id_val, PresheafOfModules.id_app, ConcreteCategory.id_apply]
  change (∑ i : Fin 1, (-1 : ℤ) ^ (i : ℕ) •
    (μ 0).val.app U (tensorSection R L (Q 1) U (φ.val.app U (v i)) q)) = _
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero, pow_zero, one_zsmul]

end PaperVerification.Segre.WeightedKoszulDegreeOne

namespace PaperVerification.Segre.DegreeOneTransport
open CategoryTheory MonoidalCategory
universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
theorem zero {E Q L : C} (e : E ≅ 𝟙_ C) (h : Q = L)
    (hc : (E ⊗ L ≅ L) = (E ⊗ Q ≅ L)) :
    (e.hom ⊗ₘ 𝟙 Q) ≫ (λ_ Q).hom ≫ eqToHom h =
      (cast hc ((e ⊗ᵢ Iso.refl L) ≪≫ λ_ L)).hom := by
  subst Q
  simp

theorem one {E M Q L : C} (e : E ≅ M) (z : L ≅ 𝟙_ C) (h : Q = L)
    (hc : (E ⊗ L ≅ M) = (E ⊗ Q ≅ M)) :
    (e.hom ⊗ₘ 𝟙 Q) ≫ (𝟙 M ⊗ₘ eqToHom h) ≫
      (𝟙 M ⊗ₘ z.hom) ≫ (ρ_ M).hom =
      (cast hc ((e ⊗ᵢ z) ≪≫ ρ_ M)).hom := by
  subst Q
  simp [← Category.assoc, tensorHom_comp_tensorHom, tensorHom_def]
end PaperVerification.Segre.DegreeOneTransport

namespace PaperVerification.Segre.ProductWeightedKoszul

open CategoryTheory MonoidalCategory AlgebraicGeometry
open ActualProductKoszulTerms

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k + 1) → Type u)
variable [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

set_option quotPrecheck false in local notation "X" => (product K I).scheme

set_option maxHeartbeats 1000000 in
/-- The actual product Koszul augmentation is its original coefficient
functional under the fixed geometric term isomorphisms. The explicit degree
transports preserve the canonical unit action. -/
@[reassoc] theorem differential_degree_one (d : ℤ)
    (φ : source K I ⟶ line K I d) :
    differential K I d φ 0 ≫ (ActualProductKoszulTerms.termZeroIso K I d).hom =
      (ActualProductKoszulTerms.termOneIso K I d).hom ≫ φ := by
  have h := WeightedKoszulDegreeOne.differential_degree_one (X).sheaf
    (source K I) (line K I d) (coefficientFamily K I d) φ
    (coefficientMultiplication K I d)
  have h0 : coefficientFamily K I d 0 = line K I d := by
    simp [coefficientFamily]
  have h1 : coefficientFamily K I d 1 = line K I 0 := by
    simp [coefficientFamily]
  have hz : (WeightedKoszulDegreeOne.termZeroIso (X).sheaf
      (source K I) (coefficientFamily K I d)).hom ≫ eqToHom h0 =
      (ActualProductKoszulTerms.termZeroIso K I d).hom := by
    unfold WeightedKoszulDegreeOne.termZeroIso ActualProductKoszulTerms.termZeroIso
    exact DegreeOneTransport.zero _ h0 _
  have ho : (WeightedKoszulDegreeOne.termOneIso (X).sheaf
      (source K I) (coefficientFamily K I d)).hom ≫
        (𝟙 (source K I) ⊗ₘ eqToHom h1) ≫
        (𝟙 (source K I) ⊗ₘ (lineZeroIso K I).hom) ≫
        (ρ_ (source K I)).hom = (ActualProductKoszulTerms.termOneIso K I d).hom := by
    unfold WeightedKoszulDegreeOne.termOneIso ActualProductKoszulTerms.termOneIso
    exact DegreeOneTransport.one _ _ h1 _
  have h' := congrArg (fun f => f ≫ eqToHom h0) h
  simp only [Category.assoc] at h'
  rw [hz] at h'
  have hm : coefficientMultiplication K I d 0 ≫ eqToHom h0 =
      (𝟙 (line K I d) ⊗ₘ eqToHom h1) ≫
      (𝟙 (line K I d) ⊗ₘ (lineZeroIso K I).hom) ≫ (ρ_ (line K I d)).hom :=
    ProductLineMultiplication.coefficientMultiplication_zero_transport K I d
  erw [hm] at h'
  change differential K I d φ 0 ≫ (ActualProductKoszulTerms.termZeroIso K I d).hom = _ at h'
  rw [h', ← ho]
  simp only [Category.assoc]
  rw [← rightUnitor_naturality]
  simp only [← tensorHom_id, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

/-- Transporting the full first map through the actual geometric term
identifications gives the original functional, exactly. -/
theorem transported_differential_degree_one (d : ℤ)
    (φ : source K I ⟶ line K I d) :
    (ActualProductKoszulTerms.termOneIso K I d).inv ≫
      differential K I d φ 0 ≫
        (ActualProductKoszulTerms.termZeroIso K I d).hom = φ := by
  rw [differential_degree_one, Iso.inv_hom_id_assoc]

end PaperVerification.Segre.ProductWeightedKoszul

end SegreWeightedKoszulDegreeOne

section SegreProductResolutionImage

/-!
# Actual critical image sections from the full product resolution

The full weighted complex is exact by the actual finite-chart theorem.
Its actual terms have the proved graph or balanced cohomology gaps and
vanish above the total rank. The first differential is exactly the
original coefficient functional. Consequently every global section of
its image sheaf lifts to the original source, and membership in that
global range is precisely membership in the actual coefficient ideals
on all product charts.
-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.ProductResolutionImage

open scoped ProjectiveChartSections ProductChartSections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open ActualProductKoszulTerms ActualProductChartFrames ActualProductSheafFrames
open ActualWeightedExactness ProductKoszulVanishing

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k + 1) → Type u)
variable [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- The graph cohomology gap implies surjectivity onto the actual image
sheaf of the original degree-two functional. -/
theorem graph_image_sections_surjective
    (hI : ∀ i, 0 < Fintype.card (I i))
    (φ : source K I ⟶ line K I 2)
    (hfinite : ∀ p : ∀ i, I i,
      Module.Finite K (MvPolynomial (FrameIndex I p) K ⧸ equationIdeal K I 2 φ p)) :
    Function.Surjective ((factorThruImage φ).app ⊤) := by
  let B := max 1 (∑ i, (Fintype.card (I i) - 1))
  apply ResolutionImageMembership.image_sections_surjective_of_resolution
    (term K I 2) (ProductWeightedKoszul.differential K I 2 φ)
    (ProductWeightedKoszul.differential_squared_unconditional K I 2 φ)
    (fun r => exact_of_finite_charts K I 2 φ hfinite r) B
    (le_max_left _ _) ?_ ?_ φ (termOneIso K I 2) (termZeroIso K I 2)
    (ProductWeightedKoszul.differential_degree_one K I 2 φ)
  · apply term_isZero_of_degree_gt K I hI 2 (B + 1)
    exact Nat.lt_succ_of_le (le_max_right _ _)
  · intro r hr _ q hq
    exact graph_term_cohomology_vanishes K I hI r q hr hq

/-- The balanced cohomology gap has the same consequence for the actual
degree-one full critical functional, under the paper's exact triangle
inequalities and without any omitted high exterior term. -/
theorem balanced_image_sections_surjective
    (hI : ∀ i, 0 < Fintype.card (I i)) (htriangle : TriangleDimensions I)
    (φ : source K I ⟶ line K I 1)
    (hfinite : ∀ p : ∀ i, I i,
      Module.Finite K (MvPolynomial (FrameIndex I p) K ⧸ equationIdeal K I 1 φ p)) :
    Function.Surjective ((factorThruImage φ).app ⊤) := by
  let B := max 1 (∑ i, (Fintype.card (I i) - 1))
  apply ResolutionImageMembership.image_sections_surjective_of_resolution
    (term K I 1) (ProductWeightedKoszul.differential K I 1 φ)
    (ProductWeightedKoszul.differential_squared_unconditional K I 1 φ)
    (fun r => exact_of_finite_charts K I 1 φ hfinite r) B
    (le_max_left _ _) ?_ ?_ φ (termOneIso K I 1) (termZeroIso K I 1)
    (ProductWeightedKoszul.differential_degree_one K I 1 φ)
  · apply term_isZero_of_degree_gt K I hI 1 (B + 1)
    exact Nat.lt_succ_of_le (le_max_right _ _)
  · intro r hr _ q hq
    exact balanced_term_cohomology_vanishes K I hI htriangle r q hr hq

/-- The polynomial expression of an original global coefficient-line
section on an actual affine product chart. -/
def chartSectionPolynomial (d : ℤ) (s : Γ(line K I d, ⊤)) (p : ∀ i, I i) :
    MvPolynomial (FrameIndex I p) K :=
  coordinateEquiv K I p
    (lineFrame K I p d ((line K I d).presheaf.map (chart K I p).leTop.op s))

/-- The entire actual coefficient ideal maps to its stated polynomial
ideal through the actual affine coordinate-ring isomorphism. -/
theorem map_coefficient_ideal (d : ℤ) (φ : source K I ⟶ line K I d)
    (p : ∀ i, I i) :
    (Ideal.span (Set.range (coefficient K I d φ p))).map
        (coordinateEquiv K I p).toRingHom = equationIdeal K I d φ p := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

theorem coefficient_mem_iff (d : ℤ) (φ : source K I ⟶ line K I d)
    (p : ∀ i, I i) (s : Γ(X, chart K I p)) :
    s ∈ Ideal.span (Set.range (coefficient K I d φ p)) ↔
      coordinateEquiv K I p s ∈ equationIdeal K I d φ p := by
  rw [← map_coefficient_ideal, Ideal.mem_map_iff_of_surjective
    (coordinateEquiv K I p).toRingHom (coordinateEquiv K I p).surjective]
  constructor
  · intro hs
    exact ⟨s, hs, rfl⟩
  · rintro ⟨t, ht, he⟩
    exact (coordinateEquiv K I p).injective he ▸ ht

set_option maxHeartbeats 1000000 in
/-- Global range membership is literal chart polynomial-ideal membership,
provided the actual image factor has the proved section-surjectivity. -/
theorem global_range_iff_coefficient_ideals (d : ℤ)
    (φ : source K I ⟶ line K I d)
    (hsurj : Function.Surjective ((factorThruImage φ).app ⊤))
    (s : Γ(line K I d, ⊤)) :
    (∃ t : Γ(source K I, ⊤), φ.app ⊤ t = s) ↔
      ∀ p : ∀ i, I i, chartSectionPolynomial K I d s p ∈ equationIdeal K I d φ p := by
  rw [ResolutionImageMembership.global_range_iff_chart_ideals φ hsurj
    (chart K I) (chart_affine K I) (chart_cover K I).ge (FrameIndex I)
    (sourceFrame K I) (fun p => lineFrame K I p d) s]
  apply forall_congr'
  intro p
  have hc : ImageChartMembership.coefficient φ (chart K I p)
      (sourceFrame K I p) (lineFrame K I p d) = coefficient K I d φ p := by
    funext q
    simp only [ImageChartMembership.coefficient,
      ImageChartMembership.sectionLinear_apply, coefficient]
    apply congrArg (fun v : FrameIndex I p → Γ((product K I).scheme, chart K I p) =>
      lineFrame K I p d (φ.app (chart K I p) (sourceFrame K I p v)))
    funext j
    by_cases hj : j = q
    · subst j
      simp
    · simp [Pi.single_apply, hj, Ne.symm hj]
  rw [hc]
  exact coefficient_mem_iff K I d φ p _

/-- The graph image theorem has no global-image surjectivity premise. -/
theorem graph_global_range_iff_chart_ideals
    (hI : ∀ i, 0 < Fintype.card (I i))
    (φ : source K I ⟶ line K I 2)
    (hfinite : ∀ p : ∀ i, I i,
      Module.Finite K (MvPolynomial (FrameIndex I p) K ⧸ equationIdeal K I 2 φ p))
    (s : Γ(line K I 2, ⊤)) :
    (∃ t : Γ(source K I, ⊤), φ.app ⊤ t = s) ↔
      ∀ p : ∀ i, I i, chartSectionPolynomial K I 2 s p ∈ equationIdeal K I 2 φ p :=
  global_range_iff_coefficient_ideals K I 2 φ
    (graph_image_sections_surjective K I hI φ hfinite) s

/-- The balanced image theorem has only the actual finite-chart and
triangle-format conditions; all global lifting is proved. -/
theorem balanced_global_range_iff_chart_ideals
    (hI : ∀ i, 0 < Fintype.card (I i)) (htriangle : TriangleDimensions I)
    (φ : source K I ⟶ line K I 1)
    (hfinite : ∀ p : ∀ i, I i,
      Module.Finite K (MvPolynomial (FrameIndex I p) K ⧸ equationIdeal K I 1 φ p))
    (s : Γ(line K I 1, ⊤)) :
    (∃ t : Γ(source K I, ⊤), φ.app ⊤ t = s) ↔
      ∀ p : ∀ i, I i, chartSectionPolynomial K I 1 s p ∈ equationIdeal K I 1 φ p :=
  global_range_iff_coefficient_ideals K I 1 φ
    (balanced_image_sections_surjective K I hI htriangle φ hfinite) s

end PaperVerification.Segre.ProductResolutionImage

end SegreProductResolutionImage

end SegreCriticalBundleGeometry

end
end
end ProbeLayer391


/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
