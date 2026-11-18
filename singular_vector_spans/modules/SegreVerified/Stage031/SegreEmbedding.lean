module
public import SegreVerified.Stage031.SegreCharts
public import SegreVerified.Stage031.SectionZeroScheme
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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false


section SegreProjectiveTheorems

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage031.SegreEmbedding"
  out.flush

/-!
# The original embedded scheme and the principal projective span theorems

The named sections preserve the original proof stages and local scopes.
-/


section SegreSchemeClosedImmersion

/-!
# The genuine Segre morphism is a closed immersion

The inverse image of every standard ambient chart is the full product
chart with that pivot. On those actual affine schemes, the map on rings is
the literal surjective Segre-coordinate map. This proves the global closed
immersion by the target-local criterion, with no dimension or reducedness
hypothesis.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.SegreSchemeMorphism

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MvPolynomial
open HomogeneousLocalization FixedProductCohomology ProductChartSections
open CoordinateTransitions ProductCoordinatePullback
open scoped ProjectiveChartSections ProductChartSections

universe u

/-- Compose an arbitrary affine chart with an already proved base triangle.
All ring objects and morphisms stay abstract while Spec.map_comp is used. -/
theorem spec_chart_triangle {X Y : Scheme.{u}} {R S T : CommRingCat.{u}}
    (j : X ⟶ Spec R) (a : S ⟶ R) (b : T ⟶ S)
    (i : Spec S ⟶ Y) (g : Y ⟶ Spec T)
    (hi : i ≫ g = Spec.map b) :
    (j ≫ Spec.map a ≫ i) ≫ g = j ≫ Spec.map (b ≫ a) := by
  calc
    (j ≫ Spec.map a ≫ i) ≫ g = j ≫ (Spec.map a ≫ (i ≫ g)) := by
      simp only [Category.assoc]
    _ = j ≫ (Spec.map a ≫ Spec.map b) :=
      congrArg (fun f : Spec S ⟶ Spec T => j ≫ (Spec.map a ≫ f)) hi
    _ = j ≫ Spec.map (b ≫ a) :=
      congrArg (fun f : Spec R ⟶ Spec T => j ≫ f) (Spec.map_comp b a).symm

/-- The affine-open structure map, using the existing direct triangle rather
than rewriting through isoSpec and chosen affine-limit constructions. -/
theorem affine_open_toBase {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] (U : X.Opens) (hU : IsAffineOpen U) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(X,U))) =
      U.ι ≫ (X ↘ Spec (.of K)) := by
  calc
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(X,U))) =
        U.toSpecΓ ≫ (hU.fromSpec ≫ (X ↘ Spec (.of K))) :=
      congrArg (fun f : Spec Γ(X,U) ⟶ Spec (.of K) => U.toSpecΓ ≫ f)
        (SectionZeroScheme.fromSpec_toBase K ⟨U,hU⟩).symm
    _ = (U.toSpecΓ ≫ hU.fromSpec) ≫ (X ↘ Spec (.of K)) :=
      (Category.assoc _ _ _).symm
    _ = U.ι ≫ (X ↘ Spec (.of K)) :=
      congrArg (fun f : U.toScheme ⟶ X => f ≫ (X ↘ Spec (.of K)))
        hU.toSpecΓ_fromSpec


section General

variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]
local notation "A" => fun i => ProductKoszulVanishing.projectiveScheme K (I i)
set_option quotPrecheck false in local notation "S" => (CoveredScheme.finiteProduct A).scheme
set_option quotPrecheck false in local notation "𝒜" => homogeneousSubmodule (∀ i,I i) K
local notation "P" => Proj 𝒜
attribute [local instance] MvPolynomial.gradedAlgebra

theorem preimage_coordinateOpen (q : ∀ i,I i) :
    morphism K I ⁻¹ᵁ ProjectiveCech.coordinateOpen q=finiteChart A q := by
  ext x
  obtain ⟨p,hp⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((finiteChart_cover A).ge (Set.mem_univ x))
  change morphism K I x ∈ ProjectiveCech.coordinateOpen q ↔ x ∈ finiteChart A q
  have hpoint : morphism K I x=
      localMorphism K I p (finiteChart A p) le_rfl ⟨x,hp⟩ := by
    exact congrArg (fun f => f ⟨x,hp⟩) (chart_ι_morphism K I p)
  rw [hpoint]
  change (⟨x,hp⟩ : (finiteChart A p).toScheme) ∈
      localMorphism K I p (finiteChart A p) le_rfl ⁻¹ᵁ
        ProjectiveCech.coordinateOpen q ↔ _
  erw [localMorphism_preimage_coordinate,
    SegreEmbeddingChartOpens.basicOpen_tensorCoordinate_chart]
  exact and_iff_right hp

/-- The same local morphism with codomain the actual ambient affine open. -/
def localAffineMorphism (p : ∀ i,I i) :
    (finiteChart A p).toScheme ⟶ (ProjectiveCech.coordinateOpen (K := K) p).toScheme :=
  (finiteChart A p).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (chartLift K I p (finiteChart A p) le_rfl)) ≫
      (Proj.basicOpenIsoSpec 𝒜 (X p) (isHomogeneous_X (R := K) p) one_pos).inv

@[reassoc] theorem localAffineMorphism_ι (p : ∀ i,I i) :
    localAffineMorphism K I p ≫ (ProjectiveCech.coordinateOpen p).ι=
      localMorphism K I p (finiteChart A p) le_rfl := by
  dsimp only [localAffineMorphism, localMorphism]
  simp only [Category.assoc]
  erw [Proj.basicOpenIsoSpec_inv_ι]

theorem morphismRestrict_coordinate (p : ∀ i,I i) :
    morphism K I ∣_ ProjectiveCech.coordinateOpen p=
      ((S).isoOfEq (preimage_coordinateOpen K I p)).hom ≫ localAffineMorphism K I p := by
  rw [← cancel_mono (ProjectiveCech.coordinateOpen (K := K) p).ι]
  rw [morphismRestrict_ι,Category.assoc,localAffineMorphism_ι,
    ← chart_ι_morphism,Scheme.isoOfEq_hom_ι_assoc]

theorem chartLift_algebraMap (p : ∀ i,I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) (c : K) :
    chartLift K I p U hp (algebraMap K (Away 𝒜 (X p)) c)=
      algebraMap K Γ(S,U) c := by
  rw [HomogeneousLocalization.algebraMap_eq_comp,RingHom.comp_apply]
  change Away.lift 𝒜 (coordinateHom K I p U hp) (pivotUnit K I p U hp)
      (algebraMap (𝒜 0) _ (algebraMap K (𝒜 0) c))=_
  rw [Away.lift_algebraMap]
  simp only [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq,
    coordinateHom, MvPolynomial.eval₂Hom_C]

def chartLiftAlgHom (p : ∀ i,I i) (U : (S).Opens) (hp : U ≤ finiteChart A p) :
    Away 𝒜 (X p) →ₐ[K] Γ(S,U) where
  __ := chartLift K I p U hp
  commutes' := chartLift_algebraMap K I p U hp

/-- The canonical local Segre map preserves the original coefficient field. -/
theorem localMorphism_toBase (p : ∀ i,I i) :
    localMorphism K I p (finiteChart A p) le_rfl ≫
      ProjectiveGlobalSections.projectiveToSpec (I := ∀ i,I i) (K := K)=
        (finiteChart A p).ι ≫ (S ↘ Spec (.of K)) := by
  let U := finiteChart A p
  let hU := finiteChart_affine A p
  have hscalar :
      (chartLift K I p U le_rfl).comp
        ((fromZeroRingHom 𝒜 (Submonoid.powers (X p))).comp
          (algebraMap K (𝒜 0)))=algebraMap K Γ(S,U) := by
    apply RingHom.ext
    intro c
    exact chartLift_algebraMap K I p U le_rfl c
  let a : CommRingCat.of (Away 𝒜 (X p)) ⟶ Γ(S,U) :=
    CommRingCat.ofHom (chartLift K I p U le_rfl)
  let b : CommRingCat.of K ⟶ CommRingCat.of (Away 𝒜 (X p)) :=
    CommRingCat.ofHom ((fromZeroRingHom 𝒜 (Submonoid.powers (X p))).comp
      (algebraMap K (𝒜 0)))
  have haway :
      Proj.awayι 𝒜 (X p) (isHomogeneous_X (R := K) p) one_pos ≫
          ProjectiveGlobalSections.projectiveToSpec (I := ∀ i,I i) (K := K) =
        Spec.map b := by
    change Proj.awayι 𝒜 (X p) (isHomogeneous_X (R := K) p) one_pos ≫
      (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom
        (algebraMap K (𝒜 0)))) = _
    calc
      _ = (Proj.awayι 𝒜 (X p) (isHomogeneous_X (R := K) p) one_pos ≫
          Proj.toSpecZero 𝒜) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K (𝒜 0))) :=
        (Category.assoc _ _ _).symm
      _ = Spec.map (CommRingCat.ofHom (fromZeroRingHom 𝒜 _)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K (𝒜 0))) :=
        congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom
          (algebraMap K (𝒜 0))))
          (Proj.awayι_toSpecZero 𝒜 (X p) (isHomogeneous_X (R := K) p) one_pos)
      _ = Spec.map b :=
        (Spec.map_comp
          (CommRingCat.ofHom (algebraMap K (𝒜 0)))
          (CommRingCat.ofHom (fromZeroRingHom 𝒜 _))).symm
  have hs : b ≫ a = CommRingCat.ofHom (algebraMap K Γ(S,U)) := by
    apply CommRingCat.hom_ext
    exact hscalar
  calc
    _ = U.toSpecΓ ≫ Spec.map (b ≫ a) :=
      spec_chart_triangle U.toSpecΓ a b _ _ haway
    _ = U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap K Γ(S,U))) :=
      congrArg (fun f : CommRingCat.of K ⟶ Γ(S,U) => U.toSpecΓ ≫ Spec.map f) hs
    _ = U.ι ≫ (S ↘ Spec (.of K)) := affine_open_toBase U hU

/-- The actual Segre map respects the original coefficient-field structure
maps; the scheme-image comparison therefore preserves finiteness over K. -/
@[reassoc] theorem morphism_toBase :
    morphism K I ≫ ProjectiveGlobalSections.projectiveToSpec
      (I := ∀ i,I i) (K := K)=S ↘ Spec (.of K) := by
  apply (chartCover K I).hom_ext
  intro p
  change (finiteChart A p).ι ≫ morphism K I ≫
    ProjectiveGlobalSections.projectiveToSpec (I := ∀ i,I i) (K := K) =
      (finiteChart A p).ι ≫ (S ↘ Spec (.of K))
  erw [chart_ι_morphism_assoc,localMorphism_toBase]

end General

section Numerical

variable {K : Type} [Field K] {k : ℕ} (n : Fin (k+1) → ℕ)
local notation "I" => fun i => Fin (n i+1)
local notation "A" => fun i => ProductKoszulVanishing.projectiveScheme K (I i)
set_option quotPrecheck false in local notation "S" => (CoveredScheme.finiteProduct A).scheme
local notation "𝒜" => homogeneousSubmodule (Staircase.Cell n) K
attribute [local instance] MvPolynomial.gradedAlgebra

theorem polynomial_tensorCoordinate (p a : Staircase.Cell n) :
    numericalProductChartSectionsEquiv (K := K) n p
      (tensorCoordinate K I p (finiteChart A p) le_rfl a)=
        AllFactorPointSpan.chartSegreCoordinate p a := by
  rw [tensorCoordinate,map_prod,SegreEmbeddingChart.chartSegreCoordinate_eq_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact numericalProductChartSectionsEquiv_coordinate n p i (a i)

/-- The actual homogeneous-localization map is exactly the independently
defined surjective affine Segre polynomial map under the canonical chart
ring equivalence. -/
theorem chartLift_polynomial (p : Staircase.Cell n) :
    (numericalProductChartSectionsEquiv (K := K) n p).toAlgHom.comp
      (chartLiftAlgHom K I p (finiteChart A p) le_rfl)=
        SegreEmbeddingChart.homogeneousChartPullback p := by
  let e := PolynomialChartRing.awayEquivPolynomial (K := K) p
  have hpoly :
      ((numericalProductChartSectionsEquiv (K := K) n p).toAlgHom.comp
        (chartLiftAlgHom K I p (finiteChart A p) le_rfl)).comp e.symm.toAlgHom=
          SegreEmbeddingChart.affinePullback p := by
    apply MvPolynomial.algHom_ext
    intro a
    have ha : e.symm (X a)=
        PaperVerification.HomogeneousChartDehomogenization.fraction 𝒜
          (isHomogeneous_X (R := K) p) 1 ⟨X a.val,isHomogeneous_X (R := K) a.val⟩ := by
      apply e.injective
      simp [e,PolynomialChartRing.awayEquivPolynomial_coordinate]
    simp only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,ha]
    rw [show chartLiftAlgHom K I p (finiteChart A p) le_rfl
        (PaperVerification.HomogeneousChartDehomogenization.fraction 𝒜
          (isHomogeneous_X (R := K) p) 1 ⟨X a.val,isHomogeneous_X (R := K) a.val⟩)=
        tensorCoordinate K I p (finiteChart A p) le_rfl a.val from
      chartLift_coordinate K I p (finiteChart A p) le_rfl a.val,
      polynomial_tensorCoordinate,SegreEmbeddingChart.affinePullback_X]
  apply AlgHom.ext
  intro z
  have h := AlgHom.congr_fun hpoly (e z)
  simpa only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.symm_apply_apply,
    SegreEmbeddingChart.homogeneousChartPullback] using h

theorem chartLift_surjective (p : Staircase.Cell n) :
    Function.Surjective (chartLift K I p (finiteChart A p) le_rfl) := by
  intro s
  let e := numericalProductChartSectionsEquiv (K := K) n p
  obtain ⟨z,hz⟩ := SegreEmbeddingChart.homogeneousChartPullback_surjective
    (K := K) p (e s)
  refine ⟨z,e.injective ?_⟩
  exact (AlgHom.congr_fun (chartLift_polynomial n p) z).trans hz

instance localAffineMorphism_isClosedImmersion (p : Staircase.Cell n) :
    IsClosedImmersion (localAffineMorphism K I p) := by
  haveI : IsIso (finiteChart A p).toSpecΓ := by
    rw [← IsAffineOpen.isoSpec_hom (finiteChart_affine A p)]
    infer_instance
  haveI := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (chartLift K I p (finiteChart A p) le_rfl))
    (chartLift_surjective n p)
  unfold localAffineMorphism
  infer_instance

/-- A genuine closed immersion for every positive coordinate vector-space
dimension, including all projective point factors and every characteristic. -/
instance isClosedImmersion : IsClosedImmersion (morphism K I) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion)
    (ProjectiveCech.coordinateOpen («I» := Staircase.Cell n) (K := K))
    ProjectiveCech.coordinate_cover]
  intro p
  rw [morphismRestrict_coordinate]
  infer_instance

end Numerical
end PaperVerification.Segre.SegreSchemeMorphism

end SegreSchemeClosedImmersion

section SegreSchemeChartPullback

/-!
# Exact structure-sheaf pullback on Segre charts

The comparison identifies the actual scheme morphism's map on sections
with the complete polynomial substitution used in the critical equations.

-/

set_option autoImplicit false
open scoped Classical BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.SegreSchemeMorphism

open CategoryTheory AlgebraicGeometry Opposite MvPolynomial
open HomogeneousLocalization FixedProductCohomology ProductChartSections
open scoped ProjectiveChartSections ProductChartSections

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]
local notation "A" => fun i => ProductKoszulVanishing.projectiveScheme K (I i)
set_option quotPrecheck false in local notation "S" => (CoveredScheme.finiteProduct A).scheme
set_option quotPrecheck false in local notation "𝒜" => homogeneousSubmodule (∀ i,I i) K
local notation "P" => Proj 𝒜

theorem resLE_coordinate (p : ∀ i,I i) :
    (morphism K I).resLE (ProjectiveCech.coordinateOpen p) (finiteChart A p)
      (preimage_coordinateOpen K I p).ge=localAffineMorphism K I p := by
  rw [← cancel_mono (ProjectiveCech.coordinateOpen (K := K) p).ι,
    Scheme.Hom.resLE_comp_ι,localAffineMorphism_ι,chart_ι_morphism]

/-- The literal map on rings is obtained by evaluating the homogeneous
localization map, before applying any abstract ring equivalence. -/
theorem appLE_awayToSection (p : ∀ i,I i) :
    Proj.awayToSection 𝒜 (X p) ≫
      (morphism K I).appLE (ProjectiveCech.coordinateOpen p) (finiteChart A p)
        (preimage_coordinateOpen K I p).ge=
      CommRingCat.ofHom (chartLift K I p (finiteChart A p) le_rfl) := by
  haveI : IsIso (finiteChart A p).toSpecΓ := by
    rw [← IsAffineOpen.isoSpec_hom (finiteChart_affine A p)]
    infer_instance
  apply Spec.map_injective
  erw [← cancel_epi (finiteChart A p).toSpecΓ,Spec.map_comp,
    Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,resLE_coordinate]
  change localAffineMorphism K I p ≫ Proj.basicOpenToSpec 𝒜 (X p)=_
  rw [← Proj.basicOpenIsoSpec_hom 𝒜 (X p) (isHomogeneous_X (R := K) p) one_pos]
  simp only [localAffineMorphism,Category.assoc,Iso.inv_hom_id,Category.comp_id]

/-- The actual affine pullback retains the canonical base-field algebra. -/
def chartPullback (p : ∀ i,I i) :
    Γ(P,ProjectiveCech.coordinateOpen p) →ₐ[K] Γ(S,finiteChart A p) := by
  letI : (morphism K I).IsOver (Spec (.of K)) := ⟨morphism_toBase K I⟩
  exact
    { toRingHom := ((morphism K I).appLE (ProjectiveCech.coordinateOpen p)
        (finiteChart A p) (preimage_coordinateOpen K I p).ge).hom
      commutes' c := AffineRectangleTensor.appLE_baseRing K (morphism K I)
        (ProjectiveCech.coordinateOpen p) (finiteChart A p)
        (preimage_coordinateOpen K I p).ge c }

@[simp] theorem chartPullback_awaySection (p : ∀ i,I i) (z : Away 𝒜 (X p)) :
    chartPullback K I p (ProjectiveChartSections.awaySectionEquiv p z)=
      chartLift K I p (finiteChart A p) le_rfl z := by
  exact congrArg (fun f => f z) (appLE_awayToSection K I p)

end PaperVerification.Segre.SegreSchemeMorphism

namespace PaperVerification.Segre.SegreSchemeMorphism

open CategoryTheory AlgebraicGeometry MvPolynomial
open FixedProductCohomology ProductChartSections
open scoped ProjectiveChartSections ProductChartSections

variable {K : Type} [Field K] {k : ℕ} (n : Fin (k+1) → ℕ)
local notation "I" => fun i => Fin (n i+1)
local notation "A" => fun i => ProductKoszulVanishing.projectiveScheme K (I i)

/-- Commutation of the entire actual chart algebra pullback with the
independently defined affine Segre substitution. -/
theorem chartPullback_polynomial (p : Staircase.Cell n)
    (s : Γ(Proj (homogeneousSubmodule (Staircase.Cell n) K),
      ProjectiveCech.coordinateOpen p)) :
    numericalProductChartSectionsEquiv (K := K) n p (chartPullback K I p s)=
      SegreEmbeddingChart.affinePullback p
        (ProjectiveChartSections.chartSectionsEquiv p s) := by
  obtain ⟨z,rfl⟩ := (ProjectiveChartSections.awaySectionEquiv (K := K) p).surjective s
  rw [chartPullback_awaySection]
  change numericalProductChartSectionsEquiv (K := K) n p
      (chartLift K I p (finiteChart A p) le_rfl z)=
    SegreEmbeddingChart.affinePullback p
      (PolynomialChartRing.awayEquivPolynomial p
        ((ProjectiveChartSections.awaySectionEquiv p).symm
          (ProjectiveChartSections.awaySectionEquiv p z)))
  rw [AlgEquiv.symm_apply_apply]
  exact AlgHom.congr_fun (chartLift_polynomial n p) z

theorem chartPullback_polynomial_hom (p : Staircase.Cell n) :
    (numericalProductChartSectionsEquiv (K := K) n p).toAlgHom.comp
      (chartPullback K I p)=
    (SegreEmbeddingChart.affinePullback p).comp
      (ProjectiveChartSections.chartSectionsEquiv p).toAlgHom := by
  apply AlgHom.ext
  intro s
  exact chartPullback_polynomial n p s

end PaperVerification.Segre.SegreSchemeMorphism

end SegreSchemeChartPullback

section SegreClosedEmbeddingIdeals

/-!
# Whole ideal sheaves under a closed embedding

An exact pullback equality of chart ideals identifies the composite closed
subscheme with the ambient intersection. This lemma uses the whole ideals,
not their radicals, and its application supplies every chart equality.

-/

set_option autoImplicit false

namespace PaperVerification.Segre.ClosedEmbeddingIdeals

open CategoryTheory AlgebraicGeometry Opposite

universe u v
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

theorem appLE_surjective (U : Y.affineOpens) (V : X.affineOpens)
    (h : f ⁻¹ᵁ U.val=V.val) :
    Function.Surjective (f.appLE U.val V.val h.ge) := by
  rcases V with ⟨V,hV⟩
  dsimp at h
  subst V
  simpa only [Scheme.Hom.appLE_eq_app] using f.app_surjective U.val U.property

theorem ker_appLE (U : Y.affineOpens) (V : X.affineOpens)
    (h : f ⁻¹ᵁ U.val=V.val) :
    RingHom.ker (f.appLE U.val V.val h.ge).hom=f.ker.ideal U := by
  rcases V with ⟨V,hV⟩
  dsimp at h
  subst V
  simp only [Scheme.Hom.appLE_eq_app,Scheme.Hom.ker_apply]

set_option backward.isDefEq.respectTransparency false in
theorem ker_subscheme_comp (J : X.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) (h : f ⁻¹ᵁ U.val=V.val) :
    (J.subschemeι ≫ f).ker.ideal U=
      Ideal.comap (f.appLE U.val V.val h.ge).hom (J.ideal V) := by
  rcases V with ⟨V,hV⟩
  dsimp at h
  subst V
  rw [Scheme.Hom.ker_apply,Scheme.Hom.comp_app,CommRingCat.hom_comp,
    ← RingHom.comap_ker,J.ker_subschemeι_app ⟨_,hV⟩]
  rw [Scheme.Hom.appLE_eq_app]

/-- If the ambient defining equations pull back to the entire intrinsic
ideal, the ambient intersection has exactly the composite inclusion's
kernel. All hypotheses are ordinary explicit chart equalities. -/
theorem ker_subscheme_comp_eq_sup (J : X.IdealSheafData) (L : Y.IdealSheafData)
    {ι : Type v} (U : ι → Y.affineOpens) (hU : (⨆ i,(U i).val)=⊤)
    (V : ι → X.affineOpens) (hV : ∀ i,f ⁻¹ᵁ (U i).val=(V i).val)
    (hmap : ∀ i,Ideal.map (f.appLE (U i).val (V i).val (hV i).ge).hom
      (L.ideal (U i))=J.ideal (V i)) :
    (J.subschemeι ≫ f).ker=f.ker ⊔ L := by
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hU
  intro i
  rw [ker_subscheme_comp f J (U i) (V i) (hV i),← hmap i,
    Ideal.comap_map_of_surjective _ (appLE_surjective f (U i) (V i) (hV i)),
    ← RingHom.ker_eq_comap_bot,ker_appLE f (U i) (V i) (hV i)]
  exact sup_comm _ _

/-- The closed-subscheme isomorphism induced by equality of the entire
ambient ideal, rather than by equality of closed points. -/
def subschemeIso (J : X.IdealSheafData) (L : Y.IdealSheafData)
    (h : (J.subschemeι ≫ f).ker=f.ker ⊔ L) :
    J.subscheme ≅ (f.ker ⊔ L).subscheme := by
  let g := J.subschemeι ≫ f
  let j := (f.ker ⊔ L).subschemeι
  have hj : j.ker=g.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact h.symm
  let a := IsClosedImmersion.lift j g hj.le
  haveI : IsIso a := IsClosedImmersion.isIso_of_ker_eq g j a
    (IsClosedImmersion.lift_fac j g hj.le) hj.symm
  exact asIso a

@[reassoc] theorem subschemeIso_hom_ι (J : X.IdealSheafData) (L : Y.IdealSheafData)
    (h : (J.subschemeι ≫ f).ker=f.ker ⊔ L) :
    (subschemeIso f J L h).hom ≫ (f.ker ⊔ L).subschemeι=J.subschemeι ≫ f := by
  exact IsClosedImmersion.lift_fac _ _ _

end PaperVerification.Segre.ClosedEmbeddingIdeals

end SegreClosedEmbeddingIdeals


end SegreProjectiveTheorems

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
