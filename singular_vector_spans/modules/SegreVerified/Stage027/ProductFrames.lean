module
public import SegreVerified.Stage027.ProductTerms
public import SegreVerified.Stage027.TensorSections
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
  out.putStrLn "SEGRE_STAGE Stage027.ProductFrames"
  out.flush

/-!
# The actual critical bundle and its weighted Koszul complex

The named sections preserve the original proof stages and local scopes.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.SchemeFiniteTensorSections

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open SheafCoefficientContraction FiniteTensorSections FixedProductProjections

universe u
variable {Y : Scheme.{u}} {k : ℕ}

/-- The finite factorwise comparison in the native scheme-section presentation. -/
theorem family_section {M N : Fin k → Y.Modules} (e : ∀ i, M i ≅ N i)
    (U : Y.Opens) (m : ∀ i, Γ(M i,U)) :
    (tensorFamilyIso e).hom.app U (finiteTensorSection Y.sheaf M (op U) m) =
      finiteTensorSection Y.sheaf N (op U) (fun i => (e i).hom.app U (m i)) :=
  FiniteTensorSections.tensorFamilyIso_section Y.sheaf e (op U) m

/-- Finite tensor interchange on the actual sections of scheme modules. -/
theorem pointwise_section (M N : Fin k → Y.Modules) (U : Y.Opens)
    (m : ∀ i, Γ(M i,U)) (n : ∀ i, Γ(N i,U)) :
    (FiniteTensor.tensorPointwiseIso M N).hom.app U
      (tensorSection Y.sheaf (FiniteTensor.tensorObj M) (FiniteTensor.tensorObj N) (op U)
        (finiteTensorSection Y.sheaf M (op U) m) (finiteTensorSection Y.sheaf N (op U) n)) =
      finiteTensorSection Y.sheaf (fun i => M i ⊗ N i) (op U)
        (fun i => tensorSection Y.sheaf (M i) (N i) (op U) (m i) (n i)) :=
  FiniteTensorSections.tensorPointwiseIso_section Y.sheaf M N (op U) m n

/-- Interchange followed by factorwise maps, evaluated on actual tensor sections. -/
theorem pointwise_family_section (M N P : Fin k → Y.Modules)
    (e : ∀ i, M i ⊗ N i ≅ P i) (U : Y.Opens)
    (m : ∀ i, Γ(M i,U)) (n : ∀ i, Γ(N i,U)) :
    (FiniteTensor.tensorPointwiseIso M N ≪≫ tensorFamilyIso e).hom.app U
      (tensorSection Y.sheaf (FiniteTensor.tensorObj M) (FiniteTensor.tensorObj N) (op U)
        (finiteTensorSection Y.sheaf M (op U) m) (finiteTensorSection Y.sheaf N (op U) n)) =
      finiteTensorSection Y.sheaf P (op U)
        (fun i => (e i).hom.app U (tensorSection Y.sheaf (M i) (N i) (op U) (m i) (n i))) := by
  simp only [Iso.trans_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pointwise_section, family_section]

/-- Collapsing factors with unit coordinates preserves the actual unit section. -/
theorem family_units_section (M : Fin k → Y.Modules)
    (e : ∀ i, M i ≅ 𝟙_ Y.Modules) (U : Y.Opens) (m : ∀ i, Γ(M i,U))
    (hm : ∀ i, (e i).hom.app U (m i) = (1 : Γ(Y,U))) :
    (tensorFamilyIso e ≪≫ FiniteTensor.tensorUnitsIso k).hom.app U
      (finiteTensorSection Y.sheaf M (op U) m) = (1 : Γ(Y,U)) := by
  simp only [Iso.trans_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [family_section]
  simp only [hm]
  exact tensorUnitsIso_section Y.sheaf k (op U)

end PaperVerification.Segre.SchemeFiniteTensorSections

section SegreActualProductChartFrames

/-!
# Actual local source and line frames on the fixed projective product

Every source basis vector is the pullback of an actual coordinate wedge in a
positive Euler kernel. The coefficient ring is the actual ring of sections of
the corresponding standard product chart. The line frame is obtained from
the actual local-fraction generator and extension of scalars along the actual
projection map; no abstract free module is substituted for a sheaf section
module.

-/

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Classical BigOperators TensorProduct ChangeOfRings

namespace PaperVerification.Segre.ActualProductChartFrames

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open FixedProductCohomology FixedProductProjections ProductKoszulVanishing
open ProductChartSections ProductCoordinatePullback ActualProductKoszulTerms
open EulerSheaf EulerSections EulerCriticalChart EulerCriticalFrame EulerCriticalFunctional

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]

abbrev chart (p : ∀ i,I i) : (product K I).scheme.Opens :=
  finiteChart (fun i => projectiveScheme K (I i)) p

abbrev factorKernel (i : Fin (k+1)) : (product K I).scheme.Modules :=
  (Scheme.Modules.pullback (factorProjection K I i)).obj (eulerKernel (I := I i) (K := K) 2)

abbrev FrameIndex (p : ∀ i,I i) := Σ i,UnitPivotKernel.OffPivot (p i)

theorem chart_affine (p : ∀ i,I i) : IsAffineOpen (chart K I p) :=
  finiteChart_affine (fun i => projectiveScheme K (I i)) p

theorem chart_cover : (⨆ p : ∀ i,I i,chart K I p)=⊤ :=
  finiteChart_cover (fun i => projectiveScheme K (I i))

/-- The genuine coordinate-wedge basis after actual affine scalar extension. -/
def factorSourceBasis (p : ∀ i,I i) (i : Fin (k+1)) :
    Module.Basis (UnitPivotKernel.OffPivot (p i))
      Γ((product K I).scheme,chart K I p) Γ(factorKernel K I i,chart K I p) := by
  let f : (product K I).scheme ⟶ Proj (MvPolynomial.homogeneousSubmodule (I i) K) :=
    factorProjection K I i
  let U := ProjectiveCech.coordinateOpen (K := K) (p i)
  let V := chart K I p
  let h : V≤f ⁻¹ᵁ U :=
    finiteChart_le_preimage (fun i => projectiveScheme K (I i)) p i
  letI : Algebra Γ(Proj (MvPolynomial.homogeneousSubmodule (I i) K), U) Γ((product K I).scheme, V) :=
    (f.appLE U V h).hom.toAlgebra
  letI := positiveEulerKernel_quasicoherent K (I i)
  exact ((EulerCriticalFrame.chartBasis (p i) U le_rfl).baseChange
    Γ((product K I).scheme,V)).map
      (AffinePullbackSections.pullbackSectionsLEEquiv _
        ((projectiveScheme K (I i)).affine (p i)) f (chart_affine K I p) h)

/-- The basis retains the literal pulled-back coordinate-wedge sections. -/
theorem factorSourceBasis_apply (p : ∀ i,I i) (i : Fin (k+1))
    (a : UnitPivotKernel.OffPivot (p i)) :
    factorSourceBasis K I p i a=
      (factorProjection K I i).pullbackSectionsLE
        (eulerKernel (I := I i) (K := K) 2)
        (ProjectiveCech.coordinateOpen (K := K) (p i)) (chart K I p)
        (finiteChart_le_preimage (fun i => projectiveScheme K (I i)) p i)
        (coordinateWedge (p i) a.val (ProjectiveCech.coordinateOpen (K := K) (p i))) := by
  letI := positiveEulerKernel_quasicoherent K (I i)
  dsimp only [factorSourceBasis]
  rw [Module.Basis.map_apply,Module.Basis.baseChange_apply,
    EulerCriticalFrame.chartBasis_apply]
  exact AffinePullbackSections.pullbackSectionsLEEquiv_one_tmul _
    ((projectiveScheme K (I i)).affine (p i)) (factorProjection K I i)
    (chart_affine K I p)
    (finiteChart_le_preimage (fun i => projectiveScheme K (I i)) p i) _

/-- The complete source frame, with one coordinate for every free coordinate
in every factor and the actual product-section comparison. -/
def sourceFrame (p : ∀ i,I i) :
    (FrameIndex I p → Γ((product K I).scheme,chart K I p)) ≃ₗ[Γ((product K I).scheme,chart K I p)]
      Γ(source K I,chart K I p) :=
  (LinearEquiv.piCurry Γ((product K I).scheme,chart K I p)
    (fun i (_ : UnitPivotKernel.OffPivot (p i)) =>
      Γ((product K I).scheme,chart K I p))).trans
    ((LinearEquiv.piCongrRight (fun i => (factorSourceBasis K I p i).equivFun.symm)).trans
      (SchemeProductSections.productSectionsEquiv (factorKernel K I) (chart K I p)).symm)

/-- Each actual projection of the source frame is exactly the corresponding
factor frame, before applying any critical functional. -/
theorem sourceFrame_component (p : ∀ i,I i)
    (v : FrameIndex I p → Γ((product K I).scheme,chart K I p)) (i : Fin (k+1)) :
    (Pi.π (factorKernel K I) i).app (chart K I p) (sourceFrame K I p v)=
      (factorSourceBasis K I p i).equivFun.symm (fun a => v ⟨i,a⟩) := by
  rw [← SchemeProductSections.productSectionsEquiv_apply]
  simp only [sourceFrame,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
    LinearEquiv.piCongrRight_apply,LinearEquiv.piCurry_apply,Sigma.curry]
  erw [LinearEquiv.apply_symm_apply]
  rfl

theorem sourceFrame_single_self (p : ∀ i,I i) (i : Fin (k+1))
    (a : UnitPivotKernel.OffPivot (p i)) :
    (Pi.π (factorKernel K I) i).app (chart K I p)
      (sourceFrame K I p (Pi.single ⟨i,a⟩ 1))=factorSourceBasis K I p i a := by
  rw [sourceFrame_component]
  apply (factorSourceBasis K I p i).equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext b
  by_cases hab : a=b
  · subst b
    simp [Pi.single_apply,Module.Basis.equivFun_self]
  · have hne : (⟨i,b⟩ : FrameIndex I p)≠⟨i,a⟩ := by
      intro h
      have he : b=a := by cases h; rfl
      exact hab he.symm
    simp [Pi.single_apply,Module.Basis.equivFun_self,hab,hne,Ne.symm hne]

theorem sourceFrame_single_other (p : ∀ i,I i) (q : FrameIndex I p)
    (i : Fin (k+1)) (hi : i≠q.1) :
    (Pi.π (factorKernel K I) i).app (chart K I p)
      (sourceFrame K I p (Pi.single q 1))=0 := by
  rw [sourceFrame_component]
  have hv : (fun a : UnitPivotKernel.OffPivot (p i) =>
      (Pi.single q (1 : Γ((product K I).scheme,chart K I p)) :
        FrameIndex I p → Γ((product K I).scheme,chart K I p)) ⟨i,a⟩)=0 := by
    funext a
    have hne : (⟨i,a⟩ : FrameIndex I p)≠q := fun h => hi (congrArg Sigma.fst h)
    simp [Pi.single_apply,hne,Ne.symm hne]
  rw [hv,map_zero]

/-- The actual local trivialization of every pulled-back integer twist. -/
def factorLineFrame (p : ∀ i,I i) (i : Fin (k+1)) (t : ℤ) :
    Γ((product K I).scheme,chart K I p) ≃ₗ[Γ((product K I).scheme,chart K I p)]
      Γ((Scheme.Modules.pullback (factorProjection K I i)).obj
        (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t),chart K I p) := by
  let f : (product K I).scheme ⟶ Proj (MvPolynomial.homogeneousSubmodule (I i) K) :=
    factorProjection K I i
  let U := ProjectiveCech.coordinateOpen (K := K) (p i)
  let V := chart K I p
  let R := Γ(Proj (MvPolynomial.homogeneousSubmodule (I i) K), U)
  let S := Γ((product K I).scheme,V)
  let h : V≤f ⁻¹ᵁ U :=
    finiteChart_le_preimage (fun i => projectiveScheme K (I i)) p i
  letI : Algebra R S := (f.appLE U V h).hom.toAlgebra
  letI : (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t).IsQuasicoherent :=
    Proj.isQuasicoherent_twistingSheaf _ _
  exact (TensorProduct.AlgebraTensorModule.rid R S S).symm.trans
    (((EulerCriticalChart.chartTrivialization (p i) U le_rfl t).baseChange R S).trans
      (AffinePullbackSections.pullbackSectionsLEEquiv
        (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t)
        ((projectiveScheme K (I i)).affine (p i)) f (chart_affine K I p) h))

/-- One is sent to the pulled-back canonical local-fraction generator. -/
theorem factorLineFrame_one (p : ∀ i,I i) (i : Fin (k+1)) (t : ℤ) :
    factorLineFrame K I p i t 1=
      (factorProjection K I i).pullbackSectionsLE
        (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t)
        (ProjectiveCech.coordinateOpen (K := K) (p i)) (chart K I p)
        (finiteChart_le_preimage (fun i => projectiveScheme K (I i)) p i)
        (EulerCriticalChart.chartTrivialization (p i)
          (ProjectiveCech.coordinateOpen (K := K) (p i)) le_rfl t 1) := by
  letI : (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t).IsQuasicoherent :=
    Proj.isQuasicoherent_twistingSheaf _ _
  dsimp only [factorLineFrame]
  rw [LinearEquiv.trans_apply,TensorProduct.AlgebraTensorModule.rid_symm_apply,
    LinearEquiv.trans_apply,LinearEquiv.baseChange_tmul]
  exact AffinePullbackSections.pullbackSectionsLEEquiv_one_tmul _
    ((projectiveScheme K (I i)).affine (p i)) (factorProjection K I i)
    (chart_affine K I p)
    (finiteChart_le_preimage (fun i => projectiveScheme K (I i)) p i) _

/-- The scalar coefficient of a pulled-back factor section is its actual
projection ring map, not an arbitrary coefficient-ring identification. -/
theorem factorLineFrame_pullback (p : ∀ i,I i) (i : Fin (k+1)) (t : ℤ)
    (r : Γ(Proj (MvPolynomial.homogeneousSubmodule (I i) K),
      ProjectiveCech.coordinateOpen (K := K) (p i))) :
    factorLineFrame K I p i t
      (factorRestriction (fun i => projectiveScheme K (I i)) p i r)=
      (factorProjection K I i).pullbackSectionsLE
        (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t)
        (ProjectiveCech.coordinateOpen (K := K) (p i)) (chart K I p)
        (finiteChart_le_preimage (fun i => projectiveScheme K (I i)) p i)
        (EulerCriticalChart.chartTrivialization (p i)
          (ProjectiveCech.coordinateOpen (K := K) (p i)) le_rfl t r) := by
  let e := EulerCriticalChart.chartTrivialization (p i)
    (ProjectiveCech.coordinateOpen (K := K) (p i)) le_rfl t
  have he : e r=r • e 1 := by rw [← _root_.map_smul]; simp
  change _=(factorProjection K I i).pullbackSectionsLE _ _ _ _ (e r)
  rw [he,map_smulₛₗ,← factorLineFrame_one,← _root_.map_smul]
  simp only [smul_eq_mul,mul_one,factorRestriction_apply]
  rfl

/-- In degree one, every coordinate section has precisely its expected
normalized coordinate coefficient in the pulled-back frame. -/
theorem factorLineFrame_coordinate (p : ∀ i,I i) (i : Fin (k+1)) (a : I i) :
    (factorLineFrame K I p i 1).symm
      ((GlobalCriticalMap.pullbackCoordinateHom (factorProjection K I i) a).app
        (chart K I p) (1 : Γ((product K I).scheme, chart K I p)))=
      factorRestriction (fun i => projectiveScheme K (I i)) p i
        (EulerCriticalChart.normalizedCoordinate (p i)
          (ProjectiveCech.coordinateOpen (K := K) (p i)) le_rfl a) := by
  apply (factorLineFrame K I p i 1).injective
  rw [LinearEquiv.apply_symm_apply,GlobalCriticalMap.pullbackCoordinateHom_app_one,
    factorLineFrame_pullback]
  rw [EulerCriticalChart.normalizedCoordinate,LinearEquiv.apply_symm_apply]

section FiniteLineFrames

variable {Y : Scheme.{u}} {U : Y.Opens}

/-- The full finite tensor is quasicoherent, including its terminal unit. -/
theorem finiteTensor_quasicoherent : {l : ℕ} → (M : Fin l → Y.Modules) →
    (∀ i,(M i).IsQuasicoherent) → (FiniteTensor.tensorObj M).IsQuasicoherent
  | 0,_,_ => by change (𝟙_ Y.Modules).IsQuasicoherent; infer_instance
  | l+1,M,hM => by
      letI := hM 0
      letI := finiteTensor_quasicoherent (fun i : Fin l => M i.succ) (fun i => hM i.succ)
      change (M 0 ⊗ FiniteTensor.tensorObj (fun i : Fin l => M i.succ)).IsQuasicoherent
      infer_instance

/-- A family of actual rank-one section frames gives the canonical frame of
their complete finite tensor over an affine open. -/
def finiteTensorFrame (hU : IsAffineOpen U) : {l : ℕ} → (M : Fin l → Y.Modules) →
    (hM : ∀ i,(M i).IsQuasicoherent) →
    (∀ i,Γ(Y,U) ≃ₗ[Γ(Y,U)] Γ(M i,U)) →
      Γ(Y,U) ≃ₗ[Γ(Y,U)] Γ(FiniteTensor.tensorObj M,U)
  | 0,_,_,_ => LinearEquiv.refl _ _
  | l+1,M,hM,e => by
      letI := hM 0
      letI := finiteTensor_quasicoherent (fun i : Fin l => M i.succ) (fun i => hM i.succ)
      exact (TensorProduct.lid Γ(Y,U) Γ(Y,U)).symm.trans
        ((TensorProduct.congr (e 0)
          (finiteTensorFrame hU (fun i : Fin l => M i.succ)
            (fun i => hM i.succ) (fun i => e i.succ))).trans
          (AffineTensorSections.affineTensorSectionsIso hU (M 0)
            (FiniteTensor.tensorObj (fun i : Fin l => M i.succ))).toLinearEquiv)

/-- The frame generator is exactly the full canonical tensor of its actual
factor generators, with the terminal unit retained. -/
theorem finiteTensorFrame_one (hU : IsAffineOpen U) {l : ℕ}
    (M : Fin l → Y.Modules) (hM : ∀ i,(M i).IsQuasicoherent)
    (e : ∀ i,Γ(Y,U) ≃ₗ[Γ(Y,U)] Γ(M i,U)) :
    finiteTensorFrame hU M hM e 1=
      FiniteTensorSections.finiteTensorSection Y.sheaf M (op U) (fun i => e i 1) := by
  induction l with
  | zero => rfl
  | succ l ih =>
      letI := hM 0
      letI := finiteTensor_quasicoherent (fun i : Fin l => M i.succ) (fun i => hM i.succ)
      simp only [finiteTensorFrame,LinearEquiv.trans_apply,TensorProduct.lid_symm_apply,
        TensorProduct.congr_tmul,ih,FiniteTensorSections.finiteTensorSection]
      exact AffineTensorProductMap.affineTensorSectionsIso_hom_tmul (M 0)
        (FiniteTensor.tensorObj (fun i : Fin l => M i.succ)) U hU _ _

end FiniteLineFrames

/-- The actual local frame of O(t,…,t), oriented from sections to scalars as
required by the image-membership and coefficient-Koszul comparisons. -/
def lineFrame (p : ∀ i,I i) (t : ℤ) :
    Γ(line K I t,chart K I p) ≃ₗ[Γ((product K I).scheme,chart K I p)]
      Γ((product K I).scheme,chart K I p) := by
  letI : ∀ i, (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t).IsQuasicoherent :=
    fun i => Proj.isQuasicoherent_twistingSheaf _ _
  exact (finiteTensorFrame (chart_affine K I p)
    (fun i => (Scheme.Modules.pullback (factorProjection K I i)).obj
      (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t))
    (fun _ => inferInstance) (fun i => factorLineFrame K I p i t)).symm

/-- The product line frame has precisely the actual canonical product
generator used by the full line-addition isomorphisms. -/
theorem lineFrame_symm_one (p : ∀ i,I i) (t : ℤ) :
    (lineFrame K I p t).symm 1=
      FiniteTensorSections.finiteTensorSection (product K I).scheme.sheaf
        (fun i => (Scheme.Modules.pullback (factorProjection K I i)).obj
          (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t))
        (op (chart K I p)) (fun i =>
          (factorProjection K I i).pullbackSectionsLE
            (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) t)
            (ProjectiveCech.coordinateOpen (K := K) (p i)) (chart K I p)
            (finiteChart_le_preimage (fun i => projectiveScheme K (I i)) p i)
            (EulerCriticalChart.chartTrivialization (p i)
              (ProjectiveCech.coordinateOpen (K := K) (p i)) le_rfl t 1)) := by
  rw [lineFrame,LinearEquiv.symm_symm]
  erw [finiteTensorFrame_one]
  simp only [factorLineFrame_one]

end PaperVerification.Segre.ActualProductChartFrames

end SegreActualProductChartFrames


section SegreProductWeightedKoszul

/-!
# The literal coefficient multiplications in the product Koszul complex

The coefficient family is O(d(1-r),…,d(1-r)). Its multiplication maps
are constructed from the actual tensor-product multiplication of twists.
In degree zero the coefficient map is the canonical unit action; this
keeps the augmentation equal to the original critical functional under
the canonical degree-zero and degree-one identifications.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.ProductWeightedKoszul

open CategoryTheory MonoidalCategory AlgebraicGeometry
open ActualProductKoszulTerms

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k + 1) → Type u)
variable [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- The actual sequence of coefficient lines in every exterior degree. -/
abbrev coefficientFamily (d : ℤ) (r : ℕ) : (X).Modules :=
  line K I (d * (1 - (r : ℤ)))

/-- Multiplication by the coefficient line, including the original unit
action at the augmentation. No map is supplied as a premise. -/
def coefficientMultiplication (d : ℤ) :
    (r : ℕ) → line K I d ⊗ coefficientFamily K I d (r + 1) ⟶
      coefficientFamily K I d r
  | 0 => by
      simpa only [coefficientFamily, Nat.zero_add, Nat.cast_zero, Nat.cast_one,
        sub_zero, sub_self, mul_zero, mul_one] using
        ((𝟙 (line K I d) ⊗ₘ (lineZeroIso K I).hom) ≫ (ρ_ (line K I d)).hom)
  | r + 1 =>
      (lineAddIso K I d (d * (1 - ((r + 2 : ℕ) : ℤ)))).hom ≫
        (eqToIso (congrArg (line K I) (by push_cast; ring :
          d + d * (1 - ((r + 2 : ℕ) : ℤ)) =
            d * (1 - ((r + 1 : ℕ) : ℤ))))).hom

/-- The weighted construction's terms are literally the full geometric
terms whose cohomology was computed. -/
def weightedTermIso (d : ℤ) (r : ℕ) :
    WeightedSheafKoszul.term (X).sheaf (source K I) (coefficientFamily K I d) r ≅
      ActualProductKoszulTerms.term K I d r :=
  Iso.refl _

/-- The actual differential associated to any actual coefficient
functional, in particular either singular-vector critical functional. -/
def differential (d : ℤ) (φ : source K I ⟶ line K I d) (r : ℕ) :
    ActualProductKoszulTerms.term K I d (r + 1) ⟶
      ActualProductKoszulTerms.term K I d r :=
  WeightedSheafKoszul.differential (X).sheaf (source K I) (line K I d)
    (coefficientFamily K I d) φ (coefficientMultiplication K I d) r

/-- The exact coefficient commutation condition, for application of the
proved weighted square-zero theorem. It is stated here explicitly until
the actual chart line frames discharge it. -/
abbrev CoefficientsCommute (d : ℤ) : Prop :=
  WeightedSheafKoszul.CoefficientsCommute.{u} (X).sheaf (line K I d)
    (coefficientFamily K I d) (coefficientMultiplication K I d)

theorem differential_squared (d : ℤ) (φ : source K I ⟶ line K I d)
    (hcomm : CoefficientsCommute K I d) (r : ℕ) :
    differential K I d φ (r + 1) ≫ differential K I d φ r = 0 :=
  WeightedSheafKoszul.differential_squared (X).sheaf (source K I) (line K I d)
    (coefficientFamily K I d) φ (coefficientMultiplication K I d) hcomm r

end PaperVerification.Segre.ProductWeightedKoszul

end SegreProductWeightedKoszul

section SegreProductLineMultiplication

/-!
# Actual multiplication in the product line frames

The generator of every integer twist is the literal local fraction. Pullback,
finite tensor interchange, and twisting-sheaf multiplication carry these
generators to the generator of the sum twist. Bilinearity then determines the
entire multiplication map in the actual affine chart frames.

-/


attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

namespace PaperVerification.Segre.CategoryHomTransport
open CategoryTheory
universe u v
/-- Transporting a morphism type agrees with the canonical equality morphisms. -/
theorem cast_comp_eqToHom {C : Type u} [Category.{v} C] {A A' B B' : C}
    (hA : A = A') (hB : B = B') (h : (A' ⟶ B') = (A ⟶ B)) (f : A' ⟶ B') :
    cast h f ≫ eqToHom hB = eqToHom hA ≫ f := by
  subst A'
  subst B'
  simp
end PaperVerification.Segre.CategoryHomTransport


namespace PaperVerification.Segre.ProductLineMultiplication

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open SheafCoefficientContraction SheafCoefficientComplex FiniteTensorSections
open PullbackTensorSections FixedProductProjections ProductKoszulVanishing
open ActualProductKoszulTerms ActualProductChartFrames ProductWeightedKoszul
open EulerCriticalChart TwistedExteriorEuler

universe u

section Factor

variable {J K : Type u} [Fintype J] [DecidableEq J] [Field K]
local notation "𝒜" => MvPolynomial.homogeneousSubmodule J K
local notation "Y" => Proj (MvPolynomial.homogeneousSubmodule J K)

/-- Multiplication of the canonical generators works for all integer twists,
including negative twists and degree zero. -/
theorem factor_generators_multiply (p : J) (U : (Y).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) p) (a b : ℤ) :
    (twistingTensorIso a b).hom.app U
      (tensorSection (Y).sheaf (Proj.twistingSheaf 𝒜 a) (Proj.twistingSheaf 𝒜 b)
        (op U) (chartTrivialization p U hU a 1) (chartTrivialization p U hU b 1)) =
      chartTrivialization p U hU (a+b) 1 := by
  letI : LinearOrder J := LinearOrder.lift' (Fintype.equivFin J) (Fintype.equivFin J).injective
  rw [EulerExteriorTwistMaps.twistingTensorIso_localTensor]
  simpa only [mul_one] using
    EulerContractionChart.chartTrivialization_mul_all p U hU a b
      (1 : Γ(Y, U)) 1

/-- The degree-zero local fraction is precisely the image of the unit section
under the genuine zero-twist isomorphism. -/
theorem factor_zero_generator (p : J) (U : (Y).Opens)
    (hU : U ≤ ProjectiveCech.coordinateOpen (K := K) p) :
    chartTrivialization p U hU 0 1 =
      Scheme.Modules.Hom.app («X» := Y) (Proj.unitIsoTwistingSheafZero 𝒜).hom U (1 : Γ(Y,U)) := by
  letI : LinearOrder J := LinearOrder.lift' (Fintype.equivFin J) (Fintype.equivFin J).injective
  erw [EulerExteriorTwist.chartTrivialization_zero,
    Proj.unitIsoTwistingSheafZero_hom_app_apply]

end Factor

variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- The actual product-line multiplication takes the two actual product
generators to the actual generator of the sum twist. -/
theorem lineAddIso_generators (p : ∀ i, I i) (a b : ℤ) :
    (lineAddIso K I a b).hom.app (chart K I p)
      (tensorSection (X).sheaf (line K I a) (line K I b) (op (chart K I p))
        ((lineFrame K I p a).symm 1) ((lineFrame K I p b).symm 1)) =
      (lineFrame K I p (a+b)).symm 1 := by
  letI : ∀ i, (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) a).IsQuasicoherent :=
    fun i => Proj.isQuasicoherent_twistingSheaf _ _
  letI : ∀ i, (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) b).IsQuasicoherent :=
    fun i => Proj.isQuasicoherent_twistingSheaf _ _
  rw [lineFrame_symm_one, lineFrame_symm_one, lineFrame_symm_one]
  refine (SchemeFiniteTensorSections.pointwise_family_section
    (fun i => (Scheme.Modules.pullback (factorProjection K I i)).obj
      (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) a))
    (fun i => (Scheme.Modules.pullback (factorProjection K I i)).obj
      (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) b))
    (fun i => (Scheme.Modules.pullback (factorProjection K I i)).obj
      (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) (a+b)))
    (fun i => (pullbackTensorRightIso (factorProjection K I i)
      (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) a)
      (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) b)).symm ≪≫
      (Scheme.Modules.pullback (factorProjection K I i)).mapIso
        (twistingTensorIso (I := I i) (K := K) a b))
    (chart K I p) _ _).trans ?_
  apply congrArg (finiteTensorSection (X).sheaf
    (fun i => (Scheme.Modules.pullback (factorProjection K I i)).obj
      (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) (a+b)))
    (op (chart K I p)))
  funext i
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw (config := { transparency := .all }) [pullbackTensorRightIso, pullbackTensor_inv_sectionLE,
    Scheme.Hom.pullbackSectionsLE_naturality, factor_generators_multiply]

/-- The actual zero-line comparison takes the canonical product generator
to the unit section of the genuine structure sheaf. -/
theorem lineZeroIso_generator (p : ∀ i, I i) :
    (lineZeroIso K I).hom.app (chart K I p) ((lineFrame K I p 0).symm 1) = (1 : Γ(X,chart K I p)) := by
  rw [lineFrame_symm_one]
  have hfactor : ∀ i : Fin (k+1),
      (((Scheme.Modules.pullback (factorProjection K I i)).mapIso
          (Proj.unitIsoTwistingSheafZero
            (MvPolynomial.homogeneousSubmodule (I i) K)).symm ≪≫
        pullbackObjUnitIso (factorProjection K I i)).hom).app (chart K I p)
        ((factorProjection K I i).pullbackSectionsLE
          (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) 0)
          (ProjectiveCech.coordinateOpen (K := K) (p i)) (chart K I p)
          (ProductCoordinatePullback.finiteChart_le_preimage
            (fun i => projectiveScheme K (I i)) p i)
          (chartTrivialization (p i) (ProjectiveCech.coordinateOpen (K := K) (p i))
            le_rfl 0 1)) = (1 : Γ(X,chart K I p)) := by
    intro i
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    rw [Scheme.Hom.pullbackSectionsLE_naturality, factor_zero_generator]
    have hu :
        (Proj.unitIsoTwistingSheafZero (MvPolynomial.homogeneousSubmodule (I i) K)).inv.val.app
          (op (ProjectiveCech.coordinateOpen (K := K) (p i)))
          ((Proj.unitIsoTwistingSheafZero (MvPolynomial.homogeneousSubmodule (I i) K)).hom.val.app
            (op (ProjectiveCech.coordinateOpen (K := K) (p i)))
            (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (I i) K),
              ProjectiveCech.coordinateOpen (K := K) (p i)))) =
          (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (I i) K),
            ProjectiveCech.coordinateOpen (K := K) (p i))) :=
      congrArg
        (fun f : (𝟙_ (Proj (MvPolynomial.homogeneousSubmodule (I i) K)).Modules) ⟶
            (𝟙_ (Proj (MvPolynomial.homogeneousSubmodule (I i) K)).Modules) =>
          f.val.app (op (ProjectiveCech.coordinateOpen (K := K) (p i)))
            (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (I i) K),
              ProjectiveCech.coordinateOpen (K := K) (p i))))
        (Proj.unitIsoTwistingSheafZero
          (MvPolynomial.homogeneousSubmodule (I i) K)).hom_inv_id
    let f := factorProjection K I i
    let U := ProjectiveCech.coordinateOpen (K := K) (p i)
    let V := chart K I p
    let h : V ≤ f ⁻¹ᵁ U := ProductCoordinatePullback.finiteChart_le_preimage
      (fun i => projectiveScheme K (I i)) p i
    refine (congrArg (fun s : Γ(Proj (MvPolynomial.homogeneousSubmodule (I i) K), U) =>
      (pullbackObjUnitIso f).hom.app V
        (f.pullbackSectionsLE (𝟙_ (Proj (MvPolynomial.homogeneousSubmodule (I i) K)).Modules)
          U V h s)) hu).trans ?_
    exact (pullbackUnit_sectionLE f U V h
      (1 : Γ(Proj (MvPolynomial.homogeneousSubmodule (I i) K), U))).trans
        (map_one (f.appLE U V h).hom)
  exact SchemeFiniteTensorSections.family_units_section
    (fun i => (Scheme.Modules.pullback (factorProjection K I i)).obj
      (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) 0))
    (fun i => (Scheme.Modules.pullback (factorProjection K I i)).mapIso
      (Proj.unitIsoTwistingSheafZero (MvPolynomial.homogeneousSubmodule (I i) K)).symm ≪≫
      pullbackObjUnitIso (factorProjection K I i)) (chart K I p) _ hfactor

/-- In the actual chart frames, the entire line multiplication is ordinary
multiplication of regular functions. The premise is not just checked on a
finite set of points or on a selected family of sections. -/
theorem lineAddIso_frame (p : ∀ i, I i) (a b : ℤ)
    (x : Γ(line K I a, chart K I p)) (y : Γ(line K I b, chart K I p)) :
    lineFrame K I p (a+b)
      (WeightedSheafKoszul.multiplicationAt (X).sheaf (lineAddIso K I a b).hom
        (op (chart K I p)) x y) =
      lineFrame K I p a x * lineFrame K I p b y := by
  let B : Γ(line K I a, chart K I p) →ₗ[Γ(X, chart K I p)]
      Γ(line K I b, chart K I p) →ₗ[Γ(X, chart K I p)]
        Γ(line K I (a+b), chart K I p) :=
    WeightedSheafKoszul.multiplicationAt (X).sheaf (lineAddIso K I a b).hom
      (op (chart K I p))
  change lineFrame K I p (a+b) (B x y) = _
  have hx : x = lineFrame K I p a x • (lineFrame K I p a).symm 1 := by
    rw [← _root_.map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  have hy : y = lineFrame K I p b y • (lineFrame K I p b).symm 1 := by
    rw [← _root_.map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  conv_lhs => rw [hx, hy]
  rw [LinearMap.map_smul₂, LinearMap.map_smul, _root_.map_smul, _root_.map_smul]
  change _ • _ • lineFrame K I p (a+b)
    ((lineAddIso K I a b).hom.app (chart K I p)
      (tensorSection (X).sheaf (line K I a) (line K I b) (op (chart K I p))
        ((lineFrame K I p a).symm 1) ((lineFrame K I p b).symm 1))) = _
  rw [lineAddIso_generators, LinearEquiv.apply_symm_apply]
  simp only [smul_eq_mul, mul_one]

/-- The scalar coordinate of the zero twist is exactly the actual unit
comparison used at the augmentation. -/
theorem lineZeroIso_frame (p : ∀ i, I i) (x : Γ(line K I 0, chart K I p)) :
    (lineZeroIso K I).hom.app (chart K I p) x = lineFrame K I p 0 x := by
  have hx : x = lineFrame K I p 0 x • (lineFrame K I p 0).symm 1 := by
    rw [← _root_.map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  conv_lhs => rw [hx]
  rw [Scheme.Modules.Hom.app_smul, lineZeroIso_generator]
  change lineFrame K I p 0 x * 1 = lineFrame K I p 0 x
  exact mul_one _

/-- Transport between equal integer degrees preserves the actual line
coordinate. This accounts explicitly for the degree identities in the
weighted coefficient sequence. -/
theorem lineFrame_cast (p : ∀ i, I i) {a b : ℤ} (h : a=b)
    (x : Γ(line K I a, chart K I p)) :
    lineFrame K I p b ((eqToIso (congrArg (line K I) h)).hom.app (chart K I p) x) =
      lineFrame K I p a x := by
  subst b
  rfl

/-- The augmentation coefficient map retains both canonical degree transports. -/
theorem coefficientMultiplication_zero_transport (d : ℤ) :
    coefficientMultiplication K I d 0 ≫
      (eqToIso (congrArg (line K I) (by simp : d * (1 - (0 : ℤ)) = d))).hom =
    (𝟙 (line K I d) ⊗ₘ
      (eqToIso (congrArg (line K I)
        (by norm_num : d * (1 - ((0 + 1 : ℕ) : ℤ)) = 0))).hom) ≫
      ((𝟙 (line K I d) ⊗ₘ (lineZeroIso K I).hom) ≫ (ρ_ (line K I d)).hom) := by
  simp [coefficientMultiplication, coefficientFamily]
  have hA : line K I d ⊗ line K I (d * (1 - ((0 + 1 : ℕ) : ℤ))) =
      line K I d ⊗ line K I 0 := by congr 2; norm_num
  have hB : line K I (d * (1 - (0 : ℤ))) = line K I d := by congr 1; simp
  exact CategoryHomTransport.cast_comp_eqToHom hA hB
    (congrArg₂ (fun A B : (X).Modules => A ⟶ B) hA.symm hB.symm)
    ((line K I d ◁ (lineZeroIso K I).hom) ≫ (ρ_ (line K I d)).hom)

set_option maxHeartbeats 2000000 in
/-- Every coefficient map of the full weighted complex has the intended
multiplication formula, including degree zero. -/
theorem coefficientMultiplication_frame (p : ∀ i, I i) (d : ℤ) (r : ℕ)
    (x : Γ(line K I d, chart K I p))
    (y : Γ(coefficientFamily K I d (r+1), chart K I p)) :
    lineFrame K I p (d * (1-(r : ℤ)))
      (WeightedSheafKoszul.multiplicationAt (X).sheaf (coefficientMultiplication K I d r)
        (op (chart K I p)) x y) =
      lineFrame K I p d x * lineFrame K I p (d * (1-((r+1 : ℕ) : ℤ))) y := by
  cases r with
  | zero =>
      have hd0 : d * (1 - ((0 + 1 : ℕ) : ℤ)) = 0 := by norm_num
      have hd1 : d * (1 - (0 : ℤ)) = d := by simp
      have h := congrArg
        (fun f : line K I d ⊗ coefficientFamily K I d (0+1) ⟶ line K I d =>
          f.app (chart K I p)
            (tensorSection (X).sheaf (line K I d) (coefficientFamily K I d (0+1))
              (op (chart K I p)) x y)) (coefficientMultiplication_zero_transport K I d)
      simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
      erw [tensorSection_map (X).sheaf, tensorSection_map (X).sheaf,
        tensorSection_rightUnitor (X).sheaf] at h
      change _ = (show Γ(X, chart K I p) from
        (lineZeroIso K I).hom.app (chart K I p)
          ((eqToIso (congrArg (line K I) hd0)).hom.app (chart K I p) y)) • x at h
      rw [lineZeroIso_frame K I p] at h
      have h' := congrArg (lineFrame K I p d) h
      have hl := lineFrame_cast K I p hd1
        (WeightedSheafKoszul.multiplicationAt (X).sheaf (coefficientMultiplication K I d 0)
          (op (chart K I p)) x y)
      have hr := lineFrame_cast K I p hd0 y
      calc
        _ = _ := hl.symm
        _ = _ := h'
        _ = _ := by
          rw [_root_.map_smul, hr]
          exact mul_comm _ _
  | succ r =>
      have hd : d + d * (1 - ((r + 2 : ℕ) : ℤ)) = d * (1 - ((r + 1 : ℕ) : ℤ)) := by
        push_cast
        ring
      change lineFrame K I p (d * (1 - ((r + 1 : ℕ) : ℤ)))
        ((eqToIso (congrArg (line K I) hd)).hom.app
          (chart K I p)
          ((lineAddIso K I d (d * (1 - ((r + 2 : ℕ) : ℤ)))).hom.app (chart K I p)
            (tensorSection (X).sheaf (line K I d) _ (op (chart K I p)) x y))) = _
      rw [lineFrame_cast K I p hd]
      exact lineAddIso_frame K I p d _ x y

end PaperVerification.Segre.ProductLineMultiplication

end SegreProductLineMultiplication

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
