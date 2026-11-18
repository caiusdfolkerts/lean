module
public import SegreVerified.Stage028.ExternalSections
public import SegreVerified.Stage025.ProjectiveSections
public import SegreVerified.Stage025.ProjectiveSpace
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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
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


section SegreGlobalCriticalSections

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage028.HomogeneousSections"
  out.flush

/-!
# Global critical sections and their literal chart equations

The named sections preserve the original proof stages and local scopes.
-/


namespace PaperVerification.Segre.GlobalSectionsScalarComparison

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

variable (K : Type u) [CommRing K] {Y : Scheme.{u}}
  [Y.Over (Spec (.of K))]

/-- Identity on global sections, between the direct global base action and
its presentation as the top component of the base-linear sections presheaf. -/
def identityEquiv (M : Y.Modules) :
    letI : Module K Γ(M, ⊤) :=
      Scheme.Modules.globalSectionsBaseModule (R := K) (X := Y) M
    Γ(M, ⊤) ≃ₗ[K] ExternalSections.sections K M ⊤ := by
  letI : Module K Γ(M, ⊤) :=
    Scheme.Modules.globalSectionsBaseModule (R := K) (X := Y) M
  refine
    { toFun := fun s => s
      invFun := fun s => s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := ?_ }
  intro c s
  change Scheme.Modules.baseRingToGlobalSections K Y c • s =
    (Y.baseRingToStructurePresheaf K).app (op ⊤) c • s
  exact (congrArg (fun r : Γ(Y, ⊤) => r • s)
    (ConcreteCategory.congr_hom (Scheme.baseRingToStructurePresheaf_app_top K Y) c)).symm

@[simp] theorem identityEquiv_apply (M : Y.Modules) (s : Γ(M, ⊤)) :
    identityEquiv K M s = s := rfl

@[simp] theorem identityEquiv_symm_apply (M : Y.Modules)
    (s : ExternalSections.sections K M ⊤) :
    (identityEquiv K M).symm s = s := rfl

end PaperVerification.Segre.GlobalSectionsScalarComparison

section SegreHomogeneousExternalSections

/-!
# Balanced Segre polynomials and the actual global sections

For every nonempty finite product of projective spaces, the entire balanced
degree-q polynomial space is canonically the global sections of the actual
external product of O(q). The comparison is the composition of the literal
factor maps p ↦ p/1, the finite tensor universal-property comparison, and the
canonical external-product map on sheaf sections.

The pure-tensor formula below records this particular map, rather than only
an equality of dimensions. Zero-dimensional projective factors are included.
-/


attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

namespace PaperVerification.Segre.HomogeneousExternalSections

open CategoryTheory AlgebraicGeometry
open FixedProductCohomology SymmetricRealization
open scoped TensorProduct

variable {K : Type} [Field K] {k : ℕ} (n : Fin (k + 1) → ℕ)

/-- The literal projective factors, with their coordinate affine covers. -/
def factors : Fin (k + 1) → CoveredScheme K :=
  fun i => ProductKoszulVanishing.projectiveScheme K (Fin (n i + 1))

/-- The actual degree-q twisting sheaf on a factor. -/
abbrev factorTwist (q : ℕ) (i : Fin (k + 1)) : (factors (K := K) n i).scheme.Modules :=
  Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K) q

/-- The actual factor twisting sheaf carries its proven quasicoherent structure. -/
instance factorTwist_quasicoherent (q : ℕ) (i : Fin (k + 1)) :
    (factorTwist (K := K) n q i).IsQuasicoherent := by
  change (Proj.twistingSheaf
    (MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K) (q : ℤ)).IsQuasicoherent
  infer_instance

/-- The actual external product O(q) ⊠ ... ⊠ O(q), on the same fixed scheme
product as the cohomology and critical-section constructions. -/
abbrev externalTwist (q : ℕ) :
    (CoveredScheme.finiteProduct (factors (K := K) n)).scheme.Modules :=
  CoveredScheme.finiteExternalTensor (factors (K := K) n) (factorTwist n q)

/-- The factor comparison is exactly polynomial divided by one. -/
def factorSectionEquiv (q : ℕ) (i : Fin (k + 1)) :
    MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K q ≃ₗ[K]
      ExternalSections.sections K (factorTwist (K := K) n q i) ⊤ :=
  (ProjectiveGlobalSections.homogeneousGlobalSectionsLinearEquiv
    (I := Fin (n i + 1)) (K := K) q).trans
      (GlobalSectionsScalarComparison.identityEquiv K _)

@[simp] theorem factorSectionEquiv_apply (q : ℕ) (i : Fin (k + 1))
    (p : MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K q) :
    factorSectionEquiv (K := K) n q i p =
      Proj.toTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K)
        rfl ⊤ p := rfl

/-- The canonical tensor-product map from factor polynomials onto every
global section of the actual external twisting sheaf. -/
def polynomialTensorSectionsEquiv (q : ℕ) :
    PolynomialTensor (K := K) (n := n) q ≃ₗ[K]
      ExternalSections.sections K (externalTwist (K := K) n q) ⊤ :=
  (PiTensorProduct.congr (factorSectionEquiv (K := K) n q)).trans
    ((FiniteTensorLinear.piEquiv
      (fun i => ExternalSections.sections K (factorTwist (K := K) n q i) ⊤)).trans
        (FiniteGlobalSections.finiteGlobalSectionsIso (factors (K := K) n)
          (factorTwist (K := K) n q) (fun _ => inferInstance)).toLinearEquiv)

/-- The actual entire balanced homogeneous space, including all its
polynomial structure, identifies canonically with the actual H⁰. -/
def balancedSectionsEquiv (q : ℕ) :
    HigherPieces.piece (K := K) (n := n) q ≃ₗ[K]
      ExternalSections.sections K (externalTwist (K := K) n q) ⊤ :=
  (polynomialTensorEquiv (K := K) (n := n) q).symm.trans
    (polynomialTensorSectionsEquiv (K := K) n q)

/-- An explicit formula on every pure tensor determines the comparison.
The right side uses the actual external-product map on actual sheaf sections. -/
theorem balancedSectionsEquiv_polynomialTensor (q : ℕ)
    (p : ∀ i : Fin (k + 1), MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K q) :
    balancedSectionsEquiv (K := K) n q
        (polynomialTensorEquiv (K := K) (n := n) q (PiTensorProduct.tprod K p)) =
      (FiniteGlobalSections.finiteGlobalSectionsIso (factors (K := K) n)
        (factorTwist (K := K) n q) (fun _ => inferInstance)).hom
          (FiniteTensorLinear.pure
            (fun i => ExternalSections.sections K (factorTwist (K := K) n q i) ⊤)
            (fun i => Proj.toTwistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K) rfl ⊤ (p i))) := by
  simp only [balancedSectionsEquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, polynomialTensorSectionsEquiv,
    PiTensorProduct.congr_tprod, factorSectionEquiv_apply,
    CategoryTheory.Iso.toLinearEquiv_apply]
  erw [FiniteTensorLinear.piEquiv_tprod]

/-- Every actual global section is reached; there is no selected subspace
of sections in the correspondence. -/
theorem balancedSections_surjective (q : ℕ) :
    Function.Surjective (balancedSectionsEquiv (K := K) n q) :=
  (balancedSectionsEquiv (K := K) n q).surjective

/-- The actual degree-one space used by the matrix formalization. -/
def degreeOneSectionsEquiv :
    Monomials.degreeOne (K := K) (n := n) ≃ₗ[K]
      ExternalSections.sections K (externalTwist (K := K) n 1) ⊤ :=
  (LinearEquiv.ofEq _ _ (by
    rw [Balanced.degreeOne_eq_balanced, HigherPieces.piece_eq_balanced])).trans
      (balancedSectionsEquiv (K := K) n 1)

/-- The actual degree-two space used by the multiplication matrix. -/
def degreeTwoSectionsEquiv :
    Monomials.degreeTwo (K := K) (n := n) ≃ₗ[K]
      ExternalSections.sections K (externalTwist (K := K) n 2) ⊤ :=
  (LinearEquiv.ofEq _ _ (by
    rw [Balanced.degreeTwo_eq_balanced, HigherPieces.piece_eq_balanced])).trans
      (balancedSectionsEquiv (K := K) n 2)

/-- The actual coordinate polynomial in one factor. -/
def coordinatePolynomial (i : Fin (k + 1)) (a : Fin (n i + 1)) :
    MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K 1 :=
  ⟨MvPolynomial.X a, MvPolynomial.isHomogeneous_X (R := K) a⟩

/-- Pure coordinate tensors produce precisely the Segre coordinate
polynomials used in every recovered multiplication matrix. -/
theorem polynomialTensorEquiv_coordinates (a : Staircase.Cell n) :
    (polynomialTensorEquiv (K := K) (n := n) 1
      (PiTensorProduct.tprod K (fun i => coordinatePolynomial (K := K) n i (a i)))).val =
        Monomials.cellPolynomial a := by
  rw [polynomialTensorEquiv_tprod, Monomials.cellPolynomial_eq_prod]
  simp only [coordinatePolynomial, MvPolynomial.rename_X]

/-- The degree-one comparison has the canonical coordinate-section formula. -/
theorem degreeOneSectionsEquiv_coordinate (a : Staircase.Cell n) :
    degreeOneSectionsEquiv (K := K) n
        ⟨Monomials.cellPolynomial a, Submodule.subset_span (Set.mem_range_self a)⟩ =
      (FiniteGlobalSections.finiteGlobalSectionsIso (factors (K := K) n)
        (factorTwist (K := K) n 1) (fun _ => inferInstance)).hom
          (FiniteTensorLinear.pure
            (fun i => ExternalSections.sections K (factorTwist (K := K) n 1 i) ⊤)
            (fun i => Proj.toTwistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K) rfl ⊤
              (coordinatePolynomial (K := K) n i (a i)))) := by
  have h := balancedSectionsEquiv_polynomialTensor (K := K) n 1
    (fun i => coordinatePolynomial (K := K) n i (a i))
  convert h using 1
  apply congrArg (balancedSectionsEquiv (K := K) n 1)
  apply Subtype.ext
  exact (polynomialTensorEquiv_coordinates (K := K) n a).symm

/-- The degree-two pure tensor uses literal products of factor coordinates. -/
def coordinatePairPolynomial (i : Fin (k + 1)) (a b : Fin (n i + 1)) :
    MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K 2 :=
  ⟨MvPolynomial.X a * MvPolynomial.X b,
    (MvPolynomial.isHomogeneous_X (R := K) a).mul (MvPolynomial.isHomogeneous_X (R := K) b)⟩

theorem polynomialTensorEquiv_coordinatePairs (a b : Staircase.Cell n) :
    (polynomialTensorEquiv (K := K) (n := n) 2
      (PiTensorProduct.tprod K
        (fun i => coordinatePairPolynomial (K := K) n i (a i) (b i)))).val =
      Monomials.cellPolynomial a * Monomials.cellPolynomial b := by
  rw [polynomialTensorEquiv_tprod, Monomials.cellPolynomial_eq_prod,
    Monomials.cellPolynomial_eq_prod]
  simp only [coordinatePairPolynomial, map_mul, MvPolynomial.rename_X]
  exact Finset.prod_mul_distrib

/-- The degree-two comparison sends actual products to the external product
of the actual factor coordinate products. This fixes the map on a spanning
family, so later image comparisons cannot select another isomorphism. -/
theorem degreeTwoSectionsEquiv_coordinateProduct (a b : Staircase.Cell n) :
    degreeTwoSectionsEquiv (K := K) n
        ⟨Monomials.cellPolynomial a * Monomials.cellPolynomial b,
          Submodule.subset_span ⟨(a, b), rfl⟩⟩ =
      (FiniteGlobalSections.finiteGlobalSectionsIso (factors (K := K) n)
        (factorTwist (K := K) n 2) (fun _ => inferInstance)).hom
          (FiniteTensorLinear.pure
            (fun i => ExternalSections.sections K (factorTwist (K := K) n 2 i) ⊤)
            (fun i => Proj.toTwistingSheaf
              (MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K) rfl ⊤
              (coordinatePairPolynomial (K := K) n i (a i) (b i)))) := by
  have h := balancedSectionsEquiv_polynomialTensor (K := K) n 2
    (fun i => coordinatePairPolynomial (K := K) n i (a i) (b i))
  convert h using 1
  apply congrArg (balancedSectionsEquiv (K := K) n 2)
  apply Subtype.ext
  exact (polynomialTensorEquiv_coordinatePairs (K := K) n a b).symm

/-- The factor section comparison respects literal twisting-sheaf
multiplication. The index on the target is the literal integer sum, so no
hidden identification of sheaves is needed in this formula. -/
theorem factorSection_mul (p q : ℕ) (i : Fin (k + 1))
    (x : MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K p)
    (y : MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K q) :
    Proj.twistingSheaf.mul
        (MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K) ⊤ (p : ℤ) (q : ℤ)
        (factorSectionEquiv (K := K) n p i x)
        (factorSectionEquiv (K := K) n q i y) =
      Proj.toTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K)
        (by omega : ((p + q : ℕ) : ℤ) = (p : ℤ) + (q : ℤ)) ⊤
        (factorHomogeneousMul (F := K) (n := n) p q i x y) := by
  simpa only [factorSectionEquiv_apply, factorHomogeneousMul,
    LinearMap.coe_mk, AddHom.coe_mk] using
    (Proj.mul_toTwistingSheaf
      (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K)
      (m := (p : ℤ)) (n := (q : ℤ)) rfl rfl ⊤ x y)

end PaperVerification.Segre.HomogeneousExternalSections

end SegreHomogeneousExternalSections

section SegreTraceGlobalSections

/-!
# The literal multiplication map on the actual global sections

The coefficient map is defined directly by finite sums of external products
of actual coordinate-product sections. It is then proved to equal the
ordinary Segre multiplication map under the canonical full H⁰ equivalence.
This is the map needed when restricting tensor-space covectors to the graph
of the last contraction. No rank-defined replacement for H⁰ is used.

-/


attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

namespace PaperVerification.Segre.TraceGlobalSections

open CategoryTheory AlgebraicGeometry
open Staircase Monomials Degeneration HomogeneousExternalSections
open scoped BigOperators TensorProduct

variable {K J : Type} [Field K] [Fintype J] [DecidableEq J]
  {k : ℕ} {n : Fin (k + 1) → ℕ}

/-- The actual external product of the coordinate-product sections. -/
def coordinatePairSection (a b : Cell n) :
    ExternalSections.sections K (externalTwist (K := K) n 2) ⊤ :=
  (FiniteGlobalSections.finiteGlobalSectionsIso (factors (K := K) n)
    (factorTwist (K := K) n 2) (fun _ => inferInstance)).hom
      (FiniteTensorLinear.pure
        (fun i => ExternalSections.sections K (factorTwist (K := K) n 2 i) ⊤)
        (fun i => Proj.toTwistingSheaf
          (MvPolynomial.homogeneousSubmodule (Fin (n i + 1)) K) rfl ⊤
          (coordinatePairPolynomial (K := K) n i (a i) (b i))))

/-- The polynomial-side product is the literal product in the full R₂. -/
def coordinateProduct (a b : Cell n) : degreeTwo (K := K) (n := n) :=
  ⟨cellPolynomial a * cellPolynomial b, Submodule.subset_span ⟨(a, b), rfl⟩⟩

@[simp] theorem degreeTwoSectionsEquiv_coordinateProduct (a b : Cell n) :
    degreeTwoSectionsEquiv (K := K) n (coordinateProduct a b) =
      coordinatePairSection (K := K) a b :=
  HomogeneousExternalSections.degreeTwoSectionsEquiv_coordinateProduct n a b

/-- A slice times a coordinate, formed directly from the actual factor
section products and their literal tensor coefficients. -/
def sliceProductSection (A : Matrix (Cell n) J K) (j : J) (v : Cell n) :
    ExternalSections.sections K (externalTwist (K := K) n 2) ⊤ :=
  ∑ u : Cell n, A u j • coordinatePairSection (K := K) u v

/-- The complete multiplication map on actual external-product sections. -/
def sliceMultiplicationSections (A : Matrix (Cell n) J K) :
    (J × Cell n → K) →ₗ[K]
      ExternalSections.sections K (externalTwist (K := K) n 2) ⊤ :=
  Fintype.linearCombination K (fun jv => sliceProductSection A jv.1 jv.2)

/-- Expansion of the actual polynomial multiplication in its genuine
spanning products. -/
theorem actualMultiplication_eq_sum (A : Matrix (Cell n) J K) (c : J × Cell n → K) :
    Trace.actualMultiplication A c =
      ∑ jv : J × Cell n, c jv •
        ∑ u : Cell n, A u jv.1 • coordinateProduct (K := K) u jv.2 := by
  apply Subtype.ext
  simp only [Trace.actualMultiplication, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_sum, Submodule.coe_smul,
    coordinateProduct, segreForm, Finset.sum_mul, smul_mul_assoc]

/-- Equality of the entire maps, not only their ranks or selected images. -/
theorem sliceMultiplicationSections_eq (A : Matrix (Cell n) J K) :
    sliceMultiplicationSections A =
      (degreeTwoSectionsEquiv (K := K) n).toLinearMap.comp
        (Trace.actualMultiplication A) := by
  apply LinearMap.ext
  intro c
  rw [LinearMap.comp_apply, actualMultiplication_eq_sum]
  simp only [sliceMultiplicationSections, Fintype.linearCombination_apply,
    sliceProductSection, map_sum, map_smul, LinearEquiv.coe_coe,
    LinearEquiv.coe_toLinearMap, degreeTwoSectionsEquiv_coordinateProduct]

/-- The whole coefficient kernel is preserved by the actual H⁰ comparison. -/
theorem kernel_sliceMultiplicationSections (A : Matrix (Cell n) J K) :
    LinearMap.ker (sliceMultiplicationSections A) =
      LinearMap.ker (Trace.actualMultiplication A) := by
  rw [sliceMultiplicationSections_eq]
  ext c
  change degreeTwoSectionsEquiv (K := K) n (Trace.actualMultiplication A c) = 0 ↔
    Trace.actualMultiplication A c = 0
  exact (degreeTwoSectionsEquiv (K := K) n).map_eq_zero_iff

end PaperVerification.Segre.TraceGlobalSections

end SegreTraceGlobalSections

section SegreFiniteGlobalSectionsFormula

/-!
# The canonical pure-section formula on the finite product

The global-section isomorphism is identified with the recursive actual
external product of sections. In each binary step this is the genuine
pullback of both sections followed by the sheaf tensor section map.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.FiniteGlobalSections

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open FixedProductCohomology ExternalSections
open scoped TensorProduct

universe u
variable {K : Type u} [Field K]

/-- The actual external product of two global sections, viewed on the
whole product by the literal equality of the top rectangle with top. -/
def binaryExternalSection (A B : CoveredScheme K)
    (M : A.scheme.Modules) (N : B.scheme.Modules)
    (m : sections K M ⊤) (n : sections K N ⊤) :
    sections K (CoveredScheme.externalTensor A B M N) ⊤ := by
  let p := pullback.fst A.toBase B.toBase
  let q := pullback.snd A.toBase B.toBase
  letI : (pullback A.toBase B.toBase).Over (Spec (.of K)) := ⟨p ≫ A.toBase⟩
  letI : p.IsOver (Spec (.of K)) := ⟨rfl⟩
  letI : q.IsOver (Spec (.of K)) :=
    ⟨(pullback.condition (f := A.toBase) (g := B.toBase)).symm⟩
  have htop : rectangle p q ⊤ ⊤ = (⊤ : (CoveredScheme.product A B).scheme.Opens) := by
    simp [rectangle]
  exact (((sectionsBasePresheafFunctor K).obj (CoveredScheme.externalTensor A B M N)).mapIso
      (eqToIso htop).op).inv (externalProduct K p q M N ⊤ ⊤ (m ⊗ₜ[K] n))

/-- On a pure tensor the actual binary global-section isomorphism is the
actual external product of those sections. -/
@[simp] theorem binaryGlobalSectionsIso_tmul (A B : CoveredScheme K)
    (M : A.scheme.Modules) (N : B.scheme.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (m : sections K M ⊤) (n : sections K N ⊤) :
    (binaryGlobalSectionsIso A B M N).hom (m ⊗ₜ[K] n) =
      binaryExternalSection A B M N m n := by
  rfl

/-- The recursively formed actual external product of global sections. -/
def finiteExternalSection : {k : ℕ} → (A : Fin (k + 1) → CoveredScheme K) →
    (M : ∀ i, (A i).scheme.Modules) → (∀ i, sections K (M i) ⊤) →
      sections K (CoveredScheme.finiteExternalTensor A M) ⊤
  | 0, _, _, s => s 0
  | k + 1, A, M, s =>
      binaryExternalSection (A 0)
        (CoveredScheme.finiteProduct (fun i : Fin (k + 1) => A i.succ)) (M 0)
        (CoveredScheme.finiteExternalTensor
          (fun i : Fin (k + 1) => A i.succ) (fun i => M i.succ))
        (s 0) (finiteExternalSection (fun i : Fin (k + 1) => A i.succ)
          (fun i => M i.succ) (fun i => s i.succ))

/-- The complete finite global-section isomorphism retains the formula on
every pure tensor. This fixes the precise geometric realization of each
Segre monomial. -/
@[simp] theorem finiteGlobalSectionsIso_pure {k : ℕ}
    (A : Fin (k + 1) → CoveredScheme K) (M : ∀ i, (A i).scheme.Modules)
    (hM : ∀ i, (M i).IsQuasicoherent) (s : ∀ i, sections K (M i) ⊤) :
    (finiteGlobalSectionsIso A M hM).hom
      (FiniteTensorLinear.pure (fun i => sections K (M i) ⊤) s) =
        finiteExternalSection A M s := by
  induction k with
  | zero =>
      simp only [finiteGlobalSectionsIso, FiniteTensorLinear.pure, finiteExternalSection]
      erw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
      exact one_smul K (s 0)
  | succ k ih =>
      letI : (M 0).IsQuasicoherent := hM 0
      letI := CoveredScheme.finiteExternalTensor_quasicoherent
        (fun i : Fin (k + 1) => A i.succ) (fun i => M i.succ) (fun i => hM i.succ)
      simp only [finiteGlobalSectionsIso, FiniteTensorLinear.pure, Iso.trans_hom,
        tensorIso_hom, ModuleCat.comp_apply, Iso.refl_hom, finiteExternalSection]
      erw [ModuleCat.MonoidalCategory.tensorHom_tmul]
      erw [ModuleCat.id_apply,
        ih (fun i : Fin (k + 1) => A i.succ) (fun i => M i.succ)
          (fun i => hM i.succ) (fun i => s i.succ)]
      rfl


end PaperVerification.Segre.FiniteGlobalSections

end SegreFiniteGlobalSectionsFormula


end SegreGlobalCriticalSections

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
