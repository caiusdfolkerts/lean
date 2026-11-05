module

public import paper_verification.relative_projective_geometry2
import all paper_verification.relative_projective_geometry2
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import all Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.FiniteType
import all Mathlib.RingTheory.FiniteType
public import Mathlib.LinearAlgebra.Prod
import all Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Localization.Away.Basic
import all Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
import all Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import paper_verification.oai_chow000_run4
import all paper_verification.oai_chow000_run4
public import Mathlib.Algebra.Polynomial.Div
import all Mathlib.Algebra.Polynomial.Div
public import Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.AlgebraicGeometry.Noetherian
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Proper -/

/-! # Proper -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Proper.BundleCycles

noncomputable section

/-! The projective spectrum of a finite module's actual symmetric
algebra is proper over the base ring. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]

theorem symmetricAlgebra_finiteType : Algebra.FiniteType R (SymmetricAlgebra R M) := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  let T := Algebra.adjoin R (SymmetricAlgebra.ι R M '' (s : Set M))
  have hi : ∀ m, SymmetricAlgebra.ι R M m ∈ T := by
    intro m
    have hm : m ∈ Submodule.span R (s : Set M) := by rw [hs]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | zero => rw [map_zero]; exact T.zero_mem
    | add x y hx hy ihx ihy => rw [map_add]; exact T.add_mem ihx ihy
    | smul r x hx ih => rw [map_smul]; exact T.smul_mem ih r
  have hT : T = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    induction x using SymmetricAlgebra.induction with
    | algebraMap r => exact T.algebraMap_mem r
    | ι m => exact hi m
    | mul a b ha hb => exact T.mul_mem ha hb
    | add a b ha hb => exact T.add_mem ha hb
  refine ⟨s.image (SymmetricAlgebra.ι R M), ?_⟩
  rw [Finset.coe_image]
  exact hT

theorem symmetricDegreeZero_finiteType :
    Algebra.FiniteType (Symmetric.Grading.BundleCycles.symmetricGrading R M 0) (SymmetricAlgebra R M) := by
  let := symmetricAlgebra_finiteType R M
  let : IsScalarTower R (Symmetric.Grading.BundleCycles.symmetricGrading R M 0) (SymmetricAlgebra R M) := by
    constructor
    intro r s a
    change (r • s.val) * a = r • (s.val * a)
    exact smul_mul_assoc r s.val a
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (Symmetric.Grading.BundleCycles.symmetricGrading R M 0) (SymmetricAlgebra R M)

instance symmetricProjectiveToBase_isProper : IsProper (Scheme.BundleCycles.symmetricProjectiveToBase R M) := by
  let := symmetricDegreeZero_finiteType R M
  let e := (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toCommRingCatIso
  let : IsIso (CommRingCat.ofHom (Symmetric.GradingIdeals.BundleCycles.symmetricDegreeZero R M).toRingHom) := e.isIso_hom
  unfold Scheme.BundleCycles.symmetricProjectiveToBase
  infer_instance

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Proper.BundleCycles
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Proper"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChart -/

/-! # Symmetric Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChart.BundleCycles

noncomputable section

/-! The distinguished affine chart of Proj Sym(R ⊕ M), with its actual
dehomogenization map to Sym(M). -/

open _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

def augmentedSymmetricVariable : SymmetricAlgebra R (R × M) :=
  SymmetricAlgebra.ι R (R × M) (1, 0)

theorem augmentedSymmetricVariable_degree :
    augmentedSymmetricVariable R M ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) 1 := by
  change SymmetricAlgebra.ι R (R × M) (1, 0) ∈ LinearMap.range (SymmetricAlgebra.ι R (R × M)) ^ 1
  simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R (R × M)) (1, 0)

def symmetricDehomogenizingLinear : R × M →ₗ[R] SymmetricAlgebra R M :=
  (Algebra.linearMap R (SymmetricAlgebra R M)).comp (LinearMap.fst R R M) +
    (SymmetricAlgebra.ι R M).comp (LinearMap.snd R R M)

def symmetricDehomogenizingMap : SymmetricAlgebra R (R × M) →ₐ[R] SymmetricAlgebra R M :=
  SymmetricAlgebra.lift (symmetricDehomogenizingLinear R M)

theorem symmetricDehomogenizingMap_generator (r : R) (m : M) :
    symmetricDehomogenizingMap R M (SymmetricAlgebra.ι R (R × M) (r, m)) =
      algebraMap R (SymmetricAlgebra R M) r + SymmetricAlgebra.ι R M m :=
  SymmetricAlgebra.lift_ι_apply (symmetricDehomogenizingLinear R M) (r, m)

theorem symmetricDehomogenizingMap_variable :
    symmetricDehomogenizingMap R M (augmentedSymmetricVariable R M) = 1 := by
  change symmetricDehomogenizingMap R M (SymmetricAlgebra.ι R (R × M) (1, 0)) = 1
  rw [symmetricDehomogenizingMap_generator, map_one, map_zero, add_zero]

abbrev augmentedSymmetricChart : Type :=
  Away (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (augmentedSymmetricVariable R M)

def augmentedSymmetricDehomogenization : augmentedSymmetricChart R M →+* SymmetricAlgebra R M :=
  (Localization.awayLift (symmetricDehomogenizingMap R M).toRingHom (augmentedSymmetricVariable R M)
    (by change IsUnit (symmetricDehomogenizingMap R M (augmentedSymmetricVariable R M));
        rw [symmetricDehomogenizingMap_variable]; exact isUnit_one)).comp
    (algebraMap (augmentedSymmetricChart R M) (Localization.Away (augmentedSymmetricVariable R M)))

theorem augmentedSymmetricDehomogenization_mk (n : ℕ) (a : SymmetricAlgebra R (R × M))
    (ha : a ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (n • 1)) :
    augmentedSymmetricDehomogenization R M
      (Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (augmentedSymmetricVariable_degree R M) n a ha) =
        symmetricDehomogenizingMap R M a := by
  have hu : IsUnit ((symmetricDehomogenizingMap R M).toRingHom (augmentedSymmetricVariable R M)) := by
    change IsUnit (symmetricDehomogenizingMap R M (augmentedSymmetricVariable R M))
    rw [symmetricDehomogenizingMap_variable]
    exact isUnit_one
  change Localization.awayLift (symmetricDehomogenizingMap R M).toRingHom (augmentedSymmetricVariable R M) hu
    (Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (augmentedSymmetricVariable_degree R M) n a ha).val = _
  rw [Away.val_mk]
  have h := Localization.awayLift_mk (symmetricDehomogenizingMap R M).toRingHom
    (augmentedSymmetricVariable R M) a 1 (by
      change symmetricDehomogenizingMap R M (augmentedSymmetricVariable R M) * 1 = 1
      rw [symmetricDehomogenizingMap_variable, mul_one]) n
  exact h.trans (by rw [one_pow, mul_one]; rfl)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChart.BundleCycles
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChart"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartAddition -/

/-! # Chart Addition -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartAddition.BundleCycles

noncomputable section

section

/-! Addition of actual homogeneous fractions with a fixed denominator. -/

open _root_.HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem gradedAway_mk_add {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (n : ℕ)
    (a b : A) (ha : a ∈ 𝒜 (n • k)) (hb : b ∈ 𝒜 (n • k)) :
    Away.mk 𝒜 hs n (a + b) (add_mem ha hb) = Away.mk 𝒜 hs n a ha + Away.mk 𝒜 hs n b hb := by
  apply HomogeneousLocalization.val_injective
  rw [val_add, Away.val_mk, Away.val_mk, Away.val_mk]
  simp only [Localization.mk_eq_mk']
  apply (IsLocalization.map_units (M := Submonoid.powers s) (Localization.Away s) ⟨s ^ n, ⟨n, rfl⟩⟩).mul_right_cancel
  rw [add_mul, IsLocalization.mk'_spec, IsLocalization.mk'_spec, IsLocalization.mk'_spec, map_add]

theorem gradedAway_mk_algebraMap {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (a : 𝒜 0) :
    Away.mk 𝒜 hs 0 a.val (by simpa only [zero_smul] using a.property) =
      fromZeroRingHom 𝒜 (Submonoid.powers s) a := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, AwayIs.BundleCycles.gradedFromZero_val]
  exact congrArg (Localization.mk a.val) (Subtype.ext (pow_zero s))

end

/-! The actual homogeneous fraction map is linear over the original
coefficient ring, with its canonical chart scalar map. -/

open _root_.HomogeneousLocalization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

def gradedChartScalarMap (s : A) : R →+* Away 𝒜 s :=
  (fromZeroRingHom 𝒜 (Submonoid.powers s)).comp (algebraMap R (𝒜 0))

abbrev gradedChartScalarAlgebra (s : A) : Algebra R (Away 𝒜 s) :=
  (gradedChartScalarMap 𝒜 s).toAlgebra

theorem gradedChartScalarMap_val (s : A) (r : R) :
    (gradedChartScalarMap 𝒜 s r).val = Localization.mk (algebraMap R A r) 1 :=
  AwayIs.BundleCycles.gradedFromZero_val 𝒜 s (algebraMap R (𝒜 0) r)

theorem gradedChartFraction_smul {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (n : ℕ)
    (r : R) (a : A) (ha : a ∈ 𝒜 (n • k)) :
    Away.mk 𝒜 hs n (r • a) ((𝒜 (n • k)).smul_mem r ha) =
      gradedChartScalarMap 𝒜 s r * Away.mk 𝒜 hs n a ha := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, Away.val_mk, gradedChartScalarMap_val, Away.val_mk, Localization.mk_mul]
  simp only [Algebra.smul_def, one_mul]

def gradedChartFractionLinear {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (n : ℕ) :
    letI := gradedChartScalarAlgebra 𝒜 s
    𝒜 (n • k) →ₗ[R] Away 𝒜 s := by
  let := gradedChartScalarAlgebra 𝒜 s
  exact {
    toFun a := Away.mk 𝒜 hs n a.val a.property
    map_add' a b := gradedAway_mk_add 𝒜 hs n a.val b.val a.property b.property
    map_smul' r a := gradedChartFraction_smul 𝒜 hs n r a.val a.property }

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartAddition.BundleCycles
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartAddition"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartGenerators -/

/-! # Symmetric Chart Generators -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartGenerators.BundleCycles

noncomputable section

/-! The inverse affine-chart map sends a module generator to its genuine
homogeneous fraction with denominator the distinguished coordinate. -/

open _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

abbrev augmentedSymmetricChartAlgebra : Algebra R (SymmetricChart.BundleCycles.augmentedSymmetricChart R M) :=
  Graded.ChartAddition.BundleCycles.gradedChartScalarAlgebra (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M)

attribute [local instance] augmentedSymmetricChartAlgebra

def augmentedSymmetricModuleLinear : M →ₗ[R] SymmetricAlgebra R (R × M) :=
  (SymmetricAlgebra.ι R (R × M)).comp (LinearMap.inr R R M)

theorem augmentedSymmetricModuleLinear_degree (m : M) :
    augmentedSymmetricModuleLinear R M m ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) 1 := by
  change SymmetricAlgebra.ι R (R × M) (0, m) ∈ LinearMap.range (SymmetricAlgebra.ι R (R × M)) ^ 1
  simpa only [pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R (R × M)) (0, m)

def augmentedSymmetricChartGenerator : M →ₗ[R] SymmetricChart.BundleCycles.augmentedSymmetricChart R M :=
  (Graded.ChartAddition.BundleCycles.gradedChartFractionLinear (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1).comp
    ((augmentedSymmetricModuleLinear R M).codRestrict _ (fun m => by
      simpa only [one_smul] using augmentedSymmetricModuleLinear_degree R M m))

def augmentedSymmetricChartInverse : SymmetricAlgebra R M →ₐ[R] SymmetricChart.BundleCycles.augmentedSymmetricChart R M :=
  SymmetricAlgebra.lift (augmentedSymmetricChartGenerator R M)

theorem augmentedSymmetricChartInverse_generator (m : M) :
    augmentedSymmetricChartInverse R M (SymmetricAlgebra.ι R M m) =
      Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1
        (augmentedSymmetricModuleLinear R M m) (by simpa only [one_smul] using augmentedSymmetricModuleLinear_degree R M m) :=
  SymmetricAlgebra.lift_ι_apply _ m

theorem augmentedSymmetricDehomogenization_generator (m : M) :
    SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M (augmentedSymmetricChartGenerator R M m) =
      SymmetricAlgebra.ι R M m := by
  exact (SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization_mk R M 1
    (augmentedSymmetricModuleLinear R M m)
    (by simpa only [one_smul] using augmentedSymmetricModuleLinear_degree R M m)).trans (by
      change SymmetricChart.BundleCycles.symmetricDehomogenizingMap R M (SymmetricAlgebra.ι R (R × M) (0, m)) = _
      rw [SymmetricChart.BundleCycles.symmetricDehomogenizingMap_generator, map_zero, zero_add])

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartGenerators.BundleCycles
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartGenerators"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartMultiplication -/

/-! # Chart Multiplication -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartMultiplication.BundleCycles

noncomputable section

/-! Multiplication and normalization of genuine homogeneous affine-chart fractions. -/

open _root_.HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem gradedAway_mk_mul {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (n m : ℕ)
    (a b : A) (ha : a ∈ 𝒜 (n • k)) (hb : b ∈ 𝒜 (m • k)) :
    Away.mk 𝒜 hs n a ha * Away.mk 𝒜 hs m b hb =
      Away.mk 𝒜 hs (n + m) (a * b) (by rw [add_smul]; exact SetLike.mul_mem_graded ha hb) := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul, Away.val_mk, Away.val_mk, Away.val_mk, Localization.mk_mul]
  exact congrArg (Localization.mk (a * b)) (Subtype.ext (pow_add s n m).symm)

theorem gradedAway_mk_self {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) :
    Away.mk 𝒜 hs 1 s (by simpa only [one_smul] using hs) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, val_one]
  have he : (⟨s ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers s) = ⟨s, Submonoid.mem_powers s⟩ :=
    Subtype.ext (pow_one s)
  exact (congrArg (Localization.mk s) he).trans
    (Localization.mk_self (⟨s, Submonoid.mem_powers s⟩ : Submonoid.powers s))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartMultiplication.BundleCycles
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartMultiplication"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartDegreeOne -/

/-! # Symmetric Chart Degree One -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartDegreeOne.BundleCycles

noncomputable section

/-! Normalizing an arbitrary degree-one generator at the distinguished
coordinate gives its dehomogenization in the actual chart. -/

open _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartAlgebra

theorem augmentedSymmetricGenerator_split (r : R) (m : M) :
    SymmetricAlgebra.ι R (R × M) (r, m) =
      r • SymmetricChart.BundleCycles.augmentedSymmetricVariable R M + SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear R M m := by
  change SymmetricAlgebra.ι R (R × M) (r, m) =
    r • SymmetricAlgebra.ι R (R × M) (1, 0) + SymmetricAlgebra.ι R (R × M) (0, m)
  rw [← map_smul, ← map_add]
  congr 1
  ext <;> simp

theorem augmentedSymmetricChart_degreeOne (v : R × M)
    (hv : SymmetricAlgebra.ι R (R × M) v ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (1 • 1)) :
    SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse R M
      (SymmetricChart.BundleCycles.symmetricDehomogenizingMap R M (SymmetricAlgebra.ι R (R × M) v)) =
        Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1
          (SymmetricAlgebra.ι R (R × M) v) hv := by
  obtain ⟨r, m⟩ := v
  rw [SymmetricChart.BundleCycles.symmetricDehomogenizingMap_generator, map_add, AlgHom.commutes,
    SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse_generator]
  have ht : SymmetricChart.BundleCycles.augmentedSymmetricVariable R M ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (1 • 1) := by
    simpa only [one_smul] using SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M
  have hm : SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear R M m ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (1 • 1) := by
    simpa only [one_smul] using SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear_degree R M m
  have hsplit : (⟨SymmetricAlgebra.ι R (R × M) (r, m), hv⟩ : Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (1 • 1)) =
      r • ⟨SymmetricChart.BundleCycles.augmentedSymmetricVariable R M, ht⟩ + ⟨SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear R M m, hm⟩ :=
    Subtype.ext (augmentedSymmetricGenerator_split R M r m)
  have h := congrArg
    (Graded.ChartAddition.BundleCycles.gradedChartFractionLinear (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1)
    hsplit
  refine (h.trans ((Graded.ChartAddition.BundleCycles.gradedAway_mk_add (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
    (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1 (r • SymmetricChart.BundleCycles.augmentedSymmetricVariable R M)
      (SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear R M m) ((Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (1 • 1)).smul_mem r ht) hm).trans ?_)).symm
  rw [Graded.ChartAddition.BundleCycles.gradedChartFraction_smul (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
    (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1 r (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M) ht,
    Graded.ChartMultiplication.BundleCycles.gradedAway_mk_self, mul_one]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartDegreeOne.BundleCycles
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartDegreeOne"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricPolynomial -/

/-! # Symmetric Polynomial -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricPolynomial.BundleCycles

noncomputable section

section

/-! The distinguished summand of an augmented symmetric algebra is
an actual polynomial variable over the module's symmetric algebra. -/

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

def augmentedSymmetricPolynomialLinear : R × M →ₗ[R] Polynomial (SymmetricAlgebra R M) :=
  (LinearMap.fst R R M).smulRight Polynomial.X +
    ((Polynomial.CAlgHom (R := R) (A := SymmetricAlgebra R M)).toLinearMap.comp
      (SymmetricAlgebra.ι R M)).comp (LinearMap.snd R R M)

def augmentedSymmetricPolynomialMap : SymmetricAlgebra R (R × M) →ₐ[R] Polynomial (SymmetricAlgebra R M) :=
  SymmetricAlgebra.lift (augmentedSymmetricPolynomialLinear R M)

theorem augmentedSymmetricPolynomialMap_generator (r : R) (m : M) :
    augmentedSymmetricPolynomialMap R M (SymmetricAlgebra.ι R (R × M) (r, m)) =
      r • Polynomial.X + Polynomial.C (SymmetricAlgebra.ι R M m) :=
  SymmetricAlgebra.lift_ι_apply _ _

theorem augmentedSymmetricPolynomialMap_variable :
    augmentedSymmetricPolynomialMap R M (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M) = Polynomial.X := by
  change augmentedSymmetricPolynomialMap R M (SymmetricAlgebra.ι R (R × M) (1, 0)) = _
  rw [augmentedSymmetricPolynomialMap_generator, one_smul, map_zero, map_zero, add_zero]

def augmentedSymmetricCoefficientMap : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R (R × M) :=
  SymmetricAlgebra.lift (SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear R M)

theorem augmentedSymmetricCoefficientMap_generator (m : M) :
    augmentedSymmetricCoefficientMap R M (SymmetricAlgebra.ι R M m) =
      SymmetricChartGenerators.BundleCycles.augmentedSymmetricModuleLinear R M m := SymmetricAlgebra.lift_ι_apply _ _

def augmentedSymmetricPolynomialInverse : Polynomial (SymmetricAlgebra R M) →ₐ[R] SymmetricAlgebra R (R × M) :=
  Polynomial.eval₂AlgHom (augmentedSymmetricCoefficientMap R M) (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M)
    (fun _ => Commute.all _ _)

theorem augmentedSymmetricPolynomialInverse_C (a : SymmetricAlgebra R M) :
    augmentedSymmetricPolynomialInverse R M (Polynomial.C a) = augmentedSymmetricCoefficientMap R M a :=
  Polynomial.eval₂_C _ _

theorem augmentedSymmetricPolynomialInverse_X :
    augmentedSymmetricPolynomialInverse R M Polynomial.X = SymmetricChart.BundleCycles.augmentedSymmetricVariable R M :=
  Polynomial.eval₂_X _ _

end

/-! The actual polynomial decomposition of the augmented symmetric
algebra, including regularity of its distinguished coordinate. -/

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

theorem augmentedSymmetricPolynomial_leftInverse :
    Function.LeftInverse (augmentedSymmetricPolynomialInverse R M) (augmentedSymmetricPolynomialMap R M) := by
  have h : (augmentedSymmetricPolynomialInverse R M).comp (augmentedSymmetricPolynomialMap R M) =
      AlgHom.id R (SymmetricAlgebra R (R × M)) := by
    apply SymmetricAlgebra.algHom_ext
    apply LinearMap.ext
    intro v
    obtain ⟨r, m⟩ := v
    change augmentedSymmetricPolynomialInverse R M
      (augmentedSymmetricPolynomialMap R M (SymmetricAlgebra.ι R (R × M) (r, m))) =
        SymmetricAlgebra.ι R (R × M) (r, m)
    rw [augmentedSymmetricPolynomialMap_generator, map_add, map_smul,
      augmentedSymmetricPolynomialInverse_X, augmentedSymmetricPolynomialInverse_C,
      augmentedSymmetricCoefficientMap_generator]
    exact (SymmetricChartDegreeOne.BundleCycles.augmentedSymmetricGenerator_split R M r m).symm
  exact fun a => DFunLike.congr_fun h a

theorem augmentedSymmetricPolynomial_coefficient :
    (augmentedSymmetricPolynomialMap R M).comp (augmentedSymmetricCoefficientMap R M) =
      Polynomial.CAlgHom := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro m
  change augmentedSymmetricPolynomialMap R M
    (augmentedSymmetricCoefficientMap R M (SymmetricAlgebra.ι R M m)) =
      Polynomial.C (SymmetricAlgebra.ι R M m)
  rw [augmentedSymmetricCoefficientMap_generator]
  change augmentedSymmetricPolynomialMap R M (SymmetricAlgebra.ι R (R × M) (0, m)) = _
  rw [augmentedSymmetricPolynomialMap_generator, zero_smul, zero_add]

theorem augmentedSymmetricPolynomial_rightInverse :
    Function.RightInverse (augmentedSymmetricPolynomialInverse R M) (augmentedSymmetricPolynomialMap R M) := by
  have h : (augmentedSymmetricPolynomialMap R M).comp (augmentedSymmetricPolynomialInverse R M) =
      AlgHom.id R (Polynomial (SymmetricAlgebra R M)) := by
    apply Polynomial.algHom_ext'
    · apply AlgHom.ext
      intro a
      change augmentedSymmetricPolynomialMap R M
        (augmentedSymmetricPolynomialInverse R M (Polynomial.C a)) = Polynomial.C a
      rw [augmentedSymmetricPolynomialInverse_C]
      exact DFunLike.congr_fun (augmentedSymmetricPolynomial_coefficient R M) a
    · change augmentedSymmetricPolynomialMap R M
        (augmentedSymmetricPolynomialInverse R M Polynomial.X) = Polynomial.X
      rw [augmentedSymmetricPolynomialInverse_X, augmentedSymmetricPolynomialMap_variable]
  exact fun a => DFunLike.congr_fun h a

def augmentedSymmetricPolynomialEquiv : SymmetricAlgebra R (R × M) ≃ₐ[R] Polynomial (SymmetricAlgebra R M) :=
  { augmentedSymmetricPolynomialMap R M with
    invFun := augmentedSymmetricPolynomialInverse R M
    left_inv := augmentedSymmetricPolynomial_leftInverse R M
    right_inv := augmentedSymmetricPolynomial_rightInverse R M }

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricPolynomial.BundleCycles
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricPolynomial"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapChartPullback -/

/-! # Map Chart Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapChartPullback.BundleCycles

noncomputable section

/-! Native affine-chart squares for the actual Proj map are pullbacks. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

theorem projectiveMap_chart_isPullback {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) (hk : 0 < k) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map f s)))
      (Proj.awayι ℬ (f s) (f.map_mem hs) hk) (Proj.awayι 𝒜 s hs hk) (Proj.map f hf) := by
  apply IsOpenImmersion.isPullback
  · exact Proj.awayι_comp_map f hf hk s hs
  · rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
    exact Proj.map_preimage_basicOpen f hf s

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapChartPullback.BundleCycles
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapChartPullback"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.SurjectiveChart -/

/-! # Surjective Chart -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.SurjectiveChart.BundleCycles

noncomputable section

/-! Surjective graded ring maps induce surjective maps of the actual
homogeneous affine-chart rings. -/

open _root_.HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)

include hf in
theorem gradedSurjective_homogeneousPreimage (n : ℕ) (b : B) (hb : b ∈ ℬ n) :
    ∃ a : A, a ∈ 𝒜 n ∧ f a = b := by
  obtain ⟨a, rfl⟩ := hf b
  refine ⟨(DirectSum.decompose 𝒜 a n).val, (DirectSum.decompose 𝒜 a n).property, ?_⟩
  exact (GradedRingHom.map_directSumDecompose 𝒜 ℬ f).trans (DirectSum.decompose_of_mem_same ℬ hb)

include hf in
theorem gradedAwayMap_surjective {s : A} {k : ℕ} (hs : s ∈ 𝒜 k) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.map_mem hs) z
  obtain ⟨a, ha, rfl⟩ := gradedSurjective_homogeneousPreimage f hf (n • k) b hb
  exact ⟨Away.mk 𝒜 hs n a ha, Away.map_mk f s hs n a ha⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.SurjectiveChart.BundleCycles
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.SurjectiveChart"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ClosedImmersion -/

/-! # Closed Immersion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ClosedImmersion.BundleCycles

noncomputable section

/-! Surjective graded homomorphisms give closed immersions of actual
projective spectra, proved on their native affine charts. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousLocalization

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hsurj : Function.Surjective f)

include hsurj in
theorem projectiveMap_isClosedImmersion : IsClosedImmersion (Proj.map f hf) := by
  apply Global.SpecialFiber.BundleCycles.isClosedImmersion_of_cover_pullbacks (Proj.map f hf) (Proj.affineOpenCover 𝒜).openCover
    (fun s => Spec (.of (Away ℬ (f s.2.val))))
    (fun s => Proj.awayι ℬ (f s.2.val) (f.map_mem s.2.property) s.1.property)
    (fun s => Spec.map (CommRingCat.ofHom (Away.map f s.2.val)))
  · intro s
    exact MapChartPullback.BundleCycles.projectiveMap_chart_isPullback f hf s.2.property s.1.property
  · intro s
    exact IsClosedImmersion.spec_of_surjective _ (Graded.SurjectiveChart.BundleCycles.gradedAwayMap_surjective f hsurj s.2.property)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ClosedImmersion.BundleCycles
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.ClosedImmersion"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ClosedImmersion -/

/-! # Closed Immersion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ClosedImmersion.BundleCycles

noncomputable section

/-! Surjections of modules give the actual closed projective
embeddings of their symmetric algebras. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)

include hf in
theorem symmetricGradedMap_surjective : Function.Surjective (Symmetric.GradedMap.BundleCycles.symmetricGradedMap f) := by
  intro a
  induction a using SymmetricAlgebra.induction with
  | algebraMap r =>
    exact ⟨algebraMap R (SymmetricAlgebra R M) r,
      (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f)).commutes r⟩
  | ι n =>
    obtain ⟨m, rfl⟩ := hf n
    exact ⟨SymmetricAlgebra.ι R M m, Symmetric.GradedMap.BundleCycles.symmetricGradedMap_generator f m⟩
  | mul a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a * b, map_mul _ a b⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ a b⟩

instance symmetricProjectiveMap_isClosedImmersion : IsClosedImmersion (Scheme.BundleCycles.symmetricProjectiveMap f hf) :=
  Projective.ClosedImmersion.BundleCycles.projectiveMap_isClosedImmersion (Symmetric.GradedMap.BundleCycles.symmetricGradedMap f) (Scheme.BundleCycles.symmetricGradedMap_irrelevant f hf)
    (symmetricGradedMap_surjective f hf)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ClosedImmersion.BundleCycles
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.ClosedImmersion"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Kernel -/

/-! # Kernel -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Kernel.BundleCycles

noncomputable section

/-! Killing the distinguished augmented coordinate has exactly the
principal kernel generated by that coordinate. -/

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

theorem symmetricInfinity_constantCoeff :
    Polynomial.constantCoeff.comp (Augmented.SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialMap R M).toRingHom =
      (Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M)).toRingHom := by
  apply Symmetric.ScalarMap.BundleCycles.symmetricRingHom_ext
  · intro r
    change Polynomial.constantCoeff (Augmented.SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialMap R M (algebraMap R _ r)) = _
    rw [AlgHom.commutes]
    change (Polynomial.C (algebraMap R (SymmetricAlgebra R M) r)).coeff 0 = _
    rw [Polynomial.coeff_C_zero]
    exact (SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp (LinearMap.snd R R M))).commutes r |>.symm
  · rintro ⟨r, m⟩
    change Polynomial.constantCoeff
      (Augmented.SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialMap R M (SymmetricAlgebra.ι R (R × M) (r, m))) =
      Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M) (SymmetricAlgebra.ι R (R × M) (r, m))
    rw [Augmented.SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialMap_generator, Symmetric.GradedMap.BundleCycles.symmetricGradedMap_generator]
    change (r • Polynomial.X + Polynomial.C (SymmetricAlgebra.ι R M m)).coeff 0 = _
    simp only [Polynomial.coeff_add, Polynomial.coeff_smul, Polynomial.coeff_X_zero,
      smul_zero, zero_add, Polynomial.coeff_C_zero]
    rfl

theorem symmetricInfinity_kernel :
    RingHom.ker (Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M)).toRingHom =
      Ideal.span {Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M} := by
  apply le_antisymm
  · intro a ha
    have hz : (Augmented.SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialMap R M a).coeff 0 = 0 :=
      (DFunLike.congr_fun (symmetricInfinity_constantCoeff R M) a).trans ha
    obtain ⟨b, hb⟩ := Polynomial.X_dvd_iff.mpr hz
    apply Ideal.mem_span_singleton.mpr
    refine ⟨Augmented.SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialInverse R M b, ?_⟩
    apply (Augmented.SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialEquiv R M).injective
    change Augmented.SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialMap R M a =
      Augmented.SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialMap R M (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M * Augmented.SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialInverse R M b)
    rw [map_mul, Augmented.SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialMap_variable,
      Augmented.SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomial_rightInverse R M b]
    exact hb
  · apply Ideal.span_le.mpr
    intro a ha
    obtain rfl : a = Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M := ha
    change Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M) (SymmetricAlgebra.ι R (R × M) (1, 0)) = 0
    rw [Symmetric.GradedMap.BundleCycles.symmetricGradedMap_generator]
    exact map_zero (SymmetricAlgebra.ι R M)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Kernel.BundleCycles
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Kernel"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.SurjectiveRange -/

/-! # Surjective Range -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.SurjectiveRange.BundleCycles

noncomputable section

/-! The image of an actual projective map from a graded quotient is
the vanishing locus of its actual ring-theoretic kernel. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hsurj : Function.Surjective f)

include hsurj in
theorem projectiveSurjective_range :
    Set.range (Proj.map f hf) = ProjectiveSpectrum.zeroLocus 𝒜 (RingHom.ker f.toRingHom) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩ a ha
    change f a ∈ q.asHomogeneousIdeal.toIdeal
    change f a = 0 at ha
    rw [ha]
    exact q.asHomogeneousIdeal.toIdeal.zero_mem
  · intro hp
    let p' : PrimeSpectrum A := ⟨p.asHomogeneousIdeal.toIdeal, p.isPrime⟩
    have hrange : p' ∈ Set.range (PrimeSpectrum.comap f.toRingHom) := by
      rw [range_comap_of_surjective B f.toRingHom hsurj]
      exact hp
    obtain ⟨q, hq⟩ := hrange
    have hqI : q.asIdeal.comap f = p.asHomogeneousIdeal.toIdeal := congrArg PrimeSpectrum.asIdeal hq
    have hmap : (p.asHomogeneousIdeal.map f).toIdeal = q.asIdeal := by
      change Ideal.map f p.asHomogeneousIdeal.toIdeal = q.asIdeal
      rw [← hqI]
      exact Ideal.map_comap_of_surjective f hsurj q.asIdeal
    let qP : Proj ℬ :=
      { asHomogeneousIdeal := p.asHomogeneousIdeal.map f
        isPrime := hmap.symm ▸ q.isPrime
        not_irrelevant_le := by
          intro h
          have hl := (LocalizationRange.BundleCycles.gradedMap_irrelevant_le 𝒜 ℬ f).trans h
          have hc : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
              (p.asHomogeneousIdeal.map f).toIdeal.comap f := Ideal.map_le_iff_le_comap.mp hl
          rw [hmap, hqI] at hc
          exact p.not_irrelevant_le hc }
    refine ⟨qP, ?_⟩
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext
    exact (congrArg (Ideal.comap f) hmap).trans hqI

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.SurjectiveRange.BundleCycles
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.SurjectiveRange"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartScalar -/

/-! # Symmetric Chart Scalar -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartScalar.BundleCycles

noncomputable section

/-! Dehomogenization respects the actual coefficient-ring structure on
the distinguished homogeneous chart. -/

open _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartAlgebra

theorem augmentedSymmetricDehomogenization_scalar (r : R) :
    SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M (algebraMap R (SymmetricChart.BundleCycles.augmentedSymmetricChart R M) r) =
      algebraMap R (SymmetricAlgebra R M) r := by
  have h := Graded.ChartAddition.BundleCycles.gradedAway_mk_algebraMap (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
    (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) (algebraMap R (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) 0) r)
  change SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M
    (fromZeroRingHom (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (Submonoid.powers (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M))
      (algebraMap R (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) 0) r)) = _
  rw [← h]
  exact (SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization_mk R M 0 _ _).trans
    ((SymmetricChart.BundleCycles.symmetricDehomogenizingMap R M).commutes r)

def augmentedSymmetricDehomogenizationAlg : SymmetricChart.BundleCycles.augmentedSymmetricChart R M →ₐ[R] SymmetricAlgebra R M :=
  { SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M with
    commutes' := augmentedSymmetricDehomogenization_scalar R M }

theorem augmentedSymmetricDehomogenization_leftInverse :
    Function.LeftInverse (SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M) (SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse R M) := by
  have h : (augmentedSymmetricDehomogenizationAlg R M).comp (SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse R M) =
      AlgHom.id R (SymmetricAlgebra R M) := by
    apply SymmetricAlgebra.algHom_ext
    ext m
    change SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M
      (SymmetricAlgebra.lift (SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartGenerator R M) (SymmetricAlgebra.ι R M m)) = _
    rw [SymmetricAlgebra.lift_ι_apply]
    exact SymmetricChartGenerators.BundleCycles.augmentedSymmetricDehomogenization_generator R M m
  exact fun a => DFunLike.congr_fun h a

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartScalar.BundleCycles
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartScalar"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartEquiv -/

/-! # Symmetric Chart Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartEquiv.BundleCycles

noncomputable section

/-! The distinguished chart of the actual augmented symmetric Proj is
canonically the affine symmetric algebra of the module. -/

open _root_.HomogeneousLocalization

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartAlgebra

theorem augmentedSymmetricChart_homogeneous (n : ℕ) (a : SymmetricAlgebra R (R × M))
    (ha : a ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) n) :
    SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse R M (SymmetricChart.BundleCycles.symmetricDehomogenizingMap R M a) =
      Away.mk (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) n a
        (by simpa only [smul_eq_mul, mul_one] using ha) := by
  change a ∈ LinearMap.range (SymmetricAlgebra.ι R (R × M)) ^ n at ha
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    exact (Graded.ChartAddition.BundleCycles.gradedAway_mk_algebraMap (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
      (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M)
      (algebraMap R (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) 0) r)).symm
  | add a b n ha hb iha ihb =>
    rw [map_add, map_add, iha, ihb]
    exact (Graded.ChartAddition.BundleCycles.gradedAway_mk_add (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
      (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) n a b _ _).symm
  | mem_mul m hm n a ha ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, map_mul, ih]
    have hv : SymmetricAlgebra.ι R (R × M) v ∈ Symmetric.Grading.BundleCycles.symmetricGrading R (R × M) (1 • 1) := by
      change SymmetricAlgebra.ι R (R × M) v ∈ LinearMap.range (SymmetricAlgebra.ι R (R × M)) ^ (1 • 1)
      simpa only [one_smul, pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R (R × M)) v
    rw [SymmetricChartDegreeOne.BundleCycles.augmentedSymmetricChart_degreeOne R M v hv]
    have h := Graded.ChartMultiplication.BundleCycles.gradedAway_mk_mul (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
      (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) 1 n (SymmetricAlgebra.ι R (R × M) v) a hv
      (by simpa only [smul_eq_mul, mul_one, Symmetric.Grading.BundleCycles.symmetricGrading] using ha)
    exact h.trans (by
      apply HomogeneousLocalization.val_injective
      rw [Away.val_mk, Away.val_mk]
      exact congrArg (Localization.mk (SymmetricAlgebra.ι R (R × M) v * a))
        (Subtype.ext (congrArg (fun k => SymmetricChart.BundleCycles.augmentedSymmetricVariable R M ^ k) (Nat.add_comm 1 n))))

theorem augmentedSymmetricDehomogenization_rightInverse :
    Function.RightInverse (SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M) (SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse R M) := by
  intro z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M))
    (SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) z
  rw [SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization_mk]
  exact augmentedSymmetricChart_homogeneous R M n a
    (by simpa only [smul_eq_mul, mul_one] using ha)

def augmentedSymmetricChartEquiv : SymmetricChart.BundleCycles.augmentedSymmetricChart R M ≃ₐ[R] SymmetricAlgebra R M :=
  { SymmetricChartScalar.BundleCycles.augmentedSymmetricDehomogenizationAlg R M with
    invFun := SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartInverse R M
    left_inv := augmentedSymmetricDehomogenization_rightInverse R M
    right_inv := SymmetricChartScalar.BundleCycles.augmentedSymmetricDehomogenization_leftInverse R M }

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartEquiv.BundleCycles
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricChartEquiv"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification -/

/-! # Affine Compactification -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification.BundleCycles

noncomputable section

/-! The affine symmetric spectrum embeds as the distinguished open in
the actual projective spectrum of the augmented module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance] Augmented.SymmetricChartGenerators.BundleCycles.augmentedSymmetricChartAlgebra

def augmentedSymmetricAffineChartIso :
    (Proj.basicOpen (Grading.BundleCycles.symmetricGrading R (R × M)) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M)).toScheme ≅
      Spec (.of (SymmetricAlgebra R M)) :=
  Proj.basicOpenIsoSpec (Grading.BundleCycles.symmetricGrading R (R × M)) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M)
    (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) (by decide : 0 < 1) ≪≫
      Scheme.Spec.mapIso (Augmented.SymmetricChartEquiv.BundleCycles.augmentedSymmetricChartEquiv R M).toRingEquiv.toCommRingCatIso.symm.op

def symmetricAffineCompactification :
    Spec (.of (SymmetricAlgebra R M)) ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M) :=
  Spec.map (CommRingCat.ofHom (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M)) ≫
    Proj.awayι (Grading.BundleCycles.symmetricGrading R (R × M)) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M)
      (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable_degree R M) (by decide : 0 < 1)

instance symmetricAffineCompactification_isOpenImmersion :
    IsOpenImmersion (symmetricAffineCompactification R M) := by
  let e := (Augmented.SymmetricChartEquiv.BundleCycles.augmentedSymmetricChartEquiv R M).toRingEquiv.toCommRingCatIso
  let : IsIso (CommRingCat.ofHom (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M)) := e.isIso_hom
  unfold symmetricAffineCompactification
  infer_instance

theorem symmetricAffineCompactification_opensRange :
    (symmetricAffineCompactification R M).opensRange =
      Proj.basicOpen (Grading.BundleCycles.symmetricGrading R (R × M)) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M) := by
  let e := (Augmented.SymmetricChartEquiv.BundleCycles.augmentedSymmetricChartEquiv R M).toRingEquiv.toCommRingCatIso
  let : IsIso (CommRingCat.ofHom (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricDehomogenization R M)) := e.isIso_hom
  unfold symmetricAffineCompactification
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Proj.opensRange_awayι _ _ _ _)

theorem symmetricAffineCompactification_over :
    symmetricAffineCompactification R M ≫ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R (R × M) =
      Spec.map (CommRingCat.ofHom (algebraMap R (SymmetricAlgebra R M))) := by
  unfold symmetricAffineCompactification SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase
  rw [Category.assoc, ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  exact Augmented.SymmetricChartScalar.BundleCycles.augmentedSymmetricDehomogenization_scalar R M r

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification.BundleCycles
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion -/

/-! # Inclusion -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion.BundleCycles

noncomputable section

/-! The actual projective spectrum of the unaugmented module is the
closed hyperplane complementary to the affine compactification chart. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

def symmetricInfinityInclusion : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M ⟶ SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M) :=
  SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveMap (LinearMap.snd R R M) (fun m => ⟨(0, m), rfl⟩)

instance symmetricInfinityInclusion_isClosedImmersion : IsClosedImmersion (symmetricInfinityInclusion R M) :=
  SymmetricProjective.ClosedImmersion.BundleCycles.symmetricProjectiveMap_isClosedImmersion (LinearMap.snd R R M) (fun m => ⟨(0, m), rfl⟩)

theorem symmetricInfinityInclusion_range :
    Set.range (symmetricInfinityInclusion R M) =
      (↑(Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification R M).opensRange : Set (SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M)))ᶜ := by
  change Set.range (Proj.map (Symmetric.GradedMap.BundleCycles.symmetricGradedMap (LinearMap.snd R R M)) _) = _
  rw [Projective.SurjectiveRange.BundleCycles.projectiveSurjective_range _ _ (SymmetricProjective.ClosedImmersion.BundleCycles.symmetricGradedMap_surjective (LinearMap.snd R R M)
    (fun m => ⟨(0, m), rfl⟩)), Kernel.BundleCycles.symmetricInfinity_kernel, ProjectiveSpectrum.zeroLocus_span,
    Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification_opensRange]
  exact ((congrArg Set.compl (ProjectiveSpectrum.basicOpen_eq_zeroLocus_compl
    (Symmetric.Grading.BundleCycles.symmetricGrading R (R × M)) (Augmented.SymmetricChart.BundleCycles.augmentedSymmetricVariable R M))).trans (compl_compl _)).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion.BundleCycles
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Noetherian -/

/-! # Noetherian -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Noetherian.BundleCycles

/-! A finite symmetric projective spectrum over a Noetherian ring
is an actual Noetherian scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R M : Type) [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]

instance symmetricProjective_isNoetherian : AlgebraicGeometry.IsNoetherian (Scheme.BundleCycles.symmetricProjectiveScheme R M) := by
  let : IsLocallyNoetherian (Scheme.BundleCycles.symmetricProjectiveScheme R M) :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.BundleCycles.symmetricProjectiveToBase R M)
  let : CompactSpace (Scheme.BundleCycles.symmetricProjectiveScheme R M) :=
    QuasiCompact.compactSpace_of_compactSpace (Scheme.BundleCycles.symmetricProjectiveToBase R M)
  exact ⟨⟩

end OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Noetherian.BundleCycles
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Noetherian"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion_isClosedImmersion, "theorem"),
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion_range, "theorem"),
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification_isOpenImmersion, "theorem"),
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification_opensRange, "theorem"),
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification_over, "theorem"),
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Proper.BundleCycles.symmetricAlgebra_finiteType, "theorem"),
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Proper.BundleCycles.symmetricProjectiveToBase_isProper, "theorem"),
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Noetherian.BundleCycles.symmetricProjective_isNoetherian, "theorem"),
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricInfinity.Inclusion.BundleCycles.symmetricInfinityInclusion, "definition"),
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.AffineCompactification.BundleCycles.symmetricAffineCompactification, "definition")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "1e13af520cff706c22f830382f7441f2"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:1e13af520cff706c22f830382f7441f2"
