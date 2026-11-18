module
public import SegreVerified.Stage025.EulerCoordinates
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
  out.putStrLn "SEGRE_STAGE Stage031.SegreCharts"
  out.flush

/-!
# The original embedded scheme and the principal projective span theorems

The named sections preserve the original proof stages and local scopes.
-/


section SegreCoordinateTransitions

/-!
# Scheme-level transition identities for normalized Segre coordinates

The identities hold in the entire structure-sheaf rings, including on
nonreduced bases. They are used to glue actual morphisms to projective space;
no equality of morphisms is inferred merely from equality on field points.

-/

set_option autoImplicit false
open scoped Classical BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.CoordinateTransitions

open CategoryTheory AlgebraicGeometry Opposite MvPolynomial
open ProjectiveCech EulerCriticalChart ProjectiveChartSections
open FixedProductCohomology ProductChartSections ProductCoordinatePullback
open scoped ProjectiveChartSections ProductChartSections

universe u

section Factor

variable {K I : Type u} [Field K] [Fintype I] [DecidableEq I]
local notation "Y" => Proj (homogeneousSubmodule I K)

theorem normalizedCoordinate_restrict (p : I) {U V : (Y).Opens}
    (hU : U ≤ coordinateOpen p) (hV : V ≤ U) (a : I) :
    (Y).presheaf.map (homOfLE hV).op (normalizedCoordinate p U hU a) =
      normalizedCoordinate p V (hV.trans hU) a := by
  apply (chartTrivialization p V (hV.trans hU) 1).injective
  change Proj.twistingSheaf.chartSectionsLinearEquiv 1 (X p)
      (isHomogeneous_X (R := K) p) V (hV.trans hU)
      ((Y).presheaf.map (homOfLE hV).op
        ((chartTrivialization p U hU 1).symm (EulerSheaf.coordinateSection a U))) = _
  erw [← Proj.twistingSheaf.res_chartSectionsLinearEquiv (hU := hU),
    LinearEquiv.apply_symm_apply,normalizedCoordinate,LinearEquiv.apply_symm_apply]
  rfl

theorem coordinateSection_restrict (p a : I) (V : (Y).Opens)
    (hV : V ≤ coordinateOpen p) :
    (Y).presheaf.map (homOfLE hV).op
      (ProjectiveChartSections.coordinateSection p a) =
        normalizedCoordinate p V hV a := by
  rw [← EulerPolynomialCoordinates.normalizedCoordinate_eq_fraction]
  exact normalizedCoordinate_restrict p le_rfl hV a

theorem normalizedCoordinate_change (p q : I) (U : (Y).Opens)
    (hp : U ≤ coordinateOpen p) (hq : U ≤ coordinateOpen q) (a : I) :
    normalizedCoordinate p U hp a =
      normalizedCoordinate p U hp q * normalizedCoordinate q U hq a := by
  have hc : EulerSheaf.coordinateSection a U =
      normalizedCoordinate q U hq a • EulerSheaf.coordinateSection q U := by
    have h := (chartTrivialization q U hq 1).apply_symm_apply
      (EulerSheaf.coordinateSection a U)
    dsimp only [chartTrivialization] at h
    erw [Proj.twistingSheaf.chartSectionsLinearEquiv_apply,
      chartGenerator_one_eq_coordinate] at h
    exact h.symm
  calc
    normalizedCoordinate p U hp a =
        (chartTrivialization p U hp 1).symm
          (normalizedCoordinate q U hq a • EulerSheaf.coordinateSection q U) :=
      congrArg (chartTrivialization p U hp 1).symm hc
    _ = normalizedCoordinate q U hq a * normalizedCoordinate p U hp q := by
      rw [map_smul]
      rfl
    _ = normalizedCoordinate p U hp q * normalizedCoordinate q U hq a := mul_comm _ _

def normalizedTransitionUnit (p q : I) (U : (Y).Opens)
    (hp : U ≤ coordinateOpen p) (hq : U ≤ coordinateOpen q) : Γ(Y,U)ˣ where
  val := normalizedCoordinate p U hp q
  inv := normalizedCoordinate q U hq p
  val_inv := by
    simpa only [normalizedCoordinate_pivot] using
      (normalizedCoordinate_change p q U hp hq p).symm
  inv_val := by
    simpa only [normalizedCoordinate_pivot] using
      (normalizedCoordinate_change q p U hq hp q).symm

end Factor

section Product

variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]

local notation "A" => fun i => ProductKoszulVanishing.projectiveScheme K (I i)
set_option quotPrecheck false in local notation "S" => (CoveredScheme.finiteProduct A).scheme

/-- A literal pulled coordinate ratio on any subopen of a standard product
chart. The scalar algebra is the original structure map to Spec K. -/
def factorCoordinate (p : ∀ i,I i) (U : (S).Opens) (hp : U ≤ finiteChart A p)
    (i : Fin (k+1)) (a : I i) : Γ(S,U) :=
  (FixedProductProjections.projection A i).appLE (coordinateOpen (p i)) U
    (hp.trans (finiteChart_le_preimage A p i))
    (ProjectiveChartSections.coordinateSection (p i) a)

@[simp] theorem factorCoordinate_pivot (p : ∀ i,I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) (i : Fin (k+1)) :
    factorCoordinate K I p U hp i (p i)=1 := by
  dsimp only [factorCoordinate]
  rw [ProjectiveChartSections.coordinateSection_pivot]
  exact map_one ((FixedProductProjections.projection A i).appLE
    (coordinateOpen (p i)) U (hp.trans (finiteChart_le_preimage A p i))).hom

theorem factorCoordinate_restrict (p : ∀ i,I i) {U V : (S).Opens}
    (hp : U ≤ finiteChart A p) (h : V ≤ U) (i : Fin (k+1)) (a : I i) :
    (S).presheaf.map (homOfLE h).op (factorCoordinate K I p U hp i a)=
      factorCoordinate K I p V (h.trans hp) i a := by
  exact congrArg (fun f => f (ProjectiveChartSections.coordinateSection (p i) a))
    (Scheme.Hom.appLE_map (FixedProductProjections.projection A i)
      (hp.trans (finiteChart_le_preimage A p i)) (homOfLE h).op)

theorem factorCoordinate_on_intersection (p q : ∀ i,I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) (hq : U ≤ finiteChart A q)
    (i : Fin (k+1)) (a : I i) :
    factorCoordinate K I p U hp i a =
      (FixedProductProjections.projection A i).appLE
        (coordinateOpen (p i) ⊓ coordinateOpen (q i)) U
        (le_inf (hp.trans (finiteChart_le_preimage A p i))
          (hq.trans (finiteChart_le_preimage A q i)))
        (normalizedCoordinate (p i)
          (coordinateOpen (p i) ⊓ coordinateOpen (q i)) inf_le_left a) := by
  rw [← coordinateSection_restrict]
  exact (congrArg (fun f => f (ProjectiveChartSections.coordinateSection (p i) a))
    (Scheme.Hom.map_appLE
      (U := coordinateOpen (p i) ⊓ coordinateOpen (q i))
      (U' := coordinateOpen (p i)) (V := U)
      (FixedProductProjections.projection A i)
      (le_inf (hp.trans (finiteChart_le_preimage A p i))
        (hq.trans (finiteChart_le_preimage A q i)))
      (homOfLE inf_le_left).op)).symm

theorem factorCoordinate_change (p q : ∀ i,I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) (hq : U ≤ finiteChart A q)
    (i : Fin (k+1)) (a : I i) :
    factorCoordinate K I p U hp i a =
      factorCoordinate K I p U hp i (q i) * factorCoordinate K I q U hq i a := by
  let V := coordinateOpen (K := K) (p i) ⊓ coordinateOpen (q i)
  let h : U ≤ (FixedProductProjections.projection A i) ⁻¹ᵁ V :=
    le_inf (hp.trans (finiteChart_le_preimage A p i))
      (hq.trans (finiteChart_le_preimage A q i))
  have hq' : factorCoordinate K I q U hq i a =
      (FixedProductProjections.projection A i).appLE V U h
        (normalizedCoordinate (q i) V inf_le_right a) := by
    rw [← coordinateSection_restrict]
    exact (congrArg (fun f => f (ProjectiveChartSections.coordinateSection (q i) a))
      (Scheme.Hom.map_appLE (U := V) (U' := coordinateOpen (q i)) (V := U)
        (FixedProductProjections.projection A i) h
        (homOfLE inf_le_right).op)).symm
  rw [factorCoordinate_on_intersection K I p q U hp hq i a,
    factorCoordinate_on_intersection K I p q U hp hq i (q i),hq']
  erw [← map_mul]
  exact congrArg ((FixedProductProjections.projection A i).appLE V U h)
    (normalizedCoordinate_change (p i) (q i) V inf_le_left inf_le_right a)

/-- The actual normalized coordinate of a pure tensor. -/
def tensorCoordinate (p : ∀ i,I i) (U : (S).Opens) (hp : U ≤ finiteChart A p)
    (a : ∀ i,I i) : Γ(S,U) := ∏ i,factorCoordinate K I p U hp i (a i)

@[simp] theorem tensorCoordinate_pivot (p : ∀ i,I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) : tensorCoordinate K I p U hp p=1 := by
  simp [tensorCoordinate]

theorem tensorCoordinate_restrict (p : ∀ i,I i) {U V : (S).Opens}
    (hp : U ≤ finiteChart A p) (h : V ≤ U) (a : ∀ i,I i) :
    (S).presheaf.map (homOfLE h).op (tensorCoordinate K I p U hp a)=
      tensorCoordinate K I p V (h.trans hp) a := by
  simp only [tensorCoordinate,map_prod,factorCoordinate_restrict]

theorem tensorCoordinate_change (p q : ∀ i,I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) (hq : U ≤ finiteChart A q) (a : ∀ i,I i) :
    tensorCoordinate K I p U hp a =
      tensorCoordinate K I p U hp q * tensorCoordinate K I q U hq a := by
  unfold tensorCoordinate
  calc
    (∏ i, factorCoordinate K I p U hp i (a i)) =
        ∏ i, (factorCoordinate K I p U hp i (q i) *
          factorCoordinate K I q U hq i (a i)) :=
      Finset.prod_congr rfl (fun i _ => factorCoordinate_change K I p q U hp hq i (a i))
    _ = _ := Finset.prod_mul_distrib

/-- The transition scalar is a unit in the entire overlap ring. -/
def transitionUnit (p q : ∀ i,I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) (hq : U ≤ finiteChart A q) : Γ(S,U)ˣ where
  val := tensorCoordinate K I p U hp q
  inv := tensorCoordinate K I q U hq p
  val_inv := by
    simpa only [tensorCoordinate_pivot] using
      (tensorCoordinate_change K I p q U hp hq p).symm
  inv_val := by
    simpa only [tensorCoordinate_pivot] using
      (tensorCoordinate_change K I q p U hq hp q).symm

/-- The full homogeneous-coordinate ring map, not just its values on points. -/
def coordinateHom (p : ∀ i,I i) (U : (S).Opens) (hp : U ≤ finiteChart A p) :
    MvPolynomial (∀ i,I i) K →+* Γ(S,U) :=
  MvPolynomial.eval₂Hom (algebraMap K Γ(S,U)) (tensorCoordinate K I p U hp)

@[simp] theorem coordinateHom_X (p : ∀ i,I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) (a : ∀ i,I i) :
    coordinateHom K I p U hp (X a)=tensorCoordinate K I p U hp a := by
  simp [coordinateHom]

theorem coordinateHom_restrict (p : ∀ i,I i) {U V : (S).Opens}
    (hp : U ≤ finiteChart A p) (h : V ≤ U) :
    ((S).presheaf.map (homOfLE h).op).hom.comp (coordinateHom K I p U hp)=
      coordinateHom K I p V (h.trans hp) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, coordinateHom, MvPolynomial.eval₂Hom_C]
    change (S).presheaf.map (homOfLE h).op (algebraMap K Γ(S,U) c)=
      algebraMap K Γ(S,V) c
    exact (congrArg (fun f => f c)
      (((S).baseRingToStructurePresheaf K).naturality (homOfLE h).op)).symm
  · intro a
    simp only [RingHom.comp_apply,coordinateHom_X,tensorCoordinate_restrict]

theorem coordinateHom_change (p q : ∀ i,I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) (hq : U ≤ finiteChart A q)
    (d : ℕ) (f : MvPolynomial (∀ i,I i) K)
    (hf : f ∈ homogeneousSubmodule (∀ i,I i) K d) :
    coordinateHom K I p U hp f =
      (transitionUnit K I p q U hp hq : Γ(S,U))^d *
        coordinateHom K I q U hq f := by
  have hpoint : tensorCoordinate K I p U hp =
      fun a => (transitionUnit K I p q U hp hq : Γ(S,U))*
        tensorCoordinate K I q U hq a := by
    funext a
    exact tensorCoordinate_change K I p q U hp hq a
  change MvPolynomial.eval₂ (algebraMap K Γ(S,U)) (tensorCoordinate K I p U hp) f=_
  rw [hpoint]
  exact (show f.IsHomogeneous d from hf).eval₂_const_mul
    (algebraMap K Γ(S,U)) (tensorCoordinate K I q U hq)
    (transitionUnit K I p q U hp hq : Γ(S,U))

end Product
end PaperVerification.Segre.CoordinateTransitions

end SegreCoordinateTransitions

section SegreEmbeddingChart

/-!
# Surjective affine chart maps for the actual Segre coordinates

The ambient projective coordinate indexed by a cell is the product of its
factor coordinates. On the chart with pivot `p`, this gives an algebra map
from the ambient affine polynomial ring to the product-chart polynomial
ring. Each product-chart variable is recovered by changing exactly one
entry of `p`. Consequently the map has an explicit polynomial right inverse
and is surjective. The final statements retain the actual degree-zero
homogeneous localization used by the ambient projective chart.

These are algebraic chart statements; the global scheme morphism and its
closed-immersion proof are constructed separately.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.SegreEmbeddingChart

open Staircase Monomials ProjectiveCharts ProjectivePointSpan AllFactorPointSpan
open MvPolynomial
open scoped BigOperators

variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K] {n : I → ℕ}

/-- The affine coordinates of the ambient projective tensor chart. -/
abbrev AmbientChartVar (p : Cell n) := {v : Cell n // v ≠ p}

/-- The Segre coordinate is literally the product of the normalized factors. -/
theorem chartSegreCoordinate_eq_prod (p v : Cell n) :
    chartSegreCoordinate (K := K) p v =
      ∏ i, chartPolynomial p ⟨i, v i⟩ := by
  rw [chartSegreCoordinate, cellPolynomial_eq_prod, map_prod]
  simp only [chartSubstitution, aeval_X]

@[simp] theorem chartSegreCoordinate_pivot (p : Cell n) :
    chartSegreCoordinate (K := K) p p = 1 := by
  rw [chartSegreCoordinate_eq_prod]
  simp [chartPolynomial]

/-- A cell differing from the pivot at just one factor recovers that factor's
free affine coordinate, including when some other factors are points. -/
theorem chartSegreCoordinate_update (p : Cell n) (i : I)
    (a : Fin (n i + 1)) (ha : a ≠ p i) :
    chartSegreCoordinate (K := K) p (Function.update p i a) =
      X (⟨⟨i, a⟩, ha⟩ : ChartVar p) := by
  classical
  rw [chartSegreCoordinate_eq_prod]
  calc
    (∏ j, chartPolynomial (K := K) p ⟨j, (Function.update p i a) j⟩) =
        chartPolynomial p ⟨i, a⟩ := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hji
        rw [Function.update_of_ne hji]
        simp [chartPolynomial]
      · simp
    _ = X (⟨⟨i, a⟩, ha⟩ : ChartVar p) := by
      simp [chartPolynomial, ha]

/-- The ambient coordinate selected to recover a given product coordinate. -/
def changedCell (p : Cell n) (q : ChartVar p) : AmbientChartVar p :=
  ⟨Function.update p q.val.1 q.val.2, by
    intro h
    exact q.property (by simpa using congrFun h q.val.1)⟩

@[simp] theorem changedCell_value (p : Cell n) (q : ChartVar p) :
    (changedCell p q).val = Function.update p q.val.1 q.val.2 := rfl

@[simp] theorem chartSegreCoordinate_changedCell (p : Cell n) (q : ChartVar p) :
    chartSegreCoordinate (K := K) p (changedCell p q).val = X q := by
  exact chartSegreCoordinate_update p q.val.1 q.val.2 q.property

/-- Pullback of all ambient affine coordinates by the literal Segre formulas. -/
def affinePullback (p : Cell n) :
    MvPolynomial (AmbientChartVar p) K →ₐ[K] MvPolynomial (ChartVar p) K :=
  aeval (fun v => chartSegreCoordinate p v.val)

@[simp] theorem affinePullback_X (p : Cell n) (v : AmbientChartVar p) :
    affinePullback (K := K) p (X v) = chartSegreCoordinate p v.val :=
  aeval_X _ _

@[simp] theorem affinePullback_changedCell (p : Cell n) (q : ChartVar p) :
    affinePullback (K := K) p (X (changedCell p q)) = X q := by
  rw [affinePullback_X, chartSegreCoordinate_changedCell]

/-- The explicit polynomial lift of each free factor coordinate. This is a
right inverse of the coordinate-ring pullback, not a presumed inverse scheme map. -/
def coordinateSection (p : Cell n) :
    MvPolynomial (ChartVar p) K →ₐ[K] MvPolynomial (AmbientChartVar p) K :=
  aeval (fun q => X (changedCell p q))

@[simp] theorem coordinateSection_X (p : Cell n) (q : ChartVar p) :
    coordinateSection (K := K) p (X q) = X (changedCell p q) :=
  aeval_X _ _

theorem affinePullback_comp_coordinateSection (p : Cell n) :
    (affinePullback (K := K) p).comp (coordinateSection p) =
      AlgHom.id K (MvPolynomial (ChartVar p) K) := by
  apply MvPolynomial.algHom_ext
  intro q
  simp only [AlgHom.comp_apply, coordinateSection_X,
    affinePullback_changedCell, AlgHom.id_apply]

@[simp] theorem affinePullback_coordinateSection (p : Cell n)
    (f : MvPolynomial (ChartVar p) K) :
    affinePullback p (coordinateSection p f) = f :=
  AlgHom.congr_fun (affinePullback_comp_coordinateSection p) f

theorem affinePullback_surjective (p : Cell n) :
    Function.Surjective (affinePullback (K := K) p) := by
  intro f
  exact ⟨coordinateSection p f, affinePullback_coordinateSection p f⟩

/-- The pivot and every off-pivot coordinate follow the same homogeneous
normalization convention as the actual ambient projective chart. -/
theorem affinePullback_normalizedVariable (p v : Cell n) :
    affinePullback (K := K) p (PolynomialChartRing.normalizedVariable p v) =
      chartSegreCoordinate p v := by
  classical
  by_cases hv : v = p
  · subst v
    simp
  · simp [PolynomialChartRing.normalizedVariable, hv]

/-- Normalizing the ambient homogeneous variables and applying the affine
pullback is precisely substitution by the literal Segre monomials. -/
theorem affinePullback_comp_normalizeCoordinates (p : Cell n) :
    (affinePullback (K := K) p).comp (PolynomialChartRing.normalizeCoordinates p) =
      aeval (chartSegreCoordinate p) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, PolynomialChartRing.normalizeCoordinates_X,
    affinePullback_normalizedVariable, aeval_X]

/-- The homogeneous linear polynomial belonging to an original tensor
covector. Its coefficients are values on the standard tensor basis. -/
def ambientLinearPolynomial (φ : Module.Dual K (Matrix (Cell n) Unit K)) :
    MvPolynomial (Cell n) K :=
  ∑ v, C (φ (coordinateTensor v ())) * X v

/-- The ambient polynomial really is the original tensor covector on
every tensor, before any Segre substitution or projective normalization. -/
theorem eval_ambientLinearPolynomial
    (φ : Module.Dual K (Matrix (Cell n) Unit K)) (B : Matrix (Cell n) Unit K) :
    MvPolynomial.eval (fun v => B v ()) (ambientLinearPolynomial φ) = φ B := by
  rw [ambientLinearPolynomial, map_sum]
  simp only [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  conv_rhs => rw [tensor_coordinate_expansion B]
  simp only [Fintype.sum_unique, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

/-- Pullback of an arbitrary ambient linear form agrees with the independently
defined chart restriction used in the singular-span argument. -/
theorem affinePullback_ambientLinearPolynomial (p : Cell n)
    (φ : Module.Dual K (Matrix (Cell n) Unit K)) :
    affinePullback p
      (PolynomialChartRing.normalizeCoordinates p (ambientLinearPolynomial φ)) =
        AllFactorPointSpan.chartRestriction p φ := by
  simp only [ambientLinearPolynomial, AllFactorPointSpan.chartRestriction,
    map_sum, map_mul, PolynomialChartRing.normalizeCoordinates_X,
    MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
    affinePullback_normalizedVariable]
  rfl

/-- One defining equation of the ambient critical linear subspace, in the
actual ambient affine projective chart. -/
def ambientAffineCriticalPolynomial (A : Matrix (Cell n) Unit K)
    (p : Cell n) (q : CriticalGraph.CriticalIndex n) :
    MvPolynomial (AmbientChartVar p) K :=
  PolynomialChartRing.normalizeCoordinates p
    (ambientLinearPolynomial ((LinearMap.proj q).comp (CriticalGraph.criticalOperator A)))

@[simp] theorem affinePullback_ambientAffineCriticalPolynomial
    (A : Matrix (Cell n) Unit K) (p : Cell n) (q : CriticalGraph.CriticalIndex n) :
    affinePullback p (ambientAffineCriticalPolynomial A p q) =
      AllFactorPointSpan.chartCriticalPolynomial A p q :=
  affinePullback_ambientLinearPolynomial p
    ((LinearMap.proj q).comp (CriticalGraph.criticalOperator A))

/-- The entire affine ideal of the ambient critical linear subspace. -/
def ambientAffineCriticalIdeal (A : Matrix (Cell n) Unit K) (p : Cell n) :
    Ideal (MvPolynomial (AmbientChartVar p) K) :=
  Ideal.span (Set.range (ambientAffineCriticalPolynomial A p))

/-- The whole ambient critical ideal pulls back to the whole intrinsic
critical ideal. No radical, point-set replacement, or reducedness is used. -/
theorem map_ambientAffineCriticalIdeal (A : Matrix (Cell n) Unit K) (p : Cell n) :
    Ideal.map (affinePullback p).toRingHom (ambientAffineCriticalIdeal A p) =
      AllFactorPointSpan.chartCriticalIdeal A p := by
  rw [ambientAffineCriticalIdeal, AllFactorPointSpan.chartCriticalIdeal, Ideal.map_span]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨g, ⟨q, rfl⟩, rfl⟩
    exact ⟨q, (affinePullback_ambientAffineCriticalPolynomial A p q).symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨ambientAffineCriticalPolynomial A p q, ⟨q, rfl⟩,
      affinePullback_ambientAffineCriticalPolynomial A p q⟩

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The same pullback with domain the actual degree-zero homogeneous
localization defining the ambient projective chart. -/
def homogeneousChartPullback (p : Cell n) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Cell n) K) (X p) →ₐ[K]
      MvPolynomial (ChartVar p) K :=
  (affinePullback p).comp (PolynomialChartRing.awayEquivPolynomial p).toAlgHom

theorem homogeneousChartPullback_surjective (p : Cell n) :
    Function.Surjective (homogeneousChartPullback (K := K) p) :=
  (affinePullback_surjective p).comp
    (PolynomialChartRing.awayEquivPolynomial (K := K) p).surjective

/-- Every homogeneous coordinate ratio has its intended Segre pullback. -/
@[simp] theorem homogeneousChartPullback_coordinate (p v : Cell n) :
    homogeneousChartPullback (K := K) p
      (PaperVerification.HomogeneousChartDehomogenization.fraction
        (homogeneousSubmodule (Cell n) K) (isHomogeneous_X (R := K) p) 1
        ⟨X v, isHomogeneous_X (R := K) v⟩) = chartSegreCoordinate p v := by
  change affinePullback p
    (PolynomialChartRing.awayEquivPolynomial p
      (PaperVerification.HomogeneousChartDehomogenization.fraction
        (homogeneousSubmodule (Cell n) K) (isHomogeneous_X (R := K) p) 1
        ⟨X v, isHomogeneous_X (R := K) v⟩)) = _
  rw [PolynomialChartRing.awayEquivPolynomial_coordinate,
    affinePullback_normalizedVariable]

end PaperVerification.Segre.SegreEmbeddingChart

end SegreEmbeddingChart

section SegreSchemeMorphism

/-!
# The actual Segre morphism of schemes

Each map is the map on spectra of the literal homogeneous-localization
homomorphism. The overlap proof compares those ring homomorphisms through
the actual transition unit. The resulting global map therefore retains
the complete structure sheaves, not merely the field-valued points.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.SegreSchemeMorphism

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MvPolynomial
open HomogeneousLocalization FixedProductCohomology ProductChartSections
open CoordinateTransitions
open scoped ProjectiveChartSections ProductChartSections

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]

local notation "A" => fun i => ProductKoszulVanishing.projectiveScheme K (I i)
set_option quotPrecheck false in local notation "S" => (CoveredScheme.finiteProduct A).scheme
set_option quotPrecheck false in local notation "𝒜" => homogeneousSubmodule (∀ i,I i) K
local notation "P" => Proj 𝒜
attribute [local instance] MvPolynomial.gradedAlgebra

theorem pivotUnit (p : ∀ i,I i) (U : (S).Opens) (hp : U ≤ finiteChart A p) :
    IsUnit (coordinateHom K I p U hp (X p)) := by
  rw [coordinateHom_X,tensorCoordinate_pivot]
  exact isUnit_one

/-- The actual pullback homomorphism from the ambient standard Proj chart. -/
def chartLift (p : ∀ i,I i) (U : (S).Opens) (hp : U ≤ finiteChart A p) :
    Away 𝒜 (X p) →+* Γ(S,U) :=
  Away.lift 𝒜 (coordinateHom K I p U hp) (pivotUnit K I p U hp)

theorem chartLift_coordinate (p : ∀ i,I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) (a : ∀ i,I i) :
    chartLift K I p U hp
      (Away.mk 𝒜 (isHomogeneous_X (R := K) p) 1 (X a) (by simpa using isHomogeneous_X (R := K) a)) =
        tensorCoordinate K I p U hp a := by
  have hu : (pivotUnit K I p U hp).unit=1 := by
    apply Units.ext
    simp only [IsUnit.unit_spec,Units.val_one,coordinateHom_X,tensorCoordinate_pivot]
  dsimp only [chartLift]
  erw [Away.lift_mk, hu]
  simp only [one_pow,inv_one,Units.val_one,
    mul_one,coordinateHom_X]

theorem chartLift_restrict (p : ∀ i,I i) {U V : (S).Opens}
    (hp : U ≤ finiteChart A p) (h : V ≤ U) :
    ((S).presheaf.map (homOfLE h).op).hom.comp (chartLift K I p U hp)=
      chartLift K I p V (h.trans hp) := by
  unfold chartLift
  rw [RingHom.comp_homogeneousLocalizationAwayLift]
  simp only [coordinateHom_restrict]

/-- An actual morphism from any subopen of a standard product chart. -/
def localMorphism (p : ∀ i,I i) (U : (S).Opens) (hp : U ≤ finiteChart A p) :
    U.toScheme ⟶ P :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartLift K I p U hp)) ≫
    Proj.awayι 𝒜 (X p) (isHomogeneous_X (R := K) p) one_pos

@[reassoc] theorem localMorphism_restrict (p : ∀ i,I i) {U V : (S).Opens}
    (hp : U ≤ finiteChart A p) (h : V ≤ U) :
    (S).homOfLE h ≫ localMorphism K I p U hp =
      localMorphism K I p V (h.trans hp) := by
  unfold localMorphism
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc,
    ← Spec.map_comp_assoc]
  congr 2
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact chartLift_restrict K I p hp h

/-- Two systems of normalized Segre coordinates induce the same actual
scheme morphism on their common domain. -/
theorem localMorphism_change (p q : ∀ i,I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) (hq : U ≤ finiteChart A q) :
    localMorphism K I p U hp=localMorphism K I q U hq := by
  have hqp : IsUnit (coordinateHom K I q U hq (X p)) := by
    rw [coordinateHom_X]
    exact (transitionUnit K I q p U hq hp).isUnit
  have hlift : chartLift K I p U hp =
      Away.lift 𝒜 (coordinateHom K I q U hq) hqp :=
    Away.lift_eq_of_forall_mem (coordinateHom K I q U hq)
      (coordinateHom K I p U hp) (transitionUnit K I p q U hp hq)
      (coordinateHom_change K I p q U hp hq) (isHomogeneous_X (R := K) p)
      (pivotUnit K I p U hp) hqp
  unfold localMorphism
  rw [hlift]
  exact congrArg (fun f => U.toSpecΓ ≫ f)
    (Proj.SpecMap_awayLift_awayι_eq («𝒜» := 𝒜)
      (coordinateHom K I q U hq) (isHomogeneous_X (R := K) p) one_pos
      (isHomogeneous_X (R := K) q) one_pos hqp (pivotUnit K I q U hq))

/-- Every standard product chart occurs in the actual scheme cover. -/
def chartCover : (S).OpenCover :=
  (S).openCoverOfIsOpenCover (finiteChart A)
    (TopologicalSpace.IsOpenCover.mk (finiteChart_cover A))

theorem localMorphism_compatible (p q : ∀ i,I i) :
    pullback.fst ((chartCover K I).f p) ((chartCover K I).f q) ≫
        localMorphism K I p (finiteChart A p) le_rfl =
      pullback.snd ((chartCover K I).f p) ((chartCover K I).f q) ≫
        localMorphism K I q (finiteChart A q) le_rfl := by
  let H := isPullback_opens_inf (finiteChart A p) (finiteChart A q)
  apply (cancel_epi H.isoPullback.hom).1
  calc
    _ = (S).homOfLE inf_le_left ≫
        localMorphism K I p (finiteChart A p) le_rfl :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ localMorphism K I p (finiteChart A p) le_rfl)
          H.isoPullback_hom_fst)
    _ = localMorphism K I p (finiteChart A p ⊓ finiteChart A q) inf_le_left :=
      localMorphism_restrict K I p le_rfl inf_le_left
    _ = localMorphism K I q (finiteChart A p ⊓ finiteChart A q) inf_le_right :=
      localMorphism_change K I p q _ inf_le_left inf_le_right
    _ = (S).homOfLE inf_le_right ≫
        localMorphism K I q (finiteChart A q) le_rfl :=
      (localMorphism_restrict K I q le_rfl inf_le_right).symm
    _ = _ :=
      (congrArg (fun f => f ≫ localMorphism K I q (finiteChart A q) le_rfl)
        H.isoPullback_hom_snd.symm).trans (Category.assoc _ _ _)

/-- The genuine Segre morphism into the projective space with one homogeneous
coordinate for each original tensor basis element. -/
def morphism : S ⟶ P :=
  (chartCover K I).glueMorphisms
    (fun p => localMorphism K I p (finiteChart A p) le_rfl)
    (localMorphism_compatible K I)

@[reassoc] theorem chart_ι_morphism (p : ∀ i,I i) :
    (finiteChart A p).ι ≫ morphism K I =
      localMorphism K I p (finiteChart A p) le_rfl :=
  (chartCover K I).ι_glueMorphisms _ _ p

theorem localMorphism_preimage_coordinate (p q : ∀ i,I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) :
    localMorphism K I p U hp ⁻¹ᵁ ProjectiveCech.coordinateOpen q =
      U.ι ⁻¹ᵁ (S).basicOpen (tensorCoordinate K I p U hp q) := by
  change U.toSpecΓ ⁻¹ᵁ Spec.map (CommRingCat.ofHom (chartLift K I p U hp)) ⁻¹ᵁ
      (Proj.awayι 𝒜 (X p) (isHomogeneous_X (R := K) p) one_pos ⁻¹ᵁ
        ProjectiveCech.coordinateOpen q) = _
  erw [Proj.awayι_preimage_basicOpen 𝒜 (isHomogeneous_X (R := K) p) one_pos
      (isHomogeneous_X (R := K) q) one_pos, SpecMap_preimage_basicOpen]
  have h : chartLift K I p U hp
      (Away.isLocalizationElem (isHomogeneous_X (R := K) p) (isHomogeneous_X (R := K) q)) =
        tensorCoordinate K I p U hp q := by
    simpa only [Away.isLocalizationElem,pow_one] using
      chartLift_coordinate K I p U hp q
  erw [h, Scheme.Opens.toSpecΓ_preimage_basicOpen]

end PaperVerification.Segre.SegreSchemeMorphism

end SegreSchemeMorphism

section SegreEmbeddingChartOpens

/-!
# Exact basic-open preimages of Segre coordinate functions

A normalized tensor coordinate is invertible precisely when all of its
factor coordinates are invertible. The resulting open is the intersection
of the two actual product charts. This uses structure-sheaf functions and
their basic opens, not just field-valued points, and supplies the open-domain
identity needed to prove the global Segre morphism is a closed immersion.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.SegreEmbeddingChartOpens

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MvPolynomial
open FixedProductCohomology FixedProductProjections ProductChartSections
open ProductCoordinatePullback ProjectiveCech CoordinateTransitions
open scoped ProjectiveChartSections ProductChartSections

universe u

section GeneralProduct

variable {K : Type u} [Field K]

/-- Membership in all factor-chart preimages gives membership in the actual
recursively constructed rectangle chart. -/
theorem mem_finiteChart_of_forall {k : ℕ} (A : Fin (k+1) → CoveredScheme K)
    (p : ∀ i, (A i).index) (x : (CoveredScheme.finiteProduct A).scheme)
    (hx : ∀ i, projection A i x ∈ (A i).opens (p i)) :
    x ∈ finiteChart A p := by
  induction k with
  | zero => exact hx 0
  | succ k ih =>
      let Atail := fun i : Fin (k+1) => A i.succ
      let ptail := fun i : Fin (k+1) => p i.succ
      let B := CoveredScheme.finiteProduct Atail
      change
        x ∈ pullback.fst (A 0).toBase B.toBase ⁻¹ᵁ (A 0).opens (p 0) ∧
          x ∈ pullback.snd (A 0).toBase B.toBase ⁻¹ᵁ finiteChart Atail ptail
      refine ⟨hx 0, ?_⟩
      exact ih Atail ptail ((pullback.snd (A 0).toBase B.toBase) x)
        (fun i => hx i.succ)

/-- The fixed iterated fibre product's chart has precisely the intended
factorwise membership condition. -/
theorem mem_finiteChart_iff {k : ℕ} (A : Fin (k+1) → CoveredScheme K)
    (p : ∀ i, (A i).index) (x : (CoveredScheme.finiteProduct A).scheme) :
    x ∈ finiteChart A p ↔ ∀ i, projection A i x ∈ (A i).opens (p i) := by
  constructor
  · intro hx i
    exact finiteChart_le_preimage A p i hx
  · exact mem_finiteChart_of_forall A p x

/-- The entire chart open is the finite intersection of the actual factor
chart preimages along the fixed projections. -/
theorem finiteChart_eq_iInf {k : ℕ} (A : Fin (k+1) → CoveredScheme K)
    (p : ∀ i, (A i).index) :
    finiteChart A p = ⨅ i, projection A i ⁻¹ᵁ (A i).opens (p i) := by
  apply TopologicalSpace.Opens.ext
  rw [TopologicalSpace.Opens.coe_iInf]
  ext x
  change (x ∈ finiteChart A p) ↔
    x ∈ ⋂ i, (projection A i ⁻¹ᵁ (A i).opens (p i) : Set _)
  rw [mem_finiteChart_iff, Set.mem_iInter]
  rfl

end GeneralProduct

section BasicOpenProduct

/-- On the common domain of finitely many sections, the product is a unit
exactly where every factor is a unit. The empty product is included. -/
theorem mem_basicOpen_finset_prod (X : Scheme.{u}) (U : X.Opens)
    {J : Type*} (s : Finset J) (f : J → Γ(X,U)) (x : X) (hx : x ∈ U) :
    x ∈ X.basicOpen (∏ j ∈ s, f j) ↔ ∀ j ∈ s, x ∈ X.basicOpen (f j) := by
  induction s using Finset.induction_on with
  | empty => simp [hx]
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha, Scheme.basicOpen_mul,
        TopologicalSpace.Opens.mem_inf, ih, Finset.forall_mem_insert]

end BasicOpenProduct

section ProjectiveFactor

variable {K I : Type u} [Field K] [Fintype I] [DecidableEq I]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The function X_a/X_p is invertible on exactly the intersection of the
two genuine projective charts. -/
theorem basicOpen_coordinateSection (p a : I) :
    (Proj (homogeneousSubmodule I K)).basicOpen
      (ProjectiveChartSections.coordinateSection (K := K) p a) =
        coordinateOpen p ⊓ coordinateOpen a := by
  simpa only [ProjectiveChartSections.coordinateSection,
    PaperVerification.HomogeneousChartDehomogenization.fraction,
    Proj.basicOpen_mul, coordinateOpen] using
      (Proj.basicOpen_awayToSection_mk
        (𝒜 := homogeneousSubmodule I K) (isHomogeneous_X (R := K) p) 1 (X a)
        (by simpa using (isHomogeneous_X (R := K) a)))

end ProjectiveFactor

section ProjectiveProduct

variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

local notation "A" => fun i => ProductKoszulVanishing.projectiveScheme K (I i)
set_option quotPrecheck false in local notation "S" => (CoveredScheme.finiteProduct A).scheme

/-- The basic open of an actual pulled coordinate ratio is its source open
intersected with the indicated factor-chart preimage. -/
theorem basicOpen_factorCoordinate (p : ∀ i, I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) (i : Fin (k+1)) (a : I i) :
    (S).basicOpen (factorCoordinate K I p U hp i a) =
      U ⊓ projection A i ⁻¹ᵁ coordinateOpen a := by
  erw [factorCoordinate, Scheme.basicOpen_appLE, basicOpen_coordinateSection,
    Scheme.Hom.preimage_inf, ← inf_assoc,
    inf_eq_left.mpr (hp.trans (finiteChart_le_preimage A p i))]

/-- A normalized Segre coordinate at `q` is invertible precisely on the
intersection with the full product chart `q`. This holds on every subopen
of the source chart, without a reducedness assumption. -/
theorem basicOpen_tensorCoordinate (p q : ∀ i, I i) (U : (S).Opens)
    (hp : U ≤ finiteChart A p) :
    (S).basicOpen (tensorCoordinate K I p U hp q) = U ⊓ finiteChart A q := by
  ext x
  by_cases hx : x ∈ U
  · erw [tensorCoordinate,
      mem_basicOpen_finset_prod S U Finset.univ
        (fun i => factorCoordinate K I p U hp i (q i)) x hx,
      TopologicalSpace.Opens.mem_inf, mem_finiteChart_iff]
    simp only [Finset.mem_univ, forall_const, basicOpen_factorCoordinate,
      TopologicalSpace.Opens.mem_inf, hx, true_and, Scheme.Hom.mem_preimage]
    rfl
  · constructor
    · intro h
      exact False.elim (hx ((S).basicOpen_le _ h))
    · intro h
      exact False.elim (hx h.1)

/-- In particular, the inverse image of the ambient tensor chart `q`,
computed from the source chart `p`, is their actual chart intersection. -/
theorem basicOpen_tensorCoordinate_chart (p q : ∀ i, I i) :
    (S).basicOpen (tensorCoordinate K I p (finiteChart A p) le_rfl q) =
      finiteChart A p ⊓ finiteChart A q :=
  basicOpen_tensorCoordinate K I p q (finiteChart A p) le_rfl

end ProjectiveProduct

end PaperVerification.Segre.SegreEmbeddingChartOpens

end SegreEmbeddingChartOpens

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
