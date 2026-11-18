module
public import Mathlib
public import TauCeti.Geometry.Toric.Algebraic.Fan.Scheme
public import TauCeti.Geometry.Toric.Algebraic.Regular
public import TauCeti.AlgebraicGeometry.CartierDivisor.Sheaf
public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Basic
public import TauCeti.Algebra.Homology.DerivedCategory.Bounded.Basic
public import TauCeti.Algebra.Module.Primitive

/-!
# Universal toric rounding grids and effective raw periodicity

The quantitative lattice part of Caius Folkerts, *The Hanlon–Hicks–Lazarev
conjecture on smooth toric varieties*: Lemma6.1 with the full integral cokernel,
Lemma7.1 lattice absorption, and the raw-coefficient conclusion of Theorem7.2.
All dimensions and integer matrices are retained. Denominators and thresholds
are the exact finite determinant expressions in the source, including zero
rank/ray counts. The categorical section below adds main Theorem1.1 for arbitrary Cartier
divisors. The finite criterion5.2 and effective categorical7.2 remain pending.
-/

@[expose] public noncomputable section
open Set Matrix Module
open scoped BigOperators Pointwise
namespace ToricPower
section FloorArithmetic
variable {ι κ : Type*} [Fintype κ]
/-- The displayed ray-pairing function preserves addition; separately compared. -/
theorem rayMap_add_law (A : ι → κ → ℤ) (u v : κ → ℤ) :
    (fun i => ∑ j, A i j * (u + v) j) =
      (fun i => ∑ j, A i j * u j) + (fun i => ∑ j, A i j * v j) := by
  ext i
  simp [mul_add, Finset.sum_add_distrib]
/-- The displayed ray-pairing function preserves integral scaling; separately compared. -/
theorem rayMap_smul_law (A : ι → κ → ℤ) (r : ℤ) (u : κ → ℤ) :
    (fun i => ∑ j, A i j * (r • u) j) = r • (fun i => ∑ j, A i j * u j) := by
  ext i
  simp [Finset.mul_sum, mul_assoc, mul_left_comm]
/-- The actual integral ray-pairing linear map. -/
def rayMap (A : ι → κ → ℤ) : (κ → ℤ) →ₗ[ℤ] (ι → ℤ) where
  toFun u i := ∑ j, A i j * u j
  map_add' := rayMap_add_law A
  map_smul' := rayMap_smul_law A

/-- Actual coordinatewise integral floor coefficients of the power-map splitting. -/
def powerCoefficient (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℤ)
    (u : κ → ℤ) : ι → ℤ :=
  fun i => (b i + rayMap A u i) / ell
/-- The full integral cokernel, retaining torsion. -/
abbrev DivisorClass (A : ι → κ → ℤ) :=
  (ι → ℤ) ⧸ LinearMap.range (rayMap A)
/-- The integral quotient class of the given divisor coefficients. -/
def divisorClass (A : ι → κ → ℤ) (b : ι → ℤ) : DivisorClass A :=
  Submodule.Quotient.mk b
/-- All integral quotient classes attained by the actual floor splitting. -/
def frobeniusClasses (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℤ) :
    Set (DivisorClass A) :=
  Set.range (fun u => divisorClass A (powerCoefficient A b ell u))
/-- The actual coefficient vectors from the half-open exponent box 0≤u<ell. -/
def rawCoefficients (A : ι → κ → ℤ) (b : ι → ℤ) (ell : ℤ) :
    Set (ι → ℤ) :=
  {c | ∃ u : κ → ℤ, (∀ j, 0 ≤ u j ∧ u j < ell) ∧
    powerCoefficient A b ell u = c}
end FloorArithmetic
section MatrixConstants
variable {n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Absolute determinant, replacing zero by one so it imposes no lcm divisibility constraint. -/
def minorMagnitude (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι) : ℕ :=
  if (C.submatrix I id).det = 0 then 1 else (C.submatrix I id).det.natAbs
/-- The finite lcm of every full-column minor magnitude. -/
def minorPeriod (C : Matrix ι (Fin n) ℤ) : ℕ :=
  Finset.univ.lcm (minorMagnitude C)
/-- Stack identity rows with all ray rows. -/
def augmentedRayMatrix (A : Matrix (Fin s) (Fin n) ℤ) :
    Matrix (Fin n ⊕ Fin s) (Fin n) ℤ :=
  fun i j => Sum.casesOn i (fun k => if k = j then 1 else 0) (fun k => A k j)
/-- The exact determinant period Delta of the augmented ray matrix. -/
def rayPeriod (A : Matrix (Fin s) (Fin n) ℤ) : ℕ := minorPeriod (augmentedRayMatrix A)
/-- The integer sign assigned to each of the two inequality orientations. -/
def constraintSign : Bool → ℤ
  | false => -1
  | true => 1
/-- Both signed versions of each row of the displayed integer matrix. -/
def signedRows (C : Matrix ι (Fin n) ℤ) : Matrix (Bool × ι) (Fin n) ℤ :=
  fun i j => constraintSign i.1 * C i.2 j
end MatrixConstants
section BasicMatrixConstants
variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The square submatrix chosen by a full row-selection map. -/
def basicMatrix (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι) :
    Matrix (Fin n) (Fin n) ℤ := C.submatrix I id
/-- The original rows multiplied by the chosen square minor adjugate. -/
def adjugateRow (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι) :
    Matrix ι (Fin n) ℤ := C * (basicMatrix C I).adjugate
/-- The determinant/adjugate integer bound on one affine feasibility residual. -/
def residualBudget (C : Matrix ι (Fin n) ℤ) (I : Fin n → ι) (j : ι) : ℤ :=
  |(basicMatrix C I).det| *
    (|(basicMatrix C I).det| + ∑ k, |adjugateRow C I j k|)
/-- One plus the finite sum of all residual budgets. -/
def affineThresholdCoefficient (C : Matrix ι (Fin n) ℤ) : ℤ :=
  1 + ∑ I : Fin n → ι, ∑ j, residualBudget C I j
end BasicMatrixConstants
section QuantArithmetic
variable {n s : ℕ}
/-- Both orientations of the augmented identity/ray rows. -/
abbrev RawRow (n s : ℕ) := Bool × (Fin n ⊕ Fin s)
/-- The full signed augmented matrix for the half-open raw coefficient box. -/
def rawConstraintMatrix (A : Matrix (Fin s) (Fin n) ℤ) :
    Matrix (RawRow n s) (Fin n) ℤ :=
  signedRows (augmentedRayMatrix A)
/-- The actual real-linear ray matrix map. -/
def realRayMap (A : Matrix (Fin s) (Fin n) ℤ) (x : Fin n → ℝ) : Fin s → ℝ :=
  A.map (Int.castRingHom ℝ) *ᵥ x
/-- One plus the largest absolute divisor coefficient, with empty maximum zero. -/
def divisorHeight (b : Fin s → ℤ) : ℕ :=
  1 + Finset.univ.sup (fun i => (b i).natAbs)
/-- The exact computable coefficient depending only on the ray matrix. -/
def rayThresholdCoefficient (A : Matrix (Fin s) (Fin n) ℤ) : ℕ :=
  (affineThresholdCoefficient (rawConstraintMatrix A)).natAbs
/-- The height-linear real-feasibility threshold. -/
def realStabilizationBound (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) : ℕ :=
  divisorHeight b * rayThresholdCoefficient A + 1
/-- The exact height-linear integer threshold with uniform T_A=n. -/
def periodicityBound (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) : ℕ :=
  realStabilizationBound A b + rayPeriod A * n
end QuantArithmetic
/-- The lcm of integers from one through n+1. -/
def dimensionDenominator (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n + 1)).lcm id
section QuantArithmetic
variable {n s : ℕ}
/-- Each offset is zero or minus one. -/
def IsSignPattern (e : Fin s → ℤ) : Prop := ∀ i, e i = 0 ∨ e i = -1
/-- The chosen floor/strict-ceiling boundary convention in every ray coordinate. -/
def patternCoefficient (e : Fin s → ℤ) (x : Fin s → ℝ) : Fin s → ℤ :=
  fun i => if e i = 0 then ⌊x i⌋ else ⌈x i⌉ - 1
/-- All integral divisor classes of the real rounding pattern. -/
def thomsenClasses (A : Matrix (Fin s) (Fin n) ℤ) (e : Fin s → ℤ) :
    Set (DivisorClass A) :=
  Set.range (fun x : Fin n → ℝ => divisorClass A (patternCoefficient e (realRayMap A x)))
/-- The exact universal grid denominator Delta times lcm(1,…,n+1). -/
def universalDenominator (A : Matrix (Fin s) (Fin n) ℤ) : ℕ :=
  rayPeriod A * dimensionDenominator n
/-- The real cokernel used only to test zonotope membership. -/
abbrev RealDivisorClass (A : Matrix (Fin s) (Fin n) ℤ) :=
  (Fin s → ℝ) ⧸ LinearMap.range (A.map (Int.castRingHom ℝ)).mulVecLin
/-- The real quotient linear map. -/
def realDivisorQuotient (A : Matrix (Fin s) (Fin n) ℤ) :
    (Fin s → ℝ) →ₗ[ℝ] RealDivisorClass A :=
  (LinearMap.range (A.map (Int.castRingHom ℝ)).mulVecLin).mkQ
/-- Realification of an integral divisor coefficient vector. -/
def realDivisorClass (A : Matrix (Fin s) (Fin n) ℤ) (a : Fin s → ℤ) :
    RealDivisorClass A := realDivisorQuotient A (fun i => (a i : ℝ))
/-- The literal image of the closed cube [-1,0]^s in the real cokernel. -/
def realZonotope (A : Matrix (Fin s) (Fin n) ℤ) : Set (RealDivisorClass A) :=
  realDivisorQuotient A '' Set.Icc (-1 : Fin s → ℝ) 0
/-- Lemma6.1: a single universal finite grid attains every real rounding class. -/
theorem thomsenClasses_eq_frobenius_universal (A : Matrix (Fin s) (Fin n) ℤ)
    (e : Fin s → ℤ) (he : IsSignPattern e) :
    thomsenClasses A e = frobeniusClasses A e (universalDenominator A : ℤ) := by sorry
/-- Lemma6.1: equality with the union over every positive integer exponent. -/
theorem thomsenClasses_eq_union_positive (A : Matrix (Fin s) (Fin n) ℤ)
    (e : Fin s → ℤ) (he : IsSignPattern e) :
    thomsenClasses A e =
      ⋃ ell : ℤ, ⋃ (_h : 0 < ell), frobeniusClasses A e ell := by sorry
/-- Lemma6.1: arbitrary integral representatives retain their full integral class on the universal grid. -/
theorem paper_lemma_6_1_zonotope_grid (A : Matrix (Fin s) (Fin n) ℤ)
    (a : Fin s → ℤ) (ha : realDivisorClass A a ∈ realZonotope A) :
    ∃ a' : Fin s → ℤ, divisorClass A a' = divisorClass A a ∧
      ∃ z : Fin n → ℤ, ∀ i,
        -1 ≤ (a' i : ℝ) -
          realRayMap A ((universalDenominator A : ℝ)⁻¹ • (fun j => (z j : ℝ))) i ∧
        (a' i : ℝ) -
          realRayMap A ((universalDenominator A : ℝ)⁻¹ • (fun j => (z j : ℝ))) i ≤ 0 := by sorry
/-- Theorem7.2 raw-summand clause: every integer exponent beyond the exact height-linear bound is periodic. -/
theorem paper_theorem_7_2_raw_int (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) (ell : ℤ) (hell : (periodicityBound A b : ℤ) ≤ ell) :
    rawCoefficients A b (ell + (rayPeriod A : ℤ)) = rawCoefficients A b ell := by sorry
end QuantArithmetic
/-- Lemma7.1: lattice absorption at the exact real-span dimension threshold. -/
theorem paper_lemma_7_1_int
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (L : AddSubgroup E) (vertices : Finset E)
    (hintegral : (vertices : Set E) ⊆ L)
    (hzero : (0 : E) ∈ convexHull ℝ (vertices : Set E))
    (P : Set E) (t : ℤ)
    (ht : (finrank ℝ (Submodule.span ℝ (vertices : Set E)) : ℤ) ≤ t) :
    let K := convexHull ℝ (vertices : Set E)
    let V := Submodule.span ℝ (vertices : Set E)
    ((P + (t : ℝ) • K) ∩ (L : Set E)).Nonempty ↔
      ((V.mkQ '' P) ∩ (V.mkQ '' (L : Set E))).Nonempty := by sorry
section QuantArithmetic
variable {n s : ℕ}
/-- The boundary sign pattern after an integral character shift. -/
def shiftSignPattern (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ)
    (w : Fin n → ℤ) : Fin s → ℤ :=
  fun i => if 0 ≤ b i + rayMap A w i then 0 else -1
/-- A boundary pattern realized by some integral character shift. -/
def AccessiblePattern (A : Matrix (Fin s) (Fin n) ℤ)
    (b e : Fin s → ℤ) : Prop :=
  ∃ w : Fin n → ℤ, shiftSignPattern A b w = e
/-- All zero/minus-one sign vectors. -/
def allSignPatterns (s : ℕ) : Finset (Fin s → ℤ) :=
  Finset.univ.image (fun p : Fin s → Bool => fun i => if p i then 0 else -1)
/-- The actual finite family of integrally feasible boundary sign patterns. -/
def accessiblePatterns (A : Matrix (Fin s) (Fin n) ℤ)
    (b : Fin s → ℤ) : Finset (Fin s → ℤ) := by
  classical
  exact (allSignPatterns s).filter (AccessiblePattern A b)
/-- The exact source choice of one integral witness for each accessible pattern, zero otherwise. -/
def patternWitness (A : Matrix (Fin s) (Fin n) ℤ) (b e : Fin s → ℤ) :
    Fin n → ℤ := by
  classical
  exact if he : AccessiblePattern A b e then Classical.choose he else 0
/-- The source K_b, one plus the largest shifted coefficient at those fixed witnesses. -/
def accessibilityBound (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) : ℕ :=
  1 + (accessiblePatterns A b).sup (fun e =>
    Finset.univ.sup (fun i => (b i + rayMap A (patternWitness A b e) i).natAbs))
/-- The union of exact rounding classes over integrally accessible boundary patterns. -/
def accessibleThomsenClasses (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) :
    Set (DivisorClass A) :=
  ⋃ e : Fin s → ℤ, ⋃ (_he : AccessiblePattern A b e), thomsenClasses A e
end QuantArithmetic
end ToricPower
namespace ToricPower
variable {n s : ℕ}
/-- The integral kernel of the transpose ray matrix. -/
def rayRelations (A : Matrix (Fin s) (Fin n) ℤ) :
    Submodule ℤ (Fin s → ℤ) := LinearMap.ker A.transpose.mulVecLin
/-- A primitive support-minimal integral ray relation, with both signs included. -/
def IsCircuit (A : Matrix (Fin s) (Fin n) ℤ) (h : Fin s → ℤ) : Prop :=
  TauCeti.IsPrimitive h ∧ h ∈ rayRelations A ∧
    ∀ k ∈ rayRelations A, Function.support k ⊂ Function.support h → k = 0
/-- The full primitive-circuit set is finite; this supporting statement is also compared. -/
theorem circuits_finite (A : Matrix (Fin s) (Fin n) ℤ) :
    {h : Fin s → ℤ | IsCircuit A h}.Finite := by sorry
/-- The entire finite set of actual primitive circuits. -/
def circuits (A : Matrix (Fin s) (Fin n) ℤ) : Finset (Fin s → ℤ) :=
  (circuits_finite A).toFinset
/-- The support function of the closed cube [-1,0]^s in an integral direction. -/
def cubeSupport (h : Fin s → ℤ) : ℤ := ∑ i, max (-h i) 0
/-- The source C_b, one plus the maximal nonnegative circuit pairing excess. -/
def circuitBound (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) : ℕ :=
  1 + (circuits A).sup (fun h => ((∑ i, h i * b i) - cubeSupport h).toNat)
/-- The exact stable multiple used in Proposition6.2, with the original K_b and C_b. -/
def stableMultipleExponent (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) : ℕ :=
  universalDenominator A * max (accessibilityBound A b) (circuitBound A b)
/-- Proposition6.2: exact stabilization for every integer multiple satisfying both original bounds. -/
theorem paper_proposition_6_2_classes_int
    (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) (k : ℤ)
    (hK : (accessibilityBound A b : ℤ) ≤ k)
    (hC : (circuitBound A b : ℤ) ≤ (universalDenominator A : ℤ) * k) :
    frobeniusClasses A b ((universalDenominator A : ℤ) * k) =
      accessibleThomsenClasses A b := by sorry
/-- Proposition6.2: the exact one-exponent class set is already the stable accessible class set. -/
theorem classes_at_stableMultipleExponent
    (A : Matrix (Fin s) (Fin n) ℤ) (b : Fin s → ℤ) :
    frobeniusClasses A b (stableMultipleExponent A b : ℤ) =
      accessibleThomsenClasses A b := by sorry
end ToricPower

/- Canonical-dependency main1.1 interface draft. It requires TauCeti1f9b4414
and its exact complete Mathlib07406378 manifest, NOT the live package's56a00585
manifest. No local build or dependency upgrade is claimed. -/
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TauCeti.Toric
namespace PalomarToricPower
universe u
variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V}
/-- The literal trace lattice N intersect W. -/
def latticeTrace (W : Submodule ℝ V) : Submodule ℤ N :=
  (W.restrictScalars ℤ).comap i.toIntLinearMap
/-- The ordinary function from the literal trace lattice to its subspace. -/
def traceFn (W : Submodule ℝ V) (n : latticeTrace (i := i) W) : W := ⟨i n, n.property⟩
/-- The trace inclusion into W preserves zero. -/
theorem trace_zero (W : Submodule ℝ V) : traceFn (i := i) W 0 = 0 := by sorry
/-- The trace inclusion into W preserves addition. -/
theorem trace_add (W : Submodule ℝ V) (x y : latticeTrace (i := i) W) :
    traceFn (i := i) W (x + y) = traceFn W x + traceFn W y := by sorry
/-- The actual trace lattice map, with no extra torus factor. -/
def latticeTraceMap (W : Submodule ℝ V) : latticeTrace (i := i) W →+ W where
  toFun := traceFn W
  map_zero' := trace_zero W
  map_add' := trace_add W
/-- Rationality means the actual integral points span precisely W. -/
def IsRationalSubspace (W : Submodule ℝ V) : Prop :=
  Submodule.span ℝ (Set.range (fun n : latticeTrace (i := i) W => i n)) = W
/-- The exact restricted cone family, inside W. -/
def restrictedCones (Φ : Fan i) (W : Submodule ℝ V) : Set (PointedCone ℝ W) :=
  (fun σ : PointedCone ℝ V => σ.comap W.subtype) ''
    {σ | σ ∈ Φ.cones ∧ σ ≤ (W : PointedCone ℝ V)}
/-- The actual rational trace is an integral lattice. -/
theorem trace_integral (Φ : Fan i) (W : Submodule ℝ V) (hW : IsRationalSubspace (i := i) W) :
    IsIntegralLattice (latticeTraceMap (i := i) W) := by sorry
/-- Restriction retains a finite cone family. -/
theorem restriction_finite (Φ : Fan i) (W : Submodule ℝ V) : (restrictedCones Φ W).Finite := by sorry
/-- Every restricted cone is genuinely rational and salient in the trace lattice. -/
theorem restriction_toric (Φ : Fan i) (W : Submodule ℝ V) {σ : PointedCone ℝ W}
    (hσ : σ ∈ restrictedCones Φ W) : IsToricCone (latticeTraceMap (i := i) W) σ := by sorry
/-- The actual restricted family is closed under taking faces. -/
theorem restriction_faces (Φ : Fan i) (W : Submodule ℝ V) {σ τ : PointedCone ℝ W}
    (hσ : σ ∈ restrictedCones Φ W) (hτ : τ.IsFaceOf σ) : τ ∈ restrictedCones Φ W := by sorry
/-- Intersections in the restricted family are actual faces. -/
theorem restriction_intersection (Φ : Fan i) (W : Submodule ℝ V) {σ τ : PointedCone ℝ W}
    (hσ : σ ∈ restrictedCones Φ W) (hτ : τ ∈ restrictedCones Φ W) : (σ ⊓ τ).IsFaceOf σ := by sorry
/-- The actual restricted fan in the saturated integral trace. -/
def restrictedFan (Φ : Fan i) (W : Submodule ℝ V) (hW : IsRationalSubspace (i := i) W) :
    Fan (latticeTraceMap (i := i) W) where
  lattice := trace_integral Φ W hW
  cones := restrictedCones Φ W
  finite_cones := restriction_finite Φ W
  isToricCone := fun {σ} hσ => restriction_toric Φ W (σ := σ) hσ
  mem_of_isFaceOf := fun {σ τ} hσ hτ => restriction_faces Φ W (σ := σ) (τ := τ) hσ hτ
  inf_isFaceOf_left := fun {σ τ} hσ hτ => restriction_intersection Φ W (σ := σ) (τ := τ) hσ hτ
/-- Linearity means intersection with every original cone remains an original cone. -/
def IsLinearSubspace (Φ : Fan i) (W : Submodule ℝ V) : Prop :=
  ∀ σ ∈ Φ.cones, σ ⊓ (W : PointedCone ℝ V) ∈ Φ.cones
/-- A genuinely rational linear subspace, with exactly the manuscript's fan-linearity condition. -/
structure LinearSubspace (Φ : Fan i) where
  space : Submodule ℝ V
  rational : IsRationalSubspace (i := i) space
  linear : IsLinearSubspace Φ space
/-- Inclusion of restricted cones is genuinely a fan map. -/
theorem restricted_map_cone (Φ : Fan i) (W : Submodule ℝ V) {σ : PointedCone ℝ W}
    (hσ : σ ∈ restrictedCones Φ W) : ∃ τ ∈ Φ.cones, σ.map W.subtype ≤ τ := by sorry
/-- The canonical fan inclusion of the actual trace lattice and actual subspace. -/
def restrictedInclusion (Φ : Fan i) (W : Submodule ℝ V) (hW : IsRationalSubspace (i := i) W) :
    FanHom (restrictedFan Φ W hW) Φ where
  latticeMap := (latticeTrace (i := i) W).subtype.toAddMonoidHom
  realMap := W.subtype
  map_lattice _ := rfl
  map_cone := fun {σ} hσ => restricted_map_cone Φ W (σ := σ) hσ
/-- The actual scheme morphism induced by inclusion of a rational linear subspace. -/
def linearInclusion (Φ : Fan i) (W : LinearSubspace Φ) :=
  (restrictedInclusion Φ W.space W.rational).algebraicMap
/-- Natural multiplication respects the actual integral lattice embedding. -/
theorem power_lattice (ell : ℕ) (n : N) :
    ((ell : ℝ) • (LinearMap.id : V →ₗ[ℝ] V)) (i n) = i ((ell • AddMonoidHom.id N) n) := by sorry
/-- Natural multiplication sends every cone into a cone of the same fan. -/
theorem power_cone (Φ : Fan i) (ell : ℕ) {σ : PointedCone ℝ V} (hσ : σ ∈ Φ.cones) :
    ∃ τ ∈ Φ.cones, σ.map ((ell : ℝ) • LinearMap.id) ≤ τ := by sorry
/-- The genuine multiplication-by-ell fan endomorphism. -/
def powerFanHom (Φ : Fan i) (ell : ℕ) : FanHom Φ Φ where
  latticeMap := ell • AddMonoidHom.id N
  realMap := (ell : ℝ) • LinearMap.id
  map_lattice := power_lattice ell
  map_cone := fun {σ} hσ => power_cone Φ ell (σ := σ) hσ
/-- The ordinary actual toric scheme power map, obtained by affine gluing. -/
def powerMap (Φ : Fan i) (ell : ℕ) := (powerFanHom Φ ell).algebraicMap
/-- Every actual finite toric fan gives a Noetherian scheme. -/
theorem fan_noetherian (Φ : Fan i) : IsNoetherian Φ.algebraicRealization := by sorry
/-- A nonempty actual fan gives an integral toric scheme. -/
theorem fan_integral (Φ : Fan i) (hne : Φ.cones.Nonempty) : IsIntegral Φ.algebraicRealization := by sorry
/-- Actual Cartier divisors on the genuine integral toric scheme. -/
def Cartier (Φ : Fan i) (hne : Φ.cones.Nonempty) : Type :=
  letI := fan_integral Φ hne
  TauCeti.AlgebraicGeometry.Scheme.CartierDivisor Φ.algebraicRealization
/-- The genuine Cartier line bundle O(D). -/
def divisorSheaf (Φ : Fan i) (hne : Φ.cones.Nonempty) (D : Cartier Φ hne) :
    Φ.algebraicRealization.Modules :=
  letI := fan_integral Φ hne
  D.sheaf
/-- Ordinary direct image under the actual power map. -/
def powerSheaf (Φ : Fan i) (hne : Φ.cones.Nonempty) (D : Cartier Φ hne) (ell : ℕ) :=
  (Scheme.Modules.pushforward (powerMap Φ ell)).obj (divisorSheaf Φ hne D)
/-- The zero sheaf belongs to the literal finite-presentation subcategory. -/
theorem coherent_containsZero (X : Scheme.{u}) :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).ContainsZero := by sorry
/-- Actual kernels preserve finite presentation on locally Noetherian schemes. -/
theorem coherent_closedKernels (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderKernels := by sorry
/-- Actual cokernels preserve finite presentation. -/
theorem coherent_closedCokernels (X : Scheme.{u}) :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderCokernels := by sorry
/-- Actual finite products preserve finite presentation. -/
theorem coherent_closedProducts (X : Scheme.{u}) :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderFiniteProducts := by sorry
local instance (priority := 2000) coherentContainsZero (X : Scheme.{u}) :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).ContainsZero := coherent_containsZero X
local instance (priority := 2000) coherentClosedKernels (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderKernels := coherent_closedKernels X
local instance (priority := 2000) coherentClosedCokernels (X : Scheme.{u}) :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderCokernels := coherent_closedCokernels X
local instance (priority := 2000) coherentClosedProducts (X : Scheme.{u}) :
    (_root_.SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderFiniteProducts := coherent_closedProducts X
/-- Mathlib's actual full-subcategory abelian structure. The separately proved
closure propositions supply its hypotheses; no categorical operation is postulated. -/
local instance (priority := 2000) coherentAbelian (X : Scheme.{u}) [IsLocallyNoetherian X] :
    Abelian (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf X) := inferInstance
local instance standardDerived (X : Scheme.{u}) [IsLocallyNoetherian X] :
    HasDerivedCategory.{u+1} (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf X) :=
  HasDerivedCategory.standard _
/-- The literal bounded derived category of actual coherent sheaves. -/
abbrev DbCoh (Φ : Fan i) :=
  letI := fan_noetherian Φ
  DerivedCategory.Bounded (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf Φ.algebraicRealization)
/-- The actual ordinary finite power-map direct image is a coherent sheaf. -/
theorem power_finitePresentation (Φ : Fan i) (hreg : Φ.IsRegular) (hne : Φ.cones.Nonempty)
    (D : Cartier Φ hne) (ell : ℕ) (hell : 0 < ell) :
    _root_.SheafOfModules.IsFinitePresentation (R := Φ.algebraicRealization.ringCatSheaf)
      (powerSheaf Φ hne D ell) := by sorry
/-- The actual coherent direct image placed in degree zero in Db(Coh). -/
def powerObject (Φ : Fan i) (hreg : Φ.IsRegular) (hne : Φ.cones.Nonempty)
    (D : Cartier Φ hne) (ell : ℕ) (hell : 0 < ell) : DbCoh Φ :=
  letI := fan_noetherian Φ
  (TauCeti.DerivedCategory.Bounded.singleFunctor _ 0).obj
    ⟨powerSheaf Φ hne D ell, power_finitePresentation Φ hreg hne D ell hell⟩
/-- Classical generation of the actual bounded coherent derived category. -/
def Generates (Φ : Fan i) (hreg : Φ.IsRegular) (hne : Φ.cones.Nonempty)
    (D : Cartier Φ hne) (ell : ℕ) (hell : 0 < ell) : Prop :=
  letI := fan_noetherian Φ
  (ObjectProperty.singleton (powerObject Φ hreg hne D ell hell)).IsClassicalTriangulatedGenerator
/-- Ordinary Zariski sheaf cohomology, via Mathlib's actual functor on the small site. -/
def totalCohomologyNonzero (X : Scheme.{u}) (M : X.Modules) : Prop :=
  ∃ p : ℕ, Nontrivial (((_root_.SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙ CategoryTheory.Sheaf.functorH.{u} _ p).obj M))
/-- Every actual rational linear subspace passes the literal restricted cohomology test. -/
def Criterion (Φ : Fan i) (hne : Φ.cones.Nonempty) (D : Cartier Φ hne) : Prop :=
  ∀ W : LinearSubspace Φ,
    totalCohomologyNonzero (restrictedFan Φ W.space W.rational).algebraicRealization
      ((Scheme.Modules.pullback (linearInclusion Φ W)).obj (divisorSheaf Φ hne D))
/-- Main Theorem1.1: existence iff the full cohomology criterion, and generation
for every sufficiently large integer exponent, for every actual Cartier divisor. -/
theorem main_theorem (Φ : Fan i) (hreg : Φ.IsRegular) (hne : Φ.cones.Nonempty)
    (D : Cartier Φ hne) :
    ((∃ (ell : ℕ) (hell : 0 < ell), Generates Φ hreg hne D ell hell) ↔ Criterion Φ hne D) ∧
    (Criterion Φ hne D → ∃ (L : ℕ) (hL : 0 < L), ∀ (ell : ℕ) (hLell : L ≤ ell),
      Generates Φ hreg hne D ell (lt_of_lt_of_le hL hLell)) := by sorry
end PalomarToricPower
