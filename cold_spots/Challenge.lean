module
public import Mathlib

@[expose] public section
/-!
# Universal cold spots of E8 and related lattices

Theorem 1.1 identifies every Gaussian cold spot with a deep hole, for E6, E8,
E7 dual, BW16, and D_n plus in every even dimension n at least eight. The
corollary covers arbitrary nonzero positive mixing measures, under the literal
finiteness hypothesis for the nonnegative energy. The radius table records
upper bounds with attainment. All custom lattice sets, Euclidean squared
distances, real infinite sums, and integral potentials below retain the exact
source semantics; neither minima nor maximizers are built into a lattice set.
The E7 dual lives in the actual seven-dimensional zero-sum subspace of R8.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace PaperVerification.PositiveMixtures
variable {ι X : Type*}
/-- Strictly positive real Gaussian parameters. -/
abbrev PositiveParameter := Set.Ioi (0 : ℝ)

/-- Nonnegative integral potential against the arbitrary positive mixing measure. -/
def gaussianMixtureENNReal (ν : Measure PositiveParameter) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ α : PositiveParameter, ENNReal.ofReal (Real.exp (-(α : ℝ) * r)) ∂ν

/-- The nonnegative infinite sum of integral potentials at all lattice distances. -/
def mixtureEnergyENNReal (d : ι → X → ℝ) (ν : Measure PositiveParameter) (x : X) : ℝ≥0∞ :=
  ∑' v : ι, gaussianMixtureENNReal ν (d v x)

/-- The real integral of the Gaussian kernel against the mixing measure. -/
def gaussianMixture (ν : Measure PositiveParameter) (r : ℝ) : ℝ :=
  ∫ α : PositiveParameter, Real.exp (-(α : ℝ) * r) ∂ν

/-- The real infinite sum of the actual integral potentials. -/
def mixtureEnergy (d : ι → X → ℝ) (ν : Measure PositiveParameter) (x : X) : ℝ :=
  ∑' v : ι, gaussianMixture ν (d v x)

end PaperVerification.PositiveMixtures
namespace PaperVerification.ColdSpots
open PaperVerification.PositiveMixtures
variable {n : ℕ}

/-- Squared Euclidean distance: the sum of coordinate squares. -/
def sqDist {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, (x i - y i) ^ 2

/-- The actual real Gaussian series over the indicated lattice set. -/
def setGaussian {n : ℕ} (L : Set (Fin n → ℝ)) (α : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑' z : L, Real.exp (-α * sqDist z.val x)

/-- A global minimum of the Gaussian lattice series over all ambient points. -/
def IsColdSpot {n : ℕ} (L : Set (Fin n → ℝ)) (α : ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ y, setGaussian L α x ≤ setGaussian L α y

/-- Infimum of squared Euclidean distances to the lattice set. -/
def squaredDepth {n : ℕ} (L : Set (Fin n → ℝ)) (x : Fin n → ℝ) : ℝ :=
  sInf ((fun z ↦ sqDist x z) '' L)

/-- A global maximum of the squared distance to the lattice set. -/
def IsDeepHole {n : ℕ} (L : Set (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  ∀ y, squaredDepth L y ≤ squaredDepth L x

/-- Multiply every real coordinate by c. -/
def scaleVec (c : ℝ) (x : Fin n → ℝ) : Fin n → ℝ := fun i => c * x i

/-- Image of a coordinate lattice set under scaling by c. -/
def scaledSet (c : ℝ) (L : Set (Fin n → ℝ)) : Set (Fin n → ℝ) := scaleVec c '' L

/-- Two real Eisenstein coordinates. -/
abbrev TriPoint := ℝ × ℝ

/-- Three pairs of real Eisenstein coordinates. -/
abbrev TriTriple := Fin 3 → TriPoint

/-- Ordinary Euclidean coordinates of three Eisenstein points. -/
def triTripleFlatten (z : TriTriple) (j : Fin 6) : ℝ :=
  Fin.addCases (m:=3) (n:=3) (motive:=fun _ ↦ ℝ)
    (fun i : Fin 3 ↦ (z i).1-(z i).2/2)
    (fun i : Fin 3 ↦ Real.sqrt 3*(z i).2/2) j

/-- Two integer Eisenstein coordinates. -/
abbrev EisInt := ℤ × ℤ

/-- Three copies of the integer Eisenstein lattice and the three gluing classes. -/
abbrev E6Index := ZMod 3 × (Fin 3 → EisInt)

/-- Embed integer Eisenstein coordinates into real Eisenstein coordinates. -/
def eisEmbed : EisInt →+ TriPoint where
  toFun z := ((z.1 : ℝ), (z.2 : ℝ))
  map_zero' := by ext <;> simp
  map_add' := by intro z w; ext <;> simp

/-- The Eisenstein gluing vector with coordinates (1/3,-1/3). -/
def triC : TriPoint := (1 / 3, -(1 / 3))

/-- The three Eisenstein lattice points with their common gluing translate. -/
def l6Point (p : E6Index) : TriTriple :=
  fun i ↦ eisEmbed (p.2 i)+(p.1.val : ℝ)•triC

/-- The union of the three actual Eisenstein gluing cosets. -/
def l6Set : Set TriTriple := Set.range l6Point

/-- The six-dimensional Euclidean realization of the Eisenstein gluing lattice. -/
def l6EuclideanSet : Set (Fin 6 → ℝ) := triTripleFlatten '' l6Set

/-- The root-normalized E6 lattice, scaling the explicit gluing lattice by sqrt(2). -/
def e6Set : Set (Fin 6 → ℝ) := scaledSet (Real.sqrt 2) l6EuclideanSet

/-- Embed an integer coordinate vector into real coordinates. -/
def intVec {n : ℕ} (z : Fin n → ℤ) : Fin n → ℝ := fun i ↦ (z i : ℝ)

/-- D_n together with its translate by the all-half vector. -/
def dPlusSet (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∃ z : Fin n → ℤ, Even (∑ i, z i) ∧
    (x = intVec z ∨ x = fun i ↦ (z i : ℝ) + 1 / 2)}

/-- The real seven-dimensional subspace of R8 with coordinate sum zero. -/
def zeroSumSpace : Submodule ℝ (Fin 8 → ℝ) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (∑ i, x i) = 0 at hx
    change (∑ i, y i) = 0 at hy
    change (∑ i, (x + y) i) = 0
    simp only [Pi.add_apply, Finset.sum_add_distrib, hx, hy, zero_add]
  smul_mem' := by
    intro a x hx
    change (∑ i, x i) = 0 at hx
    change (∑ i, (a • x) i) = 0
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx, mul_zero]

/-- Orthogonal projection to the zero-sum hyperplane. -/
def project8 (x : Fin 8 → ℝ) : zeroSumSpace :=
  ⟨fun i ↦ x i - (∑ j, x j) / 8, by
    change (∑ i, (x i - (∑ j, x j) / 8)) = 0
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring⟩

/-- The orthogonal projection of the even integer-coordinate lattice in R8. -/
def e7ProjectedSet : Set zeroSumSpace :=
  {y | ∃ z : Fin 8 → ℤ, Even (∑ i, z i) ∧ y = project8 (intVec z)}

/-- The actual Gaussian series over the projected E7 dual lattice. -/
def e7Gaussian (α : ℝ) (x : zeroSumSpace) : ℝ :=
  ∑' y : e7ProjectedSet, Real.exp (-α * sqDist y.val.val x.val)

/-- A global Gaussian minimum over the actual zero-sum ambient space. -/
def IsE7ColdSpot (α : ℝ) (x : zeroSumSpace) : Prop :=
  ∀ y : zeroSumSpace, e7Gaussian α x ≤ e7Gaussian α y

/-- Infimum of squared Euclidean distances to the E7 dual lattice. -/
def e7SquaredDepth (x : zeroSumSpace) : ℝ :=
  sInf ((fun y : zeroSumSpace ↦ sqDist x.val y.val) '' e7ProjectedSet)

/-- A global maximum of E7 dual squared depth in its ambient hyperplane. -/
def IsE7DeepHole (x : zeroSumSpace) : Prop :=
  ∀ y : zeroSumSpace, e7SquaredDepth y ≤ e7SquaredDepth x

/-- The field with two elements. -/
abbrev Binary := ZMod 2

/-- A binary word of length sixteen. -/
abbrev BinaryWord16 := Fin 16 → Binary

/-- The four binary coefficients of an affine function on a three-cube. -/
abbrev AffineCoefficients3 := Fin 4 → Binary

/-- The five binary coefficients of an affine function on a four-cube. -/
abbrev AffineCoefficients4 := AffineCoefficients3 × Binary

/-- A binary word of length eight. -/
abbrev BinaryWord8 := Fin 8 → Binary

/-- The selected binary digit of a three-cube coordinate. -/
def binaryDigit (i : Fin 8) (j : Fin 3) : Binary := ((i.val / 2 ^ j.val) % 2 : ℕ)

/-- Evaluation word of the affine binary function on the three-cube. -/
def affineWord3 (a : AffineCoefficients3) : BinaryWord8 :=
  fun i => a 3 + ∑ j : Fin 3, a j.castSucc * binaryDigit i j

/-- Evaluation word of the affine binary function on the four-cube. -/
def affineWord4 (a : AffineCoefficients4) : BinaryWord16 :=
  Fin.append (affineWord3 a.1) (fun i => affineWord3 a.1 i + a.2)

/-- Membership in the first-order Reed-Muller code RM(1,4). -/
def InRM4 (c : BinaryWord16) : Prop := ∃ a : AffineCoefficients4, c = affineWord4 a

/-- The real half-vector of a binary word of length sixteen. -/
def halfWord16 (c : BinaryWord16) : Fin 16 → ℝ := fun i => ((c i).val : ℝ) / 2

/-- The explicit lattice D16 plus half the Reed-Muller code RM(1,4). -/
def bwRMConstruction : Set (Fin 16 → ℝ) :=
  {x | ∃ z : Fin 16 → ℤ, Even (∑ i, z i) ∧ ∃ c : BinaryWord16,
    InRM4 c ∧ x = intVec z + halfWord16 c}

/-- The integral Barnes-Wall lattice, the explicit code construction scaled by sqrt(2). -/
def bw16Set : Set (Fin 16 → ℝ) := scaledSet (Real.sqrt 2) bwRMConstruction

/-- Nonnegative mixture energy summed over actual lattice-point squared distances. -/
def setMixtureEnergyENNReal (L : Set (Fin n → ℝ)) (ν : Measure PositiveParameter)
    (x : Fin n → ℝ) : ℝ≥0∞ :=
  mixtureEnergyENNReal (fun v : L => fun y => sqDist v.val y) ν x

/-- Real mixture energy summed over actual lattice-point squared distances. -/
def setMixtureEnergy (L : Set (Fin n → ℝ)) (ν : Measure PositiveParameter)
    (x : Fin n → ℝ) : ℝ :=
  mixtureEnergy (fun v : L => fun y => sqDist v.val y) ν x

/-- A global minimum of the actual convergent real mixture lattice energy. -/
def IsMixtureColdSpot (L : Set (Fin n → ℝ)) (ν : Measure PositiveParameter)
    (x : Fin n → ℝ) : Prop := ∀ y, setMixtureEnergy L ν x ≤ setMixtureEnergy L ν y

/-- Nonnegative integral-potential sum for the actual E7 dual lattice. -/
def e7MixtureEnergyENNReal (ν : Measure PositiveParameter) (x : zeroSumSpace) : ℝ≥0∞ :=
  mixtureEnergyENNReal (fun v : e7ProjectedSet => fun y : zeroSumSpace => sqDist v.val.val y.val) ν x

/-- Real integral-potential sum for the actual E7 dual lattice. -/
def e7MixtureEnergy (ν : Measure PositiveParameter) (x : zeroSumSpace) : ℝ :=
  mixtureEnergy (fun v : e7ProjectedSet => fun y : zeroSumSpace => sqDist v.val.val y.val) ν x

/-- Manuscript Theorem 1.1, including every even dimension n at least eight. -/
theorem lattice_theorem_1_1 :
    (∀ α : ℝ, 0 < α → ∀ x : Fin 6 → ℝ,
      IsColdSpot e6Set α x ↔ IsDeepHole e6Set x) ∧
    (∀ α : ℝ, 0 < α → ∀ x : Fin 8 → ℝ,
      IsColdSpot (dPlusSet 8) α x ↔ IsDeepHole (dPlusSet 8) x) ∧
    (∀ α : ℝ, 0 < α → ∀ x : zeroSumSpace,
      IsE7ColdSpot α x ↔ IsE7DeepHole x) ∧
    (∀ α : ℝ, 0 < α → ∀ x : Fin 16 → ℝ,
      IsColdSpot bw16Set α x ↔ IsDeepHole bw16Set x) ∧
    (∀ n : ℕ, 8 ≤ n → Even n → ∀ α : ℝ, 0 < α → ∀ x : Fin n → ℝ,
      IsColdSpot (dPlusSet n) α x ↔ IsDeepHole (dPlusSet n) x) := by
  sorry

/-- Every squared covering-radius bound in the introduction table, with attainment. -/
theorem lattice_covering_radius_table :
    ((∀ x : Fin 6 → ℝ, squaredDepth e6Set x ≤ 4/3) ∧
      ∃ x : Fin 6 → ℝ, squaredDepth e6Set x=4/3) ∧
    ((∀ x : Fin 8 → ℝ, squaredDepth (dPlusSet 8) x ≤ 1) ∧
      ∃ x : Fin 8 → ℝ, squaredDepth (dPlusSet 8) x=1) ∧
    ((∀ x : zeroSumSpace, e7SquaredDepth x ≤ 7/8) ∧
      ∃ x : zeroSumSpace, e7SquaredDepth x=7/8) ∧
    ((∀ x : Fin 16 → ℝ, squaredDepth bw16Set x ≤ 3) ∧
      ∃ x : Fin 16 → ℝ, squaredDepth bw16Set x=3) ∧
    (∀ n : ℕ, 8 ≤ n → Even n →
      (∀ x : Fin n → ℝ, squaredDepth (dPlusSet n) x ≤ (n:ℝ)/8) ∧
        ∃ x : Fin n → ℝ, squaredDepth (dPlusSet n) x=(n:ℝ)/8) := by
  sorry

/-- Corollary 1.2 for arbitrary nonzero mixing measures with finite nonnegative energy. -/
theorem lattice_corollary_1_2 (ν : Measure PositiveParameter) (hν : ν≠0) :
    ((∀ x : Fin 6 → ℝ, setMixtureEnergyENNReal e6Set ν x≠∞) →
      ∀ x : Fin 6 → ℝ, IsMixtureColdSpot e6Set ν x ↔ IsDeepHole e6Set x) ∧
    ((∀ x : Fin 8 → ℝ, setMixtureEnergyENNReal (dPlusSet 8) ν x≠∞) →
      ∀ x : Fin 8 → ℝ, IsMixtureColdSpot (dPlusSet 8) ν x ↔ IsDeepHole (dPlusSet 8) x) ∧
    ((∀ x : zeroSumSpace, e7MixtureEnergyENNReal ν x≠∞) →
      ∀ x : zeroSumSpace, (∀ y, e7MixtureEnergy ν x ≤ e7MixtureEnergy ν y) ↔ IsE7DeepHole x) ∧
    ((∀ x : Fin 16 → ℝ, setMixtureEnergyENNReal bw16Set ν x≠∞) →
      ∀ x : Fin 16 → ℝ, IsMixtureColdSpot bw16Set ν x ↔ IsDeepHole bw16Set x) ∧
    (∀ n : ℕ, 8 ≤ n → Even n →
      (∀ x : Fin n → ℝ, setMixtureEnergyENNReal (dPlusSet n) ν x≠∞) →
      ∀ x : Fin n → ℝ, IsMixtureColdSpot (dPlusSet n) ν x ↔ IsDeepHole (dPlusSet n) x) := by
  sorry

end PaperVerification.ColdSpots
