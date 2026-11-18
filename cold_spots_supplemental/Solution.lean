module
public import release_all

@[expose] public section
/-!
# Exact minima, equality loci and deep-hole translation classes

This supplement records the literal quantitative conclusions of the cold-spots
paper for E6, E8, E7 dual, BW16 and every even D_n plus (n >= 8).
All lattices and coordinate families are displayed below. Gaussian values are
actual infinite series, squared depth is the infimum of actual squared Euclidean
distances, and deep holes maximize that depth over the full real ambient space.
The translation classes are actual ambient quotient classes containing deep
holes. The subgroup is Mathlib's closure of the displayed lattice set; the
Solution proves equality with the original lattice subgroup before using its
class-count theorem. No finite representative set replaces this quotient.
-/
noncomputable section
open scoped BigOperators
namespace PalomarColdSpotsSupplemental
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

/-- The integer-coordinate embedding sends zero to zero. -/
theorem eisEmbed_zero_proof :
    (((0 : EisInt).1 : ℝ), ((0 : EisInt).2 : ℝ)) = (0 : TriPoint) := by
  ext <;> simp

/-- The integer-coordinate embedding preserves addition. -/
theorem eisEmbed_add_proof (z w : EisInt) :
    (((z + w).1 : ℝ), ((z + w).2 : ℝ)) =
      (((z.1 : ℝ), (z.2 : ℝ)) : TriPoint) + ((w.1 : ℝ), (w.2 : ℝ)) := by
  ext <;> simp

/-- Embed integer Eisenstein coordinates into real Eisenstein coordinates. -/
def eisEmbed : EisInt →+ TriPoint where
  toFun z := ((z.1 : ℝ), (z.2 : ℝ))
  map_zero' := eisEmbed_zero_proof
  map_add' := eisEmbed_add_proof

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

/-- The zero vector has zero coordinate sum. -/
theorem zeroSum_zero_proof : (∑ i : Fin 8, (0 : Fin 8 → ℝ) i) = 0 := by
  simp

/-- The zero-sum hyperplane is closed under vector addition. -/
theorem zeroSum_add_proof (x y : Fin 8 → ℝ)
    (hx : (∑ i, x i) = 0) (hy : (∑ i, y i) = 0) :
    (∑ i, (x + y) i) = 0 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, hx, hy, zero_add]

/-- The zero-sum hyperplane is closed under real scalar multiplication. -/
theorem zeroSum_smul_proof (a : ℝ) (x : Fin 8 → ℝ)
    (hx : (∑ i, x i) = 0) : (∑ i, (a • x) i) = 0 := by
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx, mul_zero]

/-- The real seven-dimensional subspace of R8 with coordinate sum zero. -/
def zeroSumSpace : Submodule ℝ (Fin 8 → ℝ) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := zeroSum_zero_proof
  add_mem' := by
    intro x y hx hy
    exact zeroSum_add_proof x y hx hy
  smul_mem' := by
    intro a x hx
    exact zeroSum_smul_proof a x hx

/-- Subtracting the coordinate mean gives a zero-sum vector. -/
theorem project8_zeroSum_proof (x : Fin 8 → ℝ) :
    (∑ i : Fin 8, (x i - (∑ j, x j) / 8)) = 0 := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- Orthogonal projection to the zero-sum hyperplane. -/
def project8 (x : Fin 8 → ℝ) : zeroSumSpace :=
  ⟨fun i ↦ x i - (∑ j, x j) / 8, project8_zeroSum_proof x⟩

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

/-- Literal source definition: source/paper_verification/lattice002.lean:3249. -/
def gaussian (α t : ℝ) : ℝ :=
  ∑' z : ℤ, Real.exp (-α * ((z : ℝ) - t) ^ 2)

/-- Literal source definition: source/paper_verification/lattice002.lean:3253. -/
def paritySign (z : ℤ) : ℝ := if Even z then 1 else -1

/-- Literal source definition: source/paper_verification/lattice002.lean:3256. -/
def alternatingGaussian (α t : ℝ) : ℝ :=
  ∑' z : ℤ, paritySign z * Real.exp (-α * ((z : ℝ) - t) ^ 2)

/-- Literal source definition: source/paper_verification/lattice003.lean:1469. -/
def HalfIntegerGrid (x : Fin n → ℝ) : Prop := ∀ i, ∃ k : ℤ, x i = (k : ℝ) / 2

/-- Literal source definition: source/paper_verification/lattice003.lean:1472. -/
def nonintegerCount (x : Fin n → ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => ¬∃ k : ℤ, x i = (k : ℝ)).card

/-- Literal source definition: source/paper_verification/lattice003.lean:1477. -/
def PaperHalfGrid (x : Fin n → ℝ) : Prop := HalfIntegerGrid x ∧ nonintegerCount x = n / 2

/-- Literal source definition: source/paper_verification/lattice004.lean:2555. -/
def e8FirstVector : Fin 8 → ℝ := fun i => if i = 0 then 1 else 0

/-- Literal source definition: source/paper_verification/lattice004.lean:2558. -/
def E8FirstFamily (x : Fin 8 → ℝ) : Prop :=
  ∃ y ∈ dPlusSet 8, x = e8FirstVector + y

/-- Literal source definition: source/paper_verification/lattice004.lean:2545. -/
def negativeSignCount (ε : Fin n → ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => ε i = -1).card

/-- Literal source definition: source/paper_verification/lattice004.lean:2550. -/
def E8QuarterFamily (x : Fin 8 → ℝ) : Prop :=
  ∃ m ε : Fin 8 → ℤ, Odd (∑ i, m i) ∧ (∀ i, ε i = 1 ∨ ε i = -1) ∧
    Even (negativeSignCount ε) ∧ ∀ i, x i = (m i : ℝ) + (ε i : ℝ) / 4

/-- Literal source definition: source/paper_verification/lattice004.lean:2721. -/
def E8PaperHole (x : Fin 8 → ℝ) : Prop :=
  E8FirstFamily x ∨ PaperHalfGrid x ∨ E8QuarterFamily x

/-- Literal source definition: source/paper_verification/lattice005.lean:467. -/
def triQ (z : TriPoint) : ℝ := z.1 ^ 2 - z.1 * z.2 + z.2 ^ 2

/-- Literal source definition: source/paper_verification/lattice005.lean:771. -/
def triangularGaussian (α : ℝ) (z : TriPoint) : ℝ :=
  ∑' m : EisInt, Real.exp (-α * triQ (eisEmbed m - z))

/-- Literal source definition: source/paper_verification/lattice005.lean:3105. -/
def e6PhysicalPoint (z : TriTriple) : Fin 6 → ℝ := scaleVec (Real.sqrt 2) (triTripleFlatten z)

/-- Literal source definition: source/paper_verification/lattice005.lean:2619. -/
def e6HoleWitness : TriTriple := ![0,triC,-triC]

/-- Literal source definition: source/paper_verification/lattice005.lean:3444. -/
def E6PaperHole (z : TriTriple) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3), ∃ l : TriTriple, l ∈ l6Set ∧
    ∀ i, z i=e6HoleWitness (σ i)+l i

/-- Literal source definition: source/paper_verification/lattice007.lean:1122. -/
abbrev E7FourSubset := {S : Finset (Fin 8) // S.card=4}

/-- Literal source definition: source/paper_verification/lattice007.lean:1123. -/
abbrev E7PaperIndex := Option E7FourSubset

/-- Literal source definition: source/paper_verification/lattice004.lean:1707. -/
def e8Axis : Fin 8 → ℝ := intVec (fun i ↦ if i = 0 then 1 else 0)

/-- Literal source definition: source/paper_verification/lattice007.lean:1125. -/
def e7PaperAmbient : E7PaperIndex→Fin 8→ℝ
  | none => e8Axis
  | some S => e8Axis+(fun i=>if i∈S.val then 1/2 else 0)

/-- Literal source definition: source/paper_verification/lattice007.lean:1143. -/
def e7PaperPoint (p : E7PaperIndex) : zeroSumSpace := project8 (e7PaperAmbient p)

/-- Literal source definition: source/paper_verification/lattice006.lean:1337. -/
def IsE8Root (r : Fin 8 → ℝ) : Prop := r ∈ dPlusSet 8 ∧ sqDist r 0 = 2

/-- Literal source definition: source/paper_verification/lattice004.lean:1922. -/
def InRM3 (c : BinaryWord8) : Prop := ∃ a : AffineCoefficients3, c = affineWord3 a

/-- Literal source definition: source/paper_verification/lattice004.lean:2275. -/
def bwMSet : Set (Fin 8 → ℝ) :=
  {x | ∃ z : Fin 8 → ℤ, InRM3 (fun i => (z i : Binary)) ∧
    x = fun i => (z i : ℝ) / 2}

/-- Literal source definition: source/paper_verification/lattice006.lean:1341. -/
def bwRootExponent (r g : Fin 8 → ℝ) : ℤ := ⌊2 * ∑ i, r i * g i⌋

/-- Literal source definition: source/paper_verification/lattice006.lean:1343. -/
def bwRootCharacter (r g : Fin 8 → ℝ) : ℝ := (-1 : ℝ) ^ bwRootExponent r g

/-- Ambient lattice quotient classes that contain an actual real deep hole. -/
def DeepTranslationClasses {n : ℕ} (L : AddSubgroup (Fin n → ℝ)) :=
  {C : (Fin n → ℝ) ⧸ L // ∃ x : Fin n → ℝ, IsDeepHole (L : Set _) x ∧
    (x : (Fin n → ℝ) ⧸ L) = C}

/-- The same quotient construction inside E7 dual's actual zero-sum space. -/
def E7DeepTranslationClasses :=
  {C : zeroSumSpace ⧸ AddSubgroup.closure e7ProjectedSet //
    ∃ x : zeroSumSpace, IsE7DeepHole x ∧
      (x : zeroSumSpace ⧸ AddSubgroup.closure e7ProjectedSet) = C}

private theorem e6_closure_eq :
    AddSubgroup.closure e6Set = PaperVerification.ColdSpots.e6AddSubgroup := by
  have h : e6Set = (PaperVerification.ColdSpots.e6AddSubgroup : Set _) :=
    PaperVerification.ColdSpots.e6AddSubgroup_coe.symm
  rw [h, AddSubgroup.closure_eq]

private theorem dPlus_closure_eq (n : ℕ) (heven : Even n) :
    AddSubgroup.closure (dPlusSet n) = PaperVerification.ColdSpots.dPlusAddSubgroup n heven := by
  change AddSubgroup.closure
    ((PaperVerification.ColdSpots.dPlusAddSubgroup n heven) : Set _) = _
  exact AddSubgroup.closure_eq _

private theorem e7_closure_eq :
    AddSubgroup.closure e7ProjectedSet = PaperVerification.ColdSpots.e7ProjectedAddSubgroup := by
  have h : e7ProjectedSet = (PaperVerification.ColdSpots.e7ProjectedAddSubgroup : Set _) :=
    PaperVerification.ColdSpots.e7ProjectedAddSubgroup_coe.symm
  rw [h, AddSubgroup.closure_eq]

private theorem bw16_closure_eq :
    AddSubgroup.closure bw16Set = PaperVerification.ColdSpots.bw16AddSubgroup := by
  have h : bw16Set = (PaperVerification.ColdSpots.bw16AddSubgroup : Set _) :=
    PaperVerification.ColdSpots.bw16AddSubgroup_coe.symm
  rw [h, AddSubgroup.closure_eq]

/-- Introduction table, PDF page2. -/
theorem lattice_translation_class_table :
    Nat.card (DeepTranslationClasses (AddSubgroup.closure e6Set))=2 ∧
    Nat.card (DeepTranslationClasses (AddSubgroup.closure (dPlusSet 8)))=135 ∧
    Nat.card E7DeepTranslationClasses=36 ∧
    Nat.card (DeepTranslationClasses (AddSubgroup.closure bw16Set))=120 ∧
    (∀ n : ℕ, 8 < n → Even n →
      Nat.card (DeepTranslationClasses (AddSubgroup.closure (dPlusSet n)))=n.choose (n/2)) := by
  obtain ⟨h6,h8,h7,hbw,hd⟩ := PaperVerification.ColdSpots.lattice_translation_class_table
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [e6_closure_eq]
    exact h6
  · rw [dPlus_closure_eq 8 (by decide)]
    exact h8
  · unfold E7DeepTranslationClasses
    rw [e7_closure_eq]
    exact h7
  · rw [bw16_closure_eq]
    exact hbw
  · intro n hn heven
    rw [dPlus_closure_eq n heven]
    exact hd n hn heven

/-- Theorem3.3 attained minimum, all even n>=8. -/
theorem dPlusGaussian_minimum {n : ℕ} (hn : 8 ≤ n) (heven : Even n)
    {α : ℝ} (hα : 0 < α) :
    (∀ x, (gaussian α 0 * gaussian α (1 / 2)) ^ (n / 2) ≤ setGaussian (dPlusSet n) α x) ∧
    (∃ x, setGaussian (dPlusSet n) α x = (gaussian α 0 * gaussian α (1 / 2)) ^ (n / 2)) := by
  exact PaperVerification.ColdSpots.dPlusGaussian_minimum hn heven hα

/-- Theorem3.3 dimension-eight equality families. -/
theorem gaussian_E8_minimum_iff_paper_families {α : ℝ} (hα : 0 < α) (x : Fin 8 → ℝ) :
    setGaussian (dPlusSet 8) α x=(gaussian α 0*gaussian α (1/2))^4 ↔ E8PaperHole x := by
  exact PaperVerification.ColdSpots.gaussian_E8_minimum_iff_paper_families hα x

/-- Theorem6.2 full analytic minimum and equality. -/
theorem e7Dual_gaussian_minimum {α : ℝ} (hα : 0 < α) :
    (∀ x, (gaussian α 0 * gaussian α (1 / 2)) ^ 4 / gaussian (2 * α) (1 / 4) ≤
      e7Gaussian α x) ∧
    (∀ x, e7Gaussian α x =
      (gaussian α 0 * gaussian α (1 / 2)) ^ 4 / gaussian (2 * α) (1 / 4) ↔ IsE7DeepHole x) := by
  exact PaperVerification.ColdSpots.e7Dual_gaussian_minimum hα

/-- Equation26 explicit E7 dual equality representatives. -/
theorem isE7DeepHole_iff_paper (x : zeroSumSpace) :
    IsE7DeepHole x ↔ ∃ p : E7PaperIndex,x-e7PaperPoint p∈e7ProjectedSet := by
  exact PaperVerification.ColdSpots.isE7DeepHole_iff_paper x

/-- Equation28 attained BW16 minimum. -/
theorem bw16_gaussian_minimum_literal {α : ℝ} (hα : 0 < α) :
    (∀ z : Fin 16 → ℝ,
      16 * (gaussian (2 * α) (1 / 4) ^ 16 - alternatingGaussian (2 * α) (1 / 4) ^ 16) ≤
        setGaussian bw16Set α z) ∧
      ∃ z, setGaussian bw16Set α z =
        16 * (gaussian (2 * α) (1 / 4) ^ 16 - alternatingGaussian (2 * α) (1 / 4) ^ 16) := by
  exact PaperVerification.ColdSpots.bw16_gaussian_minimum_literal hα

/-- Section7.5 literal full E8-root union. -/
theorem bw16_deepHole_iff_root_union (z : Fin 16 → ℝ) :
    IsDeepHole bw16Set z ↔
      ∃ r : Fin 8 → ℝ, IsE8Root r ∧ ∃ s t : Fin 8 → ℝ,
        s ∈ bwMSet ∧ t ∈ bwMSet ∧ bwRootCharacter r (t - s) = -1 ∧
        z = scaleVec (Real.sqrt 2)
          (Fin.append ((fun i => r i / 2) + s) ((fun i => r i / 2) + t)) := by
  exact PaperVerification.ColdSpots.bw16_deepHole_iff_root_union z

/-- Equation32 attained E6 minimum. -/
theorem e6_gaussian_minimum {α : ℝ} (hα : 0 < α) :
    (∀ x, 3*triangularGaussian (2*α) 0*triangularGaussian (2*α) triC^2 ≤
      setGaussian e6Set α x) ∧
    setGaussian e6Set α (e6PhysicalPoint e6HoleWitness)=
      3*triangularGaussian (2*α) 0*triangularGaussian (2*α) triC^2 := by
  exact PaperVerification.ColdSpots.e6_gaussian_minimum hα

/-- Section8.3 explicit E6 equality loci. -/
theorem e6_cold_spot_description {α : ℝ} (hα : 0 < α) (z : TriTriple) :
    IsColdSpot e6Set α (e6PhysicalPoint z) ↔ E6PaperHole z := by
  exact PaperVerification.ColdSpots.e6_cold_spot_description hα z

/-- Section8.3 explicit E6 deep-hole loci. -/
theorem e6_deep_hole_description (z : TriTriple) :
    IsDeepHole e6Set (e6PhysicalPoint z) ↔ E6PaperHole z := by
  exact PaperVerification.ColdSpots.e6_deep_hole_description z

/-- Equation10, all even n>8. -/
theorem dPlus_gaussian_equality_halfGrid {n : ℕ} (hn : 8 < n) (heven : Even n)
    {α : ℝ} (hα : 0 < α) (x : Fin n → ℝ) :
    setGaussian (dPlusSet n) α x =
      (gaussian α 0 * gaussian α (1 / 2)) ^ (n / 2) ↔ PaperHalfGrid x := by
  have h := PaperVerification.ColdSpots.dPlusGaussian_eq_min_iff_paperHalfGrid hn heven hα x
  rw [PaperVerification.ColdSpots.even_dimension_half_cast heven, Real.rpow_natCast] at h
  change PaperVerification.ColdSpots.setGaussian (PaperVerification.ColdSpots.dPlusSet n) α x =
    (PaperVerification.ColdSpots.gaussian α 0 * PaperVerification.ColdSpots.gaussian α (1/2)) ^ (n/2) ↔
      PaperVerification.ColdSpots.PaperHalfGrid x
  rw [PaperVerification.ColdSpots.setGaussian_dPlus_eq (by omega : 0 < n) hα]
  exact h

/-- Equation28 and Section7.5 literal minimum and full root-union equality. -/
theorem bw16_gaussian_equality_root_union_literal {α : ℝ} (hα : 0 < α) (z : Fin 16 → ℝ) :
    setGaussian bw16Set α z = 16 * (gaussian (2 * α) (1 / 4) ^ 16 - alternatingGaussian (2 * α) (1 / 4) ^ 16) ↔
      ∃ r : Fin 8 → ℝ, IsE8Root r ∧ ∃ s t : Fin 8 → ℝ,
        s ∈ bwMSet ∧ t ∈ bwMSet ∧ bwRootCharacter r (t - s) = -1 ∧
        z = scaleVec (Real.sqrt 2)
          (Fin.append ((fun i => r i / 2) + s) ((fun i => r i / 2) + t)) := by
  have h := PaperVerification.ColdSpots.bw16_gaussian_equality_iff_root_union hα z
  rw [PaperVerification.ColdSpots.bwGammaMinimum_eq_quarter (by positivity : 0 < 2 * α)] at h
  exact h

end PalomarColdSpotsSupplemental
