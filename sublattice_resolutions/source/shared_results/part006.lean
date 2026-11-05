module
public import graph_foundation.part009
public import shared_results.part005

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.DeterminantalCyclesComplete -/
section
section
namespace FourPapers.Sublattice
/-- Two-row exterior coordinates use the row-first linear order: all first-row
variables precede all second-row variables. Mathlib's untagged sum otherwise
carries only the disjoint partial order. -/
scoped instance twoRowLinearOrder {I : Type*} [LinearOrder I] : LinearOrder (Sum I I) :=
  LinearOrder.lift' (fun z : Sum I I => (toLex z : Lex (Sum I I))) (fun _ _ h => h)
end FourPapers.Sublattice

open scoped FourPapers.Sublattice

/- EXACT SOURCE BODY: FourPapers.Sublattice.CliqueCycles -/
section DeterminantalSource0

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

/-!
# Rank-one exterior cycles

The vanishing of the two-by-two minors is used as an identity in the actual
coefficient ring. Contraction, followed by exterior substitution, then gives
closed representatives for the linear strand of a two-row determinantal ideal.
No assertion about their spanning homology is made in this module.
-/

noncomputable section
namespace FourPapers.Sublattice
open CliffordAlgebra
universe u v w z
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- All minors of the two functionals vanish, as identities on the whole module. -/
def RankOneFunctionals (φ ψ : Module.Dual R M) : Prop :=
  ∀ v w, φ v * ψ w = ψ v * φ w

lemma rankOneFunctionals_of_basis {I : Type w} (b : Module.Basis I R M)
    (φ ψ : Module.Dual R M)
    (h : ∀ i j, φ (b i) * ψ (b j) = ψ (b i) * φ (b j)) :
    RankOneFunctionals φ ψ := by
  have he : φ.smulRight ψ = ψ.smulRight φ := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    exact h i j
  intro v w
  exact LinearMap.congr_fun (LinearMap.congr_fun he v) w

lemma rankOne_contraction_scale (φ ψ : Module.Dual R M)
    (h : RankOneFunctionals φ ψ) (v : M) (z : ExteriorAlgebra R M) :
    φ v • contractLeft ψ z = ψ v • contractLeft φ z := by
  have he : φ v • ψ = ψ v • φ := by
    apply LinearMap.ext
    intro w
    exact h v w
  have hh := congrArg (fun f : Module.Dual R M =>
    contractLeft (Q := (0 : QuadraticForm R M)) f z) he
  simpa only [map_smul, LinearMap.smul_apply] using hh

/-- In a rank-one two-row matrix, the two different contractions compose to
zero, over every commutative ring and in every exterior degree. -/
theorem rankOne_contraction_comp (φ ψ : Module.Dual R M)
    (h : RankOneFunctionals φ ψ) (z : ExteriorAlgebra R M) :
    contractLeft ψ (contractLeft φ z) = 0 := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [contractLeft_algebraMap, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | ι_mul z v hz =>
    rw [contractLeft_ι_mul, map_sub, map_smul, contractLeft_ι_mul,
      hz, mul_zero, sub_zero]
    exact sub_eq_zero.mpr (rankOne_contraction_scale φ ψ h v z)

variable {P : Type z} [AddCommGroup P] [Module R P]

/-- Actual exterior-algebra representative obtained by substituting a pair of
row vectors after contracting once against the first row. -/
def rankOneExteriorCycle (f : M →ₗ[R] P) (φ : Module.Dual R M)
    (z : ExteriorAlgebra R M) : ExteriorAlgebra R P :=
  ExteriorAlgebra.map f (contractLeft φ z)

/-- Substitution with pulled-back differential `φ + c ψ` gives a genuine cycle.
Taking coefficients of the parameter `c` produces the integral determinantal
linear-strand cycles, without dividing by an integer. -/
theorem rankOneExteriorCycle_closed (f : M →ₗ[R] P)
    (φ ψ : Module.Dual R M) (d : Module.Dual R P) (c : R)
    (h : RankOneFunctionals φ ψ) (hf : d.comp f = φ + c • ψ)
    (z : ExteriorAlgebra R M) :
    contractLeft d (rankOneExteriorCycle f φ z) = 0 := by
  rw [rankOneExteriorCycle, ExteriorAlgebra.contractLeft_map, hf]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    contractLeft_contractLeft, rankOne_contraction_comp φ ψ h, smul_zero,
    add_zero, map_zero]

end FourPapers.Sublattice

end
end DeterminantalSource0

/- EXACT SOURCE BODY: FourPapers.Sublattice.PolynomialExteriorCoefficient -/
section DeterminantalSource1

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

noncomputable section
namespace FourPapers.Sublattice
open Classical CliffordAlgebra
universe u v
variable {R : Type u} [CommRing R]
variable {I : Type v} [Fintype I] [LinearOrder I]

/-- Explicit coefficient extraction in the standard exterior basis. The
parameter is a polynomial coefficient, not a formal or assumed deformation. -/
def polynomialExteriorCoefficient (n : ℕ) :
    ExteriorAlgebra (Polynomial R) (I → Polynomial R) →ₗ[R]
      ExteriorAlgebra R (I → R) :=
  (Finsupp.lsum R (fun F : Finset I =>
    (Polynomial.lcoeff R n).smulRight ((Pi.basisFun R I).ExteriorAlgebra F))).comp
    (((Pi.basisFun (Polynomial R) I).ExteriorAlgebra).repr.toLinearMap.restrictScalars R)

lemma polynomialExteriorCoefficient_smul_basis (n : ℕ) (p : Polynomial R)
    (F : Finset I) :
    polynomialExteriorCoefficient (R := R) (I := I) n
      (p • (Pi.basisFun (Polynomial R) I).ExteriorAlgebra F) =
        p.coeff n • (Pi.basisFun R I).ExteriorAlgebra F := by
  simp [polynomialExteriorCoefficient,LinearMap.comp_apply,Finsupp.lsum_single]

lemma functional_eq_sum_coordinates {S : Type*} [CommRing S]
    (φ : Module.Dual S (I → S)) :
    φ = ∑i, φ (Pi.basisFun S I i) • (Pi.basisFun S I).coord i := by
  apply (Pi.basisFun S I).ext
  intro i
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp

/-- The literal signed deletion formula for a contraction with any functional. -/
lemma contraction_basis_sum {S : Type*} [CommRing S]
    (φ : Module.Dual S (I → S)) (F : Finset I) :
    contractLeft φ ((Pi.basisFun S I).ExteriorAlgebra F) =
      ∑i∈F, φ (Pi.basisFun S I i) •
        (TauCeti.ExteriorAlgebra.basisEraseSign i F •
          (Pi.basisFun S I).ExteriorAlgebra (F.erase i)) := by
  conv_lhs => rw [functional_eq_sum_coordinates φ]
  rw [map_sum]
  simp only [LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
    TauCeti.ExteriorAlgebra.contractLeft_coord_basis]
  simp only [smul_ite,smul_zero]
  rw [← Finset.sum_filter]
  simp

/-- Extracting a polynomial coefficient commutes with an actual Koszul
contraction whose entries are constant polynomials. -/
theorem polynomialExteriorCoefficient_contraction
    (φ : Module.Dual R (I → R))
    (φT : Module.Dual (Polynomial R) (I → Polynomial R))
    (hφ : ∀i, φT (Pi.basisFun (Polynomial R) I i) =
      Polynomial.C (φ (Pi.basisFun R I i)))
    (n : ℕ) (x : ExteriorAlgebra (Polynomial R) (I → Polynomial R)) :
    polynomialExteriorCoefficient n (contractLeft φT x) =
      contractLeft φ (polynomialExteriorCoefficient n x) := by
  let b := (Pi.basisFun (Polynomial R) I).ExteriorAlgebra
  have hb (p : Polynomial R) (F : Finset I) :
      polynomialExteriorCoefficient (R := R) n (contractLeft φT (p • b F)) =
        contractLeft φ (polynomialExteriorCoefficient n (p • b F)) := by
    rw [map_smul,contraction_basis_sum,Finset.smul_sum,map_sum,
      polynomialExteriorCoefficient_smul_basis,map_smul,contraction_basis_sum,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hφ]
    rcases Int.units_eq_one_or (TauCeti.ExteriorAlgebra.basisEraseSign i F) with hs | hs
    · simp only [hs,one_smul,smul_smul]
      rw [polynomialExteriorCoefficient_smul_basis]
      simp [Polynomial.coeff_mul_C]
    · simp only [hs,Units.neg_smul,one_smul,smul_neg,map_neg,smul_smul]
      rw [polynomialExteriorCoefficient_smul_basis]
      simp [Polynomial.coeff_mul_C]
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro F hF
  exact hb _ F

/-- Each coefficient of a closed polynomial exterior element is an actual
cycle. This remains valid in every characteristic and over rings with torsion. -/
theorem polynomialExteriorCoefficient_cycle
    (φ : Module.Dual R (I → R))
    (φT : Module.Dual (Polynomial R) (I → Polynomial R))
    (hφ : ∀i, φT (Pi.basisFun (Polynomial R) I i) =
      Polynomial.C (φ (Pi.basisFun R I i)))
    (n : ℕ) (x : ExteriorAlgebra (Polynomial R) (I → Polynomial R))
    (hx : contractLeft φT x=0) :
    contractLeft φ (polynomialExteriorCoefficient n x)=0 := by
  rw [←polynomialExteriorCoefficient_contraction φ φT hφ n x,hx,map_zero]

end FourPapers.Sublattice

end
end DeterminantalSource1

/- EXACT SOURCE BODY: FourPapers.Sublattice.DeterminantalCycles -/
section DeterminantalSource2

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

/-!
# Integral two-row determinantal cycle representatives

A clique of columns has rank at most one in the binomial quotient. The formulas
below give the actual cycles, before imposing any spanning theorem: substitute
`e_x + T e_y` into the contraction of a column exterior monomial, and take the
specified coefficient of the honest polynomial parameter `T`.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical CliffordAlgebra
universe u v
variable {R : Type u} [CommRing R]
variable {I : Type v} [Fintype I] [LinearOrder I]

/-- Functional with the given entries in the standard column basis. -/
def columnFunctional (x : I → R) : Module.Dual R (I → R) :=
  ∑i, x i • (Pi.basisFun R I).coord i

@[simp] lemma columnFunctional_basis (x : I → R) (i : I) :
    columnFunctional x (Pi.basisFun R I i)=x i := by
  simp only [columnFunctional, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp

/-- The actual two-row Koszul functional. -/
def twoRowFunctional (x y : I → R) : Module.Dual R (Sum I I → R) :=
  ∑i, x i • (Pi.basisFun R (Sum I I)).coord (Sum.inl i) +
  ∑i, y i • (Pi.basisFun R (Sum I I)).coord (Sum.inr i)

@[simp] lemma twoRowFunctional_basis_inl (x y : I → R) (i : I) :
    twoRowFunctional x y (Pi.basisFun R (Sum I I) (Sum.inl i))=x i := by
  simp only [twoRowFunctional, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
    Sum.inr_ne_inl]
  simp

@[simp] lemma twoRowFunctional_basis_inr (x y : I → R) (i : I) :
    twoRowFunctional x y (Pi.basisFun R (Sum I I) (Sum.inr i))=y i := by
  simp only [twoRowFunctional, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
    Sum.inr_ne_inl]
  simp

/-- Substitution sending column `i` to `e_(x,i) + T e_(y,i)`. -/
def twoRowParameterSubstitution :
    (I → Polynomial R) →ₗ[Polynomial R] (Sum I I → Polynomial R) :=
  (Pi.basisFun (Polynomial R) I).constr (M' := Sum I I → Polynomial R) (Polynomial R)
    (fun i : I => Pi.basisFun (Polynomial R) (Sum I I) (Sum.inl i) +
      (Polynomial.X : Polynomial R) •
        Pi.basisFun (Polynomial R) (Sum I I) (Sum.inr i))

lemma twoRowParameterSubstitution_pullback (x y : I → R) :
    (twoRowFunctional (Polynomial.C ∘ x) (Polynomial.C ∘ y)).comp
      (twoRowParameterSubstitution (R := R) (I := I)) =
        columnFunctional (Polynomial.C ∘ x) +
          (Polynomial.X : Polynomial R) • columnFunctional (Polynomial.C ∘ y) := by
  apply (Pi.basisFun (Polynomial R) I).ext
  intro i
  simp only [LinearMap.comp_apply, twoRowParameterSubstitution,
    Module.Basis.constr_basis, map_add, map_smul, twoRowFunctional_basis_inl,
    twoRowFunctional_basis_inr, LinearMap.add_apply, LinearMap.smul_apply,
    columnFunctional_basis]

lemma polynomialColumns_rankOne (x y : I → R)
    (h : ∀i j, x i*y j=y i*x j) :
    RankOneFunctionals (columnFunctional (Polynomial.C ∘ x))
      (columnFunctional (Polynomial.C ∘ y)) := by
  apply rankOneFunctionals_of_basis (Pi.basisFun (Polynomial R) I)
  intro i j
  simp only [columnFunctional_basis,Function.comp_apply,←map_mul,h]

/-- Closed polynomial exterior element associated with a clique of columns. -/
def determinantalCyclePolynomial (x y : I → R) (F : Finset I) :
    ExteriorAlgebra (Polynomial R) (Sum I I → Polynomial R) :=
  rankOneExteriorCycle (twoRowParameterSubstitution (R := R) (I := I))
    (columnFunctional (Polynomial.C ∘ x))
    ((Pi.basisFun (Polynomial R) I).ExteriorAlgebra F)

lemma determinantalCyclePolynomial_closed (x y : I → R)
    (h : ∀i j, x i*y j=y i*x j) (F : Finset I) :
    contractLeft (twoRowFunctional (Polynomial.C ∘ x) (Polynomial.C ∘ y))
      (determinantalCyclePolynomial x y F)=0 := by
  exact rankOneExteriorCycle_closed (twoRowParameterSubstitution (R := R) (I := I))
    (columnFunctional (Polynomial.C ∘ x)) (columnFunctional (Polynomial.C ∘ y))
    (twoRowFunctional (Polynomial.C ∘ x) (Polynomial.C ∘ y)) Polynomial.X
    (polynomialColumns_rankOne x y h) (twoRowParameterSubstitution_pullback x y)
    ((Pi.basisFun (Polynomial R) I).ExteriorAlgebra F)

/-- The coefficient cycle; every coefficient is integral in the two rows. -/
def determinantalCycle (x y : I → R) (F : Finset I) (j : ℕ) :
    ExteriorAlgebra R (Sum I I → R) :=
  polynomialExteriorCoefficient j (determinantalCyclePolynomial x y F)

/-- Every coefficient representative is an actual two-row Koszul cycle. -/
theorem determinantalCycle_closed (x y : I → R)
    (h : ∀i j, x i*y j=y i*x j) (F : Finset I) (j : ℕ) :
    contractLeft (twoRowFunctional x y) (determinantalCycle x y F j)=0 := by
  have hconst : ∀ i : Sum I I,
      twoRowFunctional (Polynomial.C ∘ x) (Polynomial.C ∘ y)
          (Pi.basisFun (Polynomial R) (Sum I I) i) =
        Polynomial.C (twoRowFunctional x y (Pi.basisFun R (Sum I I) i)) := by
    intro i
    cases i with
    | inl i => simp only [twoRowFunctional_basis_inl, Function.comp_apply]
    | inr i => simp only [twoRowFunctional_basis_inr, Function.comp_apply]
  exact polynomialExteriorCoefficient_cycle (twoRowFunctional x y)
    (twoRowFunctional (Polynomial.C ∘ x) (Polynomial.C ∘ y)) hconst j
    (determinantalCyclePolynomial x y F) (determinantalCyclePolynomial_closed x y h F)

end FourPapers.Sublattice

end
end DeterminantalSource2

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.PolynomialExteriorConstant -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000

noncomputable section
namespace FourPapers.Sublattice
open Classical CliffordAlgebra Polynomial
open scoped FourPapers.Sublattice
universe u v
variable {R : Type u} [CommRing R]
variable {I : Type v} [Fintype I] [LinearOrder I]

def polynomialVectorConstant : (I → R) →ₗ[R] (I → R[X]) :=
  (Pi.basisFun R I).constr R (fun i => Pi.basisFun R[X] I i)

@[simp] lemma polynomialVectorConstant_basis (i : I) :
    polynomialVectorConstant (R := R) (Pi.basisFun R I i) = Pi.basisFun R[X] I i := by
  exact (Pi.basisFun R I).constr_basis R _ i

/-- Actual scalar extension of the exterior generators, constructed by the
universal property of the exterior algebra. -/
def polynomialExteriorConstant :
    ExteriorAlgebra R (I → R) →ₐ[R] ExteriorAlgebra R[X] (I → R[X]) :=
  ExteriorAlgebra.lift R
    ⟨((ExteriorAlgebra.ι R[X]).restrictScalars R).comp polynomialVectorConstant,
      fun v => ExteriorAlgebra.ι_sq_zero (polynomialVectorConstant v)⟩

@[simp] lemma polynomialExteriorConstant_generator (i : I) :
    polynomialExteriorConstant (R := R)
      (ExteriorAlgebra.ι R (Pi.basisFun R I i)) =
        ExteriorAlgebra.ι R[X] (Pi.basisFun R[X] I i) := by
  simp only [polynomialExteriorConstant, ExteriorAlgebra.lift_ι_apply,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, polynomialVectorConstant_basis]

@[simp] lemma polynomialExteriorConstant_basis (F : Finset I) :
    polynomialExteriorConstant (R := R) ((Pi.basisFun R I).ExteriorAlgebra F) =
      (Pi.basisFun R[X] I).ExteriorAlgebra F := by
  rw [Module.Basis.exteriorAlgebra_eq_prod_map_sort,
    Module.Basis.exteriorAlgebra_eq_prod_map_sort, map_list_prod]
  simp only [List.map_map, Function.comp_def, polynomialExteriorConstant_generator]

/-- Coefficient extraction after a genuine constant scalar extension. This is
proved for every exterior element, so it also applies to ordered mixed words
before collecting their shuffle signs. -/
theorem polynomialExteriorCoefficient_constant_smul (p : R[X]) (j : ℕ)
    (z : ExteriorAlgebra R (I → R)) :
    polynomialExteriorCoefficient j (p • polynomialExteriorConstant z) = p.coeff j • z := by
  let b := (Pi.basisFun R I).ExteriorAlgebra
  have h : ∀ z ∈ Submodule.span R (Set.range b),
      polynomialExteriorCoefficient j (p • polynomialExteriorConstant z) = p.coeff j • z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨F, rfl⟩ := hz
        rw [polynomialExteriorConstant_basis, polynomialExteriorCoefficient_smul_basis]
    | zero => simp
    | add x y hx hy ihx ihy => simp only [map_add, smul_add, ihx, ihy]
    | smul r x hx ih =>
        rw [map_smul polynomialExteriorConstant r x, smul_comm p r,
          map_smul (polynomialExteriorCoefficient j) r _, ih, smul_comm r (p.coeff j)]
  exact h z (by rw [b.span_eq]; trivial)

lemma polynomialExteriorCoefficient_X_pow_constant (q j : ℕ)
    (z : ExteriorAlgebra R (I → R)) :
    polynomialExteriorCoefficient j ((X ^ q : R[X]) • polynomialExteriorConstant z) =
      if q = j then z else 0 := by
  rw [polynomialExteriorCoefficient_constant_smul]
  by_cases h : q = j
  · subst j
    simp
  · simp [Polynomial.coeff_X_pow, h, Ne.symm h]

lemma polynomial_C_smul_exterior (r : R)
    (z : ExteriorAlgebra R[X] (I → R[X])) : (C r : R[X]) • z = r • z :=
  IsScalarTower.algebraMap_smul R[X] r z

section OrderedProducts
variable {A : Type*} [Ring A] [Algebra R A]

/-- The product in increasing column order, as a multilinear map indexed by
the actual columns in the finite set. -/
def orderedColumnProduct (F : Finset I) : MultilinearMap R (fun _ : F => A) A :=
  (MultilinearMap.mkPiAlgebraFin R F.card A).domDomCongr (F.orderIsoOfFin rfl).toEquiv

lemma orderedColumnProduct_apply (F : Finset I) (f : F → A) :
    orderedColumnProduct (R := R) F f =
      (List.ofFn (fun i : Fin F.card => f (F.orderIsoOfFin rfl i))).prod := rfl

lemma orderedColumnProduct_map {B : Type*} [Ring B] [Algebra R B]
    (φ : A →ₐ[R] B) (F : Finset I) (f : F → A) :
    φ (orderedColumnProduct (R := R) F f) =
      orderedColumnProduct (R := R) F (fun i => φ (f i)) := by
  simp only [orderedColumnProduct_apply, map_list_prod, List.map_ofFn, Function.comp_def]

lemma orderedColumnProduct_add (F : Finset I) (f g : F → A) :
    orderedColumnProduct (R := R) F (f + g) =
      ∑ U : Finset F, orderedColumnProduct (R := R) F (U.piecewise f g) :=
  MultilinearMap.map_add_univ _ _ _

lemma orderedColumnProduct_smul (F : Finset I) (c : F → R) (f : F → A) :
    orderedColumnProduct (R := R) F (fun i => c i • f i) =
      (∏ i, c i) • orderedColumnProduct (R := R) F f :=
  MultilinearMap.map_smul_univ _ _ _

end OrderedProducts

lemma polynomialExteriorConstant_orderedProduct {J : Type*} [Fintype J] [LinearOrder J]
    (F : Finset I) (f : F → ExteriorAlgebra R (J → R)) :
    polynomialExteriorConstant (orderedColumnProduct (R := R) F f) =
      orderedColumnProduct (R := R[X]) F (fun i => polynomialExteriorConstant (f i)) := by
  simp only [orderedColumnProduct_apply, map_list_prod, List.map_ofFn, Function.comp_def]

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.polynomialExteriorCoefficient_constant_smul

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.DeterminantalExpansion -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

noncomputable section
namespace FourPapers.Sublattice
open Classical CliffordAlgebra Polynomial
open scoped FourPapers.Sublattice
universe u v
variable {R : Type u} [CommRing R]
variable {I : Type v} [Fintype I] [LinearOrder I]

lemma orderedColumnProduct_of_function {A : Type*} [Ring A] [Algebra R A]
    (F : Finset I) (f : I → A) :
    orderedColumnProduct (R := R) F (fun i => f i.val) = (F.sort.map f).prod := by
  rw [orderedColumnProduct_apply, List.ofFn_eq_map]
  change ((List.finRange F.card).map (f ∘ F.orderEmbOfFin rfl)).prod = _
  rw [← List.map_map, Finset.listMap_orderEmbOfFin_finRange]

lemma orderedColumnProduct_exteriorBasis (F : Finset I) :
    orderedColumnProduct (R := R) F
      (fun i => ExteriorAlgebra.ι R (Pi.basisFun R I i.val)) =
        (Pi.basisFun R I).ExteriorAlgebra F := by
  rw [orderedColumnProduct_of_function F
    (fun i : I => ExteriorAlgebra.ι R (Pi.basisFun R I i)),
    Module.Basis.exteriorAlgebra_eq_prod_map_sort]
  simp only [List.map_map, Function.comp_def]

/-- An ordered word with one chosen exterior row at each column. The column
order is retained, so this formula introduces no implicit shuffle signs. -/
def mixedRowWord (F : Finset I) (U : Finset F) : ExteriorAlgebra R (Sum I I → R) :=
  orderedColumnProduct (R := R) F (fun i =>
    if i ∈ U then ExteriorAlgebra.ι R (Pi.basisFun R (Sum I I) (Sum.inl i.val))
    else ExteriorAlgebra.ι R (Pi.basisFun R (Sum I I) (Sum.inr i.val)))

lemma twoRowParameterSubstitution_exteriorBasis (F : Finset I) :
    ExteriorAlgebra.map (twoRowParameterSubstitution (R := R) (I := I))
      ((Pi.basisFun R[X] I).ExteriorAlgebra F) =
      orderedColumnProduct (R := R[X]) F (fun i =>
        ExteriorAlgebra.ι R[X] (Pi.basisFun R[X] (Sum I I) (Sum.inl i.val)) +
        (X : R[X]) • ExteriorAlgebra.ι R[X] (Pi.basisFun R[X] (Sum I I) (Sum.inr i.val))) := by
  rw [← orderedColumnProduct_exteriorBasis, orderedColumnProduct_map]
  congr 1
  funext i
  simp only [ExteriorAlgebra.map_apply_ι, twoRowParameterSubstitution,
    Module.Basis.constr_basis, map_add, map_smul]

lemma mixedRowWord_parameterProduct (F : Finset I) (U : Finset F) :
    orderedColumnProduct (R := R[X]) F
      (U.piecewise
        (fun i => ExteriorAlgebra.ι R[X]
          (Pi.basisFun R[X] (Sum I I) (Sum.inl i.val)))
        (fun i => (X : R[X]) • ExteriorAlgebra.ι R[X]
          (Pi.basisFun R[X] (Sum I I) (Sum.inr i.val)))) =
      (X ^ (F.card - U.card) : R[X]) • polynomialExteriorConstant (mixedRowWord F U) := by
  have heq : U.piecewise
        (fun i => ExteriorAlgebra.ι R[X]
          (Pi.basisFun R[X] (Sum I I) (Sum.inl i.val)))
        (fun i => (X : R[X]) • ExteriorAlgebra.ι R[X]
          (Pi.basisFun R[X] (Sum I I) (Sum.inr i.val))) =
      fun i => (if i ∈ U then (1 : R[X]) else X) •
        polynomialExteriorConstant
          (if i ∈ U then ExteriorAlgebra.ι R (Pi.basisFun R (Sum I I) (Sum.inl i.val))
           else ExteriorAlgebra.ι R (Pi.basisFun R (Sum I I) (Sum.inr i.val))) := by
    funext i
    by_cases hi : i ∈ U
    · simp only [Finset.piecewise, if_pos hi, one_smul,
        polynomialExteriorConstant_generator]
    · simp only [Finset.piecewise, if_neg hi,
        polynomialExteriorConstant_generator]
  rw [heq, orderedColumnProduct_smul,
    ← polynomialExteriorConstant_orderedProduct]
  have hp : (∏ i : F, if i ∈ U then (1 : R[X]) else X) = X ^ (F.card - U.card) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have hc : Finset.univ.filter (fun i : F => i ∉ U) = Uᶜ := by ext i; simp
    rw [hc, Finset.card_compl]
    simp
  rw [hp]
  rfl

/-- Complete exterior expansion of the genuine polynomial substitution. -/
theorem twoRowParameterSubstitution_expand (F : Finset I) :
    ExteriorAlgebra.map (twoRowParameterSubstitution (R := R) (I := I))
      ((Pi.basisFun R[X] I).ExteriorAlgebra F) =
      ∑ U : Finset F, (X ^ (F.card - U.card) : R[X]) •
        polynomialExteriorConstant (mixedRowWord F U) := by
  rw [twoRowParameterSubstitution_exteriorBasis]
  change orderedColumnProduct (R := R[X]) F
    ((fun i : F => ExteriorAlgebra.ι R[X]
      (Pi.basisFun R[X] (Sum I I) (Sum.inl i.val))) +
     (fun i : F => (X : R[X]) • ExteriorAlgebra.ι R[X]
      (Pi.basisFun R[X] (Sum I I) (Sum.inr i.val)))) = _
  rw [orderedColumnProduct_add]
  exact Finset.sum_congr rfl (fun U _ => mixedRowWord_parameterProduct F U)

/-- Extracting a specified parameter coefficient keeps exactly those ordered
words with the specified number of second-row exterior generators. -/
theorem twoRowParameterSubstitution_coefficient (F : Finset I) (j : ℕ) :
    polynomialExteriorCoefficient j
      (ExteriorAlgebra.map (twoRowParameterSubstitution (R := R) (I := I))
        ((Pi.basisFun R[X] I).ExteriorAlgebra F)) =
      ∑ U : Finset F, if F.card - U.card = j then mixedRowWord F U else 0 := by
  rw [twoRowParameterSubstitution_expand, map_sum]
  apply Finset.sum_congr rfl
  intro U _
  exact polynomialExteriorCoefficient_X_pow_constant _ _ _

/-- The complete, integral signed formula for the determinant coefficient
cycle. Every coefficient is a single first-row variable; no division and no
assumption on the characteristic is used. -/
theorem determinantalCycle_expansion (x y : I → R) (F : Finset I) (j : ℕ) :
    determinantalCycle x y F j =
      ∑ i ∈ F, x i • (TauCeti.ExteriorAlgebra.basisEraseSign i F •
        ∑ U : Finset (F.erase i),
          if (F.erase i).card - U.card = j then mixedRowWord (F.erase i) U else 0) := by
  unfold determinantalCycle determinantalCyclePolynomial rankOneExteriorCycle
  simp only [contraction_basis_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  let f := ExteriorAlgebra.map (twoRowParameterSubstitution (R := R) (I := I))
  simp only [columnFunctional_basis, Function.comp_apply]
  rw [map_smul f, map_zsmul_unit f, polynomial_C_smul_exterior,
    map_smul (polynomialExteriorCoefficient j), map_zsmul_unit (polynomialExteriorCoefficient j)]
  rw [twoRowParameterSubstitution_coefficient]

/-- The first-row assignment of an expansion term includes the column that
was contracted; the coefficient variable and all exterior variables therefore
carry one combined row/column multidegree. -/
def mixedWordAssignment (F : Finset I) (i : I) (U : Finset (F.erase i)) : Finset I :=
  insert i (U.image Subtype.val)

lemma mixedWordAssignment_subset (F : Finset I) (i : I) (hi : i ∈ F)
    (U : Finset (F.erase i)) : mixedWordAssignment F i U ⊆ F := by
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact hi
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_of_mem_erase b.property

lemma mixedWordAssignment_card (F : Finset I) (i : I) (U : Finset (F.erase i)) :
    (mixedWordAssignment F i U).card = U.card + 1 := by
  have hi : i ∉ U.image Subtype.val := by
    rintro hi
    obtain ⟨a, ha, hai⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_erase.mp a.property).1 hai
  rw [mixedWordAssignment, Finset.card_insert_of_notMem hi,
    Finset.card_image_of_injective U Subtype.val_injective]

lemma mixedWordAssignment_card_of_coefficient (F : Finset I) (i : I) (hi : i ∈ F)
    (U : Finset (F.erase i)) (j : ℕ) (hj : (F.erase i).card - U.card = j) :
    (mixedWordAssignment F i U).card + j = F.card := by
  have hu : U.card ≤ (F.erase i).card := by
    calc U.card ≤ Fintype.card (F.erase i) := Finset.card_le_univ U
         _ = (F.erase i).card := Fintype.card_coe _
  rw [mixedWordAssignment_card]
  have he := Finset.card_erase_add_one hi
  omega

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.determinantalCycle_expansion

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ExteriorOrderedWords -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CliffordAlgebra
open scoped FourPapers.Sublattice
universe u v w
variable {R : Type u} [CommRing R]
variable {I : Type v} [LinearOrder I]
variable {M : Type w} [AddCommGroup M] [Module R M]

variable [Fintype I]

lemma orderedColumnProduct_generators_mem (F : Finset I) (f : F → M) :
    orderedColumnProduct (R := R) F (fun i => ExteriorAlgebra.ι R (f i)) ∈
      (⋀[R]^F.card M) := by
  have h : ExteriorAlgebra.ιMulti R F.card
      (fun i : Fin F.card => f (F.orderIsoOfFin rfl i)) ∈
      (⋀[R]^F.card M : Submodule R (ExteriorAlgebra R M)) :=
    ExteriorAlgebra.ιMulti_range R F.card (Set.mem_range_self _)
  simpa only [ExteriorAlgebra.ιMulti_apply, orderedColumnProduct_apply,
    Function.comp_apply] using h

lemma mixedRowWord_exteriorDegree (F : Finset I) (U : Finset F) :
    mixedRowWord (R := R) F U ∈ (⋀[R]^F.card (Sum I I → R)) := by
  unfold mixedRowWord
  have he : (fun i : F =>
      if i ∈ U then ExteriorAlgebra.ι R (Pi.basisFun R (Sum I I) (Sum.inl i.val))
      else ExteriorAlgebra.ι R (Pi.basisFun R (Sum I I) (Sum.inr i.val))) =
      fun i : F => ExteriorAlgebra.ι R
        (if i ∈ U then Pi.basisFun R (Sum I I) (Sum.inl i.val)
         else Pi.basisFun R (Sum I I) (Sum.inr i.val)) := by
    funext i
    split_ifs <;> rfl
  rw [he]
  exact orderedColumnProduct_generators_mem F _

/-- The determinant representative lies in exactly the required exterior
degree, independently of the coefficient characteristic. -/
theorem determinantalCycle_exteriorDegree (x y : I → R) (F : Finset I) (j : ℕ) :
    determinantalCycle x y F j ∈ (⋀[R]^(F.card - 1) (Sum I I → R)) := by
  rw [determinantalCycle_expansion]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  rcases Int.units_eq_one_or (TauCeti.ExteriorAlgebra.basisEraseSign i F) with hs | hs
  · rw [hs, one_smul]
    apply Submodule.sum_mem
    intro U hU
    split_ifs
    · simpa only [Finset.card_erase_of_mem hi] using mixedRowWord_exteriorDegree (F.erase i) U
    · exact Submodule.zero_mem _
  · rw [hs, Units.neg_smul, one_smul]
    apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro U hU
    split_ifs
    · simpa only [Finset.card_erase_of_mem hi] using mixedRowWord_exteriorDegree (F.erase i) U
    · exact Submodule.zero_mem _

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.exterior_word_unit_basis
#print axioms FourPapers.Sublattice.determinantalCycle_exteriorDegree

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ColoredColon -/
section

/-! # Exact color counts and same-color coefficient colons

The predecessor order on the augmented rows is the paper's lexicographic
order, beginning with color. Cross-color predecessor ratios have a positive
color coordinate. Consequently the color-zero restriction of each actual
chain coefficient ideal is precisely the sum of same-color colons.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
universe u
variable {d r : ℕ} {n : Fin d → ℕ}

def coloredExponent (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) :
    Exponent (FiniteVariable.{u} (coloredRows (r := r) n)) :=
  Finsupp.equivFunOnFinite.symm fun v =>
    Fin.cases (fun c => m c) (fun i c => a ⟨i,c⟩) v.1 v.2

@[simp] theorem coloredExponent_zero (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) (c : ULift.{u} (Fin r)) :
    coloredExponent m a ⟨0,c⟩=m c := rfl
@[simp] theorem coloredExponent_succ (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) (v : FiniteVariable.{u} n) :
    coloredExponent m a ⟨v.1.succ,v.2⟩=a v := rfl

def colorExponent : Exponent (FiniteVariable.{u} (coloredRows (r := r) n)) →+
    (ULift.{u} (Fin r) →₀ ℕ) where
  toFun a := Finsupp.equivFunOnFinite.symm fun c => a ⟨0,c⟩
  map_zero' := by ext c; rfl
  map_add' a b := by ext v; rfl

def baseExponent : Exponent (FiniteVariable.{u} (coloredRows (r := r) n)) →+
    Exponent (FiniteVariable.{u} n) where
  toFun a := Finsupp.equivFunOnFinite.symm fun v => a ⟨v.1.succ,v.2⟩
  map_zero' := by ext v; rfl
  map_add' a b := by ext v; rfl

@[simp] theorem colorExponent_coloredExponent (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) : colorExponent (coloredExponent m a)=m := by
  ext c
  change coloredExponent m a ⟨0,c⟩=m c
  exact coloredExponent_zero m a c
@[simp] theorem baseExponent_coloredExponent (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) : baseExponent (coloredExponent m a)=a := by
  ext v
  change coloredExponent m a ⟨v.1.succ,v.2⟩=a v
  exact coloredExponent_succ m a v

lemma coloredExponent_le_iff (m l : ULift.{u} (Fin r) →₀ ℕ)
    (a b : Exponent (FiniteVariable.{u} n)) :
    coloredExponent m a≤coloredExponent l b ↔ m≤l ∧ a≤b := by
  constructor
  · intro h
    exact ⟨fun c => h ⟨0,c⟩,fun v => h ⟨v.1.succ,v.2⟩⟩
  · rintro ⟨hm,ha⟩ ⟨i,j⟩
    revert j
    exact Fin.cases (fun c => hm c) (fun i c => ha ⟨i,c⟩) i

@[simp] theorem coloredExponent_sub (m l : ULift.{u} (Fin r) →₀ ℕ)
    (a b : Exponent (FiniteVariable.{u} n)) :
    coloredExponent m a-coloredExponent l b=coloredExponent (m-l) (a-b) := by
  ext ⟨i,j⟩
  revert j
  exact Fin.cases (fun _ => rfl) (fun _ _ => rfl) i

lemma coloredRowExponent (c : Fin r) (a : FiniteTuple n) :
    finiteRowExponent (coloredRows (r := r) n) (coloredTuple n c a)=
      coloredExponent (Finsupp.single (ULift.up c) 1) (finiteRowExponent n a) := by
  ext ⟨i,j⟩
  revert j
  refine Fin.cases ?_ ?_ i
  · intro j
    simp [finiteRowExponent,coloredRows,coloredTuple,Fin.sum_univ_succ,
      Finsupp.single_apply, coloredExponent]
  · intro i j
    simp [finiteRowExponent,coloredRows,coloredTuple,Fin.sum_univ_succ,
      Finsupp.single_apply,coloredExponent]

@[simp] theorem colorExponent_row (c : Fin r) (a : FiniteTuple n) :
    colorExponent (finiteRowExponent (coloredRows (r := r) n) (coloredTuple n c a))=
      Finsupp.single (ULift.up c) 1 := by rw [coloredRowExponent,colorExponent_coloredExponent]

@[simp] theorem baseExponent_row (c : Fin r) (a : FiniteTuple n) :
    baseExponent (finiteRowExponent (coloredRows (r := r) n) (coloredTuple n c a))=
      finiteRowExponent n a := by rw [coloredRowExponent,baseExponent_coloredExponent]

theorem coloredLexBefore_iff (c e : Fin r) (a b : FiniteTuple n) :
    finiteLexBefore (coloredRows (r := r) n) (coloredTuple n c a) (coloredTuple n e b) ↔
      c<e ∨ c=e ∧ finiteLexBefore n a b := by
  constructor
  · rintro ⟨i,hi,hprev⟩
    cases i using Fin.cases with
    | zero => exact Or.inl hi
    | succ i =>
      refine Or.inr ⟨hprev 0 (Fin.succ_pos i),i,hi,?_⟩
      intro j hj
      exact hprev j.succ (Fin.succ_lt_succ_iff.mpr hj)
  · rintro (h | ⟨rfl,i,hi,hprev⟩)
    · exact ⟨0,h,by intro j hj; exact (Fin.not_lt_zero j hj).elim⟩
    · refine ⟨i.succ,hi,?_⟩
      intro j hj
      refine Fin.cases ?_ ?_ j hj
      · intro _; rfl
      · intro j hj
        exact hprev j (Fin.succ_lt_succ_iff.mp hj)

/-- Each selected predecessor colon in its own color fiber. -/
def sameColorChainCoefficientFamily (E : Fin r → Finset (FiniteTuple n))
    {m : ℕ} (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) m) :
    Family (FiniteVariable.{u} n) :=
  Finset.univ.biUnion fun s => finitePredecessorFamily n (E ((w.val s).val 0))
    (fun i => (w.val s).val i.succ)

def chainColorCount (E : Fin r → Finset (FiniteTuple n)) {m : ℕ}
    (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) m) :
    ULift.{u} (Fin r) →₀ ℕ :=
  ∑ s, Finsupp.single (ULift.up ((w.val s).val 0)) 1

def chainBaseShift (E : Fin r → Finset (FiniteTuple n)) {m : ℕ}
    (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) m) :
    Exponent (FiniteVariable.{u} n) :=
  ∑ s, finiteRowExponent n (fun i => (w.val s).val i.succ)

@[simp] theorem chainColorCount_degree (E : Fin r → Finset (FiniteTuple n)) {m : ℕ}
    (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) m) :
    (chainColorCount E w).degree=m := by simp [chainColorCount]

lemma coloredChainShift (E : Fin r → Finset (FiniteTuple n)) {m : ℕ}
    (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) m) :
    finiteChainShift (coloredRows (r := r) n) w=
      coloredExponent (chainColorCount E w) (chainBaseShift E w) := by
  ext ⟨i,j⟩
  revert j
  refine Fin.cases ?_ ?_ i
  · intro c
    change (∑ s : Fin m, finiteRowExponent (coloredRows (r := r) n) (w.val s).val) ⟨0,c⟩ =
      (∑ s : Fin m, Finsupp.single (ULift.up ((w.val s).val 0)) 1) c
    simp only [Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro s _
    have he := coloredRowExponent (n := n) (r := r)
      ((w.val s).val 0) (fun i => (w.val s).val i.succ)
    have ha : coloredTuple n ((w.val s).val 0) (fun i => (w.val s).val i.succ)=(w.val s).val :=
      (coloredTupleEquiv n).apply_symm_apply _
    rw [ha] at he
    exact congrArg (fun b => b ⟨0,c⟩) he
  · intro i c
    change (∑ s : Fin m, finiteRowExponent (coloredRows (r := r) n) (w.val s).val) ⟨i.succ,c⟩ =
      (∑ s : Fin m, finiteRowExponent n (fun j => (w.val s).val j.succ)) ⟨i,c⟩
    simp only [Finsupp.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro s _
    have he := coloredRowExponent (n := n) (r := r)
      ((w.val s).val 0) (fun i => (w.val s).val i.succ)
    have ha : coloredTuple n ((w.val s).val 0) (fun i => (w.val s).val i.succ)=(w.val s).val :=
      (coloredTupleEquiv n).apply_symm_apply _
    rw [ha] at he
    exact congrArg (fun b => b ⟨i.succ,c⟩) he

/-- Admissibility on the minimum-color diagonal enforces the exact color
multiplicity, not merely an inequality. -/
theorem coloredChain_admissible_iff (E : Fin r → Finset (FiniteTuple n))
    (m : ULift.{u} (Fin r) →₀ ℕ) (a : Exponent (FiniteVariable.{u} n))
    (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) m.degree) :
    finiteChainShift (coloredRows (r := r) n) w≤coloredExponent m a ↔
      chainColorCount E w=m ∧ chainBaseShift E w≤a := by
  rw [coloredChainShift,coloredExponent_le_iff]
  constructor
  · rintro ⟨hc,ha⟩
    exact ⟨eq_of_le_of_degree_eq hc (chainColorCount_degree E w),ha⟩
  · rintro ⟨hc,ha⟩
    exact ⟨le_of_eq hc,ha⟩

/-- Exact restriction of the chain coefficient family in color degree zero.
This is the key reason no fieldwise Künneth assertion enters Corollary 7.2. -/
theorem coloredChainCoefficient_contains_zero (E : Fin r → Finset (FiniteTuple n))
    {m : ℕ} (w : FiniteMultichain (coloredRows (r := r) n) (coloredFamily n E) m)
    (a : Exponent (FiniteVariable.{u} n)) :
    Contains (finiteChainCoefficientFamily (coloredRows (r := r) n) w)
      (coloredExponent 0 a) ↔ Contains (sameColorChainCoefficientFamily E w) a := by
  constructor
  · rintro ⟨b,hb,hba⟩
    obtain ⟨s,_,hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hv,hlex⟩ := Finset.mem_filter.mp hv
    obtain ⟨⟨c,b⟩,rfl⟩ := (coloredTupleEquiv n).surjective v
    let e : Fin r := (w.val s).val 0
    let z : FiniteTuple n := fun i => (w.val s).val i.succ
    have hw : (w.val s).val=coloredTuple n e z := ((coloredTupleEquiv n).apply_symm_apply _).symm
    rw [hw] at hba hlex
    change finiteLexBefore (coloredRows (r := r) n) (coloredTuple n c b)
      (coloredTuple n e z) at hlex
    change finiteRowExponent (coloredRows (r := r) n) (coloredTuple n c b)-
      finiteRowExponent (coloredRows (r := r) n) (coloredTuple n e z)≤coloredExponent 0 a at hba
    rw [coloredLexBefore_iff] at hlex
    rcases hlex with hce | ⟨hce,hlex⟩
    · have hne : (ULift.up c : ULift.{u} (Fin r))≠ULift.up e := by
        intro he
        exact (ne_of_lt hce) (ULift.up_injective he)
      have h : (1 : ℕ)≤0 := by
        simpa only [coloredRowExponent,coloredExponent_sub,coloredExponent_zero,
          Finsupp.tsub_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne hne,
          tsub_zero,Finsupp.zero_apply] using hba ⟨0,ULift.up c⟩
      exact (Nat.not_succ_le_zero 0 h).elim
    · refine ⟨finiteRowExponent n b-finiteRowExponent n z,?_,?_⟩
      · exact Finset.mem_biUnion.mpr ⟨s,Finset.mem_univ s,
          Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr
            ⟨by
              change b∈E e
              rw [←hce]
              exact (coloredTuple_mem_family n E c b).mp hv,hlex⟩,rfl⟩⟩
      · intro j
        have h := hba ⟨j.1.succ,j.2⟩
        simpa only [coloredRowExponent,coloredExponent_sub,coloredExponent_succ] using h
  · rintro ⟨b,hb,hba⟩
    obtain ⟨s,_,hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hv,hlex⟩ := Finset.mem_filter.mp hv
    let c : Fin r := (w.val s).val 0
    let z : FiniteTuple n := fun i => (w.val s).val i.succ
    have hw : (w.val s).val=coloredTuple n c z := ((coloredTupleEquiv n).apply_symm_apply _).symm
    refine ⟨finiteRowExponent (coloredRows (r := r) n) (coloredTuple n c v)-
      finiteRowExponent (coloredRows (r := r) n) (w.val s).val,?_,?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨s,Finset.mem_univ s,Finset.mem_image.mpr ⟨coloredTuple n c v,?_,rfl⟩⟩
      apply Finset.mem_filter.mpr
      refine ⟨(coloredTuple_mem_family n E c v).mpr hv,?_⟩
      rw [hw,coloredLexBefore_iff]
      exact Or.inr ⟨rfl,hlex⟩
    · rw [hw,coloredRowExponent,coloredRowExponent,coloredExponent_sub,tsub_self,
        coloredExponent_le_iff]
      exact ⟨le_rfl,hba⟩

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.MixedMonomialFamily -/
section

/-! # Monomial generators of literal mixed products

The family is obtained by independently choosing a generator from each
ordinary power and summing their exponents. Its ideal is proved equal to
the actual product of powers over every commutative coefficient ring.
-/
section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid MvPolynomial
open scoped Pointwise
universe u
variable {C V : Type u} [Fintype C] [DecidableEq C] [Fintype V] [DecidableEq V]

def mixedPowerFamily (B : C → Family V) (m : C →₀ ℕ) : Family V :=
  (Fintype.piFinset (fun c => exponentPowerFamily (B c) (m c))).image (fun a => ∑c,a c)

@[simp] theorem mixedPowerFamily_zero (B : C → Family V) : mixedPowerFamily B 0={0} := by
  simp [mixedPowerFamily,exponentPowerFamily,Fintype.piFinset_singleton]

theorem mixedPowerFamily_ideal (k : Type*) [CommRing k]
    (B : C → Family V) (m : C →₀ ℕ) :
    monomialIdeal k (mixedPowerFamily B m)=powerProduct (fun c => monomialIdeal k (B c)) m := by
  unfold powerProduct
  simp_rw [← exponentPowerFamily_ideal]
  unfold monomialIdeal
  rw [Ideal.prod_span]
  apply congrArg Ideal.span
  ext f
  let T : C → Set (MvPolynomial V k) := fun c =>
    (fun a : Exponent V => monomial a (1:k)) ''
      (exponentPowerFamily (B c) (m c) : Set (Exponent V))
  change f∈((fun a : Exponent V => monomial a (1:k)) ''
    (mixedPowerFamily B m : Set (Exponent V))) ↔ f∈∏c,T c
  constructor
  · rintro ⟨a,ha,haf⟩
    obtain ⟨g,hg,hga⟩ := Finset.mem_image.mp ha
    apply (Set.mem_fintype_prod T _).mpr
    refine ⟨fun c => monomial (g c) (1:k),?_,?_⟩
    · intro c
      have hac : g c∈exponentPowerFamily (B c) (m c) := (Fintype.mem_piFinset.mp hg) c
      exact ⟨g c,hac,rfl⟩
    · exact (monomial_sum_one Finset.univ g).symm.trans
        ((congrArg (fun b : Exponent V => monomial b (1:k)) hga).trans haf)
  · intro hf
    obtain ⟨g,hg,hgprod⟩ := (Set.mem_fintype_prod T _).mp hf
    have hf' : ∀ c,∃ a : Exponent V,
        a∈exponentPowerFamily (B c) (m c) ∧ monomial a (1:k)=g c := fun c => hg c
    choose a ha he using hf'
    refine ⟨∑c,a c,Finset.mem_image.mpr ⟨a,Fintype.mem_piFinset.mpr ha,rfl⟩,?_⟩
    change monomial (∑c,a c) (1:k)=f
    rw [monomial_sum_one]
    exact (Finset.prod_congr rfl (fun c _ => he c)).trans hgprod

variable {d r : ℕ} (n : Fin d → ℕ)
  (E : Fin r → Finset (FiniteTuple n))

def mixedRowPowerFamily (m : ULift.{u} (Fin r) →₀ ℕ) : Family (FiniteVariable.{u} n) :=
  mixedPowerFamily (fun c : ULift.{u} (Fin r) => finiteRowFamily n (E c.down)) m

theorem mixedRowPowerFamily_ideal (k : Type u) [CommRing k]
    (m : ULift.{u} (Fin r) →₀ ℕ) :
    monomialIdeal k (mixedRowPowerFamily n E m)=powerProduct (coloredIdeals (k := k) n E) m := by
  rw [mixedRowPowerFamily,mixedPowerFamily_ideal]
  congr 1
  funext c
  exact (finiteSublatticeIdeal_eq_monomialIdeal n (E c.down)).symm

variable {k : Type u} [CommRing k]

lemma coloredPolynomialEquiv_C_monomial (a : Exponent (FiniteVariable.{u} n)) :
    coloredPolynomialEquiv (r := r) (k := k) n (MvPolynomial.C (monomial a 1))=
      monomial (coloredExponent (r := r) 0 a) 1 := by
  have hmap : (coloredPolynomialEquiv (r := r) (k := k) n).toRingHom.comp MvPolynomial.C=
      (rename (fun v : FiniteVariable.{u} n =>
        (⟨v.1.succ,v.2⟩ : FiniteVariable.{u} (coloredRows (r := r) n)))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [coloredPolynomialEquiv]
    · intro v
      change coloredPolynomialEquiv (r := r) (k := k) n (MvPolynomial.C (X v))=
        rename (fun v : FiniteVariable.{u} n =>
          (⟨v.1.succ,v.2⟩ : FiniteVariable.{u} (coloredRows (r := r) n))) (X v)
      rw [rename_X]
      exact coloredPolynomialEquiv_C_X (r := r) (k := k) n v
  have he : a.mapDomain (fun v : FiniteVariable.{u} n =>
      (⟨v.1.succ,v.2⟩ : FiniteVariable.{u} (coloredRows (r := r) n)))=
        coloredExponent (r := r) 0 a := by
    ext ⟨i,j⟩
    revert j
    refine Fin.cases ?_ ?_ i
    · intro c
      exact Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨v,hv⟩; cases hv)
    · intro i c
      have hinj : Function.Injective (fun v : FiniteVariable.{u} n =>
          (⟨v.1.succ,v.2⟩ : FiniteVariable.{u} (coloredRows (r := r) n))) := by
        intro v w h
        exact Sum.inr_injective ((coloredVariableEquiv n).injective h)
      exact Finsupp.mapDomain_apply_of_injective
        hinj a (⟨i,c⟩ : FiniteVariable.{u} n)
  change ((coloredPolynomialEquiv (r := r) (k := k) n).toRingHom.comp MvPolynomial.C) (monomial a 1)=_
  rw [hmap]
  change rename (fun v : FiniteVariable.{u} n =>
    (⟨v.1.succ,v.2⟩ : FiniteVariable.{u} (coloredRows (r := r) n))) (monomial a (1:k))=_
  rw [rename_monomial,he]

/-- Splitting color and original-variable exponents is coefficient-free. -/
lemma coloredExponent_split (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) :
    coloredExponent 0 a+m.sum (fun c j =>
      Finsupp.single (⟨0,c⟩ : FiniteVariable.{u} (coloredRows (r := r) n)) j)=
        coloredExponent m a := by
  apply Finsupp.ext
  intro v
  rcases v with ⟨i,j⟩
  revert j
  refine Fin.cases ?_ ?_ i
  · intro c
    rw [Finsupp.add_apply,coloredExponent_zero,coloredExponent_zero,Finsupp.zero_apply,zero_add,
      Finsupp.sum_apply]
    convert Finsupp.sum_ite_self_eq' m c using 1
    congr 1
    funext e j
    simp only [Finsupp.single_apply,Sigma.mk.inj_iff,heq_eq_eq,true_and]
  · intro i c
    change a ⟨i,c⟩ + (m.sum (fun e j =>
      Finsupp.single (⟨0,e⟩ : FiniteVariable.{u} (coloredRows (r := r) n)) j)) ⟨i.succ,c⟩=a ⟨i,c⟩
    rw [Finsupp.sum_apply]
    suffices m.sum (fun e j =>
        (Finsupp.single (⟨0,e⟩ : FiniteVariable.{u} (coloredRows (r := r) n)) j) ⟨i.succ,c⟩)=0 by
      rw [this,add_zero]
    change (∑ e ∈ m.support,
      (Finsupp.single (⟨0,e⟩ : FiniteVariable.{u} (coloredRows (r := r) n)) (m e)) ⟨i.succ,c⟩)=0
    apply Finset.sum_eq_zero
    intro e he
    exact Finsupp.single_eq_of_ne (by intro h; exact Fin.succ_ne_zero i (congrArg Sigma.fst h))

lemma coloredPolynomialEquiv_monomial (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) :
    coloredPolynomialEquiv (k := k) n (monomial m (monomial a 1))=
      monomial (coloredExponent m a) 1 := by
  rw [monomial_eq,map_mul,coloredPolynomialEquiv_C_monomial,map_finsuppProd]
  simp only [map_pow,coloredPolynomialEquiv_X]
  simp only [X_pow_eq_monomial]
  have hprod : m.prod (fun c j =>
      (monomial (Finsupp.single (⟨0,c⟩ : FiniteVariable.{u} (coloredRows (r := r) n)) j) (1:k)))=
        monomial (m.sum (fun c j => Finsupp.single ⟨0,c⟩ j)) 1 := by
    simpa only [C_1,one_mul] using
      (monomial_finsupp_sum_index m (fun c j =>
        Finsupp.single (⟨0,c⟩ : FiniteVariable.{u} (coloredRows (r := r) n)) j) (1:k)).symm
  rw [hprod,monomial_mul,one_mul]
  apply congrArg (fun b : Exponent (FiniteVariable.{u} (coloredRows (r := r) n)) => monomial b (1:k))
  exact coloredExponent_split n m a

/-- The exact monomial-membership form of the mixed-product diagonal.
Its combinatorial conclusion is coefficient-independent. -/
theorem coloredPower_contains_iff (m : ULift.{u} (Fin r) →₀ ℕ)
    (a : Exponent (FiniteVariable.{u} n)) :
    Contains (exponentPowerFamily (finiteRowFamily (coloredRows (r := r) n)
      (coloredFamily n E)) m.degree) (coloredExponent m a) ↔
      Contains (mixedRowPowerFamily n E m) a := by
  rw [← monomial_mem_iff (k := ULift.{u} ℤ),← monomial_mem_iff (k := ULift.{u} ℤ),
    finitePowerFamily_ideal,mixedRowPowerFamily_ideal]
  rw [← coloredIdeal_map_eq_sublattice (k := ULift.{u} ℤ) n E,← Ideal.map_pow,
    ← coloredPolynomialEquiv_monomial (k := ULift.{u} ℤ) n m a]
  exact (Ideal.apply_mem_of_equiv_iff
    (f := (coloredPolynomialEquiv (k := ULift.{u} ℤ) n).toRingEquiv)
    (I := coloredIdeal (coloredIdeals (k := ULift.{u} ℤ) n E)^m.degree)
    (x := monomial m (monomial a 1))).trans
      (coloredIdeal_power_minimal_monomial_iff (coloredIdeals (k := ULift.{u} ℤ) n E) m (monomial a 1))

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AllRingComplete -/
section
section
set_option Elab.async false


/- SOURCE FourPapers.Sublattice.AllRingTor -/
section ExtensionSource0

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000

/-!
# The all-powers decomposition in actual derived Tor over every coefficient ring

The zero coefficient ring is included. Its modules are proved to be subsingletons;
this is the only case not covered by the regular-sequence resolution API. Fine
components are images of the genuine homogeneous Koszul inclusions in Mathlib's
`Tor`, with the coefficient module in the paper's second tensor slot.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg.Polymatroid CommAlg.Koszul
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Over the zero coefficient ring every module is zero. This categorical
construction keeps the restricted scalar structures explicit. -/
def zeroCoefficientModuleIso [Subsingleton k] (M N : ModuleCat.{u} k) : M≅N where
  hom := 0
  inv := 0
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact @Subsingleton.elim M (Module.subsingleton k M) _ _
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact @Subsingleton.elim N (Module.subsingleton k N) _ _

/-- Extend the checked Koszul computation to the zero ring, whose every module
is zero. No nontriviality assumption is retained in the resulting isomorphism. -/
def allRingCoefficientTorIso (B : Family V) (p : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor p (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))) ≅
      (underlyingComplex (k := k) B).homology p := by
  classical
  by_cases hn : Nontrivial k
  · letI := hn
    exact coefficientTorIso B p
  · have hs : Subsingleton k := by
      rcases subsingleton_or_nontrivial k with hs | ht
      · exact hs
      · exact (hn ht).elim
    letI := hs
    exact zeroCoefficientModuleIso _ _

def allRingQuotientTorIso (B : Family V) (p : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
      (finitePolynomialTor p
        (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B))) ≅
      (quotientUnderlyingComplex (k := k) B).homology p := by
  classical
  by_cases hn : Nontrivial k
  · letI := hn
    exact quotientTorIso B p
  · have hs : Subsingleton k := by
      rcases subsingleton_or_nontrivial k with hs | ht
      · exact hs
      · exact (hn ht).elim
    letI := hs
    exact zeroCoefficientModuleIso _ _

/-- Mathlib's actual derived Tor with the polynomial module first and the
coefficient ring, acting by evaluation at zero, second. -/
def paperTor (M : ModuleCat.{u} (MvPolynomial V k)) (p : ℕ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).obj
    (((Tor (ModuleCat (MvPolynomial V k)) p).obj M).obj
      (residueCoefficientModule (V := V) (k := k)))

def homogeneousToPaperTor (B : Family V) (α : Exponent V) (p : ℕ) :
    (homogeneousComplex (k := k) B α).homology p ⟶
      paperTor (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)) p :=
  HomologicalComplex.homologyMap (homogeneousInclusion (k := k) B α) p ≫
    (allRingCoefficientTorIso B p).inv ≫
    (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).map
      (finitePolynomialTorPaperIso p
        (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B))).hom

lemma homogeneousToPaperTor_injective (B : Family V) (α : Exponent V) (p : ℕ) :
    Function.Injective (homogeneousToPaperTor (k := k) B α p).hom := by
  let e := (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).mapIso
    (finitePolynomialTorPaperIso p
      (ModuleCat.of (MvPolynomial V k) (monomialIdeal k B)))
  change Function.Injective (fun x => e.toLinearEquiv
    ((allRingCoefficientTorIso (k := k) B p).symm.toLinearEquiv
      ((HomologicalComplex.homologyMap (homogeneousInclusion (k := k) B α) p).hom x)))
  exact e.toLinearEquiv.injective.comp
    ((allRingCoefficientTorIso (k := k) B p).symm.toLinearEquiv.injective.comp
      (homogeneousHomology_injective B α p))

def quotientHomogeneousToPaperTor (B : Family V) (α : Exponent V) (p : ℕ) :
    (quotientHomogeneousComplex (k := k) B α).homology p ⟶
      paperTor (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B)) p :=
  HomologicalComplex.homologyMap (quotientHomogeneousInclusion (k := k) B α) p ≫
    (allRingQuotientTorIso B p).inv ≫
    (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).map
      (finitePolynomialTorPaperIso p
        (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B))).hom

lemma quotientHomogeneousToPaperTor_injective (B : Family V) (α : Exponent V) (p : ℕ) :
    Function.Injective (quotientHomogeneousToPaperTor (k := k) B α p).hom := by
  let e := (ModuleCat.restrictScalars (algebraMap k (MvPolynomial V k))).mapIso
    (finitePolynomialTorPaperIso p
      (ModuleCat.of (MvPolynomial V k) (CoefficientQuotient (k := k) B)))
  change Function.Injective (fun x => e.toLinearEquiv
    ((allRingQuotientTorIso (k := k) B p).symm.toLinearEquiv
      ((HomologicalComplex.homologyMap (quotientHomogeneousInclusion (k := k) B α) p).hom x)))
  exact e.toLinearEquiv.injective.comp
    ((allRingQuotientTorIso (k := k) B p).symm.toLinearEquiv.injective.comp
      (quotientHomogeneousHomology_injective B α p))

/-- Genuine fine-degree image submodule of the paper's derived Tor. -/
def paperGradedTor (B : Family V) (α : Exponent V) (p : ℕ) :=
  LinearMap.range (homogeneousToPaperTor (k := k) B α p).hom

def quotientPaperGradedTor (B : Family V) (α : Exponent V) (p : ℕ) :=
  LinearMap.range (quotientHomogeneousToPaperTor (k := k) B α p).hom

def paperGradedTorIso (B : Family V) (α : Exponent V) (p : ℕ) :
    (homogeneousComplex (k := k) B α).homology p ≅
      ModuleCat.of k (paperGradedTor (k := k) B α p) :=
  (LinearEquiv.ofInjective (homogeneousToPaperTor (k := k) B α p).hom
    (homogeneousToPaperTor_injective B α p)).toModuleIso

def quotientPaperGradedTorIso (B : Family V) (α : Exponent V) (p : ℕ) :
    (quotientHomogeneousComplex (k := k) B α).homology p ≅
      ModuleCat.of k (quotientPaperGradedTor (k := k) B α p) :=
  (LinearEquiv.ofInjective (quotientHomogeneousToPaperTor (k := k) B α p).hom
    (quotientHomogeneousToPaperTor_injective B α p)).toModuleIso

variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- Equation (7.2) in natural fine degree, over every commutative coefficient
ring, as an isomorphism of actual derived-Tor submodules. The admissible index
set is precisely the multichains with nonnegative residual fine degree. -/
def allRingPowerTorIso (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0< m) (α : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    ModuleCat.of k (paperGradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) α p) ≅
      ModuleCat.of k (∀w : AdmissibleChain n E m α,
        quotientPaperGradedTor (k := k) (finiteChainCoefficientFamily n w.val)
          (α-finiteChainShift n w.val) p) :=
  (paperGradedTorIso (k := k) (exponentPowerFamily (finiteRowFamily n E) m) α p).symm ≪≫
    allPowerHomogeneousHomologyIso hE m hm α p ≪≫
    (LinearEquiv.piCongrRight (fun w : AdmissibleChain n E m α =>
      (quotientPaperGradedTorIso (k := k) (finiteChainCoefficientFamily n w.val)
        (α-finiteChainShift n w.val) p).toLinearEquiv)).toModuleIso

end FourPapers.Sublattice

end
end ExtensionSource0


/- SOURCE FourPapers.Sublattice.AllRingIntegerTor -/
section ExtensionSource1

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000

noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg.Polymatroid CommAlg.Koszul
universe u

section ZeroExtension
variable {k I : Type*} [CommRing k] {M : I → Type*}
  [∀i, AddCommGroup (M i)] [∀i, Module k (M i)]

/-- Extend a family across omitted zero modules. This is an explicit linear
isomorphism, including both inverse identities. -/
def piZeroExtension (P : I → Prop) (hz : ∀i, ¬P i → Subsingleton (M i)) :
    (∀i : {i // P i}, M i.val) ≃ₗ[k] (∀i, M i) where
  toFun f i := if h : P i then f ⟨i,h⟩ else 0
  invFun f i := f i.val
  left_inv f := by funext i; simp only [dif_pos i.property]
  right_inv f := by
    funext i
    by_cases hi : P i
    · simp only [dif_pos hi]
    · letI := hz i hi
      exact Subsingleton.elim _ _
  map_add' f g := by
    funext i
    by_cases hi : P i <;> simp [hi]
  map_smul' c f := by
    funext i
    by_cases hi : P i <;> simp [hi]
end ZeroExtension

variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def paperIntegerGradedTor (B : Family V) (α : V →₀ ℤ) (p : ℕ) :=
  integerRegrade (fun a => paperGradedTor (k := k) B a p) α

def quotientPaperIntegerGradedTor (B : Family V) (α : V →₀ ℤ) (p : ℕ) :=
  integerRegrade (fun a => quotientPaperGradedTor (k := k) B a p) α

lemma paperIntegerGradedTor_nat (B : Family V) (α : Exponent V) (p : ℕ) :
    paperIntegerGradedTor (k := k) B (integerExponent α) p =
      paperGradedTor (k := k) B α p := integerRegrade_nat _ _

lemma quotientPaperIntegerGradedTor_nat (B : Family V) (α : Exponent V) (p : ℕ) :
    quotientPaperIntegerGradedTor (k := k) B (integerExponent α) p =
      quotientPaperGradedTor (k := k) B α p := integerRegrade_nat _ _

lemma paperIntegerGradedTor_negative (B : Family V) (α : V →₀ ℤ) (p : ℕ)
    {v : V} (hv : α v < 0) : paperIntegerGradedTor (k := k) B α p = ⊥ :=
  integerRegrade_eq_bot_of_negative _ α hv

lemma quotientPaperIntegerGradedTor_negative (B : Family V) (α : V →₀ ℤ) (p : ℕ)
    {v : V} (hv : α v < 0) : quotientPaperIntegerGradedTor (k := k) B α p = ⊥ :=
  integerRegrade_eq_bot_of_negative _ α hv

lemma quotientPaperIntegerGradedTor_shift (B : Family V) (α b : Exponent V)
    (h : b ≤ α) (p : ℕ) :
    quotientPaperIntegerGradedTor (k := k) B (integerExponent α-integerExponent b) p =
      quotientPaperGradedTor (k := k) B (α-b) p := by
  rw [← integerExponent_tsub h,quotientPaperIntegerGradedTor_nat]

lemma quotientPaperIntegerGradedTor_shift_zero (B : Family V) (α b : Exponent V)
    (h : ¬ b ≤ α) (p : ℕ) :
    quotientPaperIntegerGradedTor (k := k) B (integerExponent α-integerExponent b) p = ⊥ := by
  obtain ⟨v,hv⟩ : ∃v, α v < b v := by
    by_contra hn
    push_neg at hn
    exact h hn
  apply quotientPaperIntegerGradedTor_negative B _ p
  change (α v : ℤ)-(b v : ℤ)<0
  exact sub_neg.mpr (Int.ofNat_lt.mpr hv)

variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- Restore every multichain in the natural-degree Tor decomposition. The omitted
negative residual components are proved to be zero submodules of actual Tor. -/
def allRingPowerTorFullIndexIso (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0< m) (α : Exponent (FiniteVariable.{u} n)) (p : ℕ) :
    ModuleCat.of k (paperIntegerGradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) (integerExponent α) p) ≅
      ModuleCat.of k (∀w : FiniteMultichain n E m,
        quotientPaperIntegerGradedTor (k := k) (finiteChainCoefficientFamily n w)
          (integerExponent α-integerExponent (finiteChainShift n w)) p) := by
  let e₁ := LinearEquiv.ofEq _ _
    (paperIntegerGradedTor_nat (k := k) (exponentPowerFamily (finiteRowFamily n E) m) α p)
  let e₂ := LinearEquiv.piCongrRight (fun w : AdmissibleChain n E m α =>
    (LinearEquiv.ofEq _ _ (quotientPaperIntegerGradedTor_shift (k := k)
      (finiteChainCoefficientFamily n w.val) α (finiteChainShift n w.val) w.property p)).symm)
  let e₃ := piZeroExtension (k := k)
    (M := fun w : FiniteMultichain n E m => quotientPaperIntegerGradedTor (k := k)
      (finiteChainCoefficientFamily n w) (integerExponent α-integerExponent (finiteChainShift n w)) p)
    (fun w => finiteChainShift n w ≤ α) (by
      intro w hw
      rw [quotientPaperIntegerGradedTor_shift_zero _ _ _ hw]
      infer_instance)
  exact e₁.toModuleIso ≪≫ allRingPowerTorIso hE m hm α p ≪≫
    e₂.toModuleIso ≪≫ e₃.toModuleIso

/-- Full unrestricted integer fine-degree statement of (7.2), over every
commutative ring. Its target is the literal finite direct sum of actual derived
Tor components, including all integer torsion and every multichain. -/
def allRingIntegerPowerTorIso (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0< m) (α : FiniteVariable.{u} n →₀ ℤ) (p : ℕ) :
    ModuleCat.of k (paperIntegerGradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) α p) ≅
      ModuleCat.of k (Π₀ w : FiniteMultichain n E m,
        quotientPaperIntegerGradedTor (k := k) (finiteChainCoefficientFamily n w)
          (α-integerExponent (finiteChainShift n w)) p) := by
  by_cases hα : ∀v, 0≤α v
  · let hex := (integerExponent_exists_iff α).mpr hα
    let a := Classical.choose hex
    have ha : integerExponent a=α := Classical.choose_spec hex
    rw [←ha]
    exact allRingPowerTorFullIndexIso hE m hm a p ≪≫
      (DFinsupp.linearEquivFunOnFintype (R := k)
        (M := fun w : FiniteMultichain n E m => quotientPaperIntegerGradedTor (k := k)
          (finiteChainCoefficientFamily n w)
          (integerExponent a-integerExponent (finiteChainShift n w)) p)).symm.toModuleIso
  · have hex : ∃v, α v<0 := by simpa only [not_forall,not_le] using hα
    let v := Classical.choose hex
    have hv : α v<0 := Classical.choose_spec hex
    have hleft := paperIntegerGradedTor_negative (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) α p hv
    letI : Subsingleton (paperIntegerGradedTor (k := k)
        (exponentPowerFamily (finiteRowFamily n E) m) α p) := by
      rw [hleft]
      infer_instance
    have hright (w : FiniteMultichain n E m) :
        quotientPaperIntegerGradedTor (k := k) (finiteChainCoefficientFamily n w)
          (α-integerExponent (finiteChainShift n w)) p = ⊥ := by
      apply quotientPaperIntegerGradedTor_negative
      change α v-((finiteChainShift n w) v : ℤ)<0
      exact (sub_le_self _ (Int.ofNat_nonneg _)).trans_lt hv
    letI (w : FiniteMultichain n E m) : Subsingleton
        (quotientPaperIntegerGradedTor (k := k) (finiteChainCoefficientFamily n w)
          (α-integerExponent (finiteChainShift n w)) p) := by
      rw [hright w]
      infer_instance
    exact (LinearEquiv.ofSubsingleton (R := k) _ _).toModuleIso

end FourPapers.Sublattice

end
end ExtensionSource1


end
end

/- BEGIN EXACT BODY: FourPapers.Common.MonomialOrderRestriction -/
section

/-! # Restriction of a monomial order to an actual subset of variables -/
section
set_option autoImplicit false
noncomputable section
namespace FourPapers
open Classical
open scoped MonomialOrder
variable {V W : Type*}

def monomialOrderEmbeddingHom (m : MonomialOrder W) (e : V ↪ W) :
    (V→₀ℕ) →+ m.syn := m.toSyn.toAddMonoidHom.comp (Finsupp.mapDomain.addMonoidHom e)

lemma monomialOrderEmbeddingHom_injective (m : MonomialOrder W) (e : V ↪ W) :
    Function.Injective (monomialOrderEmbeddingHom m e) :=
  m.toSyn.injective.comp (Finsupp.mapDomain_injective e.injective)

/-- The order is literally induced from the larger polynomial ring, using
the image additive submonoid as its ordered synonym. -/
def monomialOrderRestriction (m : MonomialOrder W) (e : V ↪ W) : MonomialOrder V where
  syn := ↥(AddMonoidHom.mrange (monomialOrderEmbeddingHom m e))
  toSyn := AddEquiv.ofLeftInverse' (monomialOrderEmbeddingHom m e)
    (Function.leftInverse_invFun (monomialOrderEmbeddingHom_injective m e))
  toSyn_monotone := by
    intro a b hab
    exact m.toSyn_monotone (Finsupp.mapDomain_mono hab)

@[simp] theorem monomialOrderRestriction_le (m : MonomialOrder W) (e : V ↪ W)
    (a b : V→₀ℕ) :
    a ≼[monomialOrderRestriction m e] b ↔ a.mapDomain e ≼[m] b.mapDomain e := Iff.rfl

end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerPowerBasis -/
section

/-! # Products of a Gröbner basis when initial ideals commute with powers -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
noncomputable section

namespace FourPapers

open Classical MvPolynomial
open scoped Pointwise

variable {R : Type*} [CommSemiring R]

theorem ideal_span_set_power (S : Set R) (s : ℕ) :
    Ideal.span (S ^ s) = (Ideal.span S) ^ s := by
  induction s with
  | zero => simp
  | succ s ih => rw [pow_succ, ← Ideal.span_mul_span, ih, pow_succ]

variable {K V : Type*} [CommRing K] [NoZeroDivisors K]
  (m : MonomialOrder V)

def leadingTermMonoidHom : MvPolynomial V K →* MvPolynomial V K where
  toFun := m.leadingTerm
  map_one' := m.leadingTerm_one
  map_mul' := m.leadingTerm_mul

/-- The products are the literal pointwise set power of the supplied
polynomials. No new generators, field extension, or unproved standard-basis
assertion are hidden in the conclusion. -/
theorem products_isGroebnerBasis_of_initial_power
    (G : Set (MvPolynomial V K)) (J : Ideal (MvPolynomial V K))
    (hG : m.IsGroebnerBasis G J) (s : ℕ)
    (hpower : initialIdeal m (J ^ s) = (initialIdeal m J) ^ s) :
    m.IsGroebnerBasis (G ^ s) (J ^ s) := by
  apply MonomialOrder.IsGroebnerBasis.mk
  · clear hpower
    induction s with
    | zero =>
        intro f _
        simpa only [pow_zero, Ideal.one_eq_top, SetLike.mem_coe] using
          (show f ∈ (⊤ : Ideal (MvPolynomial V K)) from trivial)
    | succ s ih =>
        intro f hf
        rw [pow_succ] at hf ⊢
        obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hf
        exact Ideal.mul_mem_mul (ih ha) (hG.subset hb)
  · change initialIdeal m (J ^ s) = Ideal.span (m.leadingTerm '' (G ^ s))
    rw [hpower, initialIdeal, hG.span_leadingTerm_image, ← ideal_span_set_power]
    apply congrArg Ideal.span
    exact (Set.image_pow (leadingTermMonoidHom m) G s).symm

end FourPapers

end
end
end

/- BEGIN EXACT BODY: FourPapers.Symmetric.Vendor.RingTheory.MvPolynomial.Groebner.Map -/
section
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-!
# Gröbner bases under an injective change of coefficients

Let `m` be a monomial order on `σ →₀ ℕ` and let `φ : R →+* S` be an injective ring homomorphism,
for instance a field extension `k → K`. The coefficient map `MvPolynomial.map φ` does not change
supports, so it preserves leading monomials and commutes with leading coefficients, leading
terms and S-polynomials. It therefore carries remainders to remainders, and, by Buchberger's
criterion, a Gröbner basis `G` of an ideal `I` to a Gröbner basis `map φ '' G` of the extended
ideal `I.map (map φ)`, provided the nonzero members of `G` have unit leading coefficients.

So extending the coefficients changes neither Gröbner bases nor ideals of leading terms: the ideal
of leading terms of the extended ideal is the extension of the ideal of leading terms of `I`, and
the extended ideal contracts back to `I`. Over a field this holds for every ideal, since every
ideal is a Gröbner basis of itself and every nonzero polynomial has a unit leading coefficient.

## Main results

* `MonomialOrder.IsRemainder.map`: if `r` is a remainder of `f` on division by `B`, then
  `map φ r` is a remainder of `map φ f` on division by `map φ '' B`.
* `MonomialOrder.IsGroebnerBasis.map`: the image of a Gröbner basis of `I` whose nonzero members
  have unit leading coefficients is a Gröbner basis of `I.map (map φ)`.
* `MonomialOrder.isGroebnerBasis_map_iff`: conversely, a subset `G ⊆ I` whose nonzero members have
  unit leading coefficients is a Gröbner basis of `I` as soon as its image is a Gröbner basis of
  `I.map (map φ)`.
* `MonomialOrder.IsGroebnerBasis.comap_map_eq`: an ideal with such a Gröbner basis is the
  contraction of its extension.
* `MonomialOrder.IsGroebnerBasis.span_leadingTerm_map` and, over a field,
  `MonomialOrder.span_leadingTerm_map`: the ideal of leading terms of the extension of `I` is the
  extension of the ideal of leading terms of `I`.

## References

* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §6, Theorem 6
  (Buchberger's criterion), which shows that a Gröbner basis computation only involves the field
  of definition of the generators.
-/

section
namespace MonomialOrder

open MvPolynomial

variable {σ R S : Type*} {m : MonomialOrder σ}

section CommSemiring

variable [CommSemiring R] [CommSemiring S] {φ : R →+* S} {f r : MvPolynomial σ R}
  {B : Set (MvPolynomial σ R)}

/-- An injective coefficient map carries a remainder of `f` on division by `B` to a remainder of
the image of `f` on division by the image of `B`. -/
theorem IsRemainder.map (hφ : Function.Injective φ) (h : m.IsRemainder f B r) :
    m.IsRemainder (MvPolynomial.map φ f) (MvPolynomial.map φ '' B) (MvPolynomial.map φ r) := by
  classical
  obtain ⟨g, hfg, hdeg⟩ := h.exists_linearCombination
  -- The quotient attached to `map φ b` is `map φ` of the quotient attached to `b`.
  let e : B → MvPolynomial.map φ '' B := fun b ↦ ⟨_, Set.mem_image_of_mem _ b.2⟩
  have he : Function.Injective e := fun b c hbc ↦
    Subtype.ext (map_injective φ hφ (congrArg Subtype.val hbc))
  let g' : B →₀ MvPolynomial σ S := g.mapRange (MvPolynomial.map φ) (map_zero _)
  refine isRemainder_iff.2 ⟨⟨g'.mapDomain e, ?_, ?_⟩, ?_⟩
  · rw [Finsupp.linearCombination_mapDomain, hfg, map_add, Finsupp.linearCombination_apply,
      Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp), map_finsuppSum]
    simp [e]
  · rintro ⟨_, b, hb, rfl⟩
    have hgb : g'.mapDomain e ⟨_, Set.mem_image_of_mem _ hb⟩ = MvPolynomial.map φ (g ⟨b, hb⟩) :=
      Finsupp.mapDomain_apply_of_injective he g' ⟨b, hb⟩
    simpa only [hgb, m.withBotDegree_map_of_injective hφ] using hdeg ⟨b, hb⟩
  · rintro c hc _ ⟨b, hb, rfl⟩ hb0
    rw [support_map_of_injective _ hφ] at hc
    rw [m.degree_map_of_injective hφ]
    exact h.not_degree_le hc hb fun h ↦ hb0 (by rw [h, map_zero])

end CommSemiring

section CommRing

variable [CommRing R] [CommRing S] {φ : R →+* S} {G : Set (MvPolynomial σ R)}
  {I : Ideal (MvPolynomial σ R)}

/-- **Extension of coefficients.** An injective coefficient map `φ` carries a Gröbner basis of `I`
whose nonzero members have unit leading coefficients to a Gröbner basis of the extended ideal
`I.map (map φ)`. -/
theorem IsGroebnerBasis.map (hφ : Function.Injective φ) (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis (MvPolynomial.map φ '' G) (I.map (MvPolynomial.map φ)) := by
  rw [h.ideal_eq_span, Ideal.map_span]
  refine isGroebnerBasis_span_of_isRemainder_sPolynomial_zero ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩ hg0
    rw [m.leadingCoeff_map_of_injective hφ]
    exact (hG g hg fun h ↦ hg0 (by rw [h, map_zero])).map φ
  rintro _ ⟨g₁, hg₁, rfl⟩ _ ⟨g₂, hg₂, rfl⟩
  have := (h.isRemainder_sPolynomial_zero hg₁ hg₂).map hφ
  rwa [map_zero, ← m.sPolynomial_map_of_injective hφ] at this

/-- Let `φ` be an injective coefficient map and let `G ⊆ I` have nonzero members with unit leading
coefficients. Then `G` is a Gröbner basis of `I` if and only if `map φ '' G` is a Gröbner basis of
the extended ideal `I.map (map φ)`. -/
theorem isGroebnerBasis_map_iff (hφ : Function.Injective φ)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) (hGI : G ⊆ I) :
    m.IsGroebnerBasis (map φ '' G) (I.map (map φ)) ↔ m.IsGroebnerBasis G I := by
  refine ⟨fun h ↦ (isGroebnerBasis_iff_forall_exists_degree_le_degree hG).2
    ⟨hGI, fun p hp hp0 ↦ ?_⟩, fun h ↦ h.map hφ hG⟩
  obtain ⟨_, ⟨g, hg, rfl⟩, hg0, hle⟩ := h.exists_degree_le_degree (Ideal.mem_map_of_mem _ hp)
    ((map_ne_zero_iff _ (map_injective φ hφ)).2 hp0)
  rw [m.degree_map_of_injective hφ, m.degree_map_of_injective hφ] at hle
  exact ⟨g, hg, fun h ↦ hg0 (by rw [h, map_zero]), hle⟩

/-- **Contraction of an extended ideal.** If `I` has a Gröbner basis whose nonzero members have
unit leading coefficients, then the extension of `I` along an injective coefficient map `φ`
contracts back to `I`: a polynomial over `R` lying in the ideal generated by `I` over `S` already
lies in `I`. -/
theorem IsGroebnerBasis.comap_map_eq (hφ : Function.Injective φ) (h : m.IsGroebnerBasis G I)
    (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    (I.map (MvPolynomial.map φ)).comap (MvPolynomial.map φ) = I := by
  refine le_antisymm (fun f hf ↦ ?_) Ideal.le_comap_map
  -- The image of a remainder of `f` is a remainder of `map φ f ∈ I.map (map φ)`, hence zero.
  obtain ⟨r, hr⟩ := exists_isRemainder hG f
  have hr0 := ((h.map hφ hG).remainder_eq_zero_iff_mem (hr.map hφ)).2 hf
  rw [map_eq_zero_iff _ (map_injective φ hφ)] at hr0
  exact (h.remainder_eq_zero_iff_mem hr).1 hr0

/-- **Leading terms of an extended ideal.** If `I` has a Gröbner basis whose nonzero members have
unit leading coefficients, then the ideal of leading terms of the extension of `I` along an
injective coefficient map `φ` is the extension of the ideal of leading terms of `I`. -/
theorem IsGroebnerBasis.span_leadingTerm_map (hφ : Function.Injective φ)
    (h : m.IsGroebnerBasis G I) (hG : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    Ideal.span (m.leadingTerm '' (I.map (MvPolynomial.map φ) : Set (MvPolynomial σ S))) =
      (Ideal.span (m.leadingTerm '' I)).map (MvPolynomial.map φ) := by
  rw [(h.map hφ hG).span_leadingTerm_image, h.span_leadingTerm_image, Ideal.map_span,
    Set.image_image, Set.image_image]
  simp_rw [m.leadingTerm_map_of_injective hφ]

/-- **Leading terms under extension of a field of coefficients.** For a field `k` and a ring
homomorphism `φ : k →+* S` to a nontrivial ring, for instance a field extension, the ideal of
leading terms of the extension of an ideal `I` of `k[σ]` is the extension of the ideal of leading
terms of `I`. -/
theorem span_leadingTerm_map {k : Type*} [Field k] [Nontrivial S] (φ : k →+* S)
    (I : Ideal (MvPolynomial σ k)) :
    Ideal.span (m.leadingTerm '' (I.map (map φ) : Set (MvPolynomial σ S))) =
      (Ideal.span (m.leadingTerm '' I)).map (map φ) :=
  (isGroebnerBasis_self I).span_leadingTerm_map φ.injective fun _ _ ↦ m.isUnit_leadingCoeff.2

end CommRing

end MonomialOrder

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegralComplex -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-!
# Integral Koszul decomposition

The complexes below are the actual homogeneous strands of the polynomial
Koszul complex, and their direct sum is the categorical finite direct sum.
The comparison is a chain isomorphism, hence in particular a chain homotopy
equivalence.  Its construction works over every commutative coefficient ring.

`integralPowerTorIso` states equation (7.2) in unrestricted integer fine degree
using actual derived Tor, with every multichain present.  The negative residual
components are zero by the checked grading construction in `AllRingComplete`.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul CommAlg.Polymatroid
open scoped ZeroObject
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

/-- Equation (7.1), as an actual chain isomorphism over any commutative ring.
The admissible chains omit precisely the zero negative-degree complexes. -/
def integralPowerKoszulIso (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (α : Exponent (FiniteVariable.{u} n)) :
    homogeneousComplex (k := k) (exponentPowerFamily (finiteRowFamily n E) m) α ≅
      ⨁ (fun w : AdmissibleChain n E m α =>
        quotientHomogeneousComplex (k := k) (finiteChainCoefficientFamily n w.val)
          (α - finiteChainShift n w.val)) :=
  (idealTotalKoszulIso (k := k)
    (exponentPowerFamily (finiteRowFamily n E) m) α).symm ≪≫
  (allPowerFaceComparisonIso (k := k) hE m hm α).symm ≪≫
  FourPapers.dfinsuppComplexIso
    (fun w : AdmissibleChain n E m α => quotientTotalData (k := k)
      (finiteChainCoefficientFamily n w.val) (α - finiteChainShift n w.val)) ≪≫
  FourPapers.finiteDirectSumBiproductIso
    (fun w : AdmissibleChain n E m α => (quotientTotalData (k := k)
      (finiteChainCoefficientFamily n w.val) (α - finiteChainShift n w.val)).complex) ≪≫
  biproduct.mapIso (fun w : AdmissibleChain n E m α =>
    quotientTotalKoszulIso (k := k) (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val))

/-- The homotopy equivalence explicitly requested in Theorem 7.1.  Both
homotopies follow from the proved inverse identities of the chain isomorphism. -/
def integralPowerKoszulHomotopyEquiv (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (α : Exponent (FiniteVariable.{u} n)) :
    HomotopyEquiv
      (homogeneousComplex (k := k) (exponentPowerFamily (finiteRowFamily n E) m) α)
      (⨁ (fun w : AdmissibleChain n E m α =>
        quotientHomogeneousComplex (k := k) (finiteChainCoefficientFamily n w.val)
          (α - finiteChainShift n w.val))) :=
  HomotopyEquiv.ofIso (integralPowerKoszulIso hE m hm α)

/-- Equation (7.2) with all integer degrees and all multichains, over every
commutative coefficient ring, including the zero ring. -/
def integralPowerTorIso (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (α : FiniteVariable.{u} n →₀ ℤ) (p : ℕ) :
    ModuleCat.of k (paperIntegerGradedTor (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) α p) ≅
      ModuleCat.of k (Π₀ w : FiniteMultichain n E m,
        quotientPaperIntegerGradedTor (k := k) (finiteChainCoefficientFamily n w)
          (α - integerExponent (finiteChainShift n w)) p) :=
  allRingIntegerPowerTorIso hE m hm α p

section IntegerComplexes
variable {V : Type u} [Fintype V] [LinearOrder V]

/-- Extension of a naturally fine-graded polynomial complex to integer fine
degree. Polynomial and exterior monomials have nonnegative exponents, so all
components outside the nonnegative orthant are the zero complex. -/
def integerComplexExtension
    (C : Exponent V → ChainComplex (ModuleCat.{u} k) ℕ) (α : V →₀ ℤ) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  if h : ∃ a, integerExponent a = α then C (Classical.choose h) else 0

lemma integerComplexExtension_nat
    (C : Exponent V → ChainComplex (ModuleCat.{u} k) ℕ) (a : Exponent V) :
    integerComplexExtension C (integerExponent a) = C a := by
  have h : ∃ b, integerExponent b = integerExponent a := ⟨a, rfl⟩
  rw [integerComplexExtension, dif_pos h]
  congr 1
  exact integerExponent_injective (Classical.choose_spec h)

lemma integerComplexExtension_negative
    (C : Exponent V → ChainComplex (ModuleCat.{u} k) ℕ) (α : V →₀ ℤ)
    {v : V} (hv : α v < 0) : integerComplexExtension C α = 0 := by
  apply dif_neg
  rintro ⟨a, ha⟩
  exact (not_lt_of_ge (integerExponent_nonneg a v)) (ha.symm ▸ hv)

/-- The actual polynomial Koszul strand in unrestricted integer fine degree. -/
def integerHomogeneousComplex (B : Family V) (α : V →₀ ℤ) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  integerComplexExtension (homogeneousComplex (k := k) B) α

/-- The actual quotient Koszul strand in unrestricted integer fine degree. -/
def quotientIntegerHomogeneousComplex (B : Family V) (α : V →₀ ℤ) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  integerComplexExtension (quotientHomogeneousComplex (k := k) B) α

lemma quotientIntegerHomogeneousComplex_shift (B : Family V) (α b : Exponent V)
    (h : b ≤ α) :
    quotientIntegerHomogeneousComplex (k := k) B
      (integerExponent α - integerExponent b) =
      quotientHomogeneousComplex (k := k) B (α - b) := by
  rw [← integerExponent_tsub h]
  exact integerComplexExtension_nat _ _

lemma quotientIntegerHomogeneousComplex_shift_zero (B : Family V) (α b : Exponent V)
    (h : ¬ b ≤ α) :
    quotientIntegerHomogeneousComplex (k := k) B
      (integerExponent α - integerExponent b) = 0 := by
  obtain ⟨v, hv⟩ : ∃ v, α v < b v := by
    by_contra hn
    push_neg at hn
    exact h hn
  apply integerComplexExtension_negative
  change (α v : ℤ) - (b v : ℤ) < 0
  exact sub_neg.mpr (Int.ofNat_lt.mpr hv)

end IntegerComplexes

section ZeroSummands
universe v
variable {C : Type*} [Category C] [HasZeroMorphisms C]
  {I : Type v} (F : I → C) (P : I → Prop)
  [HasBiproduct F] [HasBiproduct (Subtype.restrict P F)]

/-- Removing only proved zero summands preserves the categorical direct sum. -/
def biproductZeroExtensionIso (hz : ∀ i, ¬ P i → IsZero (F i)) :
    (⨁ Subtype.restrict P F) ≅ ⨁ F where
  hom := biproduct.fromSubtype F P
  inv := biproduct.toSubtype F P
  hom_inv_id := biproduct.fromSubtype_toSubtype F P
  inv_hom_id := by
    rw [biproduct.toSubtype_fromSubtype]
    have he : (fun i => if P i then 𝟙 (F i) else 0) = fun i => 𝟙 (F i) := by
      funext i
      by_cases hi : P i
      · rw [if_pos hi]
      · rw [if_neg hi]
        exact (hz i hi).eq_of_src _ _
    rw [he]
    apply biproduct.hom_ext
    intro i
    simp

end ZeroSummands

/-- Equation (7.1) with every multichain explicitly present and unrestricted
integer fine degree. Zero strands are justified by the nonnegative polynomial
and exterior grading; there is no restriction on the chosen fine degree. -/
def integralIntegerPowerKoszulIso (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (α : FiniteVariable.{u} n →₀ ℤ) :
    integerHomogeneousComplex (k := k)
      (exponentPowerFamily (finiteRowFamily n E) m) α ≅
      ⨁ (fun w : FiniteMultichain n E m =>
        quotientIntegerHomogeneousComplex (k := k) (finiteChainCoefficientFamily n w)
          (α - integerExponent (finiteChainShift n w))) := by
  by_cases hα : ∀ v, 0 ≤ α v
  · let hex := (integerExponent_exists_iff α).mpr hα
    let a := Classical.choose hex
    have ha : integerExponent a = α := Classical.choose_spec hex
    rw [← ha]
    let F := fun w : FiniteMultichain n E m =>
      quotientIntegerHomogeneousComplex (k := k) (finiteChainCoefficientFamily n w)
        (integerExponent a - integerExponent (finiteChainShift n w))
    let e := biproductZeroExtensionIso F (fun w => finiteChainShift n w ≤ a) (by
      intro w hw
      dsimp [F]
      rw [quotientIntegerHomogeneousComplex_shift_zero _ _ _ hw]
      exact isZero_zero _)
    exact eqToIso (integerComplexExtension_nat _ _) ≪≫
      integralPowerKoszulIso hE m hm a ≪≫
      biproduct.mapIso (fun w : AdmissibleChain n E m a =>
        eqToIso (quotientIntegerHomogeneousComplex_shift
          (finiteChainCoefficientFamily n w.val) a
          (finiteChainShift n w.val) w.property).symm) ≪≫ e
  · have hex : ∃ v, α v < 0 := by simpa only [not_forall, not_le] using hα
    let v := Classical.choose hex
    have hv : α v < 0 := Classical.choose_spec hex
    have hleft : IsZero (integerHomogeneousComplex (k := k)
        (exponentPowerFamily (finiteRowFamily n E) m) α) := by
      dsimp [integerHomogeneousComplex]
      rw [integerComplexExtension_negative _ α hv]
      exact isZero_zero _
    have hright (w : FiniteMultichain n E m) :
        IsZero (quotientIntegerHomogeneousComplex (k := k)
          (finiteChainCoefficientFamily n w)
          (α - integerExponent (finiteChainShift n w))) := by
      dsimp [quotientIntegerHomogeneousComplex]
      rw [integerComplexExtension_negative _ _ (v := v) (by
        change α v - ((finiteChainShift n w) v : ℤ) < 0
        exact (sub_le_self _ (Int.ofNat_nonneg _)).trans_lt hv)]
      exact isZero_zero _
    apply hleft.iso
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro w
    exact (hright w).eq_of_tgt _ _

/-- Theorem 7.1 in its stated homotopy-equivalence form, with unrestricted
integer fine degree and the full direct sum over multichains. -/
def integralIntegerPowerKoszulHomotopyEquiv (hE : finiteLatticeClosed n E)
    (m : ℕ) (hm : 0 < m) (α : FiniteVariable.{u} n →₀ ℤ) :
    HomotopyEquiv
      (integerHomogeneousComplex (k := k)
        (exponentPowerFamily (finiteRowFamily n E) m) α)
      (⨁ (fun w : FiniteMultichain n E m =>
        quotientIntegerHomogeneousComplex (k := k) (finiteChainCoefficientFamily n w)
          (α - integerExponent (finiteChainShift n w)))) :=
  HomotopyEquiv.ofIso (integralIntegerPowerKoszulIso hE m hm α)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.integralPowerKoszulIso
#print axioms FourPapers.Sublattice.integralPowerKoszulHomotopyEquiv
#print axioms FourPapers.Sublattice.integralPowerTorIso
#print axioms FourPapers.Sublattice.integralIntegerPowerKoszulIso
#print axioms FourPapers.Sublattice.integralIntegerPowerKoszulHomotopyEquiv

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegralIntegerKoszulStrands -/
section

/-!
# Integer Koszul components are literal basis-degree subcomplexes

This identifies the natural-grading extension with the subcomplex cut
out by the integer degrees of the actual coefficient–exterior basis.
The negative-degree assertion is a theorem about those submodules.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice.IntegerStrandComparison
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Polymatroid
universe u
variable {R V : Type u} [CommRing R]
  {I M : ℕ → Type u} [∀ p,AddCommGroup (M p)] [∀ p,Module R (M p)]
  (b : ∀ p,Module.Basis (I p) R (M p)) (degree : ∀ p,I p→V→₀ℕ)
  (D : ∀ p,M (p+1)→ₗ[R] M p)
  (hsq : ∀ p,(D p).comp (D (p+1))=0)
  (hhom : ∀ p a z,z∈Grading.Piece (b (p+1)) (degree (p+1)) a →
    D p z∈Grading.Piece (b p) (degree p) a)

def piece (α : V→₀ℤ) (p : ℕ) : Submodule R (M p) :=
  Grading.Piece (b p) (integerExponent ∘ degree p) α

theorem piece_nat (a : V→₀ℕ) (p : ℕ) :
    piece b degree (integerExponent a) p=Grading.Piece (b p) (degree p) a := by
  rw [piece,←integerRegrade_basisPiece,integerRegrade_nat]

theorem piece_not_image (α : V→₀ℤ) (hα : ¬∃ a,integerExponent a=α) (p : ℕ) :
    piece b degree α p=⊥ := by
  rw [piece,←integerRegrade_basisPiece]
  exact integerRegrade_eq_bot_of_not_image _ _ hα

include hhom in
theorem differential_mem (α : V→₀ℤ) (p : ℕ) (z : M (p+1))
    (hz : z∈piece b degree α (p+1)) : D p z∈piece b degree α p := by
  by_cases hα : ∃ a,integerExponent a=α
  · obtain ⟨a,rfl⟩ := hα
    rw [piece_nat] at hz ⊢
    exact hhom p a z hz
  · rw [piece_not_image b degree α hα] at hz
    rw [show z=0 from hz,map_zero]
    exact Submodule.zero_mem _

def differential (α : V→₀ℤ) (p : ℕ) :
    piece b degree α (p+1)→ₗ[R] piece b degree α p :=
  ((D p).domRestrict (piece b degree α (p+1))).codRestrict _
    (fun z => differential_mem b degree D hhom α p z.val z.property)

include hsq in
theorem differential_square (α : V→₀ℤ) (p : ℕ) :
    (differential b degree D hhom α p).comp
      (differential b degree D hhom α (p+1))=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun (hsq p) z.val

def complex (α : V→₀ℤ) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun p => ModuleCat.of R (piece b degree α p))
    (fun p => ModuleCat.ofHom (differential b degree D hhom α p))
    (fun p => ModuleCat.hom_ext (differential_square b degree D hsq hhom α p))

@[simp] theorem complex_d (α : V→₀ℤ) (p : ℕ) :
    (complex b degree D hsq hhom α).d (p+1) p=
      ModuleCat.ofHom (differential b degree D hhom α p) := by simp [complex]

def naturalDifferential (a : V→₀ℕ) (p : ℕ) :
    Grading.Piece (b (p+1)) (degree (p+1)) a →ₗ[R] Grading.Piece (b p) (degree p) a :=
  ((D p).domRestrict _).codRestrict _ (fun z => hhom p a z.val z.property)

include hsq in
theorem naturalDifferential_square (a : V→₀ℕ) (p : ℕ) :
    (naturalDifferential b degree D hhom a p).comp
      (naturalDifferential b degree D hhom a (p+1))=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun (hsq p) z.val

def naturalComplex (a : V→₀ℕ) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun p => ModuleCat.of R (Grading.Piece (b p) (degree p) a))
    (fun p => ModuleCat.ofHom (naturalDifferential b degree D hhom a p))
    (fun p => ModuleCat.hom_ext (naturalDifferential_square b degree D hsq hhom a p))

@[simp] theorem naturalComplex_d (a : V→₀ℕ) (p : ℕ) :
    (naturalComplex b degree D hsq hhom a).d (p+1) p=
      ModuleCat.ofHom (naturalDifferential b degree D hhom a p) := by simp [naturalComplex]

def naturalIso (a : V→₀ℕ) :
    naturalComplex b degree D hsq hhom a ≅ complex b degree D hsq hhom (integerExponent a) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => (LinearEquiv.ofEq _ _ (piece_nat b degree a p).symm).toModuleIso) (by
      intro i j hij
      obtain rfl : i=j+1 := hij.symm
      rw [naturalComplex_d,complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      rfl)

theorem complex_isZero (α : V→₀ℤ) (hα : ¬∃ a,integerExponent a=α) :
    IsZero (complex b degree D hsq hhom α) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hz : z.val=0 := by
    have hz' : z.val ∈ (⊥ : Submodule R (M p)) := by
      simpa only [piece_not_image b degree α hα] using z.property
    exact hz'
  exact Subtype.ext hz

def extensionIso (α : V→₀ℤ) :
    integerComplexExtension (naturalComplex b degree D hsq hhom) α ≅
      complex b degree D hsq hhom α := by
  unfold integerComplexExtension
  split_ifs with hα
  · exact naturalIso b degree D hsq hhom (Classical.choose hα) ≪≫
      eqToIso (congrArg (complex b degree D hsq hhom) (Classical.choose_spec hα))
  · exact (isZero_zero _).iso (complex_isZero b degree D hsq hhom α hα)

end FourPapers.Sublattice.IntegerStrandComparison

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def actualIntegerHomogeneousComplex (B : Family V) (α : V→₀ℤ) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  IntegerStrandComparison.complex (R := k) (V := V)
    (I := fun p => MonomialIndex B p)
    (M := fun p => Set.powersetCard V p →₀ monomialIdeal k B)
    (monomialCoefficientBasis (k:=k) B)
    (fun p => monomialDegree (B := B) (i := p))
    (monomialDifferential (k := k) B) (monomialDifferential_comp (k := k) B)
    (fun p a z hz => by
      change z ∈ homogeneousPiece (k := k) B a (p + 1) at hz
      change monomialDifferential (k := k) B p z ∈ homogeneousPiece (k := k) B a p
      exact monomialDifferential_homogeneous (k := k) B a p hz) α

def integerHomogeneousActualIso (B : Family V) (α : V→₀ℤ) :
    integerHomogeneousComplex (k:=k) B α ≅ actualIntegerHomogeneousComplex B α := by
  let e := IntegerStrandComparison.extensionIso (R := k) (V := V)
      (I := fun p => MonomialIndex B p)
      (M := fun p => Set.powersetCard V p →₀ monomialIdeal k B)
      (monomialCoefficientBasis (k:=k) B)
      (fun p => monomialDegree (B := B) (i := p))
      (monomialDifferential (k := k) B) (monomialDifferential_comp (k := k) B)
      (fun p a z hz => by
        change z ∈ homogeneousPiece (k := k) B a (p + 1) at hz
        change monomialDifferential (k := k) B p z ∈ homogeneousPiece (k := k) B a p
        exact monomialDifferential_homogeneous (k := k) B a p hz) α
  refine ?_ ≪≫ e
  change integerComplexExtension (homogeneousComplex (k := k) B) α ≅
    integerComplexExtension _ α
  unfold integerComplexExtension
  split_ifs with hα
  · refine HomologicalComplex.Hom.isoOfComponents (fun p => Iso.refl _) ?_
    intro i j hij
    obtain rfl : i = j + 1 := hij.symm
    rw [homogeneousComplex_d, IntegerStrandComparison.naturalComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  · exact Iso.refl _

def actualQuotientIntegerHomogeneousComplex (B : Family V) (α : V→₀ℤ) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  IntegerStrandComparison.complex (R := k) (V := V)
    (I := fun p => QuotientIndex B p)
    (M := fun p => Set.powersetCard V p →₀ CoefficientQuotient (k := k) B)
    (quotientCoefficientBasis (k:=k) B)
    (fun p => quotientDegree (B := B) (i := p))
    (quotientDifferential (k := k) B) (quotientDifferential_comp (k := k) B)
    (fun p a z hz => by
      change z ∈ quotientPiece (k := k) B a (p + 1) at hz
      change quotientDifferential (k := k) B p z ∈ quotientPiece (k := k) B a p
      exact quotientDifferential_homogeneous (k := k) B a p hz) α

def quotientIntegerHomogeneousActualIso (B : Family V) (α : V→₀ℤ) :
    quotientIntegerHomogeneousComplex (k:=k) B α ≅ actualQuotientIntegerHomogeneousComplex B α := by
  let e := IntegerStrandComparison.extensionIso (R := k) (V := V)
      (I := fun p => QuotientIndex B p)
      (M := fun p => Set.powersetCard V p →₀ CoefficientQuotient (k := k) B)
      (quotientCoefficientBasis (k:=k) B)
      (fun p => quotientDegree (B := B) (i := p))
      (quotientDifferential (k := k) B) (quotientDifferential_comp (k := k) B)
      (fun p a z hz => by
        change z ∈ quotientPiece (k := k) B a (p + 1) at hz
        change quotientDifferential (k := k) B p z ∈ quotientPiece (k := k) B a p
        exact quotientDifferential_homogeneous (k := k) B a p hz) α
  refine ?_ ≪≫ e
  change integerComplexExtension (quotientHomogeneousComplex (k := k) B) α ≅
    integerComplexExtension _ α
  unfold integerComplexExtension
  split_ifs with hα
  · refine HomologicalComplex.Hom.isoOfComponents (fun p => Iso.refl _) ?_
    intro i j hij
    obtain rfl : i = j + 1 := hij.symm
    rw [quotientHomogeneousComplex_d, IntegerStrandComparison.naturalComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  · exact Iso.refl _

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.InitialColumnPrefixes -/
section

/-! # Initial-column prefixes and their unchanged predecessor colons

A prefix retains precisely the facets whose last column is below the
chosen column count. The families are nested colored sublattices. Their
actual predecessor colon ideals agree with the original ones: the
coordinatewise predecessor generators are unchanged, even though the
redundant lexicographic generating families need not be identical.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Polymatroid
universe u
variable {d N r : ℕ}
variable (E : Finset (FiniteTuple (UnitIntervalRows d N)))
local notation "n" => UnitIntervalRows d N

def initialColumnPrefix (c : ℕ) : Finset (FiniteTuple n) :=
  E.filter (fun a => (a (Fin.last d)).val<c)

@[simp] theorem mem_initialColumnPrefix (c : ℕ) (a : FiniteTuple n) :
    a∈initialColumnPrefix E c ↔ a∈E ∧ (a (Fin.last d)).val<c := by
  simp only [initialColumnPrefix,Finset.mem_filter]

theorem initialColumnPrefix_mono : Monotone (initialColumnPrefix E) := by
  intro c e h a ha
  exact (mem_initialColumnPrefix E e a).mpr
    ⟨((mem_initialColumnPrefix E c a).mp ha).1,
      ((mem_initialColumnPrefix E c a).mp ha).2.trans_le h⟩

variable {E}

theorem UnitIntervalFacetFamily.initialColumnPrefix
    (hE : UnitIntervalFacetFamily E) (c : ℕ) :
    UnitIntervalFacetFamily (initialColumnPrefix E c) := by
  constructor
  · intro a ha
    exact hE.increasing a ((mem_initialColumnPrefix E c a).mp ha).1
  · intro a ha b hmono hab hba
    obtain ⟨haE,hac⟩ := (mem_initialColumnPrefix E c a).mp ha
    exact (mem_initialColumnPrefix E c b).mpr
      ⟨hE.interval a haE b hmono hab hba,lt_of_le_of_lt hba hac⟩

variable (E)

def initialColumnPrefixes (c : Fin r → ℕ) : Fin r → Finset (FiniteTuple n) :=
  fun i => initialColumnPrefix E (c i)

variable {E}

include E in
theorem initialColumnPrefixes_colored (hE : UnitIntervalFacetFamily E)
    (c : Fin r → ℕ) (hc : Monotone c) :
    ColoredLatticeClosed n (initialColumnPrefixes E c) := by
  constructor
  · intro i a ha j b hb
    obtain ⟨haE,hac⟩ := (mem_initialColumnPrefix E (c i) a).mp ha
    obtain ⟨hbE,hbc⟩ := (mem_initialColumnPrefix E (c j) b).mp hb
    apply (mem_initialColumnPrefix E (c (i⊓j)) (a⊓b)).mpr
    refine ⟨hE.latticeClosed.1 a haE b hbE,?_⟩
    by_cases hij : i≤j
    · rw [inf_eq_left.mpr hij]
      exact lt_of_le_of_lt (min_le_left _ _) hac
    · rw [inf_eq_right.mpr (le_of_not_ge hij)]
      exact lt_of_le_of_lt (min_le_right _ _) hbc
  · intro i a ha j b hb
    obtain ⟨haE,hac⟩ := (mem_initialColumnPrefix E (c i) a).mp ha
    obtain ⟨hbE,hbc⟩ := (mem_initialColumnPrefix E (c j) b).mp hb
    apply (mem_initialColumnPrefix E (c (i⊔j)) (a⊔b)).mpr
    refine ⟨hE.latticeClosed.2 a haE b hbE,?_⟩
    exact max_lt (hac.trans_le (hc le_sup_left)) (hbc.trans_le (hc le_sup_right))

theorem initialColumnPrefix_coordinatePredecessors (c : ℕ) (a : FiniteTuple n)
    (ha : a∈initialColumnPrefix E c) :
    finiteCoordinatePredecessorFamily (initialColumnPrefix E c) a=
      finiteCoordinatePredecessorFamily E a := by
  unfold finiteCoordinatePredecessorFamily
  congr 1
  ext b
  simp only [Finset.mem_filter,mem_initialColumnPrefix]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · rintro ⟨hb,hba,hne⟩
    exact ⟨⟨hb,lt_of_le_of_lt (hba (Fin.last d))
      ((mem_initialColumnPrefix E c a).mp ha).2⟩,hba,hne⟩

theorem initialColumnPrefix_predecessor_contains (hE : UnitIntervalFacetFamily E)
    (c : ℕ) (a : FiniteTuple n) (ha : a∈initialColumnPrefix E c)
    (α : Exponent (FiniteVariable.{u} n)) :
    Contains (finitePredecessorFamily n (initialColumnPrefix E c) a) α ↔
      Contains (finitePredecessorFamily n E a) α := by
  rw [← finiteCoordinatePredecessor_contains_iff (hE.initialColumnPrefix c).latticeClosed ha,
    initialColumnPrefix_coordinatePredecessors c a ha,
    finiteCoordinatePredecessor_contains_iff hE.latticeClosed
      ((mem_initialColumnPrefix E c a).mp ha).1]

/-- The exact colon identity used in Section 6.3, over every coefficient ring. -/
theorem initialColumnPrefix_predecessorColon {k : Type*} [CommSemiring k]
    (hE : UnitIntervalFacetFamily E) (c : ℕ) (a : FiniteTuple n)
    (ha : a∈initialColumnPrefix E c) :
    finitePredecessorColon n (k := k) (initialColumnPrefix E c) a=
      finitePredecessorColon n (k := k) E a := by
  rw [← finiteCoordinatePredecessor_ideal (hE.initialColumnPrefix c).latticeClosed ha,
    initialColumnPrefix_coordinatePredecessors c a ha,
    finiteCoordinatePredecessor_ideal hE.latticeClosed
      ((mem_initialColumnPrefix E c a).mp ha).1]

theorem initialColumnPrefix_chain_member
    {d N r m : ℕ} {E : Finset (FiniteTuple (UnitIntervalRows d N))}
    (c : Fin r → ℕ)
    (w : FiniteMultichain (coloredRows (r := r) (UnitIntervalRows d N))
      (coloredFamily (UnitIntervalRows d N) (initialColumnPrefixes E c)) m)
    (s : Fin m) :
    (fun i : Fin (d+1) => (w.val s).val i.succ)∈
      initialColumnPrefix E (c ((w.val s).val 0)) := by
  apply (coloredTuple_mem_family (UnitIntervalRows d N) (initialColumnPrefixes E c) _ _).mp
  change (coloredTupleEquiv (UnitIntervalRows d N))
    ((coloredTupleEquiv (UnitIntervalRows d N)).symm (w.val s).val)∈_
  rw [Equiv.apply_symm_apply]
  exact (w.val s).property

def initialColumnPrefix_baseChain
    {d N r m : ℕ} {E : Finset (FiniteTuple (UnitIntervalRows d N))}
    (c : Fin r → ℕ)
    (w : FiniteMultichain (coloredRows (r := r) (UnitIntervalRows d N))
      (coloredFamily (UnitIntervalRows d N) (initialColumnPrefixes E c)) m) :
    FiniteMultichain (UnitIntervalRows d N) E m :=
  ⟨fun s => ⟨fun i : Fin (d+1) => (w.val s).val i.succ,
      ((mem_initialColumnPrefix E _ _).mp (initialColumnPrefix_chain_member c w s)).1⟩,
    by intro s t hst i; exact w.property hst i.succ⟩

/-- The actual mixed coefficient ideal has precisely the same membership
predicate as the coefficient ideal of the underlying uncolored chain. -/
theorem initialColumnPrefix_chain_contains
    {d N r m : ℕ} {E : Finset (FiniteTuple (UnitIntervalRows d N))}
    (c : Fin r → ℕ)
    (w : FiniteMultichain (coloredRows (r := r) (UnitIntervalRows d N))
      (coloredFamily (UnitIntervalRows d N) (initialColumnPrefixes E c)) m)
    (hE : UnitIntervalFacetFamily E)
    (α : Exponent (FiniteVariable.{u} (UnitIntervalRows d N))) :
    Contains (sameColorChainCoefficientFamily (initialColumnPrefixes E c) w) α ↔
      Contains (finiteChainCoefficientFamily (UnitIntervalRows d N)
        (initialColumnPrefix_baseChain c w)) α := by
  constructor
  · rintro ⟨b,hb,hba⟩
    obtain ⟨s,hs,hb⟩ := Finset.mem_biUnion.mp hb
    have h := (initialColumnPrefix_predecessor_contains hE _ _
      (initialColumnPrefix_chain_member c w s) α).mp ⟨b,hb,hba⟩
    obtain ⟨a,ha,haα⟩ := h
    exact ⟨a,Finset.mem_biUnion.mpr ⟨s,Finset.mem_univ _,ha⟩,haα⟩
  · rintro ⟨b,hb,hba⟩
    obtain ⟨s,hs,hb⟩ := Finset.mem_biUnion.mp hb
    have h := (initialColumnPrefix_predecessor_contains hE _ _
      (initialColumnPrefix_chain_member c w s) α).mpr ⟨b,hb,hba⟩
    obtain ⟨a,ha,haα⟩ := h
    exact ⟨a,Finset.mem_biUnion.mpr ⟨s,Finset.mem_univ _,ha⟩,haα⟩

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphGroebnerOrder -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical MvPolynomial
universe u
variable {N : ℕ} {k : Type u} [CommRing k] [IsDomain k]

def graphOrderedVariableEquiv :
    FiniteVariable.{u} (GraphRows N) ≃ Lex (Fin 2 × ULift.{u} (Fin N)) where
  toFun v := toLex (v.1,v.2)
  invFun v := ⟨(ofLex v).1,(ofLex v).2⟩
  left_inv v := by cases v; rfl
  right_inv v := by cases v; rfl

/-- The actual lexicographic monomial order with all first-row variables
before all second-row variables and increasing vertex labels within each row.
The exterior-basis order used elsewhere is left independent of this choice. -/
def graphLexOrder : MonomialOrder (FiniteVariable.{u} (GraphRows N)) := by
  letI : WellFoundedGT (Lex (Fin 2 × ULift.{u} (Fin N))) := Finite.to_wellFoundedGT
  let m : MonomialOrder (Lex (Fin 2 × ULift.{u} (Fin N))) := MonomialOrder.lex
  have hd : Monotone (Finsupp.domCongr graphOrderedVariableEquiv :
      (FiniteVariable.{u} (GraphRows N) →₀ ℕ) → (Lex (Fin 2 × ULift.{u} (Fin N)) →₀ ℕ)) := by
    intro a b hab v
    simpa only [Finsupp.domCongr_apply,Finsupp.equivMapDomain_apply] using
      hab (graphOrderedVariableEquiv.symm v)
  exact {
    syn := m.syn
    addCommMonoidSyn := m.addCommMonoidSyn
    linearOrderSyn := m.linearOrderSyn
    isOrderedAddMonoid_syn := m.isOrderedAddMonoid_syn
    wellFoundedLT_syn := m.wellFoundedLT_syn
    toSyn := (Finsupp.domCongr graphOrderedVariableEquiv).trans m.toSyn
    toSyn_monotone := m.toSyn_monotone.comp hd
  }

def graphPairExponent (i j : Fin N) : FiniteVariable.{u} (GraphRows N) →₀ ℕ :=
  Finsupp.single ⟨0,ULift.up i⟩ 1+Finsupp.single ⟨1,ULift.up j⟩ 1

lemma graphPairExponent_eq_row (i j : Fin N) :
    graphPairExponent.{u} i j=finiteRowExponent (GraphRows N) (graphTuple i j) := by
  ext v
  rcases v with ⟨r,⟨h⟩⟩
  fin_cases r <;> simp [graphPairExponent,finiteRowExponent_apply,Finsupp.single_apply]

lemma graphPairExponent_order {i j : Fin N} (hij : i< j) :
    graphLexOrder.toSyn (graphPairExponent.{u} j i)<
      graphLexOrder.toSyn (graphPairExponent.{u} i j) := by
  change toLex (Finsupp.domCongr graphOrderedVariableEquiv (graphPairExponent j i))<
    toLex (Finsupp.domCongr graphOrderedVariableEquiv (graphPairExponent i j))
  simp only [graphPairExponent,map_add,Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_single,graphOrderedVariableEquiv]
  change toLex (Finsupp.single (toLex (0,ULift.up j)) 1 + Finsupp.single (toLex (1,ULift.up i)) 1) <
    toLex (Finsupp.single (toLex (0,ULift.up i)) 1 + Finsupp.single (toLex (1,ULift.up j)) 1)
  rw [Finsupp.Lex.lt_iff]
  refine ⟨toLex (0,ULift.up i),?_,?_⟩
  · intro v hv
    obtain ⟨⟨r,⟨h⟩⟩,rfl⟩ := toLex.surjective v
    change toLex (r,ULift.up h)< toLex (0,ULift.up i) at hv
    have hh : h< i := by
      rcases Prod.Lex.toLex_lt_toLex.mp hv with hr | ⟨hr,hh⟩
      · exact (not_lt_of_ge (Fin.zero_le r) hr).elim
      · exact hh
    have hhi : h≠i := hh.ne
    have hhj : h≠j := (hh.trans hij).ne
    simp [Finsupp.add_apply,Finsupp.single_apply,hhi,Ne.symm hhi,hhj,Ne.symm hhj]
  · simp [Finsupp.add_apply,Finsupp.single_apply,hij.ne,Ne.symm hij.ne]

/-- The actual quadratic binomial edge generator in the paper's two rows. -/
def graphBinomial (i j : Fin N) : MvPolynomial (FiniteVariable.{u} (GraphRows N)) k :=
  monomial (graphPairExponent i j) 1-monomial (graphPairExponent j i) 1

lemma graphBinomial_variables (i j : Fin N) :
    graphBinomial (k:=k) i j=
      X ⟨0,ULift.up i⟩*X ⟨1,ULift.up j⟩-
        X ⟨0,ULift.up j⟩*X ⟨1,ULift.up i⟩ := by
  simp [graphBinomial,graphPairExponent,X,monomial_mul_monomial]

lemma graphBinomial_swap (i j : Fin N) :
    graphBinomial (k:=k) j i= -graphBinomial (k:=k) i j := by
  simp only [graphBinomial,neg_sub]

lemma graphBinomial_degree {i j : Fin N} (hij : i< j) :
    graphLexOrder.degree (graphBinomial (k:=k) i j)=graphPairExponent i j :=
  MonicBinomialBuchberger.binomial_degree graphLexOrder (graphPairExponent_order hij)

lemma graphBinomial_leadingCoeff {i j : Fin N} (hij : i< j) :
    graphLexOrder.leadingCoeff (graphBinomial (k:=k) i j)=1 :=
  MonicBinomialBuchberger.binomial_leadingCoeff graphLexOrder (graphPairExponent_order hij)

lemma graphBinomial_ne_zero {i j : Fin N} (hij : i< j) :
    graphBinomial (k:=k) i j≠0 :=
  MonicBinomialBuchberger.binomial_ne_zero graphLexOrder (graphPairExponent_order hij)

def graphBinomialGenerators (G : SimpleGraph (Fin N)) :
    Set (MvPolynomial (FiniteVariable.{u} (GraphRows N)) k) :=
  {f | ∃i j, i< j ∧ G.Adj i j ∧ f=graphBinomial i j}

def graphBinomialIdeal (G : SimpleGraph (Fin N)) :
    Ideal (MvPolynomial (FiniteVariable.{u} (GraphRows N)) k) :=
  Ideal.span (graphBinomialGenerators G)

lemma graphBinomial_mem {G : SimpleGraph (Fin N)} {i j : Fin N}
    (hij : i< j) (hG : G.Adj i j) :
    graphBinomial (k:=k) i j∈graphBinomialGenerators G := ⟨i,j,hij,hG,rfl⟩

end FourPapers.Sublattice


end
end
end


end
