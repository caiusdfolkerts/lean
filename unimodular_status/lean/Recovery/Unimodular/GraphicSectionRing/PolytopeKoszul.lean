module

public import Recovery.Unimodular.GraphicSectionRing.EhrhartAlgebra
public import Recovery.Unimodular.GraphicSectionRing.Koszul

/-!
# Proposition 6.10 for the original real polytope and its actual Ehrhart algebra

The statement retains the original lattice points and original toric ideal.
All integral dilations, normal generation, the squarefree quadratic initial
ideal, and diagonal ordinary derived Tor are proved, over every field and
without an interior-point or full-dimensionality hypothesis.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Pointwise BigOperators MonomialOrder

namespace Unimodular.GraphicSectionRing

universe u
variable {n d : ℕ} (P : Set (RealLattice n)) (e : Lattice n ≃ₗ[ℤ] Lattice d)
  (C : Set (Constraint d)) (hP : P = RealCoordinates.coordinateBody e C)
  (K : Type u) [Field K]

/-- A genuine basis of the actual original-polytope Ehrhart algebra. -/
def ehrhartBasis :
    Module.Basis (Option (FlagKoszul.Positive (FlagModel.Relation C))) K (EhrhartAlgebra P e C hP K) :=
  FlagKoszul.AlgebraTransport.basis (sectionEhrhartEquiv P e C hP K) (FlagModel.basis C K)

@[simp] theorem ehrhartBasis_none : ehrhartBasis P e C hP K none = 1 :=
  FlagKoszul.AlgebraTransport.unit_transport (sectionEhrhartEquiv P e C hP K)
    (FlagModel.basis C K) (FlagModel.basis_none C K)

@[simp] theorem ehrhartBasis_some (v : FlagKoszul.Positive (FlagModel.Relation C)) :
    ehrhartBasis P e C hP K (some v) =
      AddMonoidAlgebra.single (sectionEhrhartIndex P e C hP (sectionDegree C v.val)) 1 := by
  change sectionEhrhartEquiv P e C hP K (FlagModel.basis C K (some v)) = _
  rw [FlagModel.basis_some, sectionEhrhartEquiv_single]

/-- The basis degree is proved equal to the literal first coordinate of its
original-lattice exponent; it is not replaced by the auxiliary height. -/
theorem ehrhartBasis_degree (v : FlagKoszul.Positive (FlagModel.Relation C)) :
    ehrhartInternalDegree P e C hP (sectionEhrhartIndex P e C hP (sectionDegree C v.val)) =
      FlagKoszul.positiveDegree (FlagModel.Relation C) v :=
  internalDegree_sectionDegree C v.val

@[simp] theorem ehrhartAugmentation_basis (v : FlagKoszul.Positive (FlagModel.Relation C)) :
    ehrhartAugmentation P e C hP K (ehrhartBasis P e C hP K (some v)) = 0 :=
  FlagKoszul.AlgebraTransport.augmentation_transport (sectionEhrhartEquiv P e C hP K)
    (sectionAugmentation C K) (FlagModel.basis C K) (FlagModel.augmentation_basis C K) v

theorem ehrhart_product_degree :
    ∀ a b c, PaperVerification.AugmentedAlgebraBasis.productCoefficients
      (ehrhartBasis P e C hP K) a b c ≠ 0 →
      FlagKoszul.positiveDegree (FlagModel.Relation C) c =
        FlagKoszul.positiveDegree (FlagModel.Relation C) a +
          FlagKoszul.positiveDegree (FlagModel.Relation C) b :=
  FlagKoszul.AlgebraTransport.productDegree_transport (sectionEhrhartEquiv P e C hP K)
    (FlagModel.basis C K) (FlagKoszul.positiveDegree (FlagModel.Relation C))
    (FlagModel.product_degree C K)

/-- Genuine homogeneous reduced-bar boundaries for the original real P. -/
theorem ehrhart_reduced_cycle_is_boundary (hbounded : Bornology.IsBounded P)
    (r N : ℕ) (hrN : r < N)
    (z : List (FlagKoszul.Positive (FlagModel.Relation C)) →₀ K)
    (hz : z ∈ FlagKoszul.BarReindex.homogeneousPiece
      (FlagKoszul.positiveDegree (FlagModel.Relation C)) r N)
    (hdz : PaperVerification.ReducedBarBasis.differential (ehrhartBasis P e C hP K) z = 0) :
    ∃ y ∈ FlagKoszul.BarReindex.homogeneousPiece
      (FlagKoszul.positiveDegree (FlagModel.Relation C)) (r + 1) N,
      -PaperVerification.ReducedBarBasis.differential (ehrhartBasis P e C hP K) y = z := by
  letI : Finite (Point C) := coordinate_points_finite e C (by simpa only [hP] using hbounded)
  letI : Fintype (Point C) := Fintype.ofFinite (Point C)
  exact FlagKoszul.AlgebraTransport.boundaries_transport (sectionEhrhartEquiv P e C hP K)
    (FlagModel.basis C K) (FlagKoszul.positiveDegree (FlagModel.Relation C))
    (Koszul.section_reduced_cycle_is_boundary C) r N hrN z hz hdz

/-- This abbreviation is exactly diagonal vanishing in ordinary derived Tor,
with the actual degree-zero augmentation and literal homogeneous degree. The
universe lift renames only the basis index. -/
abbrev EhrhartIsKoszul : Prop :=
  PaperVerification.WeightedBar.HasDiagonalTor (ehrhartAugmentation P e C hP K)
    (FlagKoszul.BarReindex.basis
      (Equiv.ulift.symm : FlagKoszul.Positive (FlagModel.Relation C) ≃
        ULift.{u} (FlagKoszul.Positive (FlagModel.Relation C))) (ehrhartBasis P e C hP K))
    (FlagKoszul.BarReindex.unit_transport Equiv.ulift.symm (ehrhartBasis P e C hP K)
      (ehrhartBasis_none P e C hP K))
    (FlagKoszul.BarReindex.augmentation_transport Equiv.ulift.symm
      (ehrhartAugmentation P e C hP K) (ehrhartBasis P e C hP K)
      (ehrhartAugmentation_basis P e C hP K))
    (FlagKoszul.positiveDegree (FlagModel.Relation C) ∘ Equiv.ulift)
    (FlagKoszul.BarReindex.productDegree_transport Equiv.ulift.symm (ehrhartBasis P e C hP K)
      (FlagKoszul.positiveDegree (FlagModel.Relation C)) (ehrhart_product_degree P e C hP K))

/-- Koszulness of the actual Ehrhart algebra of P over every field. -/
theorem ehrhartAlgebra_hasDiagonalTor (hbounded : Bornology.IsBounded P) :
    EhrhartIsKoszul P e C hP K :=
  FlagKoszul.BarReindex.hasDiagonalTor_ulift
    (ehrhartAugmentation P e C hP K) (ehrhartBasis P e C hP K)
    (ehrhartBasis_none P e C hP K) (ehrhartAugmentation_basis P e C hP K)
    (FlagKoszul.positiveDegree (FlagModel.Relation C)) (ehrhart_product_degree P e C hP K)
    (FlagKoszul.positiveDegree_pos (FlagModel.Relation C))
    (ehrhart_reduced_cycle_is_boundary P e C hP K hbounded)

/-- Full polytope clause of Proposition 6.10, on the original lattice and
actual real P. Finiteness is derived from boundedness and every positive
dilation degree is retained. The original-variable polynomial kernel is exact. -/
theorem theorem_6_10_polytope (hbounded : Bornology.IsBounded P) :
    (∃ m : MonomialOrder.{0,0} (LatticePoint P),
      initialIdeal m (toricIdeal (Subtype.val : LatticePoint P → Lattice n) K) =
        quadraticMonomialIdeal (e ∘ (Subtype.val : LatticePoint P → Lattice n)) K ∧
      ∀ v ∈ forbiddenExponents (e ∘ (Subtype.val : LatticePoint P → Lattice n)),
        v.degree = 2 ∧ ∀ i, v i ≤ 1) ∧
    (∀ k : ℕ, 0 < k → ∀ x : Lattice n, latticeCast x ∈ (k : ℝ) • P →
      ∃ v : Fin k → Lattice n, (∀ i, latticeCast (v i) ∈ P) ∧ ∑ i, v i = x) ∧
    Function.Surjective (ehrhartPolynomialMap P e C hP K) ∧
    RingHom.ker (ehrhartPolynomialMap P e C hP K).toRingHom =
      toricIdeal (Subtype.val : LatticePoint P → Lattice n) K ∧
    EhrhartIsKoszul P e C hP K := by
  refine ⟨?_, ?_, ehrhartPolynomialMap_surjective P e C hP K,
    ehrhartPolynomialMap_ker P e C hP K, ehrhartAlgebra_hasDiagonalTor P e C hP K hbounded⟩
  · apply bounded_graphic_lattice_point_initial_ideal P hbounded e C ?_ K
    intro x
    rw [hP, RealCoordinates.cast_mem_coordinateBody]
  · intro k hk x hx
    subst P
    exact coordinate_integer_decomposition e C hk x hx

#print axioms ehrhartBasis_degree
#print axioms ehrhart_reduced_cycle_is_boundary
#print axioms ehrhartAlgebra_hasDiagonalTor
#print axioms theorem_6_10_polytope

end Unimodular.GraphicSectionRing

#check Unimodular.GraphicSectionRing.theorem_6_10_polytope
