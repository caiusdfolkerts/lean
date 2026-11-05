module

public import Continuation.Geometry.OriginalGraphicAlgebra
public import Recovery.Unimodular.GraphicSectionRing.PolytopeKoszul

/-!
# Proposition 6.10 on the original abstract integral lattice

The input is a bounded actual real set and its literal difference-inequality
presentation after an integral coordinate isomorphism. The conclusion retains
the original point variables, toric ideal, geometric Ehrhart exponent monoid,
degree-zero augmentation, all positive integer decompositions, and ordinary
derived Tor. The existing graphic balancing and bar-boundary theorems supply
the proof; no normality, generation, or Koszul property is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open TauCeti.Toric
open scoped BigOperators Pointwise MonomialOrder

universe u v w

namespace Unimodular.GraphicSectionRing.OriginalLattice

variable {N : Type u} [AddCommGroup N]
    {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} {ι : N →+ V} (hi : IsIntegralLattice ι)
    (e : N ≃ₗ[ℤ] Lattice d) (C : Set (Constraint d)) (P : Set V)
    (hP : P = coordinateBody hi e C)

include hP in
/-- A genuine monomial order on the unchanged original point variables.
The relation ideal is the kernel in k[ℕ × N], identified with the coordinate
kernel by the proved injective monomial-algebra map. -/
theorem squarefree_quadratic_initial_ideal (hbounded : Bornology.IsBounded P)
    (K : Type w) [CommRing K] [Nontrivial K] :
    ∃ m : MonomialOrder.{u,u} (LatticePoint ι P),
      initialIdeal m (toricIdeal (Subtype.val : LatticePoint ι P → N) K) =
        quadraticMonomialIdeal (e ∘ (Subtype.val : LatticePoint ι P → N)) K ∧
      ∀ z ∈ forbiddenExponents (e ∘ (Subtype.val : LatticePoint ι P → N)),
        z.degree = 2 ∧ ∀ x, z x ≤ 1 := by
  classical
  letI : Finite (LatticePoint ι P) := lattice_points_finite e C hi P hP hbounded
  letI : Fintype (LatticePoint ι P) := Fintype.ofFinite _
  let p : LatticePoint ι P → Lattice d := e ∘ Subtype.val
  have hp : Function.Injective p := e.injective.comp Subtype.val_injective
  have hb : BalancedClosed p := by
    intro x y
    have hx := (lattice_mem_coordinateBody hi e C x.val).mp (by
      simpa only [hP] using x.property)
    have hy := (lattice_mem_coordinateBody hi e C y.val).mp (by
      simpa only [hP] using y.property)
    let l : LatticePoint ι P := ⟨e.symm (lower (e x.val) (e y.val)), by
      apply (show ι _ ∈ P ↔ ι _ ∈ _ from Set.ext_iff.mp hP _).mpr
      apply (lattice_mem_coordinateBody hi e C _).mpr
      simpa only [e.apply_symm_apply] using lower_satisfies hx hy⟩
    let r : LatticePoint ι P := ⟨e.symm (upper (e x.val) (e y.val)), by
      apply (show ι _ ∈ P ↔ ι _ ∈ _ from Set.ext_iff.mp hP _).mpr
      apply (lattice_mem_coordinateBody hi e C _).mpr
      simpa only [e.apply_symm_apply] using upper_satisfies hx hy⟩
    exact ⟨l, r, e.apply_symm_apply _, e.apply_symm_apply _⟩
  let ord : LinearOrder (LatticePoint ι P) :=
    LinearOrder.lift' (Fintype.equivFin (LatticePoint ι P))
      (Fintype.equivFin (LatticePoint ι P)).injective
  have wf : @WellFoundedGT (LatticePoint ι P) ord.toLT :=
    InvImage.wf (Fintype.equivFin (LatticePoint ι P))
      (inferInstance : WellFoundedGT (Fin (Fintype.card (LatticePoint ι P))))
  let base : MonomialOrder.{u,u} (LatticePoint ι P) :=
    @MonomialOrder.lex (LatticePoint ι P) ord wf
  refine ⟨WeightedOrder.refine (monomialWeight p) base, ?_, ?_⟩
  · rw [← toricIdeal_coordinates (Subtype.val : LatticePoint ι P → N)
      e.toAddMonoidHom e.injective K]
    exact balancedClosed_initialIdeal p hp hb K base
  · exact fun z hz => forbiddenExponents_squarefree_quadratic p hz

section Field

/-
The coefficient field and the original exponent lattice are placed in one
universe, as in the ordinary ModuleCat-based Tor API. The geometric flag
basis is lifted to that same universe; its original internal degree is kept.
-/
variable (K : Type u) [Field K]

def ehrhartBasis :
    Module.Basis (Option (FlagKoszul.Positive (FlagModel.Relation C))) K
      (EhrhartAlgebra hi e C P hP K) :=
  FlagKoszul.AlgebraTransport.basis (sectionEhrhartEquiv hi e C P hP K) (FlagModel.basis C K)

@[simp] theorem ehrhartBasis_none : ehrhartBasis hi e C P hP K none = 1 :=
  FlagKoszul.AlgebraTransport.unit_transport (sectionEhrhartEquiv hi e C P hP K)
    (FlagModel.basis C K) (FlagModel.basis_none C K)

@[simp] theorem ehrhartBasis_some (z : FlagKoszul.Positive (FlagModel.Relation C)) :
    ehrhartBasis hi e C P hP K (some z) =
      AddMonoidAlgebra.single (sectionEhrhartIndex hi e C P hP (sectionDegree C z.val)) 1 := by
  change sectionEhrhartEquiv hi e C P hP K (FlagModel.basis C K (some z)) = _
  rw [FlagModel.basis_some, sectionEhrhartEquiv_single]

/-- The degree attached to a transported basis element is its actual
original Ehrhart exponent's degree, not the auxiliary triangulation height. -/
theorem ehrhartBasis_degree (z : FlagKoszul.Positive (FlagModel.Relation C)) :
    ehrhartInternalDegree hi e C P hP (sectionEhrhartIndex hi e C P hP (sectionDegree C z.val)) =
      FlagKoszul.positiveDegree (FlagModel.Relation C) z := by
  rw [ehrhartInternalDegree_transport]
  exact internalDegree_sectionDegree C z.val

/-- The ordinary degree-zero augmentation on the original algebra.
Its geometric meaning is proved for every original monomial below. -/
def ehrhartAugmentation : EhrhartAlgebra hi e C P hP K →ₐ[K] K :=
  FlagKoszul.AlgebraTransport.augmentation (sectionEhrhartEquiv hi e C P hP K)
    (sectionAugmentation C K)

@[simp] theorem ehrhartAugmentation_single (z : ehrhartSemigroup hi e C P hP) (a : K) :
    ehrhartAugmentation hi e C P hP K (AddMonoidAlgebra.single z a) =
      if z.val.1 = 0 then a else 0 := by
  change sectionAugmentation C K
    ((sectionEhrhartEquiv hi e C P hP K).symm (AddMonoidAlgebra.single z a)) = _
  rw [sectionEhrhartEquiv, AddMonoidAlgebra.domCongr_symm,
    AddMonoidAlgebra.domCongr_single, sectionAugmentation_single]
  rfl

@[simp] theorem ehrhartAugmentation_basis (z : FlagKoszul.Positive (FlagModel.Relation C)) :
    ehrhartAugmentation hi e C P hP K (ehrhartBasis hi e C P hP K (some z)) = 0 :=
  FlagKoszul.AlgebraTransport.augmentation_transport (sectionEhrhartEquiv hi e C P hP K)
    (sectionAugmentation C K) (FlagModel.basis C K) (FlagModel.augmentation_basis C K) z

theorem ehrhart_product_degree :
    ∀ x y z, PaperVerification.AugmentedAlgebraBasis.productCoefficients
      (ehrhartBasis hi e C P hP K) x y z ≠ 0 →
      FlagKoszul.positiveDegree (FlagModel.Relation C) z =
        FlagKoszul.positiveDegree (FlagModel.Relation C) x +
          FlagKoszul.positiveDegree (FlagModel.Relation C) y :=
  FlagKoszul.AlgebraTransport.productDegree_transport (sectionEhrhartEquiv hi e C P hP K)
    (FlagModel.basis C K) (FlagKoszul.positiveDegree (FlagModel.Relation C))
    (FlagModel.product_degree C K)

/-- Genuine ordinary derived augmentation Tor, with the literal original
Ehrhart degree. The only index change is the universe lift of the proved
homogeneous monomial basis. -/
abbrev EhrhartIsKoszul : Prop :=
  PaperVerification.WeightedBar.HasDiagonalTor (ehrhartAugmentation hi e C P hP K)
    (FlagKoszul.BarReindex.basis
      (Equiv.ulift.symm : FlagKoszul.Positive (FlagModel.Relation C) ≃
        ULift.{u} (FlagKoszul.Positive (FlagModel.Relation C))) (ehrhartBasis hi e C P hP K))
    (FlagKoszul.BarReindex.unit_transport Equiv.ulift.symm (ehrhartBasis hi e C P hP K)
      (ehrhartBasis_none hi e C P hP K))
    (FlagKoszul.BarReindex.augmentation_transport Equiv.ulift.symm
      (ehrhartAugmentation hi e C P hP K) (ehrhartBasis hi e C P hP K)
      (ehrhartAugmentation_basis hi e C P hP K))
    (FlagKoszul.positiveDegree (FlagModel.Relation C) ∘ Equiv.ulift)
    (FlagKoszul.BarReindex.productDegree_transport Equiv.ulift.symm
      (ehrhartBasis hi e C P hP K) (FlagKoszul.positiveDegree (FlagModel.Relation C))
      (ehrhart_product_degree hi e C P hP K))

/-- Existing homogeneous bar boundaries are transported along the proved
algebra equivalence. No acyclicity or Tor concentration is supplied as input. -/
theorem ehrhartAlgebra_hasDiagonalTor (hbounded : Bornology.IsBounded P) :
    EhrhartIsKoszul hi e C P hP K := by
  letI : Finite (GraphicSectionRing.Point C) := coordinate_points_finite e C hi P hP hbounded
  letI : Fintype (GraphicSectionRing.Point C) := Fintype.ofFinite _
  exact FlagKoszul.AlgebraTransport.hasDiagonalTor_ulift
    (sectionEhrhartEquiv hi e C P hP K) (sectionAugmentation C K)
    (FlagModel.basis C K) (FlagModel.basis_none C K) (FlagModel.augmentation_basis C K)
    (FlagKoszul.positiveDegree (FlagModel.Relation C)) (FlagModel.product_degree C K)
    (FlagKoszul.positiveDegree_pos (FlagModel.Relation C))
    (Koszul.section_reduced_cycle_is_boundary C)

/-- Proposition 6.10 on the actual original integral lattice and real set.
The only presentation hypothesis is the paper's integral coordinate change
to difference inequalities. All original variables, exponents, and positive
dilation degrees are retained, in arbitrary rank, including rank zero. -/
theorem theorem_6_10_arbitrary_lattice (hbounded : Bornology.IsBounded P) :
    (∃ m : MonomialOrder.{u,u} (LatticePoint ι P),
      initialIdeal m (toricIdeal (Subtype.val : LatticePoint ι P → N) K) =
        quadraticMonomialIdeal (e ∘ (Subtype.val : LatticePoint ι P → N)) K ∧
      ∀ z ∈ forbiddenExponents (e ∘ (Subtype.val : LatticePoint ι P → N)),
        z.degree = 2 ∧ ∀ x, z x ≤ 1) ∧
    (∀ k : ℕ, 0 < k → ∀ x : N, ι x ∈ (k : ℝ) • P →
      ∃ z : Fin k → N, (∀ i, ι (z i) ∈ P) ∧ ∑ i, z i = x) ∧
    Function.Surjective (ehrhartPolynomialMap hi e C P hP K) ∧
    RingHom.ker (ehrhartPolynomialMap hi e C P hP K).toRingHom =
      toricIdeal (Subtype.val : LatticePoint ι P → N) K ∧
    EhrhartIsKoszul hi e C P hP K := by
  refine ⟨squarefree_quadratic_initial_ideal hi e C P hP hbounded K, ?_,
    ehrhartPolynomialMap_surjective hi e C P hP K,
    ehrhartPolynomialMap_ker hi e C P hP K,
    ehrhartAlgebra_hasDiagonalTor hi e C P hP K hbounded⟩
  intro k hk x hx
  exact integer_decomposition hi e C P hP hk x hx

end Field

#print axioms squarefree_quadratic_initial_ideal
#print axioms ehrhartBasis_degree
#print axioms ehrhartAugmentation_single
#print axioms ehrhartAlgebra_hasDiagonalTor
#print axioms theorem_6_10_arbitrary_lattice

end Unimodular.GraphicSectionRing.OriginalLattice
