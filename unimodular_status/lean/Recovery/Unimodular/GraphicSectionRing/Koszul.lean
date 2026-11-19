module

public import Recovery.Unimodular.GraphicSectionRing.FlagModel
public import Recovery.Unimodular.GraphicSectionRing.FilteredBoundaries
public import Recovery.Unimodular.FlagKoszul.FlagTor
public import Recovery.Unimodular.FlagKoszul.IndependentTor

/-!
# Koszulness of the actual graphic section semigroup algebra

The monomial flag algebra's constructed bar boundaries are transferred by
finite descent in the independently constructed height. The ordinary internal
degree and homological degree are retained, so the endpoint concerns actual
ordinary derived augmentation Tor, not a surrogate vanishing predicate.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.GraphicSectionRing.Koszul

open PaperVerification.Fermion.BasisFiltered
open PaperVerification.ReducedBarBasis
open PaperVerification.WeightedBar

variable {K I : Type*} [Field K]

abbrev piece (δ : I → ℕ) (r N : ℕ) : Submodule K (List I →₀ K) :=
  FlagKoszul.BarReindex.homogeneousPiece δ r N

/-- The elementary degree-preservation statement has independent universes;
no category of modules is needed to prove it. -/
theorem differential_mem_piece {A : Type*} [Ring A] [Algebra K A]
    (B : Module.Basis (Option I) K A) (δ : I → ℕ)
    (hδ : ∀ a b c, PaperVerification.AugmentedAlgebraBasis.productCoefficients B a b c ≠ 0 →
      δ c = δ a + δ b) {r N : ℕ} (z : List I →₀ K)
    (hz : z ∈ piece δ (r + 1) N) : differential B z ∈ piece δ r N := by
  have hl : z ∈ PaperVerification.NoncommutativeBar.lengthPiece I K (r + 1) :=
    fun L hL => (hz hL).1
  have hd : z ∈ degreePiece δ N := fun L hL => (hz hL).2
  have hdl : differential B z ∈ PaperVerification.NoncommutativeBar.lengthPiece I K r := by
    clear hz hd
    rw [PaperVerification.NoncommutativeBar.lengthPiece_eq_span] at hl
    induction hl using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨L, hL, rfl⟩ := hz
      change L.length = r + 1 at hL
      rw [differential_single, one_smul]
      simpa only [hL, Nat.add_sub_cancel] using
        PaperVerification.NoncommutativeBar.reducedDifferentialBasis_mem_lengthPiece B L
    | zero => simpa only [map_zero] using
        (PaperVerification.NoncommutativeBar.lengthPiece I K r).zero_mem
    | add z w hz hw ihz ihw => simpa only [map_add] using
        (PaperVerification.NoncommutativeBar.lengthPiece I K r).add_mem ihz ihw
    | smul a z hz ih => simpa only [map_smul] using
        (PaperVerification.NoncommutativeBar.lengthPiece I K r).smul_mem a ih
  have hdd := differential_mem_degreePiece B δ hδ z hd
  exact fun L hL => ⟨hdl hL, hdd hL⟩

/-- Taking an auxiliary-height component preserves both actual bar degrees. -/
theorem component_mem_piece (δ w : I → ℕ) (r N m : ℕ) (z : List I →₀ K)
    (hz : z ∈ piece δ r N) :
    component (BarComparison.wordBasis (K := K)) (BarComparison.wordWeight w) m z ∈
      piece δ r N := by
  intro L hL
  apply hz
  apply Finsupp.mem_support_iff.mpr
  intro hzL
  have he := repr_component (BarComparison.wordBasis (K := K))
    (BarComparison.wordWeight w) m z L
  have he' : (component (BarComparison.wordBasis (K := K))
      (BarComparison.wordWeight w) m z) L =
      if BarComparison.wordWeight w L = m then z L else 0 := he
  have hn := Finsupp.mem_support_iff.mp hL
  rw [he', hzL] at hn
  simp at hn

variable {n : ℕ} (C : Set (Constraint n)) [Fintype (Point C)]

/-- Constructed homogeneous boundaries for the genuine reduced bar complex
of the actual lattice section algebra, in every degree above the diagonal. -/
theorem section_reduced_cycle_is_boundary (r N : ℕ) (hrN : r < N)
    (z : List (FlagKoszul.Positive (FlagModel.Relation C)) →₀ K)
    (hz : z ∈ piece (FlagKoszul.positiveDegree (FlagModel.Relation C)) r N)
    (hdz : differential (FlagModel.basis C K) z = 0) :
    ∃ y ∈ piece (FlagKoszul.positiveDegree (FlagModel.Relation C)) (r + 1) N,
      -differential (FlagModel.basis C K) y = z := by
  let B := FlagModel.basis C K
  let B₀ := FlagKoszul.augmentedBasis (FlagModel.Relation C) (K := K)
  let δ := FlagKoszul.positiveDegree (FlagModel.Relation C)
  let w := FlagModel.weight C
  have hzero (y) : differential B (differential B y) = 0 :=
    differential_squared (sectionAugmentation C K) B (FlagModel.basis_none C K)
      (FlagModel.augmentation_basis C K) y
  have hlead := BarComparison.differential_hasLeadingMap B B₀ w (FlagModel.product_hasTop C K)
  have hhom := BarComparison.leading_differential_preservesComponents B B₀ w
    (FlagModel.product_hasTop C K)
  have hmodel : ∀ x, x ∈ piece δ r N → differential B₀ x = 0 →
      ∃ y, y ∈ piece δ (r + 1) N ∧ differential B₀ y = x := by
    intro x hx hd
    obtain ⟨y, hy, hdy⟩ := FlagKoszul.FlagBar.reduced_cycle_is_boundary
      (FlagModel.relation_refl C) (FlagModel.relation_symm C) r N hrN x hx hd
    exact ⟨-y, Submodule.neg_mem _ hy, by rw [map_neg]; exact hdy⟩
  obtain ⟨y, hy, hdy⟩ := FilteredBoundaries.cycle_is_boundary
    (BarComparison.wordBasis (K := K)) (BarComparison.wordWeight w)
    (differential B) (differential B₀) (piece δ r N) (piece δ (r + 1) N)
    hzero hlead hhom (component_mem_piece δ w r N) (component_mem_piece δ w (r + 1) N)
    (fun y hy => differential_mem_piece B δ (FlagModel.product_degree C K) y hy)
    hmodel z hz hdz
  refine ⟨-y, Submodule.neg_mem _ hy, ?_⟩
  rw [map_neg, neg_neg]
  exact hdy

#print axioms component_mem_piece
#print axioms section_reduced_cycle_is_boundary

end Unimodular.GraphicSectionRing.Koszul

namespace Unimodular.GraphicSectionRing.Koszul

open Unimodular.FlagKoszul.BarReindex

universe u
variable {n : ℕ} (C : Set (Constraint n)) [Fintype (Point C)] (K : Type u) [Field K]

/-- The actual section semigroup algebra is Koszul over every field. All
ordinary derived Tor groups retain their homological and original internal
degrees; the harmless universe lift renames only the positive basis index. -/
theorem sectionAlgebra_hasDiagonalTor :
    PaperVerification.WeightedBar.HasDiagonalTor (sectionAugmentation C K)
      (basis (Equiv.ulift.symm : FlagKoszul.Positive (FlagModel.Relation C) ≃
        ULift.{u} (FlagKoszul.Positive (FlagModel.Relation C))) (FlagModel.basis C K))
      (unit_transport Equiv.ulift.symm (FlagModel.basis C K) (FlagModel.basis_none C K))
      (augmentation_transport Equiv.ulift.symm (sectionAugmentation C K)
        (FlagModel.basis C K) (FlagModel.augmentation_basis C K))
      (FlagKoszul.positiveDegree (FlagModel.Relation C) ∘ Equiv.ulift)
      (productDegree_transport Equiv.ulift.symm (FlagModel.basis C K)
        (FlagKoszul.positiveDegree (FlagModel.Relation C)) (FlagModel.product_degree C K)) :=
  hasDiagonalTor_ulift (sectionAugmentation C K) (FlagModel.basis C K)
    (FlagModel.basis_none C K) (FlagModel.augmentation_basis C K)
    (FlagKoszul.positiveDegree (FlagModel.Relation C)) (FlagModel.product_degree C K)
    (FlagKoszul.positiveDegree_pos (FlagModel.Relation C))
    (section_reduced_cycle_is_boundary C)

#print axioms sectionAlgebra_hasDiagonalTor

end Unimodular.GraphicSectionRing.Koszul

#check Unimodular.GraphicSectionRing.Koszul.sectionAlgebra_hasDiagonalTor
