module
public import graph_foundation.part014
public import shared_results.part020_parity_homology_selected_equiv

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.MixedTransfer.GroebnerReesOrderComparison -/
section

/-! # Rees Koszul degeneration for the original monomial order

No integer weight representing the term order is assumed. The associated
algebra and its differential are the literal initial Rees Koszul algebra.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.MixedTransfer.OrderedRees

open Classical CommAlg FourPapers.Sublattice MvPolynomial
open FourPapers.IntegerFiltered.MultiplicativeFiltration

universe u
variable {K V C : Type u} [Fintype C] [DecidableEq C] [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J I : C → Ideal (MvPolynomial V K))
  (hinit : ∀ s, initialIdealForBasis m ((powerProduct J s)) = (powerProduct I s))
  (G : (C →₀ ℕ) → Set (MvPolynomial V K))
  (hG : ∀ s, m.IsGroebnerBasis (G s) ((powerProduct J s)))
  (hu : ∀ s g, g ∈ G s → g ≠ 0 → IsUnit (m.leadingCoeff g))

local notation "b" => groebnerReesKoszulBasis m J G hG hu
local notation "c" => initialReesKoszulBasis m J I hinit G hG hu
local notation "w" => reesKoszulWeight m J
local notation "F" => idealReesKoszulFiltration m J I hinit G hG hu
local notation "hprod" => initialReesKoszul_product_homogeneous m J I hinit G hG hu
local notation "hlead" => groebnerReesKoszul_product_leading m J I hinit G hG hu
local notation "h1" => (fun a ha => le_of_eq (groebnerReesKoszul_one_weight m J G hG hu a ha))
local notation "hone" => groebnerReesKoszul_leading_one m J I hinit G hG hu

theorem differential_homogeneous (a z : IdealReesKoszulIndex m J)
    (hz : (c).repr ((idealReesKoszulDGA I).d (c a)) z ≠ 0) : w z = w a :=
  congrArg m.toSyn (initialReesKoszul_d_fine m J I hinit G hG hu a z hz)

theorem differential_leading (a z : IdealReesKoszulIndex m J) (hz : w a ≤ w z) :
    (b).repr ((idealReesKoszulDGA J).d (b a)) z = (c).repr ((idealReesKoszulDGA I).d (c a)) z :=
  groebnerReesKoszul_d_leading m J I hinit G hG hu m.toSyn.toAddMonoidHom
    (groebnerReesBasis_product_leading_coeff m J I hinit G hG hu) a z hz

theorem parity_homogeneous (a z : IdealReesKoszulIndex m J)
    (hz : (c).repr ((idealReesKoszulDGA I).parity (c a)) z ≠ 0) : w z = w a :=
  congrArg w (initialReesKoszul_parity_support m J I hinit G hG hu a z hz)

theorem parity_leading (a z : IdealReesKoszulIndex m J) (_ : w a ≤ w z) :
    (b).repr ((idealReesKoszulDGA J).parity (b a)) z = (c).repr ((idealReesKoszulDGA I).parity (c a)) z :=
  reesKoszul_parity_coeff_equal m J I hinit G hG hu a z

def differential_preserves : ∀ n x, x ∈ (F).level n → (idealReesKoszulDGA J).d x ∈ (F).level n :=
  OrderedBasis.differential_preserves b c w hprod hlead h1 (idealReesKoszulDGA J)
    (idealReesKoszulDGA I) (differential_homogeneous m J I hinit G hG hu)
    (differential_leading m J I hinit G hG hu)

def parity_preserves : ∀ n x, x ∈ (F).level n → (idealReesKoszulDGA J).parity x ∈ (F).level n :=
  OrderedBasis.parity_preserves b c w hprod hlead h1 (idealReesKoszulDGA J)
    (idealReesKoszulDGA I) (parity_homogeneous m J I hinit G hG hu)
    (parity_leading m J I hinit G hG hu)

local notation "hd" => differential_preserves m J I hinit G hG hu
local notation "hp" => parity_preserves m J I hinit G hG hu

-- The named concrete homology equivalence is an optional convenience
-- specialization; propagation below uses the proved abstract equivalence.
attribute [local irreducible] groebnerReesKoszulBasis initialReesKoszulBasis
  idealReesKoszulDGA

set_option backward.isDefEq.respectTransparency true in
theorem all_cycle_lifts (U : Set (C →₀ ℕ))
    (hgen : Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA I)
      (Auxiliary.initialSelectedPiece m J I hinit G hG hu U)) = ⊤)
    (hlift : (F).RelativeLiftsCycles (idealReesKoszulDGA J)
      (Auxiliary.selectedPiece m J G hG hu U)) :
    (F).LiftsCycles (idealReesKoszulDGA J) :=
  OrderedBasis.liftsCycles_of_selected_generators (K := K) (A := IdealReesKoszul J)
    (B := IdealReesKoszul I) (I := IdealReesKoszulIndex m J) (Γ := m.syn)
    b c w hprod hlead h1 hone
    (idealReesKoszulDGA J) (idealReesKoszulDGA I)
    (differential_homogeneous m J I hinit G hG hu)
    (differential_leading m J I hinit G hG hu)
    (parity_homogeneous m J I hinit G hG hu)
    (parity_leading m J I hinit G hG hu) {a | a.1.1 ∈ U} hgen hlift

set_option backward.isDefEq.respectTransparency true in
theorem homology_generated_in_degree_one (U : Set (C →₀ ℕ))
    (hgen : Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA I)
      (Auxiliary.initialSelectedPiece m J I hinit G hG hu U)) = ⊤)
    (hlift : (F).RelativeLiftsCycles (idealReesKoszulDGA J)
      (Auxiliary.selectedPiece m J G hG hu U)) :
    Algebra.adjoin K (selectedHomologyClasses (idealReesKoszulDGA J)
      (Auxiliary.selectedPiece m J G hG hu U)) = ⊤ :=
  OrderedBasis.homology_generated_of_selected_generators (K := K) (A := IdealReesKoszul J)
    (B := IdealReesKoszul I) (I := IdealReesKoszulIndex m J) (Γ := m.syn)
    b c w hprod hlead h1 hone
    (idealReesKoszulDGA J) (idealReesKoszulDGA I)
    (differential_homogeneous m J I hinit G hG hu)
    (differential_leading m J I hinit G hG hu)
    (parity_homogeneous m J I hinit G hG hu)
    (parity_leading m J I hinit G hG hu) {a | a.1.1 ∈ U} hgen hlift

end FourPapers.MixedTransfer.OrderedRees

end
end
end


end
