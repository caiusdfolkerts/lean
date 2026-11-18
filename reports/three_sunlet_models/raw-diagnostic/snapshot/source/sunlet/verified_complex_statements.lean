module
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import sunlet.cyclic_orbit_models
public import sunlet.distinct_derangements
public import sunlet.paper_statements
public import sunlet.verified_cyclic_paper
public import sunlet.verified_model_fibers
public import sunlet.verified_network_conclusion
public import sunlet.verified_normalized_generic_fiber

@[expose] public section
set_option Elab.async false

#check "SUNLET_VERIFIEDCOMPLEXSTATEMENTS_IMPORTS_READY"

section Stage_ComplexGroundField


/-!
# The complex coefficient field

Mathlib proves the fundamental theorem of algebra in the imported module.
The paper's complex statements therefore use the actual complex field and
its proved algebraic closedness, rather than an additional field hypothesis.
-/


namespace Sunlet.ComplexGroundField

theorem complex_isAlgClosed : IsAlgClosed ℂ := inferInstance

theorem complex_charZero : CharZero ℂ := inferInstance

theorem complex_infinite : Infinite ℂ := inferInstance

end Sunlet.ComplexGroundField
end Stage_ComplexGroundField
#check "SUNLET_VERIFIEDCOMPLEXSTATEMENTS_ComplexGroundField_DONE"

section Stage_ComplexPaperSpecializations


/-!
# Principal results over the actual complex numbers

These are literal specializations of the proved general-field statements.
No algebraic-closedness or characteristic assumption appears among their
hypotheses: the corresponding instances come from `ComplexGroundField`.
The complete model maps, all parameter ranges, and all fiber conclusions
are retained.
-/

noncomputable section

namespace Sunlet.ComplexPaper

attribute [local instance] Classical.propDecidable

section Latin

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
  [DecidableEq ι] [DecidableEq Ω]
  (L : NormalizedLatinSystem ι Ω) (o : Ω)

/-- The first assertion of Theorem 4.2, including all boundary points of
the complex toric closure and a nonempty dense open in its secant. -/
theorem generic_unique_unordered_decomposition (hm : 5 ≤ Fintype.card Ω) :
    ∃ P : MvPolynomial (L.NonidentityColor × Ω) ℂ,
      MvPolynomial.aeval
        (ToricPairAlgebra.genericCoordinates (k := ℂ) o L.nonidentityPerm) P ≠ 0 ∧
      (ToricPairAlgebra.principalOpen (k := ℂ) o L.nonidentityPerm P).Nonempty ∧
      PolynomialClosureProduct.closure
          (ToricPairAlgebra.principalOpen (k := ℂ) o L.nonidentityPerm P) =
        ToricPairAlgebra.secantClosure (k := ℂ) o L.nonidentityPerm ∧
      ∀ z ∈ ToricPairAlgebra.principalOpen (k := ℂ) o L.nonidentityPerm P,
        ∃ x ∈ ToricPairAlgebra.toricClosure (k := ℂ) o L.nonidentityPerm,
          ∃ y ∈ ToricPairAlgebra.toricClosure (k := ℂ) o L.nonidentityPerm,
            x + y = z ∧
            ∀ x' ∈ ToricPairAlgebra.toricClosure (k := ℂ) o L.nonidentityPerm,
              ∀ y' ∈ ToricPairAlgebra.toricClosure (k := ℂ) o L.nonidentityPerm,
                x' + y' = z → (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') :=
  L.generic_unique_unordered_decomposition (k := ℂ) o hm

/-- Theorem 4.2: degree of the literal normalized complex map. -/
theorem normalized_generic_degree (hm : 5 ≤ Fintype.card Ω) :
    Module.finrank (L.NormalizedImageField (k := ℂ) o)
      (L.NormalizedSourceField (k := ℂ) o) =
        2 * Nat.card (L.loopAt o).AbelianGroup ^ 2 :=
  L.normalized_generic_degree (k := ℂ) o hm

theorem paper_theorem_4_2_algebraic_fibers (hm : 5 ≤ Fintype.card Ω) :
    Nat.card (L.DiscreteFiber (K := ℂ) o) = 2 * Nat.card (L.loopAt o).AbelianGroup ^ 2 ∧
    ∃ W : MvPolynomial (ι × Ω) ℂ,
      (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := ℂ) L.perm) W).Nonempty ∧
      MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ
        (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := ℂ) L.perm) W)) =
          Sunlet.imageClosure L.perm ∧
      ∀ q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := ℂ) L.perm) W,
        ∃ C : L.DiscreteFiber (K := ℂ) o → Set (ParamVar ι Ω → ℂ),
          (∀ j, ∃ A : Ideal (MvPolynomial (ParamVar ι Ω) ℂ), C j = MvPolynomial.zeroLocus ℂ A) ∧
          Pairwise (fun i j => Disjoint (C i) (C j)) ∧
          (⋃ j, C j) = FiberAlgebraic.affineFiberSet L.perm q ∧
          ∀ j, Nonempty (AlgebraicSets.PolynomialEquiv (C j) (FiberAlgebraic.gaugeSpace (K := ℂ))) :=
  L.paper_theorem_4_2_algebraic_fibers (K := ℂ) o hm

theorem six_family_general_algebraic_fiber (hm : 5 ≤ Fintype.card Ω) :
    Nat.card (L.DiscreteFiber (K := ℂ) o) = 2 * Nat.card (L.loopAt o).AbelianGroup ^ 2 ∧
    ∃ W : MvPolynomial (ι × Ω) ℂ,
      (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := ℂ) L.perm) W).Nonempty ∧
      MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ
        (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := ℂ) L.perm) W)) =
          Sunlet.imageClosure L.perm ∧
      ∀ q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := ℂ) L.perm) W,
        (∀ a, q (a, o) ≠ 0) ∧
        ∃ C : L.DiscreteFiber (K := ℂ) o → Set (SixFamilyFibers.ParamVar ι Ω → ℂ),
          (∀ j, ∃ A : Ideal (MvPolynomial (SixFamilyFibers.ParamVar ι Ω) ℂ),
            C j = MvPolynomial.zeroLocus ℂ A) ∧
          Pairwise (fun i j => Disjoint (C i) (C j)) ∧
          (⋃ j, C j) = SixFamilyAlgebraic.affineFiberSet L.perm q ∧
          ∀ j, Nonempty (AlgebraicSets.PolynomialEquiv (C j)
            (SixFamilyAlgebraic.gaugeSpace (K := ℂ) (ι := ι))) :=
  L.six_family_general_algebraic_fiber (K := ℂ) o hm

theorem normalized_isGalois (hm : 5 ≤ Fintype.card Ω) :
    IsGalois (L.NormalizedImageField (k := ℂ) o)
      (L.NormalizedSourceField (k := ℂ) o) :=
  L.normalized_isGalois (k := ℂ) o hm

def normalizedGaloisEquiv (hm : 5 ≤ Fintype.card Ω) :
    (L.loopAt o).CharacterWreath (k := ℂ) ≃*
      (L.NormalizedSourceField (k := ℂ) o ≃ₐ[L.NormalizedImageField (k := ℂ) o]
        L.NormalizedSourceField (k := ℂ) o) :=
  L.normalizedGaloisEquiv (k := ℂ) o hm

end Latin

section LiteralDimension

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem paper_theorem_1_1
    (m : ℕ) (hm : 5 ≤ m) (π : Fin m → Equiv.Perm Ω)
    (hcard : Fintype.card Ω = m)
    (he : π ⟨0, by omega⟩ = Equiv.refl Ω)
    (hcolumns : ∀ b, Function.Injective (fun a => π a b)) :
    ringKrullDim (MvPolynomial (Fin m × Ω) ℂ ⧸
      MvPolynomial.vanishingIdeal ℂ (imageClosure (K := ℂ) π)) =
        (5 * m - 4 : ℕ) :=
  Sunlet.paper_theorem_1_1_fin (K := ℂ) m hm π hcard he hcolumns

theorem paper_theorem_2_3
    (c : ℕ) (π : Fin (c + 1) → Equiv.Perm Ω)
    (he : π 0 = Equiv.refl Ω)
    (hπ : Function.Injective (fun a : {a : Fin (c + 1) // a ≠ 0} => π a))
    (hder : ∀ a, a ≠ 0 → ∀ b, π a b ≠ b)
    (S : TransitiveColorSplit π 0) :
    ringKrullDim (MvPolynomial (Fin (c + 1) × Ω) ℂ ⧸
      MvPolynomial.vanishingIdeal ℂ (imageClosure (K := ℂ) π)) =
        (3 * Fintype.card Ω + 2 * c - 2 : ℕ) :=
  Sunlet.paper_theorem_2_3_literal (K := ℂ) c π he hπ hder S

end LiteralDimension

section Network

open NetworkGraphDecomposition NetworkGraphModel NetworkDisplayedFlowCuts

variable {V G : Type*} [Fintype V] [DecidableEq V]
  [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem paper_corollary_8_1 (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (O : Orientation H) (R : ReticulationData H)
    (B : AddSubgroup (AddAut G)) (hm : 5≤Fintype.card G) :
    ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Leaf H) G) ℂ ⧸
      MvPolynomial.vanishingIdeal ℂ
        (PolynomialImage.closure (leafCutCoordinate (K := ℂ) H O R
          (OrbitClasses.classOf B))))=
        ((Fintype.card (OrbitClasses.Class B)-1)*(edgeCount H-cycleCount H)+1-
          NetworkTriangleIncidence.defect B*triangleCount H : ℕ) :=
  NetworkTheorem.paper_corollary_8_1_leaf_cut (K := ℂ) H hH O R B hm

theorem paper_corollary_8_1_unrestricted
    (H : SimpleGraph V) (hH : IsBinaryCactus H)
    (O : Orientation H) (R : ReticulationData H) (hm : 5≤Fintype.card G) :
    ringKrullDim (MvPolynomial (NetworkFlowGluing.Flow (Leaf H) G) ℂ ⧸
      MvPolynomial.vanishingIdeal ℂ
        (PolynomialImage.closure (leafCutCoordinate (K := ℂ) H O R (id : G → G))))=
        ((Fintype.card G-1)*(2*leafCount H-3+2*cycleCount H)+1 : ℕ) :=
  NetworkTheorem.paper_corollary_8_1_unrestricted_leaf_cut (K := ℂ) H hH O R hm

end Network

section Orbit

open OrbitClasses

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem paper_theorem_7_1
    (B : AddSubgroup (AddAut G)) (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (GroupCoordinates.FlowIndex G) ℂ ⧸
      MvPolynomial.vanishingIdeal ℂ
        (ClassGroupCoordinates.tripleImageClosure (K := ℂ) (classOf B))) =
      (if Fintype.card (Class B) = 2 then (5 : ℕ)
        else if OrbitIndexTwoException B then 10 else 5 * Fintype.card (Class B) - 4) :=
  OrbitClasses.paper_theorem_7_1 (K := ℂ) B hm

end Orbit

section CyclicProjection

open CyclicSelectedField

theorem paper_theorem_6_1
    (m : ℕ) (hm : 6 ≤ m) :
    letI : NeZero m := ⟨by omega⟩
    Fintype.card (FullObserved m hm) = 8*m-12 ∧
    Function.Injective (fullObservationIndex m hm) ∧
    Set.range (fullObservationIndex m hm) = {ab | LiteralRetained m ab} ∧
    let R := originalModelRationalInverse (k := ℂ) m hm
    R.inverseOpen.Nonempty ∧
    MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ R.inverseOpen) =
      GroupCoordinates.imageClosure (K := ℂ) (G := ZMod m) ∧
    ∀ x ∈ R.inverseOpen, R.inverse (x ∘ fullObservationIndex m hm) = x :=
  CyclicSelectedField.paper_theorem_6_1_all_orders (k := ℂ) m hm

end CyclicProjection

section PrimeLoop

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (L : LoopData Ω)

theorem paper_corollary_5_1_degree (hm : 5 ≤ Fintype.card Ω)
    (hprime : Nat.Prime (Fintype.card Ω)) (hnonassoc : ¬L.IsAssociative) :
    Module.finrank (L.asLatin.NormalizedImageField (k := ℂ) L.identity)
      (L.asLatin.NormalizedSourceField (k := ℂ) L.identity) = 2 :=
  L.paper_corollary_5_1_degree (k := ℂ) hm hprime hnonassoc

theorem paper_corollary_5_1_automorphisms (hm : 5 ≤ Fintype.card Ω)
    (hprime : Nat.Prime (Fintype.card Ω)) (hnonassoc : ¬L.IsAssociative)
    (σ : L.asLatin.NormalizedSourceField (k := ℂ) L.identity ≃ₐ[
      L.asLatin.NormalizedImageField (k := ℂ) L.identity]
        L.asLatin.NormalizedSourceField (k := ℂ) L.identity) :
    σ = 1 ∨ σ = L.asLatin.normalizedInterchange L.identity :=
  L.paper_corollary_5_1_automorphisms (k := ℂ) hm hprime hnonassoc σ

/-- The full pointwise ambiguity assertion of Corollary 5.1 over ℂ. -/
theorem paper_corollary_5_1_point_ambiguity (hm : 5 ≤ Fintype.card Ω)
    (hprime : Nat.Prime (Fintype.card Ω)) (hnonassoc : ¬L.IsAssociative) :
    ∃ W : MvPolynomial (Ω × Ω) ℂ,
      (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := ℂ) L.left) W).Nonempty ∧
      MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ
        (PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := ℂ) L.left) W)) =
          Sunlet.imageClosure L.left ∧
      ∀ q ∈ PolynomialImage.principalOpen (Sunlet.coordinatePolynomial (K := ℂ) L.left) W,
        ∃ p : Normalization.Parameters ℂ Ω Ω L.identity L.identity,
          Normalization.parameterMap L.left p = q ∧
          p ≠ Normalization.interchangeParameters p ∧
          ∀ r : Normalization.Parameters ℂ Ω Ω L.identity L.identity,
            Normalization.parameterMap L.left r = q ↔
              r = p ∨ r = Normalization.interchangeParameters p :=
  L.paper_corollary_5_1_point_ambiguity (K := ℂ) hm hprime hnonassoc

end PrimeLoop

section GeneralPartitions

open OrbitHeight

theorem paper_theorem_7_1_inverse_stable
    {G C : Type*} [AddCommGroup G] [Fintype G] [Fintype C]
    (P : InverseStablePartition G C) (hm : 5 ≤ Fintype.card G) :
    ringKrullDim (MvPolynomial (GroupCoordinates.FlowIndex G) ℂ ⧸
      MvPolynomial.vanishingIdeal ℂ
        (ClassGroupCoordinates.tripleImageClosure (K := ℂ) P.classOf)) =
      (if Fintype.card C = 2 then (5 : ℕ)
        else if P.IndexTwoException then 10 else 5 * Fintype.card C - 4) :=
  OrbitHeight.inverse_stable_original_coordinates_order_free (K := ℂ) P hm

end GeneralPartitions

section CyclicOrbits

open OrbitClasses

theorem paper_corollary_7_4
    (n : ℕ) (hn : 5 ≤ n) (B : AddSubgroup (AddAut (ZMod n))) :
    letI : NeZero n := ⟨by omega⟩
    ringKrullDim (MvPolynomial (GroupCoordinates.FlowIndex (ZMod n)) ℂ ⧸
      MvPolynomial.vanishingIdeal ℂ
        (ClassGroupCoordinates.tripleImageClosure (K := ℂ) (classOf B))) =
      (if n.Prime ∧ B = ⊤ then (5 : ℕ) else 5 * Fintype.card (Class B) - 4) :=
  OrbitClasses.paper_corollary_7_4 (K := ℂ) n hn B

end CyclicOrbits

end Sunlet.ComplexPaper
end
end Stage_ComplexPaperSpecializations
#check "SUNLET_VERIFIEDCOMPLEXSTATEMENTS_ComplexPaperSpecializations_DONE"

#check Sunlet.ComplexGroundField.complex_isAlgClosed
#print axioms Sunlet.ComplexGroundField.complex_isAlgClosed

#check Sunlet.ComplexGroundField.complex_charZero
#print axioms Sunlet.ComplexGroundField.complex_charZero

#check Sunlet.ComplexPaper.paper_theorem_1_1
#print axioms Sunlet.ComplexPaper.paper_theorem_1_1

#check Sunlet.ComplexPaper.paper_theorem_2_3
#print axioms Sunlet.ComplexPaper.paper_theorem_2_3

#check Sunlet.ComplexPaper.generic_unique_unordered_decomposition
#print axioms Sunlet.ComplexPaper.generic_unique_unordered_decomposition

#check Sunlet.ComplexPaper.normalized_generic_degree
#print axioms Sunlet.ComplexPaper.normalized_generic_degree

#check Sunlet.ComplexPaper.normalized_isGalois
#print axioms Sunlet.ComplexPaper.normalized_isGalois

#check Sunlet.ComplexPaper.normalizedGaloisEquiv
#print axioms Sunlet.ComplexPaper.normalizedGaloisEquiv

#check Sunlet.ComplexPaper.paper_theorem_4_2_algebraic_fibers
#print axioms Sunlet.ComplexPaper.paper_theorem_4_2_algebraic_fibers

#check Sunlet.ComplexPaper.six_family_general_algebraic_fiber
#print axioms Sunlet.ComplexPaper.six_family_general_algebraic_fiber

#check Sunlet.ComplexPaper.paper_corollary_5_1_point_ambiguity
#print axioms Sunlet.ComplexPaper.paper_corollary_5_1_point_ambiguity

#check Sunlet.ComplexPaper.paper_theorem_6_1
#print axioms Sunlet.ComplexPaper.paper_theorem_6_1

#check Sunlet.ComplexPaper.paper_theorem_7_1
#print axioms Sunlet.ComplexPaper.paper_theorem_7_1

#check Sunlet.ComplexPaper.paper_theorem_7_1_inverse_stable
#print axioms Sunlet.ComplexPaper.paper_theorem_7_1_inverse_stable

#check Sunlet.ComplexPaper.paper_corollary_7_4
#print axioms Sunlet.ComplexPaper.paper_corollary_7_4

#check Sunlet.ComplexPaper.paper_corollary_8_1
#print axioms Sunlet.ComplexPaper.paper_corollary_8_1

#check Sunlet.ComplexPaper.paper_corollary_8_1_unrestricted
#print axioms Sunlet.ComplexPaper.paper_corollary_8_1_unrestricted
