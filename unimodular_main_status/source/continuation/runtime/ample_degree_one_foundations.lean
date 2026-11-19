module

public import Continuation.Runtime.SectionEmbeddingRecovered

/-!
# Ordinary ampleness and the degree-one section morphism

These lemmas supply the actual section-theoretic interfaces needed to descend
an ample positive-power embedding to degree one. Nonvanishing is compared
with the ordinary stalk-span definition, and all polynomial identities refer
to genuine rational values of sections of the original sheaf.

Closed immersion and the pullback of O(1) are proved in the subsequent
modules; these foundational lemmas do not assert Property N_p.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

universe u
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricSchemes
open scoped Classical BaseSections

namespace Unimodular.NefBig

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

/-- The ordinary tensor-power criterion implies precisely the recovered
Cartier nonvanishing-open criterion; the actual sheaf is unchanged. -/
theorem isAmple_cocycle_of_isAmpleModule (hC : IsAmpleModule C.sheaf) :
    C.IsAmple := by
  obtain ⟨hInv, hcompact, hcover⟩ := hC
  refine ⟨hcompact, ?_⟩
  intro x
  obtain ⟨m, hm, s, hx, hs⟩ := hcover x
  letI := hInv m
  let e := C.tensorSheafPowerIso m
  have he : (C.pow m).nonvanishingOpen (e.hom.app ⊤ s) =
      (tensorSheafPower C.sheaf m).nonvanishingLocus s := by
    rw [cocycle_nonvanishingOpen_eq, Scheme.Modules.nonvanishingLocus_hom_app]
  exact ⟨m, hm, e.hom.app ⊤ s,
    by simpa only [he] using hx, by simpa only [he] using hs⟩

/-- A proved equivalence, rather than identification of two named
ampleness predicates. -/
theorem isAmpleModule_iff_cocycle : IsAmpleModule C.sheaf ↔ C.IsAmple :=
  ⟨isAmple_cocycle_of_isAmpleModule C, isAmpleModule_of_cocycle C⟩

end Unimodular.NefBig

namespace PaperVerification.ToricSchemes.RationalCartierCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} [IsIntegral X] (C : RationalCartierCocycle X)

/-- Natural Cartier powers associate by equality of their actual local
generators, not by a new interpretation of tensor powers. -/
theorem pow_pow_eq (a b : ℕ) : (C.pow a).pow b = C.pow (a * b) := by
  cases C
  simp only [pow, pow_mul]

theorem pow_one_eq : C.pow 1 = C := by
  cases C
  simp only [pow, pow_one]

variable (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
  {ι : Type u} (s : ι → Γ(C.sheaf, ⊤))

/-- The exact local-coordinate identity for a homogeneous polynomial in
actual degree-one sections. This is also valid on an empty local chart. -/
theorem localCoefficient_homogeneous_polynomial (N : ℕ)
    (t : Γ((C.pow N).sheaf, ⊤)) (p : MvPolynomial ι k)
    (hp : p.IsHomogeneous N)
    (hvalue : C.sectionProjectiveFieldMap k s p =
      (C.pow N).toCartierData.sectionValue ⊤ t) (i : C.index) :
    (C.pow N).localCoefficient i t =
      MvPolynomial.eval₂Hom (BaseSections.scalarMap k X (C.openSet i))
        (fun j => C.localCoefficient i (s j)) p := by
  by_cases hU : Nonempty (C.openSet i)
  · letI := hU
    letI : Nonempty ((C.pow N).openSet i) := hU
    let F := (X.germToFunctionField ⊤).hom.comp (BaseSections.scalarMap k X ⊤)
    let v : ι → X.functionField := fun j => C.toCartierData.sectionValue ⊤ (s j)
    have he : (X.germToFunctionField (C.openSet i)).hom.comp
        (MvPolynomial.eval₂Hom (BaseSections.scalarMap k X (C.openSet i))
          (fun j => C.localCoefficient i (s j))) =
        MvPolynomial.eval₂Hom F
          (fun j => (C.generator i : X.functionField)⁻¹ * v j) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        exact BaseSections.germ_scalarMap_top k X (C.openSet i) a
      · intro j
        simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
        rw [C.localCoefficient_value]
        change v j / (C.generator i : X.functionField) =
          (C.generator i : X.functionField)⁻¹ * v j
        rw [div_eq_mul_inv, mul_comm]
    apply X.germToFunctionField_injective (C.openSet i)
    calc
      _ = (C.pow N).toCartierData.sectionValue ⊤ t /
          (C.generator i : X.functionField) ^ N :=
        (C.pow N).localCoefficient_value i t
      _ = _ := ?_
    change (C.pow N).toCartierData.sectionValue ⊤ t /
      (C.generator i : X.functionField) ^ N =
      ((X.germToFunctionField (C.openSet i)).hom.comp
        (MvPolynomial.eval₂Hom (BaseSections.scalarMap k X (C.openSet i))
          (fun j => C.localCoefficient i (s j)))) p
    rw [he, ← hvalue]
    change p.eval₂ F v / (C.generator i : X.functionField) ^ N =
      p.eval₂ F (fun j => (C.generator i : X.functionField)⁻¹ * v j)
    rw [homogeneous_eval_scaled F v _ p N hp, inv_pow, div_eq_mul_inv, mul_comm]
  · have hbot : C.openSet i = ⊥ := by
      apply le_antisymm ?_ bot_le
      intro x hx
      exact (hU ⟨⟨x, hx⟩⟩).elim
    letI : Subsingleton Γ(X, (C.pow N).openSet i) :=
      regularSections_subsingleton_of_empty X (C.openSet i) hbot
    exact Subsingleton.elim _ _

private theorem eval₂_mem_ideal_of_constantCoeff_zero
    {R : Type u} [CommRing R] (I : Ideal R) (f : k →+* R) (v : ι → R)
    (hv : ∀ i, v i ∈ I) (p : MvPolynomial ι k) (hp : p.coeff 0 = 0) :
    MvPolynomial.eval₂Hom f v p ∈ I := by
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  have he : (Ideal.Quotient.mk I).comp (MvPolynomial.eval₂Hom f v) =
      ((Ideal.Quotient.mk I).comp f).comp MvPolynomial.constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X',
        MvPolynomial.constantCoeff_X, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hv i)
  change ((Ideal.Quotient.mk I).comp (MvPolynomial.eval₂Hom f v)) p = 0
  rw [he]
  simpa only [RingHom.comp_apply, MvPolynomial.constantCoeff_eq, hp, map_zero]

/-- A positive-degree polynomial section cannot be nonzero in a fibre at
which every original degree-one section vanishes. -/
theorem nonvanishingOpen_homogeneous_polynomial_le (N : ℕ) (hN : 0 < N)
    (t : Γ((C.pow N).sheaf, ⊤)) (p : MvPolynomial ι k)
    (hp : p.IsHomogeneous N)
    (hvalue : C.sectionProjectiveFieldMap k s p =
      (C.pow N).toCartierData.sectionValue ⊤ t) :
    (C.pow N).nonvanishingOpen t ≤ ⨆ i, C.nonvanishingOpen (s i) := by
  intro x hx
  by_contra hnone
  have hnone' (j : ι) : x ∉ C.nonvanishingOpen (s j) :=
    fun hj => hnone (Opens.mem_iSup.mpr ⟨j, hj⟩)
  obtain ⟨i, hxi⟩ := C.covers x
  have ht := ((C.pow N).mem_nonvanishingOpen_iff_not_mem_maximalIdeal i t x hxi).mp hx
  apply ht
  rw [C.localCoefficient_homogeneous_polynomial k s N t p hp hvalue i]
  change (X.presheaf.germ (C.openSet i) x hxi).hom
    (p.eval₂ (BaseSections.scalarMap k X (C.openSet i))
      (fun j => C.localCoefficient i (s j))) ∈ _
  rw [MvPolynomial.eval₂_comp_left]
  refine eval₂_mem_ideal_of_constantCoeff_zero k _ _ _ (fun j => ?_) p ?_
  ·
    exact not_not.mp (fun hj => hnone' j
      ((C.mem_nonvanishingOpen_iff_not_mem_maximalIdeal i (s j) x hxi).mpr hj))
  · exact hp.coeff_eq_zero (d := 0) (by simpa using (Nat.ne_of_gt hN).symm)

/-- Genuine homogeneous generation and ordinary ampleness imply that the
original degree-one sections generate the line bundle at every point. -/
theorem nonvanishing_cover_of_homogeneous_generation
    (hC : Unimodular.NefBig.IsAmpleModule C.sheaf)
    (hgen : ∀ (N : ℕ) (t : Γ((C.pow N).sheaf, ⊤)),
      ∃ p : MvPolynomial ι k, p.IsHomogeneous N ∧
        C.sectionProjectiveFieldMap k s p =
          (C.pow N).toCartierData.sectionValue ⊤ t) :
    (⨆ i, C.nonvanishingOpen (s i)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨N, hN, t, hx, _⟩ :=
    (Unimodular.NefBig.isAmple_cocycle_of_isAmpleModule C hC).2 x
  obtain ⟨p, hp, hvalue⟩ := hgen N t
  exact C.nonvanishingOpen_homogeneous_polynomial_le k s N hN t p hp hvalue hx

/-- The degree-one morphism here is the actual glued morphism into
polynomial Proj. Its construction uses no assumed embedding criterion. -/
def degreeOneSectionMorphism
    (hC : Unimodular.NefBig.IsAmpleModule C.sheaf)
    (hgen : ∀ (N : ℕ) (t : Γ((C.pow N).sheaf, ⊤)),
      ∃ p : MvPolynomial ι k, p.IsHomogeneous N ∧
        C.sectionProjectiveFieldMap k s p =
          (C.pow N).toCartierData.sectionValue ⊤ t) :
    X ⟶ Proj (MvPolynomial.homogeneousSubmodule ι k) :=
  C.sectionProjectiveMap k s (C.nonvanishing_cover_of_homogeneous_generation k s hC hgen)

@[simp] theorem degreeOneSectionMorphism_preimage
    (hC : Unimodular.NefBig.IsAmpleModule C.sheaf)
    (hgen : ∀ (N : ℕ) (t : Γ((C.pow N).sheaf, ⊤)),
      ∃ p : MvPolynomial ι k, p.IsHomogeneous N ∧
        C.sectionProjectiveFieldMap k s p =
          (C.pow N).toCartierData.sectionValue ⊤ t) (i : ι) :
    C.degreeOneSectionMorphism k s hC hgen ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule ι k) (MvPolynomial.X i) =
        C.nonvanishingOpen (s i) :=
  C.sectionProjectiveMap_preimage k s _ i

end PaperVerification.ToricSchemes.RationalCartierCocycle

#print axioms Unimodular.NefBig.isAmpleModule_iff_cocycle
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.localCoefficient_homogeneous_polynomial
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.nonvanishing_cover_of_homogeneous_generation
#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.degreeOneSectionMorphism_preimage

end
