module
public import graph_foundation.part014
public import shared_results.part020_mixed_unit_color_generation

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.IdealCoordinateLeading -/
section

/-! # The actual coordinate differential differs from its monomial model

This proof uses the previously established strict normal-form remainder.
Both complexes are included into the same polynomial Koszul coordinates,
where the differential preserves the full fine degree.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open FourPapers.Universal FourPapers.FilteredHomology

private theorem basisMap_repr_of_injective_index
    {R X Y I J : Type*} [Semiring R]
    [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]
    (b : Module.Basis I R X) (c : Module.Basis J R Y)
    (e : I → J) (he : Function.Injective e) (f : X →ₗ[R] Y)
    (hf : ∀ i, f (b i) = c (e i)) (x : X) (i : I) :
    c.repr (f x) (e i) = b.repr x i := by
  have h : (c.coord (e i)).comp f = b.coord i := by
    apply b.ext
    intro j
    change (c.repr (f (b j))) (e i) = (b.repr (b j)) i
    rw [hf]
    simp only [Module.Basis.repr_self, Finsupp.single_apply, he.eq_iff]
  exact LinearMap.congr_fun h x

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (P : QuotientGroebnerData V K)

def actualIdealAmbientIndex (p : ℕ) (a : ActualIdealIndex P p) : QuotientIndex (∅ : Family V) p :=
  ⟨a.1,⟨a.2.val,emptyFamily_allowed a.2.val⟩⟩

theorem actualIdealAmbientIndex_injective (p : ℕ) :
    Function.Injective (actualIdealAmbientIndex P p) := by
  rintro ⟨F,a⟩ ⟨H,b⟩ h
  have hF : F=H := congrArg Sigma.fst h
  subst H
  have ha : a.val=b.val := congrArg (fun z : QuotientIndex (∅ : Family V) p => z.2.val) h
  exact congrArg (Sigma.mk F) (Subtype.ext ha)

def initialIdealAmbientMap (p : ℕ) :
    (Set.powersetCard V p →₀ P.ideal) →ₗ[K] AmbientKoszulCoordinates (k:=K) (V:=V) p :=
  (idealCoordinatesToAmbient (monomialIdeal K P.family) p).comp (actualIdealMonomialEquiv P p).toLinearMap

theorem initialIdealAmbient_basis_single (p : ℕ) (a : ActualIdealIndex P p) :
    initialIdealAmbientMap P p (actualIdealCoefficientBasis P p a) =
      Finsupp.single a.1 (emptyCoefficientPolynomialEquiv.symm (monomial a.2.val (1:K))) := by
  ext F
  rw [initialIdealAmbientMap,LinearMap.comp_apply,LinearEquiv.coe_coe,actualIdealMonomialEquiv_basis,
    idealCoordinatesToAmbient_apply,monomialCoefficientBasis_apply]
  simp only [actualIdealMonomialIndexEquiv, Equiv.coe_fn_mk]
  by_cases hF : a.1=F
  · rw [Finsupp.single_apply,if_pos hF,Finsupp.single_apply,if_pos hF,monomialBasis_val]
  · rw [Finsupp.single_apply,if_neg hF,Finsupp.single_apply,if_neg hF]
    change emptyCoefficientPolynomialEquiv.symm (0 : MvPolynomial V K) = 0
    exact emptyCoefficientPolynomialEquiv.symm.map_zero

theorem initialIdealAmbient_basis (p : ℕ) (a : ActualIdealIndex P p) :
    initialIdealAmbientMap P p (actualIdealCoefficientBasis P p a) =
      quotientCoefficientBasis (k:=K) (∅ : Family V) p (actualIdealAmbientIndex P p a) := by
  rw [initialIdealAmbient_basis_single,quotientCoefficientBasis_apply]
  apply congrArg (Finsupp.single a.1)
  apply emptyCoefficientPolynomialEquiv.injective
  rw [AlgEquiv.apply_symm_apply,emptyCoefficientPolynomialEquiv_monomial]
  rfl

theorem initialIdealAmbient_repr (p : ℕ) (x : Set.powersetCard V p →₀ P.ideal)
    (a : ActualIdealIndex P p) :
    (quotientCoefficientBasis (k:=K) (∅ : Family V) p).repr
      (initialIdealAmbientMap P p x) (actualIdealAmbientIndex P p a) =
      (actualIdealCoefficientBasis P p).repr x a :=
  basisMap_repr_of_injective_index (R := K)
    (X := Set.powersetCard V p →₀ P.ideal)
    (Y := AmbientKoszulCoordinates (k := K) (V := V) p)
    (I := ActualIdealIndex P p) (J := QuotientIndex (∅ : Family V) p)
    (actualIdealCoefficientBasis P p)
    (quotientCoefficientBasis (k:=K) (∅ : Family V) p)
    (actualIdealAmbientIndex P p) (actualIdealAmbientIndex_injective P p)
    (initialIdealAmbientMap P p) (initialIdealAmbient_basis P p) x a

theorem initialIdealAmbient_differential (p : ℕ) (x : Set.powersetCard V (p+1) →₀ P.ideal) :
    initialIdealAmbientMap P p (initialActualIdealDifferential P p x) =
      quotientDifferential (k:=K) (∅ : Family V) p (initialIdealAmbientMap P (p+1) x) := by
  rw [initialIdealAmbientMap,LinearMap.comp_apply,LinearEquiv.coe_coe,
    actualIdealMonomialEquiv_differential]
  exact (idealCoordinatesToAmbient_differential (monomialIdeal K P.family) p
    (actualIdealMonomialEquiv P (p+1) x)).symm

theorem idealAmbient_basis_difference (p : ℕ) (a : ActualIdealIndex P p) :
    idealCoordinatesToAmbient P.ideal p (actualIdealCoefficientBasis P p a) -
      initialIdealAmbientMap P p (actualIdealCoefficientBasis P p a) =
      -Finsupp.single a.1 (emptyCoefficientPolynomialEquiv.symm
        (P.groebner.normalForm P.unitLeading (monomial a.2.val 1))) := by
  rw [initialIdealAmbient_basis_single]
  ext F
  simp only [Finsupp.sub_apply,Finsupp.neg_apply,idealCoordinatesToAmbient_apply,
    actualIdealCoefficientBasis_apply,Finsupp.single_apply]
  split_ifs with hF
  · apply emptyCoefficientPolynomialEquiv.injective
    simp only [map_sub,map_neg,AlgEquiv.apply_symm_apply]
    change (monomial a.2.val 1 - P.groebner.normalForm P.unitLeading
      (monomial a.2.val 1)) - monomial a.2.val 1 = _
    abel
  · simp only [map_zero,sub_zero,neg_zero]
    change emptyCoefficientPolynomialEquiv.symm (0 : MvPolynomial V K) = 0
    exact emptyCoefficientPolynomialEquiv.symm.map_zero

/-- Subtraction in the coefficient coordinates is evaluated through the
actual scalar action, with no change of additive-group presentation. -/
theorem actualIdealCoefficientBasis_repr_sub (p : ℕ)
    (x y : Set.powersetCard V p →₀ P.ideal) (a : ActualIdealIndex P p) :
    (actualIdealCoefficientBasis P p).repr (x-y) a =
      (actualIdealCoefficientBasis P p).repr x a -
        (actualIdealCoefficientBasis P p).repr y a := by
  rw [actualIdealCoordinate_sub_eq_add_neg_one_smul P p x y,
    (actualIdealCoefficientBasis P p).repr.map_add,
    (actualIdealCoefficientBasis P p).repr.map_smul]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    neg_one_mul, sub_eq_add_neg]


variable (w : V → ℕ)
  (htail : ∀ g∈P.generators, g≠0 → ∀ a∈(monomial (P.order.degree g) 1-g).support,
    Finsupp.weight w a < Finsupp.weight w (P.order.degree g))

include htail in
theorem idealAmbient_basis_difference_lower (p : ℕ) (a : ActualIdealIndex P p) :
    idealCoordinatesToAmbient P.ideal p (actualIdealCoefficientBasis P p a) -
      initialIdealAmbientMap P p (actualIdealCoefficientBasis P p a) ∈
      (quotientCoordinateFiltration (∅ : Family V) w p).level
        (Finsupp.weight w (actualIdealDegree a)) := by
  rw [idealAmbient_basis_difference,quotientCoordinateFiltration,basisFiltration_mem]
  intro b hb
  rw [map_neg,Finsupp.neg_apply,neg_eq_zero]
  have hr : (quotientCoefficientBasis (k:=K) (∅ : Family V) p).repr
      (Finsupp.single a.1 (emptyCoefficientPolynomialEquiv.symm
        (P.groebner.normalForm P.unitLeading (monomial a.2.val 1)))) b =
      if a.1=b.1 then (P.groebner.normalForm P.unitLeading
        (monomial a.2.val 1)).coeff b.2.val else 0 := by
    rw [quotientCoefficientBasis,Finsupp.basis_repr,Finsupp.single_apply]
    split_ifs
    · rw [emptyCoefficientPolynomialEquiv_repr,AlgEquiv.apply_symm_apply]
    · simp only [map_zero,Finsupp.zero_apply]
  rw [hr]
  split_ifs with hF
  · by_contra hc
    have hnf := (mem_restrictSupport_iff K).mp
      (groebner_normalForm_strictly_lowers_of_tails P.order P.ideal P.generators
        P.groebner P.unitLeading w htail a.2.val a.2.property)
      (mem_support_iff.mpr hc)
    change Finsupp.weight w b.2.val < Finsupp.weight w a.2.val at hnf
    simp only [actualIdealDegree,quotientDegree,map_add,hF] at hb
    omega
  · rfl

include htail in
/-- Equal-or-higher weight coefficients of the actual differential agree
with those of the actual monomial differential transported to the same basis. -/
theorem actualIdealPrevious_strictly_lowers_of_tails
    (p : ℕ) (a : ActualIdealIndex P p) (b : ActualIdealIndex P p.pred)
    (hweight : Finsupp.weight w (actualIdealDegree a) ≤ Finsupp.weight w (actualIdealDegree b)) :
    (actualIdealCoefficientBasis P p.pred).repr
      (actualIdealPreviousDifferential P.ideal p (actualIdealCoefficientBasis P p a) -
        initialActualIdealPrevious P p (actualIdealCoefficientBasis P p a)) b = 0 := by
  cases p with
  | zero =>
    change (actualIdealCoefficientBasis P 0).repr
      ((0 : Set.powersetCard V 0 →₀ P.ideal) - 0) b = 0
    rw [actualIdealCoefficientBasis_repr_sub]
    simp only [(actualIdealCoefficientBasis P 0).repr.map_zero, Finsupp.zero_apply, sub_self]
  | succ p =>
    let x := actualIdealCoefficientBasis P (p+1) a
    have hd := basisHomogeneous_preserves
      (quotientCoefficientBasis (k:=K) (∅ : Family V) (p+1))
      (quotientCoefficientBasis (k:=K) (∅ : Family V) p)
      (fun a => Finsupp.weight w (quotientDegree a))
      (fun a => Finsupp.weight w (quotientDegree a))
      (quotientDifferential (k:=K) (∅ : Family V) p)
      (quotientDifferential_basis_regraded (∅ : Family V) (Finsupp.weight w) p)
      (Finsupp.weight w (actualIdealDegree a)) _
      (idealAmbient_basis_difference_lower P w htail (p+1) a)
    rw [map_sub,idealCoordinatesToAmbient_differential,← initialIdealAmbient_differential] at hd
    have hz := (basisFiltration_mem
      (quotientCoefficientBasis (k:=K) (∅ : Family V) p)
      (fun a => Finsupp.weight w (quotientDegree a))
      (Finsupp.weight w (actualIdealDegree a)) _).mp hd
      (actualIdealAmbientIndex P p b) hweight
    simp only [map_sub, Finsupp.sub_apply] at hz
    rw [initialIdealAmbient_repr P p] at hz
    simp only [idealCoordinatesToAmbient_repr, actualIdealAmbientIndex,
      ← actualIdealCoefficientBasis_repr] at hz
    change (actualIdealCoefficientBasis P p).repr
      (actualIdealCoordinateDifferential P.ideal p x -
        initialActualIdealDifferential P p x) b = 0
    rw [actualIdealCoefficientBasis_repr_sub]
    exact hz

end FourPapers.Sublattice

end
end
end


end
