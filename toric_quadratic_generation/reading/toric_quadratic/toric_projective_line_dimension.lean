module

public import PaperVerification.ToricRankOneFans
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field

@[expose] public section

/-! # The actual Krull dimension of the two-chart projective line -/

noncomputable section

namespace PaperVerification.ToricGeometry

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PaperVerification.ToricSchemes

variable (k : Type*) [Field k]

theorem projectiveLine_orderKrullDim : Order.krullDim (projectiveLineScheme k) = 1 := by
  apply le_antisymm
  · rw [Order.krullDim_eq_iSup_coheight]
    apply iSup_le
    intro x
    obtain ⟨negative,p,rfl⟩ := projectiveLinePolynomialChart_jointly_surjective k x
    let R := CommRingCat.of (Polynomial k)
    let q : Spec R := p
    have hc : Order.coheight ((projectiveLinePolynomialChart k negative) q) =
        p.asIdeal.height :=
      (coheight_eq_of_isOpenImmersion (x := q)
        (projectiveLinePolynomialChart k negative)).trans
          (idealHeight_eq_coheight R q).symm
    have h := Ideal.height_le_ringKrullDim_of_ne_top p.isPrime.ne_top
    have hp : (p.asIdeal.height : WithBot ENat) ≤ 1 := by
      simpa only [Polynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field,zero_add] using h
    exact (congrArg (fun d : ENat => (d : WithBot ENat)) hc).trans_le hp
  · let p := polynomialOrigin k
    letI : IsDiscreteValuationRing (Localization.AtPrime p.asIdeal) :=
      principalPrimeLocalization_isDiscreteValuationRing
        (Polynomial k) (Localization.AtPrime p.asIdeal) p.asIdeal
        Polynomial.X Polynomial.X_ne_zero (polynomialOrigin_ideal k)
    have hc := affineOpen_coheight_eq_one (.of (Polynomial k))
      (projectiveLinePolynomialChart k false) p
    have h := Order.coheight_le_krullDim
      (projectiveLinePolynomialChart k false p)
    simpa only [hc,WithBot.coe_one] using h

/-- The dimension is the usual dimension by chains of irreducible closed
subsets of the actual underlying topological space. -/
theorem projectiveLine_topologicalKrullDim :
    topologicalKrullDim (projectiveLineScheme k) = 1 := by
  change Order.krullDim (IrreducibleCloseds (projectiveLineScheme k)) = 1
  rw [Order.krullDim_eq_of_orderIso
    (irreducibleSetEquivPoints (α := projectiveLineScheme k))]
  exact projectiveLine_orderKrullDim k

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.projectiveLine_topologicalKrullDim
