module

public import PaperVerification.FermionUniformMomentGrading
public import PaperVerification.FermionCoinvariantHilbert
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The full physical Hilbert series of the genuine coinvariant quotients

Polynomial degree and both exterior
color degrees are measured in the original ambient algebra. The comparison
with the moment presentation fixes every ambient representative. The finite
basis is then restricted to those independently defined physical components.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion

open MvPolynomial Exterior
variable {R : Type*} [CommRing R] {n : ℕ}
local instance physicalHilbertOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

/-- The three ordinary degrees of the literal paper monomial. -/
def paperBoxDegree (z : (Finset (Fin n)×Finset (Fin n))×(Fin n→ℕ)) :
    ℕ×(ℕ×ℕ) := (∑ i,z.2 i,(z.1.1.card,z.1.2.card))

theorem physicalOddBidegree_disjSum (T S : Finset (Fin n)) :
    exteriorWordDegree physicalOddBidegree (T.disjSum S)=(T.card,S.card) := by
  simp [exteriorWordDegree,physicalOddBidegree,Finset.sum_disjSum]

theorem boxMonomial_physical_mem (T S : Finset (Fin n)) (e : Fin n→ℕ) :
    boxMonomial (K := R) T S e∈physicalSuperPart (paperBoxDegree ((T,S),e)) := by
  rw [boxMonomial_eq_tensor]
  have hd : Finsupp.weight (fun _ : Fin n ↦ (1 : ℕ))
      (Finsupp.equivFunOnFinite.symm e)=∑ i,e i := by
    simp only [Finsupp.weight_eq_sum,Finsupp.coe_equivFunOnFinite_symm,
      nsmul_eq_mul,Nat.cast_id,mul_one]
  have hp := isWeightedHomogeneous_monomial (R := R)
    (fun _ : Fin n ↦ (1 : ℕ)) (Finsupp.equivFunOnFinite.symm e) (1 : R) hd
  simpa only [physicalSuperPart,paperBoxDegree,physicalOddBidegree_disjSum] using
    polynomialExteriorPart_tmul_word (fun _ : Fin n ↦ 1) physicalOddBidegree
      (monomial (Finsupp.equivFunOnFinite.symm e) (1 : R)) (∑ i,e i) hp (T.disjSum S)

namespace PhysicalHilbert

/-- A faithful encoding of all three degrees as an ordinary polynomial exponent. -/
def exponent (g : ℕ×(ℕ×ℕ)) : Fin 3→₀ℕ :=
  Finsupp.single 0 g.1+Finsupp.single 1 g.2.1+Finsupp.single 2 g.2.2

theorem exponent_injective : Function.Injective exponent := by
  intro g h he
  have h0 := congrArg (fun e : Fin 3→₀ℕ ↦ e 0) he
  have h1 := congrArg (fun e : Fin 3→₀ℕ ↦ e 1) he
  have h2 := congrArg (fun e : Fin 3→₀ℕ ↦ e 2) he
  simp only [exponent,Finsupp.add_apply,Finsupp.single_apply] at h0 h1 h2
  norm_num at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- Finite generating polynomial of an honestly graded basis index. -/
def polynomial {I : Type*} [Fintype I] (degree : I→ℕ×(ℕ×ℕ)) :
    MvPolynomial (Fin 3) ℕ := ∑ i,monomial (exponent (degree i)) 1

theorem coefficient {I : Type*} [Fintype I] (degree : I→ℕ×(ℕ×ℕ))
    (g : ℕ×(ℕ×ℕ)) :
    (polynomial degree).coeff (exponent g)=Fintype.card {i // degree i=g} := by
  rw [polynomial,MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial,exponent_injective.eq_iff]
  simp only [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter,eq_comm]

theorem monomial_eq (g : ℕ×(ℕ×ℕ)) :
    (monomial (exponent g) 1 : MvPolynomial (Fin 3) ℕ)=
      X 0^g.1*X 1^g.2.1*X 2^g.2.2 := by
  simp only [X_pow_eq_monomial,monomial_mul,one_mul,exponent]

theorem polynomial_eq {I : Type*} [Fintype I] (degree : I→ℕ×(ℕ×ℕ)) :
    polynomial degree=∑ i,(X 0 : MvPolynomial (Fin 3) ℕ)^(degree i).1*
      X 1^(degree i).2.1*X 2^(degree i).2.2 := by
  simp only [polynomial,monomial_eq]

end PhysicalHilbert

namespace Coinvariants

variable {r a : ℕ}

/-- Physical three-degree in the independently defined positive-invariant quotient. -/
def coinvariantPhysicalPiece (a b : ℕ) (g : ℕ×(ℕ×ℕ)) :
    Submodule R (CoinvariantAlgebra (R := R) (n := n) (r := r) a b) :=
  (physicalSuperPart g).map
    ((positiveInvariantIdeal (R := R) (n := n) (r := r) a b).ringCon.mkₐ R).toLinearMap

/-- Equality of actual defining ideals transports the ambient-image grading,
without redefining any degree piece through a quotient basis. -/
def physicalQuotientGradingOfIdealEq {I J : TwoSidedIdeal (SuperRing R n)}
    (h : I=J)
    (hJ : GradedAlgebra (R := R) (A := J.ringCon.Quotient) (fun g : ℕ×(ℕ×ℕ) ↦
      (physicalSuperPart g).map (J.ringCon.mkₐ R).toLinearMap)) :
    GradedAlgebra (R := R) (A := I.ringCon.Quotient) (fun g : ℕ×(ℕ×ℕ) ↦
      (physicalSuperPart g).map (I.ringCon.mkₐ R).toLinearMap) := by
  cases h
  exact hJ

section Field
variable {F : Type*} [Field F]

/-- The original opposite-character quotient has the genuine polynomial
and two exterior gradings on the independently defined ambient images. -/
def oppositeCoinvariantPhysicalGrading (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    GradedAlgebra (R := F) (A := CoinvariantAlgebra (R := F) (n := n) (r := r) a (r-a))
      (coinvariantPhysicalPiece (R := F) (n := n) (r := r) a (r-a)) :=
  physicalQuotientGradingOfIdealEq (R := F) (positiveInvariantIdeal_eq_paired hr ha har hfac ζ hζ)
    (uniformPairedPhysicalGrading (fun _ : Fin n ↦ (1 : F)) r a (r-a))

/-- The same physical grading for trivial exterior characters. -/
def trivialColorCoinvariantPhysicalGrading (hr : 0<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) :
    GradedAlgebra (R := F) (A := CoinvariantAlgebra (R := F) (n := n) (r := r) 0 0)
      (coinvariantPhysicalPiece (R := F) (n := n) (r := r) 0 0) :=
  physicalQuotientGradingOfIdealEq (R := F) (positiveInvariantIdeal_eq_strict hr hfac ζ hζ)
    (uniformStrictPhysicalGrading (fun _ : Fin n ↦ (1 : F)) r)

def oppositePhysicalPieceEquiv (hn : 0<n) (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (g : ℕ×(ℕ×ℕ)) :
    coinvariantPhysicalPiece (R := F) (n := n) (r := r) a (r-a) g ≃ₗ[F]
      uniformPairedPhysicalPart (fun _ : Fin n ↦ (1 : F)) r a (r-a) g := by
  simpa only [coinvariantPhysicalPiece,uniformPairedPhysicalPart,gradedImagePart] using
    (quotientImageEquivOfIdealEq (positiveInvariantIdeal_eq_paired hr ha har hfac ζ hζ)
      (physicalSuperPart (R := F) (n := n) g))

theorem oppositeMomentBasis_physical_mem (hn : 0<n) (hr : 0<r) (har : a≤r)
    (hfac : IsUnit (n.factorial : F))
    (z : PairedIndex (oppositePowerData hn hr har hfac)) :
    pairedPaperBasis (oppositePowerData hn hr har hfac) z∈
      uniformPairedPhysicalPart (fun _ : Fin n ↦ (1 : F)) r a (r-a)
        (paperBoxDegree z.val) := by
  rw [pairedPaperBasis_apply]
  change _ ∈ (physicalSuperPart (R := F) (n := n) (paperBoxDegree z.val)).map _
  exact Submodule.mem_map.mpr ⟨boxMonomial z.val.1.1 z.val.1.2 z.val.2,
    boxMonomial_physical_mem _ _ _,rfl⟩

set_option maxHeartbeats 1000000 in
/-- The basis of each original physical degree, with every exponent and
both color supports retained in the index. -/
def oppositePhysicalPieceBasis (hn : 0<n) (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (g : ℕ×(ℕ×ℕ)) :
    Module.Basis {z : PairedIndex (oppositePowerData hn hr har.le hfac) //
      paperBoxDegree z.val=g} F
      (coinvariantPhysicalPiece (R := F) (n := n) (r := r) a (r-a) g) := by
  letI := uniformPairedPhysicalGrading (fun _ : Fin n ↦ (1 : F)) r a (r-a)
  let originalBasis := pairedPaperBasis (oppositePowerData (R := F) hn hr har.le hfac)
  let b := actualMultigradedPieceBasis (R := F)
    (A := PairedQuotient (fun _ : Fin n ↦ (1 : F))
      (fun i ↦ X i^r) (fun i ↦ X i^a) (fun i ↦ X i^(r-a)))
    (I := PairedIndex (oppositePowerData hn hr har.le hfac)) (Γ := ℕ×(ℕ×ℕ))
    (uniformPairedPhysicalPart (fun _ : Fin n ↦ (1 : F)) r a (r-a))
    (by simpa only [oppositePowerData] using originalBasis)
    (fun z : PairedIndex (oppositePowerData hn hr har.le hfac) ↦ paperBoxDegree z.val)
    (oppositeMomentBasis_physical_mem hn hr har.le hfac) g
  let e := oppositePhysicalPieceEquiv hn hr ha har hfac ζ hζ g
  let transported := b.map e.symm
  exact transported

/-- All coefficients of the full three-graded Hilbert series, for the
actual wreath-product invariant quotient and the full stated field range. -/
theorem oppositeCoinvariant_physical_hilbert_coefficient
    (hn : 0<n) (hr : 0<r) (ha : 0<a) (har : a<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (g : ℕ×(ℕ×ℕ)) :
    Module.finrank F
      (coinvariantPhysicalPiece (R := F) (n := n) (r := r) a (r-a) g)=
      (PhysicalHilbert.polynomial (fun z : PairedIndex
        (oppositePowerData hn hr har.le hfac) ↦ paperBoxDegree z.val)).coeff
          (PhysicalHilbert.exponent g) := by
  rw [Module.finrank_eq_card_basis (oppositePhysicalPieceBasis hn hr ha har hfac ζ hζ g),
    PhysicalHilbert.coefficient]

def trivialColorPhysicalPieceEquiv (hn : 0<n) (hr : 0<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (g : ℕ×(ℕ×ℕ)) :
    coinvariantPhysicalPiece (R := F) (n := n) (r := r) 0 0 g ≃ₗ[F]
      uniformStrictPhysicalPart (fun _ : Fin n ↦ (1 : F)) r g := by
  simpa only [coinvariantPhysicalPiece,uniformStrictPhysicalPart,gradedImagePart] using
    (quotientImageEquivOfIdealEq (positiveInvariantIdeal_eq_strict hr hfac ζ hζ)
      (physicalSuperPart (R := F) (n := n) g))

theorem trivialMomentBasis_physical_mem (hn : 0<n) (hr : 0<r)
    (hfac : IsUnit (n.factorial : F))
    (z : StrictIndex (trivialColorPowerData hn hr hfac)) :
    strictPaperBasis (trivialColorPowerData hn hr hfac) z∈
      uniformStrictPhysicalPart (fun _ : Fin n ↦ (1 : F)) r (paperBoxDegree z.val) := by
  rw [strictPaperBasis_apply]
  change _ ∈ (physicalSuperPart (R := F) (n := n) (paperBoxDegree z.val)).map _
  exact Submodule.mem_map.mpr ⟨boxMonomial z.val.1.1 z.val.1.2 z.val.2,
    boxMonomial_physical_mem _ _ _,rfl⟩

set_option maxHeartbeats 1000000 in
def trivialColorPhysicalPieceBasis (hn : 0<n) (hr : 0<r)
    (hfac : IsUnit (n.factorial : F)) (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r)
    (g : ℕ×(ℕ×ℕ)) :
    Module.Basis {z : StrictIndex (trivialColorPowerData hn hr hfac) //
      paperBoxDegree z.val=g} F
      (coinvariantPhysicalPiece (R := F) (n := n) (r := r) 0 0 g) := by
  letI := uniformStrictPhysicalGrading (fun _ : Fin n ↦ (1 : F)) r
  let originalBasis := strictPaperBasis (trivialColorPowerData (R := F) hn hr hfac)
  let b := actualMultigradedPieceBasis (R := F)
    (A := StrictQuotient (fun _ : Fin n ↦ (1 : F)) (fun i ↦ X i^r))
    (I := StrictIndex (trivialColorPowerData hn hr hfac)) (Γ := ℕ×(ℕ×ℕ))
    (uniformStrictPhysicalPart (fun _ : Fin n ↦ (1 : F)) r)
    (by simpa only [trivialColorPowerData] using originalBasis)
    (fun z : StrictIndex (trivialColorPowerData hn hr hfac) ↦ paperBoxDegree z.val)
    (trivialMomentBasis_physical_mem hn hr hfac) g
  let e := trivialColorPhysicalPieceEquiv hn hr hfac ζ hζ g
  let transported := b.map e.symm
  exact transported

theorem trivialColorCoinvariant_physical_hilbert_coefficient
    (hn : 0<n) (hr : 0<r) (hfac : IsUnit (n.factorial : F))
    (ζ : Fˣ) (hζ : IsPrimitiveRoot (ζ : F) r) (g : ℕ×(ℕ×ℕ)) :
    Module.finrank F (coinvariantPhysicalPiece (R := F) (n := n) (r := r) 0 0 g)=
      (PhysicalHilbert.polynomial (fun z : StrictIndex
        (trivialColorPowerData hn hr hfac) ↦ paperBoxDegree z.val)).coeff
          (PhysicalHilbert.exponent g) := by
  rw [Module.finrank_eq_card_basis (trivialColorPhysicalPieceBasis hn hr hfac ζ hζ g),
    PhysicalHilbert.coefficient]

end Field

/-- The original type-A quotient is physically graded over arbitrary
commutative base rings in which n! is a unit. -/
def typeACoinvariantPhysicalGrading (hfac : IsUnit (n.factorial : R)) :
    GradedAlgebra (R := R) (A := CoinvariantAlgebra (R := R) (n := n) (r := 1) 0 0)
      (coinvariantPhysicalPiece (R := R) (n := n) (r := 1) 0 0) :=
  physicalQuotientGradingOfIdealEq (R := R)
    ((positiveInvariantIdeal_eq_blockIdeal_typeA hfac).trans
      (blockIdeal_eq_strictIdeal (by decide : 0<1)))
    (uniformStrictPhysicalGrading (fun _ : Fin n ↦ (1 : R)) 1)

/-- The same physical comparison over arbitrary coefficient rings in type A. -/
def typeAPhysicalPieceEquiv (hn : 0<n) (hfac : IsUnit (n.factorial : R))
    (g : ℕ×(ℕ×ℕ)) :
    coinvariantPhysicalPiece (R := R) (n := n) (r := 1) 0 0 g ≃ₗ[R]
      uniformStrictPhysicalPart (fun _ : Fin n ↦ (1 : R)) 1 g := by
  simpa only [coinvariantPhysicalPiece,uniformStrictPhysicalPart,gradedImagePart] using
    (quotientImageEquivOfIdealEq
      ((positiveInvariantIdeal_eq_blockIdeal_typeA hfac).trans
        (blockIdeal_eq_strictIdeal (by decide : 0<1)))
      (physicalSuperPart (R := R) (n := n) g))

def typeAPhysicalPieceBasis (hn : 0<n) (hfac : IsUnit (n.factorial : R))
    (g : ℕ×(ℕ×ℕ)) :
    Module.Basis {z : StrictIndex (trivialColorPowerData hn (by decide : 0<1) hfac) //
      paperBoxDegree z.val=g} R
      (coinvariantPhysicalPiece (R := R) (n := n) (r := 1) 0 0 g) := by
  letI := uniformStrictPhysicalGrading (fun _ : Fin n ↦ (1 : R)) 1
  have hb (z : StrictIndex (trivialColorPowerData hn (by decide : 0<1) hfac)) :
      strictPaperBasis (trivialColorPowerData hn (by decide : 0<1) hfac) z∈
        uniformStrictPhysicalPart (fun _ : Fin n ↦ (1 : R)) 1 (paperBoxDegree z.val) := by
    rw [strictPaperBasis_apply]
    change _ ∈ (physicalSuperPart (R := R) (n := n) (paperBoxDegree z.val)).map _
    exact Submodule.mem_map.mpr ⟨boxMonomial z.val.1.1 z.val.1.2 z.val.2,
      boxMonomial_physical_mem _ _ _,rfl⟩
  exact (actualMultigradedPieceBasis (R := R)
    (A := StrictQuotient (fun _ : Fin n ↦ (1 : R)) (fun i ↦ X i^1))
    (I := StrictIndex (trivialColorPowerData hn (by decide : 0<1) hfac))
    (Γ := ℕ×(ℕ×ℕ))
    (uniformStrictPhysicalPart (fun _ : Fin n ↦ (1 : R)) 1)
    (strictPaperBasis (trivialColorPowerData hn (by decide : 0<1) hfac))
    (fun z : StrictIndex (trivialColorPowerData hn (by decide : 0<1) hfac) ↦
      paperBoxDegree z.val) hb g).map (typeAPhysicalPieceEquiv hn hfac g).symm

end Coinvariants
end PaperVerification.Fermion
