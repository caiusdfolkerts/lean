module

public import PaperVerification.FermionMultiplicityInitialAlgebra
public import PaperVerification.FermionBlockNormalForm

/-!
# The literal multiplicity factors and their colon quotients

Creator diagonal products contain only a unit depending on the coloring.
Removing that unit gives the paper's product indexed by multiplicities.
The complete coefficient-quotient basis and the vanishing of inadmissible
blocks are derived from the actual triangular normal form, including words
whose polynomial boxes are empty.

-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.Fermion

open MvPolynomial Exterior
open scoped BigOperators

variable {F : Type*} [Field F] {n : ℕ}

local instance FermionMultiplicityBlocks_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

abbrev MultiplicityVector (n : ℕ) := Fin n → Fin 3

def wordMultiplicityVector (T : Finset (OddIndex n)) : MultiplicityVector n :=
  fun i ↦ ⟨wordMultiplicity T i,by
    classical
    by_cases hθ : Sum.inl i∈T <;> by_cases hξ : Sum.inr i∈T <;>
      simp only [wordMultiplicity,hθ,hξ,if_true,if_false] <;> omega⟩

def multiplicityFactor (φ : Fin n → PolynomialRing F n) (m : MultiplicityVector n) :
    PolynomialRing F n :=
  ∏ i,(φ i*∏ j∈Finset.Ioi i,(φ i-φ j))^(m i).val

theorem creatorWordPolynomial_eq_multiplicityFactor
    (d : StrictData (K := F) (n := n)) (T : Finset (OddIndex n)) :
    creatorWordPolynomial d.creatorData T=
      C (wordBeta d.beta T)*multiplicityFactor d.phi (wordMultiplicityVector T) := by
  classical
  let g (i : Fin n) : PolynomialRing F n := d.phi i*∏ j∈Finset.Ioi i,(d.phi i-d.phi j)
  have hstart : creatorWordPolynomial d.creatorData T=
      ∏ a:OddIndex n,if a∈T then
        prefixCreatorDiagonal d.phi (fun i ↦ C (d.beta i)) d.phi d.phi a else 1 := by
    simp only [creatorWordPolynomial,StrictData.creatorData]
    simp
  rw [hstart,Fintype.prod_sum_type,←Finset.prod_mul_distrib]
  have hrow (i : Fin n) :
      (if Sum.inl i∈T then C (d.beta i)*g i else 1)*
        (if Sum.inr i∈T then g i else 1)=
      C (if Sum.inl i∈T then d.beta i else 1)*(g i)^wordMultiplicity T i := by
    by_cases hθ : Sum.inl i∈T <;> by_cases hξ : Sum.inr i∈T <;>
      simp only [hθ,hξ,if_true,if_false,wordMultiplicity,add_zero,zero_add,
        pow_zero,pow_one,map_one,pow_two] <;> ring
  have hr := congrArg (fun f : Fin n → PolynomialRing F n ↦ ∏ i,f i) (funext hrow)
  simp only [prefixCreatorDiagonal,Finset.filter_lt_eq_Ioi,mul_assoc] at ⊢
  change (∏ i,(if Sum.inl i∈T then C (d.beta i)*g i else 1)*
    (if Sum.inr i∈T then g i else 1))=_
  rw [hr,Finset.prod_mul_distrib,←map_prod]
  refine congrArg₂ (fun x y : PolynomialRing F n ↦ x*y) ?_ ?_
  · apply congrArg C
    unfold wordBeta
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : Sum.inl i∈T <;> simp only [h,if_true,if_false]
  · rfl

theorem principalColon_unit_mul {P : Type*} [CommRing P]
    (J : Ideal P) (u g : P) (hu : IsUnit u) :
    principalColon J (u*g)=principalColon J g := by
  obtain ⟨u,rfl⟩ := hu
  ext p
  rw [mem_principalColon,mem_principalColon]
  constructor
  · intro hp
    have hh := J.mul_mem_left (↑(u⁻¹) : P) hp
    have he : (↑(u⁻¹) : P)*(p*((u : P)*g))=p*g := by
      calc
        (↑(u⁻¹) : P)*(p*((u : P)*g))=
            ((↑(u⁻¹) : P)*(u : P))*(p*g) := by ring
        _=p*g := by simp
    exact he ▸ hh
  · intro hp
    have hh := J.mul_mem_left (u : P) hp
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

theorem creatorColon_eq_multiplicityColon
    (d : StrictData (K := F) (n := n)) (T : Finset (OddIndex n)) :
    principalColon (coupledOrdinaryIdeal d.pairedExtension)
        (creatorWordPolynomial d.creatorData T)=
      principalColon (coupledOrdinaryIdeal d.pairedExtension)
        (multiplicityFactor d.phi (wordMultiplicityVector T)) := by
  rw [creatorWordPolynomial_eq_multiplicityFactor]
  apply principalColon_unit_mul
  apply IsUnit.map C
  exact isUnit_iff_ne_zero.mpr
    (wordBeta_ne_zero d.beta (Newton.singleton_weight_ne_zero d.beta d.allowed_weights.2) T)

/-- All colorings of one multiplicity vector have the same coefficient ideal. -/
theorem strict_multiplicity_initialIdeal_mem_iff_blocks
    (d : StrictData (K := F) (n := n)) (z : SuperRing F n) :
    z∈strictMultiplicityInitialIdeal d ↔
      ∀ T,(superPolynomialBasis (K := F)).repr z T∈
        principalColon (coupledOrdinaryIdeal d.pairedExtension)
          (multiplicityFactor d.phi (wordMultiplicityVector T)) := by
  rw [strict_multiplicity_initialIdeal_mem_iff]
  exact forall_congr' fun T ↦ by rw [creatorColon_eq_multiplicityColon]

def strictCreatorColonBasis (d : StrictData (K := F) (n := n))
    (T : Finset (OddIndex n)) :
    Module.Basis (StrictWordPolynomialIndex d.r T) F
      (PolynomialRing F n ⧸ principalColon (coupledOrdinaryIdeal d.pairedExtension)
        (creatorWordPolynomial d.creatorData T)) := by
  let J := coupledOrdinaryIdeal d.pairedExtension
  let f := creatorWordPolynomial d.creatorData T
  let K : Submodule F (PolynomialRing F n) := (multiplyIntoQuotient (K := F) J f).ker
  let L : Submodule F (PolynomialRing F n) := (principalColon J f).restrictScalars F
  let B : Module.Basis (StrictWordPolynomialIndex d.r T) F
      (PolynomialRing F n ⧸ K) :=
    (strictMultiplicityPresentation d).diagonalQuotientBasis T
  exact B.map ((Submodule.quotEquivOfEq K L (multiplyIntoQuotient_ker (K := F) J f)).trans
    (Submodule.Quotient.restrictScalarsEquiv F (principalColon J f)))

@[simp] theorem strictCreatorColonBasis_apply (d : StrictData (K := F) (n := n))
    (T : Finset (OddIndex n)) (a : StrictWordPolynomialIndex d.r T) :
    strictCreatorColonBasis d T a=
      Ideal.Quotient.mk (principalColon (coupledOrdinaryIdeal d.pairedExtension)
        (creatorWordPolynomial d.creatorData T)) (monomial a.val.val 1) := by
  let J := coupledOrdinaryIdeal d.pairedExtension
  let f := creatorWordPolynomial d.creatorData T
  let K : Submodule F (PolynomialRing F n) := (multiplyIntoQuotient (K := F) J f).ker
  let L : Submodule F (PolynomialRing F n) := (principalColon J f).restrictScalars F
  let e : (PolynomialRing F n ⧸ K) ≃ₗ[F] (PolynomialRing F n ⧸ principalColon J f) :=
    (Submodule.quotEquivOfEq K L (multiplyIntoQuotient_ker (K := F) J f)).trans
      (Submodule.Quotient.restrictScalarsEquiv F (principalColon J f))
  have hb := (strictMultiplicityPresentation d).diagonalQuotientBasis_apply T a
  simp only [strictMultiplicityPresentation_diagonal,strictMultiplicityPresentation_polynomial,
    Submodule.mkQ_apply] at hb
  have he := congrArg e hb
  simp only [e,LinearEquiv.trans_apply,Submodule.quotEquivOfEq_mk] at he
  have hs : (Submodule.Quotient.restrictScalarsEquiv F (principalColon J f))
      (Submodule.Quotient.mk (p := L) (monomial a.val.val (1 : F))) =
      Ideal.Quotient.mk (principalColon J f) (monomial a.val.val (1 : F)) := by
    rfl
  simpa only [strictCreatorColonBasis,Module.Basis.map_apply,LinearEquiv.trans_apply] using
    he.trans hs

def strictMultiplicityColonBasis (d : StrictData (K := F) (n := n))
    (T : Finset (OddIndex n)) :
    Module.Basis (StrictWordPolynomialIndex d.r T) F
      (PolynomialRing F n ⧸ principalColon (coupledOrdinaryIdeal d.pairedExtension)
        (multiplicityFactor d.phi (wordMultiplicityVector T))) :=
  (strictCreatorColonBasis d T).map
    ((Ideal.quotientEquivAlgOfEq F (creatorColon_eq_multiplicityColon d T)).toLinearEquiv)

/-- Inadmissible multiplicity words have zero coefficient quotient. This
includes valid nonnegative paths which reach height zero. -/
theorem strictMultiplicityColon_eq_top_of_not_strict
    (d : StrictData (K := F) (n := n)) (T : Finset (OddIndex n)) (hT : ¬StrictWord T) :
    principalColon (coupledOrdinaryIdeal d.pairedExtension)
      (multiplicityFactor d.phi (wordMultiplicityVector T))=⊤ := by
  haveI : IsEmpty (StrictWordPolynomialIndex d.r T) :=
    ⟨fun a ↦ hT (strictWord_of_polynomialIndex d.r T a)⟩
  let B := strictMultiplicityColonBasis d T
  have hzero : (1 : PolynomialRing F n ⧸ principalColon
      (coupledOrdinaryIdeal d.pairedExtension)
        (multiplicityFactor d.phi (wordMultiplicityVector T)))=0 := by
    apply B.repr.injective
    ext i
    exact isEmptyElim i
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.Quotient.eq_zero_iff_mem.mp hzero) isUnit_one

abbrev MultiplicityColoring (m : MultiplicityVector n) :=
  {T : Finset (OddIndex n) // wordMultiplicityVector T=m}

instance multiplicityColoring_fintype (m : MultiplicityVector n) :
    Fintype (MultiplicityColoring m) := by
  classical
  unfold MultiplicityColoring
  infer_instance

/-- This is the exact regrouping of the full exterior basis into multiplicity
blocks; no colors or zero-height words are discarded. -/
def multiplicityColoringEquiv : Finset (OddIndex n) ≃ Σ m:MultiplicityVector n,MultiplicityColoring m where
  toFun T := ⟨wordMultiplicityVector T,⟨T,rfl⟩⟩
  invFun z := z.2.val
  left_inv T := rfl
  right_inv z := by
    rcases z with ⟨m,T,hT⟩
    subst m
    rfl

end PaperVerification.Fermion
