module

public import PaperVerification.FermionColorAction
public import PaperVerification.FermionBlockColorMaps
public import PaperVerification.FermionTypeAMultiplicity

/-!
# Independent GL(2) actions on the genuine multiplicity initial algebra

Each index has its own color matrix. The action preserves the independently
defined exterior index degree and hence each literal multiplicity block.
The actual coefficient-ideal theorem then proves invariance of the initial
ideal, rather than assuming invariance of a proposed special fiber.

-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Fermion.ColorAction

open Exterior

variable {R : Type*} [CommRing R] {n : ℕ}

local instance FermionIndependentColorAction_localInst_1 : LinearOrder (OddIndex n) :=
  LinearOrder.lift' modeRank modeRank_injective

def indexLinear (A : Fin n → ColorMatrix R) : OddModule R n →ₗ[R] OddModule R n where
  toFun v := Sum.elim
    (fun i ↦ A i 0 0*v (.inl i)+A i 0 1*v (.inr i))
    (fun i ↦ A i 1 0*v (.inl i)+A i 1 1*v (.inr i))
  map_add' v w := by
    funext j
    cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.add_apply] <;> ring
  map_smul' c v := by
    funext j
    cases j <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.smul_apply,
      smul_eq_mul,RingHom.id_apply] <;> ring

@[simp] theorem indexLinear_one :
    indexLinear (fun _ : Fin n ↦ (1 : ColorMatrix R))=LinearMap.id := by
  ext v j
  cases j <;> simp [indexLinear,Matrix.one_apply]

theorem indexLinear_mul (A B : Fin n → ColorMatrix R) :
    indexLinear (fun i ↦ A i*B i)=(indexLinear A).comp (indexLinear B) := by
  ext v j
  cases j <;> simp only [indexLinear,LinearMap.coe_mk,AddHom.coe_mk,
    Sum.elim_inl,Sum.elim_inr,LinearMap.comp_apply,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem indexLinear_theta (A : Fin n → ColorMatrix R) (i : Fin n) :
    indexLinear A (Pi.single (.inl i) 1)=
      A i 0 0 • Pi.single (.inl i) 1+A i 1 0 • Pi.single (.inr i) 1 := by
  funext j
  cases j with
  | inl j =>
      by_cases h : j=i
      · subst j; simp [indexLinear,Pi.single_apply]
      · simp [indexLinear,Pi.single_apply,h,Ne.symm h]
  | inr j =>
      by_cases h : j=i
      · subst j; simp [indexLinear,Pi.single_apply]
      · simp [indexLinear,Pi.single_apply,h,Ne.symm h]

theorem indexLinear_xi (A : Fin n → ColorMatrix R) (i : Fin n) :
    indexLinear A (Pi.single (.inr i) 1)=
      A i 0 1 • Pi.single (.inl i) 1+A i 1 1 • Pi.single (.inr i) 1 := by
  funext j
  cases j with
  | inl j =>
      by_cases h : j=i
      · subst j; simp [indexLinear,Pi.single_apply]
      · simp [indexLinear,Pi.single_apply,h,Ne.symm h]
  | inr j =>
      by_cases h : j=i
      · subst j; simp [indexLinear,Pi.single_apply]
      · simp [indexLinear,Pi.single_apply,h,Ne.symm h]

def indexAmbient (A : Fin n → ColorMatrix R) :
    SuperRing R n →ₐ[PolynomialRing R n] SuperRing R n :=
  Algebra.TensorProduct.map (AlgHom.id (PolynomialRing R n) (PolynomialRing R n))
    (ExteriorAlgebra.map (indexLinear A))

@[simp] theorem indexAmbient_constant (A : ColorMatrix R) :
    indexAmbient (fun _ : Fin n ↦ A)=ambient A := rfl

@[simp] theorem indexAmbient_one :
    indexAmbient (fun _ : Fin n ↦ (1 : ColorMatrix R))=AlgHom.id (PolynomialRing R n) _ := by
  rw [indexAmbient,indexLinear_one,ExteriorAlgebra.map_id,Algebra.TensorProduct.map_id]

theorem indexAmbient_mul (A B : Fin n → ColorMatrix R) :
    indexAmbient (fun i ↦ A i*B i)=(indexAmbient A).comp (indexAmbient B) := by
  simp only [indexAmbient,indexLinear_mul,←ExteriorAlgebra.map_comp_map,
    Algebra.TensorProduct.map_id_comp]

def indexAmbientEquiv (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) R) :
    SuperRing R n ≃ₐ[PolynomialRing R n] SuperRing R n :=
  AlgEquiv.ofAlgHom (indexAmbient (fun i ↦ (g i).val))
    (indexAmbient (fun i ↦ (g i).inv))
    (by
      rw [←indexAmbient_mul]
      simp only [Units.val_inv,indexAmbient_one])
    (by
      rw [←indexAmbient_mul]
      simp only [Units.inv_val,indexAmbient_one])

theorem exterior_indexMap_mem (A : Fin n → ColorMatrix R)
    {r : Fin n → ℕ} {x : ExteriorAlgebra R (OddModule R n)}
    (hx : x∈exteriorWeightedPart indexDegree r) :
    ExteriorAlgebra.map (indexLinear A) x∈exteriorWeightedPart indexDegree r := by
  letI := exteriorWeightedGrading (A := R) (indexDegree (n := n))
  apply exteriorWeighted_map_mem indexDegree (exteriorWeightedPart indexDegree)
    (ExteriorAlgebra.map (indexLinear A)) _ hx
  have htheta (i : Fin n) :
      ExteriorAlgebra.map (indexLinear A) (exteriorGenerator (A := R) (Sum.inl i)) =
        A i 0 0 • exteriorGenerator (Sum.inl i) +
          A i 1 0 • exteriorGenerator (Sum.inr i) := by
    simp only [exteriorGenerator,ExteriorAlgebra.map_apply_ι]
    rw [← map_smul,← map_smul,← map_add]
    apply congrArg (ExteriorAlgebra.ι R)
    funext j
    cases j with
    | inl j =>
        by_cases h : j=i
        · subst j; simp [indexLinear,Pi.single_apply]
        · simp [indexLinear,Pi.single_apply,h,Ne.symm h]
    | inr j =>
        by_cases h : j=i
        · subst j; simp [indexLinear,Pi.single_apply]
        · simp [indexLinear,Pi.single_apply,h,Ne.symm h]
  have hxi (i : Fin n) :
      ExteriorAlgebra.map (indexLinear A) (exteriorGenerator (A := R) (Sum.inr i)) =
        A i 0 1 • exteriorGenerator (Sum.inl i) +
          A i 1 1 • exteriorGenerator (Sum.inr i) := by
    simp only [exteriorGenerator,ExteriorAlgebra.map_apply_ι]
    rw [← map_smul,← map_smul,← map_add]
    apply congrArg (ExteriorAlgebra.ι R)
    funext j
    cases j with
    | inl j =>
        by_cases h : j=i
        · subst j; simp [indexLinear,Pi.single_apply]
        · simp [indexLinear,Pi.single_apply,h,Ne.symm h]
    | inr j =>
        by_cases h : j=i
        · subst j; simp [indexLinear,Pi.single_apply]
        · simp [indexLinear,Pi.single_apply,h,Ne.symm h]
  intro j
  cases j with
  | inl i =>
      rw [htheta]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (exteriorGenerator_weighted_mem indexDegree (.inl i)))
        (Submodule.smul_mem _ _ (exteriorGenerator_weighted_mem indexDegree (.inr i)))
  | inr i =>
      rw [hxi]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (exteriorGenerator_weighted_mem indexDegree (.inl i)))
        (Submodule.smul_mem _ _ (exteriorGenerator_weighted_mem indexDegree (.inr i)))

theorem includeRight_mem_multiplicityPart (T : Finset (OddIndex n))
    {x : ExteriorAlgebra R (OddModule R n)}
    (hx : x∈exteriorWeightedPart indexDegree (exteriorWordDegree indexDegree T)) :
    Algebra.TensorProduct.includeRight (A := PolynomialRing R n) x∈
      basisDegreePart (superPolynomialBasis (K := R)) wordMultiplicityVector
        (wordMultiplicityVector T) := by
  let L := (basisDegreePart (superPolynomialBasis (K := R)) wordMultiplicityVector
    (wordMultiplicityVector T)).restrictScalars R
  change Algebra.TensorProduct.includeRight x∈L
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨S,hS,rfl⟩ := hx
      have hb : superPolynomialBasis (K := R) S ∈
          basisDegreePart (superPolynomialBasis (K := R)) wordMultiplicityVector
            (wordMultiplicityVector T) :=
        Submodule.subset_span ⟨S,wordMultiplicityVector_eq_of_indexDegree_eq hS,rfl⟩
      simpa only [L,Submodule.restrictScalars_mem,superPolynomialBasis_apply,
        Algebra.TensorProduct.includeRight_apply] using hb
  | zero => simpa only [map_zero] using L.zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using L.add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using L.smul_mem c ih

theorem indexAmbient_basis_mem (A : Fin n → ColorMatrix R) (T : Finset (OddIndex n)) :
    indexAmbient A (superPolynomialBasis (K := R) T)∈
      basisDegreePart (superPolynomialBasis (K := R)) wordMultiplicityVector
        (wordMultiplicityVector T) := by
  rw [superPolynomialBasis_apply]
  change (1 : PolynomialRing R n) ⊗ₜ[R]
    ExteriorAlgebra.map (indexLinear A) ((Pi.basisFun R (OddIndex n)).ExteriorAlgebra T)∈_
  exact includeRight_mem_multiplicityPart T
    (exterior_indexMap_mem A (exteriorWeightedPart_basis indexDegree T))

section InitialQuotient
variable {F : Type*} [Field F]

theorem indexAmbient_preserves_initialIdeal (A : Fin n → ColorMatrix F)
    (d : StrictData (K := F) (n := n)) {z : SuperRing F n}
    (hz : z∈strictMultiplicityInitialIdeal d) :
    indexAmbient A z∈strictMultiplicityInitialIdeal d := by
  rw [strict_multiplicity_initialIdeal_mem_iff_blocks] at hz ⊢
  exact map_preserves_coefficientIdeals (superPolynomialBasis (K := F))
    wordMultiplicityVector
    (fun m ↦ principalColon (coupledOrdinaryIdeal d.pairedExtension) (multiplicityFactor d.phi m))
    (indexAmbient A).toLinearMap (indexAmbient_basis_mem A) hz

def initialQuotientEquiv (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
    (d : StrictData (K := F) (n := n)) :
    (strictMultiplicityInitialIdeal d).ringCon.Quotient ≃ₐ[F]
      (strictMultiplicityInitialIdeal d).ringCon.Quotient :=
  twoSidedQuotientEquiv ((indexAmbientEquiv g).restrictScalars F)
    (strictMultiplicityInitialIdeal d) (strictMultiplicityInitialIdeal d)
    (fun _ hz ↦ indexAmbient_preserves_initialIdeal (fun i ↦ (g i).val) d hz)
    (fun _ hz ↦ indexAmbient_preserves_initialIdeal (fun i ↦ (g i).inv) d hz)

@[simp] theorem initialQuotientEquiv_mk
    (g : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
    (d : StrictData (K := F) (n := n)) (z : SuperRing F n) :
    initialQuotientEquiv g d ((strictMultiplicityInitialIdeal d).ringCon.mkₐ F z)=
      (strictMultiplicityInitialIdeal d).ringCon.mkₐ F
        (indexAmbient (fun i ↦ (g i).val) z) := rfl

def initialQuotientAction (d : StrictData (K := F) (n := n)) :
    (Fin n → Matrix.GeneralLinearGroup (Fin 2) F) →*
      ((strictMultiplicityInitialIdeal d).ringCon.Quotient ≃ₐ[F]
        (strictMultiplicityInitialIdeal d).ringCon.Quotient) where
  toFun g := initialQuotientEquiv g d
  map_one' := by
    apply AlgEquiv.ext
    intro z
    obtain ⟨x,rfl⟩ := (strictMultiplicityInitialIdeal d).ringCon.mkₐ_surjective (α := F) z
    change (strictMultiplicityInitialIdeal d).ringCon.mkₐ F
      (indexAmbient (fun _ ↦ (1 : ColorMatrix F)) x)=_
    rw [indexAmbient_one]
    rfl
  map_mul' g h := by
    apply AlgEquiv.ext
    intro z
    obtain ⟨x,rfl⟩ := (strictMultiplicityInitialIdeal d).ringCon.mkₐ_surjective (α := F) z
    simp only [AlgEquiv.mul_apply,initialQuotientEquiv_mk]
    change (strictMultiplicityInitialIdeal d).ringCon.mkₐ F
      (indexAmbient (fun i ↦ (g i).val*(h i).val) x)=_
    rw [indexAmbient_mul]
    rfl

end InitialQuotient
end PaperVerification.Fermion.ColorAction
