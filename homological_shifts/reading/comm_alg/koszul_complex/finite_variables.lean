import CommAlg.KoszulComplex.Coordinates

/-!
# The genuine polynomial Tor complex for arbitrary finite variable types

An enumeration is used only to construct a regular-sequence resolution.
An explicit linear equivalence then identifies its Koszul complex with the
family indexed by the original variable type. All homology is transported
through actual chain-complex isomorphisms.
-/

noncomputable section

namespace CommAlg.Koszul

open CategoryTheory MvPolynomial

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def finiteVariableList : List (MvPolynomial V k) :=
  List.ofFn (fun i : Fin (Fintype.card V) => X ((Fintype.equivFin V).symm i))

def finiteVariableIndex : Fin (finiteVariableList (V := V) (k := k)).length ≃ V :=
  (finCongr (by simp [finiteVariableList])).trans (Fintype.equivFin V).symm

@[simp] theorem finiteVariableList_get
    (i : Fin (finiteVariableList (V := V) (k := k)).length) :
    (finiteVariableList (V := V) (k := k)).get i =
      X (finiteVariableIndex (V := V) (k := k) i) := by
  exact List.get_ofFn (fun j : Fin (Fintype.card V) =>
    X ((Fintype.equivFin V).symm j)) i

theorem finite_variables_regular [Nontrivial k] :
    RingTheory.Sequence.IsRegular (MvPolynomial V k) (finiteVariableList (V := V) (k := k)) := by
  simpa only [finiteVariableList, List.map_ofFn, Function.comp_def] using
    variables_regular (k := k) (List.ofFn (Fintype.equivFin V).symm)
      (List.nodup_ofFn.mpr (Fintype.equivFin V).symm.injective)

theorem ofList_finite_variables :
    Ideal.ofList (finiteVariableList (V := V) (k := k)) = idealOfVars V k := by
  apply congrArg Ideal.span
  ext f
  simp only [finiteVariableList, List.mem_ofFn, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(Fintype.equivFin V).symm i, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨Fintype.equivFin V v, by simp⟩

abbrev FiniteResidue (V k : Type u) [CommRing k] :=
  MvPolynomial V k ⧸ idealOfVars V k

/-- An actual projective resolution of the coefficient ring, viewed as the
quotient by all polynomial variables. -/
def finitePolynomialResolution [Nontrivial k] :
    ProjectiveResolution (ModuleCat.of (MvPolynomial V k) (FiniteResidue V k)) :=
  transportResolution
    (regularSequenceResolution (finiteVariableList (V := V) (k := k)) finite_variables_regular)
    (Submodule.quotEquivOfEq _ _ (ofList_finite_variables (V := V) (k := k))).toModuleIso

@[simp] theorem finitePolynomialResolution_complex [Nontrivial k] :
    (finitePolynomialResolution (V := V) (k := k)).complex =
      koszulComplex.ofList (finiteVariableList (V := V) (k := k)) := rfl

def finiteVariableLinearEquiv :
    (Fin (finiteVariableList (V := V) (k := k)).length → MvPolynomial V k) ≃ₗ[MvPolynomial V k]
      (V → MvPolynomial V k) :=
  LinearEquiv.funCongrLeft _ _ (finiteVariableIndex (V := V) (k := k)).symm

theorem finiteVariableLinearEquiv_single
    (i : Fin (finiteVariableList (V := V) (k := k)).length) :
    finiteVariableLinearEquiv (Pi.single i (1 : MvPolynomial V k)) =
      Pi.single (finiteVariableIndex (V := V) (k := k) i) (1 : MvPolynomial V k) := by
  funext v
  change (Pi.single (M := fun _ => MvPolynomial V k) i 1)
      ((finiteVariableIndex (V := V) (k := k)).symm v) =
    (Pi.single (M := fun _ => MvPolynomial V k)
      (finiteVariableIndex (V := V) (k := k) i) 1) v
  by_cases h : finiteVariableIndex (V := V) (k := k) i = v
  · subst v
    simp
  · have h' : (finiteVariableIndex (V := V) (k := k)).symm v ≠ i := by
      intro he
      exact h (by rw [← he, Equiv.apply_symm_apply])
    simp [Pi.single_apply, h, h', Ne.symm h']

theorem finiteVariableLinearEquiv_comp :
    (Fintype.linearCombination (MvPolynomial V k) (X : V → MvPolynomial V k)) ∘ₗ
      (finiteVariableLinearEquiv (V := V) (k := k)).toLinearMap =
        Fintype.linearCombination (MvPolynomial V k)
          (finiteVariableList (V := V) (k := k)).get := by
  apply (Pi.basisFun (MvPolynomial V k)
    (Fin (finiteVariableList (V := V) (k := k)).length)).ext
  intro i
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply]
  rw [finiteVariableLinearEquiv_single]
  simpa [Fintype.linearCombination_apply, Pi.single_apply, ite_mul] using
    (finiteVariableList_get (V := V) (k := k) i).symm

/-- The enumerated regular-sequence complex and the original variable-indexed
Koszul complex are genuinely isomorphic. -/
def finiteVariableKoszulIso :
    koszulComplex.ofList (finiteVariableList (V := V) (k := k)) ≅
      koszulComplex (Fintype.linearCombination (MvPolynomial V k) (X : V → MvPolynomial V k)) :=
  koszulComplex.isoOfEquiv _ finiteVariableLinearEquiv _ finiteVariableLinearEquiv_comp

def finiteCoefficientComplexIso (M : ModuleCat.{u} (MvPolynomial V k)) :
    coefficientComplex (finiteVariableList (V := V) (k := k)) M ≅
      familyCoefficientComplex (X : V → MvPolynomial V k) M :=
  (((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat (MvPolynomial V k))).obj M).mapHomologicalComplex
    (ComplexShape.down ℕ)).mapIso finiteVariableKoszulIso

/-- Mathlib's genuine first-factor derived tensor functor with the actual
polynomial residue module, for the original finite variable type. -/
def finitePolynomialTor (i : ℕ) (M : ModuleCat.{u} (MvPolynomial V k)) :
    ModuleCat.{u} (MvPolynomial V k) :=
  ((Tor' (ModuleCat (MvPolynomial V k)) i).obj
    (ModuleCat.of (MvPolynomial V k) (FiniteResidue V k))).obj M

/-- Genuine derived Tor is computed by the original variable-indexed
coefficient Koszul complex, in every degree and for every module. -/
def finitePolynomialTorIso [Nontrivial k] (i : ℕ)
    (M : ModuleCat.{u} (MvPolynomial V k)) :
    finitePolynomialTor i M ≅
      (familyCoefficientComplex (X : V → MvPolynomial V k) M).homology i :=
  (finitePolynomialResolution (V := V) (k := k)).isoLeftDerivedObj
    ((CategoryTheory.MonoidalCategory.tensoringRight _).obj M) i ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat (MvPolynomial V k)) (ComplexShape.down ℕ) i).mapIso
        (finiteCoefficientComplexIso M)

end CommAlg.Koszul
