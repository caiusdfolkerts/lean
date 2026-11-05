module
public import graph_foundation.part012
public import shared_results.part011

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.BigradedPolynomialAlgebra -/
section

/-!
# The actual auxiliary-degree modules of a bigraded polynomial algebra

For the given grading P_(q,m), the module A_(*,m) is the span of its actual
internal-degree submodules. Polynomial stability is derived from the
degree-(1,0) variable hypothesis. Its internal grading is the restriction of
P itself, and its graded Betti numbers use the genuine derived Tor functor.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section

namespace FourPapers.BigradedPolynomialAlgebra

open Classical CommAlg MvPolynomial

universe u
variable {K A V : Type u} [Field K] [CommRing A] [Algebra K A]
  [Fintype V] [LinearOrder V] [Algebra (MvPolynomial V K) A]
  [IsScalarTower K (MvPolynomial V K) A]
  (P : ℤ × ℕ → Submodule K A) [GradedAlgebra P]
  (hX : ∀ v, algebraMap (MvPolynomial V K) A (X v) ∈ P (1,0))

abbrev FullIndex := Σ γ : ℤ × ℕ, Module.Free.ChooseBasisIndex K (P γ)

def fullBasis : Module.Basis (FullIndex P) K A :=
  (DirectSum.Decomposition.isInternal P).collectedBasis
    (fun γ => Module.Free.chooseBasis K (P γ))

theorem fullBasis_mem (a : FullIndex P) : fullBasis P a ∈ P a.1 :=
  (DirectSum.Decomposition.isInternal P).collectedBasis_mem
    (fun γ => Module.Free.chooseBasis K (P γ)) a

theorem fullBasis_piece (γ : ℤ × ℕ) :
    Grading.Piece (fullBasis P) (fun a => a.1) γ=P γ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,rfl⟩
    change a.1 = γ at ha
    rw [← ha]
    exact fullBasis_mem P a
  · intro x hx
    rw [Grading.mem_piece]
    intro a ha
    by_contra hne
    exact ha ((DirectSum.Decomposition.isInternal P).collectedBasis_repr_of_mem_ne
      (fun γ => Module.Free.chooseBasis K (P γ)) (Ne.symm hne) hx)

theorem fullBasis_projection (γ : ℤ × ℕ) :
    Grading.projection (fullBasis P) (fun a => a.1) γ=GradedAlgebra.proj P γ := by
  apply (fullBasis P).ext
  intro a
  rw [Grading.projection_basis,GradedAlgebra.proj_apply]
  by_cases ha : a.1=γ
  · rw [if_pos ha,DirectSum.decompose_of_mem_same P (ha ▸ fullBasis_mem P a)]
  · rw [if_neg ha,DirectSum.decompose_of_mem_ne P (fullBasis_mem P a) ha]

def auxiliaryCoefficientPiece (m : ℕ) : Submodule K A :=
  Submodule.span K {a : A | ∃ q : ℤ,a∈P (q,m)}

include hX in
theorem variable_grade (v : V) (q : ℤ) (m : ℕ) (a : A) (ha : a∈P (q,m)) :
    (X v : MvPolynomial V K) • a ∈ P (q+1,m) := by
  rw [Algebra.smul_def]
  have he := SetLike.mul_mem_graded (hX v) ha
  simpa only [Prod.mk_add_mk,zero_add,add_zero,add_comm] using he

include hX in
theorem auxiliaryCoefficientPiece_X (m : ℕ) (v : V) (a : A)
    (ha : a∈auxiliaryCoefficientPiece P m) :
    (X v : MvPolynomial V K) • a∈auxiliaryCoefficientPiece P m := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨q,hq⟩ := ha
      exact Submodule.subset_span ⟨q+1,variable_grade P hX v q m a hq⟩
  | zero => simpa only [smul_zero] using (auxiliaryCoefficientPiece P m).zero_mem
  | add a b ha hb iha ihb =>
      simpa only [smul_add] using (auxiliaryCoefficientPiece P m).add_mem iha ihb
  | smul c a ha ih =>
      rw [smul_comm]
      exact (auxiliaryCoefficientPiece P m).smul_mem c ih

/-- The actual auxiliary component is a polynomial submodule, with its
usual coefficient multiplication action. -/
def auxiliaryModule (m : ℕ) : Submodule (MvPolynomial V K) A where
  carrier := auxiliaryCoefficientPiece P m
  zero_mem' := (auxiliaryCoefficientPiece P m).zero_mem
  add_mem' := (auxiliaryCoefficientPiece P m).add_mem
  smul_mem' p a ha := by
    induction p using MvPolynomial.induction_on generalizing a with
    | C c =>
        have he : (C c : MvPolynomial V K) • a=c • a := by
          simpa only [MvPolynomial.algebraMap_eq] using algebraMap_smul (MvPolynomial V K) c a
        rw [he]
        exact (auxiliaryCoefficientPiece P m).smul_mem c ha
    | add p q hp hq =>
        rw [add_smul]
        exact (auxiliaryCoefficientPiece P m).add_mem (hp a ha) (hq a ha)
    | mul_X p v hp =>
        rw [mul_smul]
        exact hp _ (auxiliaryCoefficientPiece_X P hX m v a ha)

def auxiliaryCoefficientEquiv (m : ℕ) :
    auxiliaryCoefficientPiece P m ≃ₗ[K] auxiliaryModule P hX m where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem auxiliaryCoefficientPiece_eq_basis (m : ℕ) :
    auxiliaryCoefficientPiece P m=Grading.Piece (fullBasis P) (fun a => a.1.2) m := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨q,hq⟩
    change x ∈ Grading.Piece (fullBasis P) (fun a => a.1.2) m
    rw [Grading.mem_piece]
    intro a ha
    by_contra hne
    apply ha
    exact (DirectSum.Decomposition.isInternal P).collectedBasis_repr_of_mem_ne
      (fun γ => Module.Free.chooseBasis K (P γ))
      (fun he => hne (congrArg Prod.snd he).symm) hq
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,rfl⟩
    change a.1.2 = m at ha
    apply Submodule.subset_span
    refine ⟨a.1.1, ?_⟩
    rw [← ha]
    exact fullBasis_mem P a

abbrev AuxiliaryIndex (m : ℕ) := {a : FullIndex P // a.1.2=m}

def auxiliaryBasis (m : ℕ) : Module.Basis (AuxiliaryIndex P m) K (auxiliaryModule P hX m) :=
  (Grading.restrictedBasis (fullBasis P) (fun a => a.1.2=m)).map
    ((LinearEquiv.ofEq _ _ (auxiliaryCoefficientPiece_eq_basis P m).symm).trans
      (auxiliaryCoefficientEquiv P hX m))

@[simp] theorem auxiliaryBasis_val (m : ℕ) (a : AuxiliaryIndex P m) :
    (auxiliaryBasis P hX m a).val=fullBasis P a.val := by
  change (Grading.restrictedBasis (fullBasis P) (fun a => a.1.2=m) a).val=_
  exact Grading.restrictedBasis_val _ _ _

theorem auxiliaryBasis_repr (m : ℕ) (x : auxiliaryModule P hX m) (a : AuxiliaryIndex P m) :
    (auxiliaryBasis P hX m).repr x a=(fullBasis P).repr x.val a.val := by
  let y : Grading.Piece (fullBasis P) (fun a => a.1.2) m := ⟨x.val,by
    rw [← auxiliaryCoefficientPiece_eq_basis]
    exact x.property⟩
  change (Grading.restrictedBasis (fullBasis P) (fun a => a.1.2=m)).repr
    y a=_
  exact restrictedBasis_repr (fullBasis P) (fun a => a.1.2=m) y a

/-- The internal grading is the restriction of the original P_(q,m). -/
def auxiliaryGrading (m : ℕ) (q : ℤ) : Submodule K (auxiliaryModule P hX m) :=
  (P (q,m)).comap ((auxiliaryModule P hX m).subtype.restrictScalars K)

theorem auxiliaryGrading_eq_basis (m : ℕ) (q : ℤ) :
    Grading.Piece (auxiliaryBasis P hX m) (fun a => a.val.1.1) q=
      auxiliaryGrading P hX m q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,rfl⟩
    change (auxiliaryBasis P hX m a).val∈P (q,m)
    rw [auxiliaryBasis_val]
    change a.val.1.1 = q at ha
    have hm := fullBasis_mem P a.val
    have hg : a.val.1=(q,m) := Prod.ext ha a.property
    simpa only [hg] using hm
  · intro x hx
    rw [Grading.mem_piece]
    intro a ha
    rw [auxiliaryBasis_repr] at ha
    by_contra hne
    apply ha
    exact (DirectSum.Decomposition.isInternal P).collectedBasis_repr_of_mem_ne
      (fun γ => Module.Free.chooseBasis K (P γ))
      (fun he => hne (congrArg Prod.fst he).symm) hx

instance auxiliaryGrading_decomposition (m : ℕ) :
    DirectSum.Decomposition (auxiliaryGrading P hX m) := by
  have he : Grading.Piece (auxiliaryBasis P hX m) (fun a => a.val.1.1)=
      auxiliaryGrading P hX m := funext (auxiliaryGrading_eq_basis P hX m)
  rw [← he]
  exact basisGradingDecomposition (auxiliaryBasis P hX m) (fun a => a.val.1.1)

theorem auxiliaryGrading_X (m : ℕ) (v : V) (q : ℤ) (a : auxiliaryModule P hX m)
    (ha : a∈auxiliaryGrading P hX m q) :
    (X v : MvPolynomial V K) • a∈auxiliaryGrading P hX m (q+1) :=
  variable_grade P hX v q m a.val ha

def auxiliaryGradingInclusion (m : ℕ) (q : ℤ) :
    auxiliaryGrading P hX m q →ₗ[K] P (q,m) where
  toFun x := ⟨x.val.val,x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem auxiliaryGrading_finite [∀ γ,Module.Finite K (P γ)] (m : ℕ) (q : ℤ) :
    Module.Finite K (auxiliaryGrading P hX m q) :=
  Module.Finite.of_injective (auxiliaryGradingInclusion P hX m q)
    (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : P (q,m) => z.val) h)))

/-- This is β^S_(p,q)(A_(*,m)), with the actual polynomial module and the
actual degree-q submodule of Mathlib's derived Tor. -/
def bettiNumber (m p : ℕ) (q : ℤ) : ℕ :=
  GradedPolynomialModuleTor.bettiNumber (auxiliaryGrading P hX m)
    (auxiliaryGrading_X P hX m) p q

end FourPapers.BigradedPolynomialAlgebra

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteSymbolicPowers -/
section

/-!
# Literal symbolic powers in the finite-row polynomial presentation

The symbolic powers are the localization-and-contraction ideals at the
actual minimal primes. Their transport along the explicit variable
bijection is proved here; no independent copy of a symbolic-power predicate
is substituted for those ideals.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Localization membership for the symbolic power of an arbitrary ideal.
Unlike the prime-power characterization, this keeps `J^s` in the numerator
and needs no radicality hypothesis. -/
theorem mem_symbolicPower_localization_iff (J : Ideal R) (s : ℕ) (f : R) :
    f ∈ symbolicPower J s ↔
      ∀ P ∈ J.minimalPrimes, ∃ g ∉ P, g*f ∈ J^s := by
  unfold symbolicPower
  simp only [Submodule.mem_iInf]
  constructor
  · intro hf P hP
    letI : P.IsPrime := hP.isPrime
    have h := hf ⟨P,hP⟩
    change f ∈ ((J^s).map (algebraMap R (Localization.AtPrime P))).comap
      (algebraMap R (Localization.AtPrime P)) at h
    rw [Ideal.mem_comap, IsLocalization.algebraMap_mem_map_algebraMap_iff
      P.primeCompl (Localization.AtPrime P)] at h
    exact h
  · intro hf P
    letI : P.val.IsPrime := P.property.isPrime
    change f ∈ ((J^s).map (algebraMap R (Localization.AtPrime P.val))).comap
      (algebraMap R (Localization.AtPrime P.val))
    rw [Ideal.mem_comap, IsLocalization.algebraMap_mem_map_algebraMap_iff
      P.val.primeCompl (Localization.AtPrime P.val)]
    exact hf P.val P.property

/-- A ring isomorphism transports the complete set of actual minimal
primes, including the empty set for the unit ideal. -/
theorem minimalPrimes_map_ringEquiv (e : R ≃+* S) (J : Ideal R) :
    (J.map e.toRingHom).minimalPrimes = Ideal.map e.toRingHom '' J.minimalPrimes := by
  rw [Ideal.minimalPrimes_map_of_surjective e.surjective,
    (RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective, sup_bot_eq]

/-- Symbolic powers commute with an actual ring isomorphism. -/
theorem symbolicPower_map_ringEquiv (e : R ≃+* S) (J : Ideal R) (s : ℕ) :
    (symbolicPower J s).map e.toRingHom = symbolicPower (J.map e.toRingHom) s := by
  ext y
  obtain ⟨x,rfl⟩ := e.surjective y
  have hm : e x ∈ Ideal.map e.toRingHom (symbolicPower J s) ↔
      x ∈ symbolicPower J s := Ideal.apply_mem_of_equiv_iff (f := e)
  rw [hm, mem_symbolicPower_localization_iff,
    mem_symbolicPower_localization_iff]
  constructor
  · intro hx Q hQ
    rw [minimalPrimes_map_ringEquiv] at hQ
    obtain ⟨P,hP,rfl⟩ := hQ
    obtain ⟨g,hg,hgf⟩ := hx P hP
    refine ⟨e g, ?_, ?_⟩
    · intro h
      exact hg (Ideal.apply_mem_of_equiv_iff.mp h)
    · rw [← map_mul, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem e.toRingHom hgf
  · intro hx P hP
    have hP' : P.map e.toRingHom ∈ (J.map e.toRingHom).minimalPrimes := by
      rw [minimalPrimes_map_ringEquiv]
      exact ⟨P,hP,rfl⟩
    obtain ⟨g,hg,hgf⟩ := hx (P.map e.toRingHom) hP'
    refine ⟨e.symm g, ?_, ?_⟩
    · intro h
      apply hg
      have hmap : e (e.symm g) ∈ Ideal.map e.toRingHom P :=
        Ideal.mem_map_of_mem e.toRingHom h
      simpa only [e.apply_symm_apply] using hmap
    · apply (Ideal.apply_mem_of_equiv_iff (f := e)).mp
      rw [map_mul, e.apply_symm_apply, Ideal.map_pow]
      exact hgf

end FourPapers

namespace FourPapers.Sublattice

open Classical MvPolynomial
open scoped MonomialOrder

universe u v
variable {d : ℕ} (n : Fin d → ℕ) {K : Type v} [Field K]

private theorem finite_initial_rename
    (m : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
    (E : Finset (FiniteTuple n))
    (hinit : initialIdeal m J = finiteSublatticeIdeal n E) :
    initialIdeal (monomialOrderReindex (finiteVariableEquiv n).symm m)
      (J.map (finiteLabelPolynomialEquiv (K := K) n).toRingHom) =
        RowCutNetwork.monomialIdeal n K E := by
  let m' := monomialOrderReindex (finiteVariableEquiv n).symm m
  have hm : ∀ a b : FiniteVariable.{u} n →₀ ℕ,
      a ≼[m] b ↔ a.mapDomain (finiteVariableEquiv n) ≼[m']
        b.mapDomain (finiteVariableEquiv n) := by
    intro a b
    simp only [m', monomialOrderReindex_symm_toSyn]
  change initialIdeal m'
    (Ideal.map (MvPolynomial.rename (finiteVariableEquiv n)).toRingHom J) = _
  rw [← initialIdeal_rename (finiteVariableEquiv n) m m' hm J, hinit]
  exact finiteSublatticeIdeal_rename n E

/-- Radicality is transported from the actual squarefree sublattice initial
ideal, with no extra radicality hypothesis on the deformed ideal. -/
theorem finite_radical_of_sublattice_initial
    (m : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
    (E : Finset (FiniteTuple n))
    (hinit : initialIdeal m J = finiteSublatticeIdeal n E) : J.IsRadical := by
  let e := finiteLabelPolynomialEquiv (K := K) n
  have h := RowCutNetwork.radical_of_sublattice_initial n
    (monomialOrderReindex (finiteVariableEquiv n).symm m)
    (J.map e.toRingHom) E (finite_initial_rename n m J E hinit)
  have hc := h.comap (f := e.toRingHom)
  rw [Ideal.comap_map_of_bijective e.toRingHom e.bijective] at hc
  exact hc

/-- Every ordinary power equals the literal symbolic power at all actual
minimal primes, in exactly the variable presentation used by the Koszul
and graded Tor comparison. -/
theorem finite_symbolicPower_eq_power
    (m : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : initialIdeal m J = finiteSublatticeIdeal n E) (s : ℕ) :
    symbolicPower J s = J^s := by
  let e := finiteLabelPolynomialEquiv (K := K) n
  have hs := RowCutNetwork.symbolicPower_eq_power n
    (monomialOrderReindex (finiteVariableEquiv n).symm m)
    (J.map e.toRingHom) E hE.1 hE.2 (finite_initial_rename n m J E hinit) s
  apply e.toRingEquiv.idealComapOrderIso.symm.injective
  change (symbolicPower J s).map e.toRingHom = (J^s).map e.toRingHom
  rw [symbolicPower_map_ringEquiv e.toRingEquiv, Ideal.map_pow]
  exact hs

/-- The minimal-prime-power convention agrees as well, since the ideal has
been proved radical from its original initial ideal. -/
theorem finite_radicalSymbolicPower_eq_power
    (m : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : initialIdeal m J = finiteSublatticeIdeal n E) (s : ℕ) :
    radicalSymbolicPower J s = J^s := by
  rw [← symbolicPower_eq_radicalSymbolicPower J
    (finite_radical_of_sublattice_initial n m J E hinit)]
  exact finite_symbolicPower_eq_power n m J E hE hinit s

/-- All ideal identities in Theorem 4.3, before the separate homological
comparison, with the original arbitrary monomial order retained. -/
theorem finite_theorem43_ideal_identities
    (m : MonomialOrder (FiniteVariable.{u} n))
    (J : Ideal (MvPolynomial (FiniteVariable.{u} n) K))
    (E : Finset (FiniteTuple n)) (hE : finiteLatticeClosed n E)
    (hinit : initialIdeal m J = finiteSublatticeIdeal n E) (s : ℕ) :
    symbolicPower J s = J^s ∧
      radicalSymbolicPower J s = J^s ∧
      initialIdeal m (symbolicPower J s) = (finiteSublatticeIdeal n E)^s ∧
      initialIdeal m (J^s) = (finiteSublatticeIdeal n E)^s := by
  have hs := finite_symbolicPower_eq_power n m J E hE hinit s
  have hr := finite_radicalSymbolicPower_eq_power n m J E hE hinit s
  have hi := finite_initialIdeal_power_eq n m J E hE hinit s
  exact ⟨hs,hr,by rw [hs]; exact hi,hi⟩

end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIntegralContraction -/
section

/-!
# A graded integral contraction of the actual ideal Koszul complex

The input freeness concerns the literal ordinary-strand kernel/image
quotients. It is used only to split those genuine complexes. The resulting
source is identified by a bijection of actual bases with `J ⊗ exterior`.
The homotopy preserves ordinary internal degree and raises exterior degree.
This supplies the graded contraction used in the integral resolution.
-/

section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] ordinaryPieceAddCommGroup ordinaryPieceModule

open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial DirectSum
open HomologicalPerturbation
open scoped TensorProduct

def contractionByBasisEquiv
    {R M H N I J : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
    [AddCommGroup N] [Module R N]
    (C : LinearContraction (R := R) (M := M) (H := H))
    (b : Module.Basis I R M) (c : Module.Basis J R N) (e : I ≃ J) :
    LinearContraction (R := R) (M := N) (H := H) :=
  C.changeSource (b.equiv c e)

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k] [Nontrivial k]
  (P : QuotientGroebnerData V k)
  (hJ : P.ideal.IsHomogeneous (weightedHomogeneousSubmodule k (fun _ : V => (1 : ℕ))))

theorem actualIdealOrdinarySquare (q p : ℕ) :
    (actualIdealOrdinaryDifferential P hJ q p).comp
      (actualIdealOrdinaryDifferential P hJ q (p+1)) = 0 :=
  actualIdealOrdinaryDifferential_comp P hJ q (p+1)

def actualIdealSplittingHomologyEquiv (q p : ℕ) :
    ProjectiveComplexSplitting.Homology (fun p => ↥(actualIdealOrdinaryPiece P q p))
      (actualIdealOrdinaryDifferential P hJ q) (actualIdealOrdinarySquare P hJ q) p ≃ₗ[k]
        actualIdealOrdinaryHomology P hJ q p :=
  ProjectiveComplexSplitting.splittingHomologyEquiv
    (fun p => ↥(actualIdealOrdinaryPiece P q p)) (actualIdealOrdinaryDifferential P hJ q)
    (actualIdealOrdinarySquare P hJ q) p

theorem actualIdealOrdinaryTerm_projective (q p : ℕ) :
    Module.Projective k (actualIdealOrdinaryPiece P q p) := by
  letI := actualIdealOrdinaryPiece_free P q p
  infer_instance

variable (hfree : ∀ q p, Module.Free k (actualIdealOrdinaryHomology P hJ q p))

include hfree in
theorem actualIdealSplittingHomology_projective (q p : ℕ) :
    Module.Projective k (ProjectiveComplexSplitting.Homology (fun p => ↥(actualIdealOrdinaryPiece P q p))
      (actualIdealOrdinaryDifferential P hJ q) (actualIdealOrdinarySquare P hJ q) p) := by
  letI := hfree q p
  letI := Module.Free.of_equiv (actualIdealSplittingHomologyEquiv P hJ q p).symm
  infer_instance

abbrev IdealGradedTotal := ⨁ q, ⨁ p, actualIdealOrdinaryPiece P q p
abbrev IdealGradedHomology := ⨁ q, ⨁ p, actualIdealOrdinaryHomology P hJ q p

/-- Use the literal quotient group structure transparently when assembling
the direct sum. This avoids introducing a second opaque instance wrapper. -/
abbrev actualIdealOrdinaryHomologyAddCommGroup (q p : ℕ) :
    AddCommGroup (actualIdealOrdinaryHomology P hJ q p) :=
  Submodule.Quotient.addCommGroup (R := k)
    (M := ↥(LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p)))
    (LinearMap.range (FilteredHomology.boundaryMap
      (actualIdealOrdinaryDifferential P hJ q p) (actualIdealOrdinaryPrevious P hJ q p)
      (actualIdealOrdinaryDifferential_comp P hJ q p)))

abbrev actualIdealOrdinaryHomologyModule (q p : ℕ) :
    Module k (actualIdealOrdinaryHomology P hJ q p) :=
  Submodule.Quotient.module (R := k)
    (M := ↥(LinearMap.ker (actualIdealOrdinaryPrevious P hJ q p)))
    (LinearMap.range (FilteredHomology.boundaryMap
      (actualIdealOrdinaryDifferential P hJ q p) (actualIdealOrdinaryPrevious P hJ q p)
      (actualIdealOrdinaryDifferential_comp P hJ q p)))

attribute [instance 100] actualIdealOrdinaryHomologyAddCommGroup
  actualIdealOrdinaryHomologyModule

def actualIdealStrandContraction (q : ℕ) :
    LinearContraction (R := k) (M := ⨁ p, actualIdealOrdinaryPiece P q p)
      (H := ⨁ p, actualIdealOrdinaryHomology P hJ q p) :=
  (ProjectiveComplexSplitting.totalLinearContraction
    (fun p => ↥(actualIdealOrdinaryPiece P q p)) (actualIdealOrdinaryDifferential P hJ q)
    (actualIdealOrdinarySquare P hJ q) (actualIdealOrdinaryTerm_projective P q)
    (actualIdealSplittingHomology_projective P hJ hfree q)).changeTarget
      (DirectSum.congrLinearEquiv (actualIdealSplittingHomologyEquiv P hJ q))

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
def actualIdealGradedContraction :
    LinearContraction (R := k) (M := IdealGradedTotal P) (H := IdealGradedHomology P hJ) :=
  LinearContraction.directSum (R := k) (I := ℕ)
    (M := fun q => ⨁ p, actualIdealOrdinaryPiece P q p)
    (H := fun q => ⨁ p, actualIdealOrdinaryHomology P hJ q p)
    (actualIdealStrandContraction P hJ hfree)

abbrev IdealTensorIndex := NonstandardIndex P.order P.ideal × Finset V
abbrev IdealGradedIndex := Σ q : ℕ, Σ p : ℕ,
  {a : ActualIdealIndex P p // (actualIdealDegree a).degree = q}

def idealGradedIndexEquiv : IdealGradedIndex P ≃ IdealTensorIndex P where
  toFun a := (a.2.2.val.2, a.2.2.val.1.val)
  invFun a := ⟨(a.1.val + faceExponent a.2).degree, a.2.card,
    ⟨⟨⟨a.2,rfl⟩,a.1⟩,rfl⟩⟩
  left_inv a := by
    rcases a with ⟨q,p,⟨⟨F,a⟩,ha⟩⟩
    rcases F with ⟨F,hF⟩
    subst p
    subst q
    rfl
  right_inv a := rfl

def idealGradedBasis : Module.Basis (IdealGradedIndex P) k (IdealGradedTotal P) :=
  FourPapers.nestedDirectSumBasis (R := k)
    (H := fun q p => ↥(actualIdealOrdinaryPiece P q p))
    (T := fun q p => {a : ActualIdealIndex P p // (actualIdealDegree a).degree = q})
    (actualIdealOrdinaryBasis P)

def idealTensorBasis : Module.Basis (IdealTensorIndex P) k
    (TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal)) :=
  (groebnerIdealBasis P.order P.ideal P.generators P.groebner P.unitLeading).tensorProduct
    Simplicial.basis

def idealGradedTotalEquiv : IdealGradedTotal P ≃ₗ[k]
    TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal) :=
  (idealGradedBasis P).equiv (idealTensorBasis P) (idealGradedIndexEquiv P)

@[simp] theorem idealGradedBasis_apply (q p : ℕ)
    (a : {a : ActualIdealIndex P p // (actualIdealDegree a).degree = q}) :
    idealGradedBasis P ⟨q,p,a⟩ =
      DirectSum.lof k ℕ (fun q => ⨁ p, actualIdealOrdinaryPiece P q p) q
        (DirectSum.lof k ℕ (fun p => ↥(actualIdealOrdinaryPiece P q p)) p (actualIdealOrdinaryBasis P q p a)) :=
  FourPapers.nestedDirectSumBasis_apply (R := k)
    (H := fun q p => ↥(actualIdealOrdinaryPiece P q p))
    (T := fun q p => {a : ActualIdealIndex P p // (actualIdealDegree a).degree = q})
    (actualIdealOrdinaryBasis P) ⟨q,p,a⟩

/-- On each original homogeneous chain vector, the equivalence is exactly
the standard tensor-exterior coordinate inclusion. -/
theorem idealGradedTotalEquiv_lof (q p : ℕ) (x : actualIdealOrdinaryPiece P q p) :
    idealGradedTotalEquiv P
      (DirectSum.lof k ℕ (fun q => ⨁ p, actualIdealOrdinaryPiece P q p) q
        (DirectSum.lof k ℕ (fun p => ↥(actualIdealOrdinaryPiece P q p)) p x)) =
      TensorExteriorKoszul.lift (K := k) p x.val := by
  have he : (idealGradedTotalEquiv P).toLinearMap.comp
      ((DirectSum.lof k ℕ (fun q => ⨁ p, actualIdealOrdinaryPiece P q p) q).comp
        (DirectSum.lof k ℕ (fun p => ↥(actualIdealOrdinaryPiece P q p)) p)) =
    (TensorExteriorKoszul.lift (K := k) (M := P.ideal) p).comp
      (actualIdealOrdinaryPiece P q p).subtype := by
    apply (actualIdealOrdinaryBasis P q p).ext
    intro a
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← idealGradedBasis_apply]
    change (idealGradedBasis P).equiv (idealTensorBasis P) (idealGradedIndexEquiv P)
      (idealGradedBasis P ⟨q, p, a⟩) = TensorExteriorKoszul.lift (K := k) p
      (actualIdealOrdinaryBasis P q p a).val
    rw [Module.Basis.equiv_apply, idealTensorBasis, Module.Basis.tensorProduct_apply]
    simp only [actualIdealOrdinaryBasis_val,
      actualIdealCoefficientBasis_apply, TensorExteriorKoszul.lift_single,
      groebnerIdealBasis_apply, idealGradedIndexEquiv]
    rfl
  exact LinearMap.congr_fun he x

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency true in
/-- The contraction now has the literal coefficient-action Koszul module
as source; its target is the actual direct sum of homogeneous homology. -/
def actualIdealTensorContraction :
    LinearContraction (R := k)
      (M := TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
      (H := IdealGradedHomology P hJ) :=
  contractionByBasisEquiv
    (R := k) (M := IdealGradedTotal P) (H := IdealGradedHomology P hJ)
    (N := TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
    (actualIdealGradedContraction P hJ hfree)
    (idealGradedBasis P) (idealTensorBasis P) (idealGradedIndexEquiv P)

private lemma tensorDifferential_lift_zero {R M : Type u} [CommRing R]
    [Algebra k R] [AddCommGroup M] [Module R M] [Module k M]
    [IsScalarTower k R M] (y : V → R) (x : Set.powersetCard V 0 →₀ M) :
    TensorExteriorKoszul.differential (K := k) (M := M) y
      (TensorExteriorKoszul.lift (K := k) 0 x) = 0 := by
  have he : (TensorExteriorKoszul.differential (K := k) (M := M) y).comp
      (TensorExteriorKoszul.lift (K := k) (V := V) (M := M) 0) = 0 := by
    apply Finsupp.lhom_ext
    intro F a
    change TensorExteriorKoszul.differential (K := k) (M := M) y
      (TensorExteriorKoszul.lift (K := k) 0 (Finsupp.single F a)) = 0
    have hF : F.val = ∅ := Finset.card_eq_zero.mp F.property
    rw [TensorExteriorKoszul.lift_single, TensorExteriorKoszul.differential_tmul]
    simp only [hF, Simplicial.contraction_basis, Finset.notMem_empty, if_false,
      TensorProduct.tmul_zero, Finset.sum_const_zero]
  exact LinearMap.congr_fun he x

lemma actualIdealTensorDifferential_lift_zero
    (x : Set.powersetCard V 0 →₀ P.ideal) :
    TensorExteriorKoszul.differential (K := k) (M := P.ideal)
      (X : V → MvPolynomial V k) (TensorExteriorKoszul.lift (K := k) 0 x) = 0 :=
  tensorDifferential_lift_zero (R := MvPolynomial V k) (M := P.ideal) X x

theorem idealGradedTotalEquiv_d (x : IdealGradedTotal P) :
    idealGradedTotalEquiv P ((actualIdealGradedContraction P hJ hfree).d x) =
      TensorExteriorKoszul.differential (K := k) (M := P.ideal)
        (X : V → MvPolynomial V k) (idealGradedTotalEquiv P x) := by
  have he : (idealGradedTotalEquiv P).toLinearMap.comp
      (actualIdealGradedContraction P hJ hfree).d =
    (TensorExteriorKoszul.differential (K := k) (M := P.ideal)
      (X : V → MvPolynomial V k)).comp (idealGradedTotalEquiv P).toLinearMap := by
    apply DirectSum.linearMap_ext
    intro q
    apply DirectSum.linearMap_ext
    intro p
    apply LinearMap.ext
    intro x
    change idealGradedTotalEquiv P ((actualIdealGradedContraction P hJ hfree).d
      (DirectSum.lof k ℕ (fun q => ⨁ p, actualIdealOrdinaryPiece P q p) q
        (DirectSum.lof k ℕ (fun p => ↥(actualIdealOrdinaryPiece P q p)) p x))) =
      TensorExteriorKoszul.differential (K := k) (M := P.ideal)
        (X : V → MvPolynomial V k)
        (idealGradedTotalEquiv P
          (DirectSum.lof k ℕ (fun q => ⨁ p, actualIdealOrdinaryPiece P q p) q
            (DirectSum.lof k ℕ (fun p => ↥(actualIdealOrdinaryPiece P q p)) p x)))
    rw [actualIdealGradedContraction, LinearContraction.directSum_d_lof,
      idealGradedTotalEquiv_lof]
    change idealGradedTotalEquiv P
      (DirectSum.lof k ℕ (fun q => ⨁ p, actualIdealOrdinaryPiece P q p) q
        (ProjectiveComplexSplitting.totalDifferential (fun p => ↥(actualIdealOrdinaryPiece P q p))
          (actualIdealOrdinaryDifferential P hJ q)
          (DirectSum.lof k ℕ (fun p => ↥(actualIdealOrdinaryPiece P q p)) p x))) = _
    cases p with
    | zero =>
        rw [ProjectiveComplexSplitting.totalDifferential_lof_zero, map_zero, map_zero,
          actualIdealTensorDifferential_lift_zero]
    | succ p =>
        rw [ProjectiveComplexSplitting.totalDifferential_lof_succ,
          idealGradedTotalEquiv_lof]
        exact (TensorExteriorKoszul.differential_lift (K := k)
          (X : V → MvPolynomial V k) p x.val).symm
  exact LinearMap.congr_fun he x

/-- The transported differential is the literal coefficient-action Koszul
differential, not only an abstract isomorphic complex. -/
theorem actualIdealTensorContraction_d :
    (actualIdealTensorContraction P hJ hfree).d =
      TensorExteriorKoszul.differential (K := k) (M := P.ideal)
        (X : V → MvPolynomial V k) := by
  apply LinearMap.ext
  intro x
  change idealGradedTotalEquiv P ((actualIdealGradedContraction P hJ hfree).d
    ((idealGradedTotalEquiv P).symm x)) = _
  rw [idealGradedTotalEquiv_d, LinearEquiv.apply_symm_apply]

/-- The chosen homotopy has the required two genuine degrees: its
coefficient is still in ordinary degree `q`, and its exterior degree is `p+1`. -/
theorem actualIdealTensorContraction_h_lift (q p : ℕ)
    (x : actualIdealOrdinaryPiece P q p) :
    (actualIdealTensorContraction P hJ hfree).h
      (TensorExteriorKoszul.lift (K := k) p x.val) =
      TensorExteriorKoszul.lift (K := k) (p+1)
        (ProjectiveComplexSplitting.homotopy (fun p => ↥(actualIdealOrdinaryPiece P q p))
          (actualIdealOrdinaryDifferential P hJ q) (actualIdealOrdinarySquare P hJ q)
          (actualIdealOrdinaryTerm_projective P q)
          (actualIdealSplittingHomology_projective P hJ hfree q) p x).val := by
  rw [← idealGradedTotalEquiv_lof P q p x]
  change idealGradedTotalEquiv P ((actualIdealGradedContraction P hJ hfree).h
    ((idealGradedTotalEquiv P).symm (idealGradedTotalEquiv P _))) = _
  rw [LinearEquiv.symm_apply_apply, actualIdealGradedContraction,
    LinearContraction.directSum_h_lof]
  change idealGradedTotalEquiv P
    (DirectSum.lof k ℕ (fun q => ⨁ p, actualIdealOrdinaryPiece P q p) q
      (ProjectiveComplexSplitting.totalHomotopy (fun p => ↥(actualIdealOrdinaryPiece P q p))
        (actualIdealOrdinaryDifferential P hJ q) (actualIdealOrdinarySquare P hJ q)
        (actualIdealOrdinaryTerm_projective P q)
        (actualIdealSplittingHomology_projective P hJ hfree q)
        (DirectSum.lof k ℕ (fun p => ↥(actualIdealOrdinaryPiece P q p)) p x))) = _
  rw [ProjectiveComplexSplitting.totalHomotopy_lof, idealGradedTotalEquiv_lof]

/- Subsequent degree arguments use the proved map identities above.
Keeping the implementation opaque to elaboration avoids expanding every
projective splitting when a homogeneous submodule is compared. -/
attribute [irreducible] actualIdealTensorContraction idealTensorBasis

private lemma regradeTensorPiece
    {R X I Γ A : Type*} [CommRing R] [AddCommMonoid X] [Module R X]
    (b : Module.Basis I R X) (deg : I → Γ) (a : Γ) (coarse : Γ → A)
    {x : X} (hx : x ∈ Grading.Piece b deg a) :
    x ∈ Grading.Piece b (fun i => coarse (deg i)) (coarse a) := by
  apply Submodule.span_mono (Set.image_mono (fun i hi => ?_)) hx
  exact congrArg coarse hi


def idealTensorOrdinaryDegree (a : IdealTensorIndex P) : ℕ :=
  a.1.val.degree + a.2.card

def idealTensorBidegree (a : IdealTensorIndex P) : ℕ × ℕ :=
  (idealTensorOrdinaryDegree P a, a.2.card)

/-- The tensor coordinate inclusion preserves both genuine degrees. The
coefficient degree is obtained from the polynomial ideal basis and the
exterior degree from the cardinality of its actual face. -/
theorem idealTensor_lift_bidegree (q p : ℕ) (x : actualIdealOrdinaryPiece P q p) :
    TensorExteriorKoszul.lift (K := k) (M := P.ideal) p x.val ∈
      Grading.Piece (idealTensorBasis P) (idealTensorBidegree P) (q,p) := by
  let L := Grading.Piece (idealTensorBasis P) (idealTensorBidegree P) (q,p)
  have hle : actualIdealOrdinaryPiece P q p ≤ L.comap
      (TensorExteriorKoszul.lift (K := k) (M := P.ideal) p) := by
    apply Submodule.span_le.mpr
    rintro z ⟨a, ha, rfl⟩
    have he : TensorExteriorKoszul.lift (K := k) (M := P.ideal) p
        (actualIdealCoefficientBasis P p a) = idealTensorBasis P (a.2,a.1.val) := by
      simp only [actualIdealCoefficientBasis_apply, TensorExteriorKoszul.lift_single,
        idealTensorBasis, Module.Basis.tensorProduct_apply, groebnerIdealBasis_apply]
    change TensorExteriorKoszul.lift (K := k) (M := P.ideal) p
      (actualIdealCoefficientBasis P p a) ∈ L
    rw [he]
    apply Submodule.subset_span
    refine ⟨(a.2,a.1.val), ?_, rfl⟩
    change (actualIdealDegree a).degree = q at ha
    apply Prod.ext
    · simpa only [idealTensorBidegree, idealTensorOrdinaryDegree,
        actualIdealDegree, map_add, degree_faceExponent] using ha
    · exact a.1.property
  exact hle x.property

theorem idealTensor_lift_ordinary (q p : ℕ) (x : actualIdealOrdinaryPiece P q p) :
    TensorExteriorKoszul.lift (K := k) (M := P.ideal) p x.val ∈
      Grading.Piece (idealTensorBasis P) (idealTensorOrdinaryDegree P) q := by
  exact regradeTensorPiece (R := k)
      (X := TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
      (idealTensorBasis P) (idealTensorBidegree P) (q,p) Prod.fst
      (x := TensorExteriorKoszul.lift (K := k) (M := P.ideal) p x.val)
      (idealTensor_lift_bidegree P q p x)

/-- On each actual tensor basis vector, the contraction homotopy preserves
ordinary degree and raises exterior degree by exactly one. -/
theorem actualIdealTensorContraction_h_bidegree (a : IdealTensorIndex P) :
    (actualIdealTensorContraction P hJ hfree).h (idealTensorBasis P a) ∈
      Grading.Piece (idealTensorBasis P) (idealTensorBidegree P)
        (idealTensorOrdinaryDegree P a, a.2.card+1) := by
  let q := idealTensorOrdinaryDegree P a
  let p := a.2.card
  let i : ActualIdealIndex P p := ⟨⟨a.2,rfl⟩,a.1⟩
  have hi : (actualIdealDegree i).degree=q := by
    simp only [i, q, actualIdealDegree, map_add, degree_faceExponent, idealTensorOrdinaryDegree]
  let x : actualIdealOrdinaryPiece P q p := actualIdealOrdinaryBasis P q p ⟨i,hi⟩
  have hx : TensorExteriorKoszul.lift (K := k) (M := P.ideal) p x.val = idealTensorBasis P a := by
    simp only [x, actualIdealOrdinaryBasis_val,
      actualIdealCoefficientBasis_apply, TensorExteriorKoszul.lift_single,
      idealTensorBasis, Module.Basis.tensorProduct_apply', groebnerIdealBasis_apply, i]
  rw [← hx, actualIdealTensorContraction_h_lift]
  exact idealTensor_lift_bidegree P q (p+1) _

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
theorem actualIdealTensorContraction_h_ordinary (a : IdealTensorIndex P) :
    (actualIdealTensorContraction P hJ hfree).h (idealTensorBasis P a) ∈
      Grading.Piece (idealTensorBasis P) (idealTensorOrdinaryDegree P)
        (idealTensorOrdinaryDegree P a) := by
  exact regradeTensorPiece (R := k)
      (X := TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
      (idealTensorBasis P) (idealTensorBidegree P)
      (idealTensorOrdinaryDegree P a, a.2.card+1) Prod.fst
      (x := (actualIdealTensorContraction P hJ hfree).h (idealTensorBasis P a))
      (actualIdealTensorContraction_h_bidegree P hJ hfree a)

/-- This proved coefficient inequality constructs the finite perturbation
inverse; it is not a boundedness hypothesis left in the graph theorem. -/
theorem actualIdealTensorContraction_h_nonincreasing :
    DegreeNonincreasing (R := k)
      (M := TensorExteriorKoszul.Total (K := k) (V := V) (M := P.ideal))
      (idealTensorBasis P) (idealTensorOrdinaryDegree P)
      (actualIdealTensorContraction P hJ hfree).h := by
  intro a b hab
  by_contra hc
  have he := (Grading.mem_piece (idealTensorBasis P) (idealTensorOrdinaryDegree P)
    (idealTensorOrdinaryDegree P a) _).mp
      (actualIdealTensorContraction_h_ordinary P hJ hfree a) b hc
  exact (ne_of_lt hab) he.symm

end FourPapers.Sublattice

end
end
end


end
