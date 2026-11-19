module
public import Mathlib
/-! The roots-and-ramification decomposition of the separated two-fermion quotient. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace PaperVerification.Fermion
section
open Polynomial
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
def moment (x : Fin n → R) (v : Fin n → M) (k : ℕ) : M := ∑ i, x i ^ k • v i
end
section
open Polynomial
variable {R : Type*} [CommRing R] {n : ℕ}
variable {A : Type*} [Ring A] [Algebra R A]
def momentIdeal {κ : Type*} (x : Fin n → R) (v : κ → Fin n → A) : TwoSidedIdeal A := TwoSidedIdeal.span (Set.range fun p : κ × ℕ ↦
  moment x (v p.1) p.2)
end
section
open scoped TensorProduct
universe u
variable (K : Type u) [CommRing K] (n : ℕ)
abbrev PolynomialRing := MvPolynomial (Fin n) K
abbrev OddIndex := Fin n ⊕ Fin n
abbrev OddModule := OddIndex n → K
theorem polynomialSelfCommute : SMulCommClass K (PolynomialRing K n) (PolynomialRing K n) := by sorry
theorem polynomialSelfTower : IsScalarTower K (PolynomialRing K n) (PolynomialRing K n) := by sorry
theorem exteriorSelfCommute : SMulCommClass K (ExteriorAlgebra K (OddModule K n)) (ExteriorAlgebra K (OddModule K n)) := by sorry
theorem exteriorSelfTower : IsScalarTower K (ExteriorAlgebra K (OddModule K n)) (ExteriorAlgebra K (OddModule K n)) := by sorry
attribute [instance 2100] polynomialSelfCommute polynomialSelfTower exteriorSelfCommute exteriorSelfTower
abbrev SuperRing := PolynomialRing K n ⊗[K] ExteriorAlgebra K (OddModule K n)
@[reducible] noncomputable instance superQuotientModule (I : TwoSidedIdeal (SuperRing K n)) :
    Module K I.ringCon.Quotient := by
  let q : SuperRing K n →+ I.ringCon.Quotient :=
    { toFun := fun x ↦ (x : I.ringCon.Quotient)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact Function.Surjective.module K q
    (fun x ↦ I.ringCon.mk'_surjective x) (fun _ _ ↦ rfl)
noncomputable def theta (i : Fin n) : SuperRing K n := Algebra.TensorProduct.includeRight (ExteriorAlgebra.ι K (Pi.single (Sum.inl i)
  1))
noncomputable def xi (i : Fin n) : SuperRing K n := Algebra.TensorProduct.includeRight (ExteriorAlgebra.ι K (Pi.single (Sum.inr i) 1))
inductive MomentKind
  | polynomial | theta | xi | mixed
  deriving DecidableEq
end
section
open scoped TensorProduct
universe u
variable (K : Type u) [CommRing K] (n : ℕ)
variable {K n}
noncomputable def pairedCoefficients (β : Fin n → K)
    (a b : Fin n → PolynomialRing K n) : MomentKind → Fin n → SuperRing K n
  | .polynomial, i => (MvPolynomial.C (β i) * a i * b i) • (1 : SuperRing K n)
  | .theta, i => b i • theta K n i
  | .xi, i => (MvPolynomial.C (β i) * a i) • xi K n i
  | .mixed, i => theta K n i * xi K n i
noncomputable abbrev pairedIdeal (β : Fin n → K) (φ a b : Fin n → PolynomialRing K n) : TwoSidedIdeal (SuperRing K n) := momentIdeal φ
  (pairedCoefficients β a b)
abbrev PairedQuotient (β : Fin n → K) (φ a b : Fin n → PolynomialRing K n) := (pairedIdeal β φ a b).ringCon.Quotient
def AllowedWeights (β : Fin n → K) : Prop := IsUnit (n.factorial : K) ∧ ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)
def monomialWeight (r : Fin n → ℕ) (e : Fin n →₀ ℕ) : ℚ := ∑ i, (e i : ℚ) / (r i : ℚ)
def HasHighestPower (r : Fin n → ℕ) (p : PolynomialRing K n) (i : Fin n) (d : ℕ) : Prop := p.coeff (Finsupp.single i d) = 1 ∧ ∀ e ∈
  p.support, e ≠ Finsupp.single i d → monomialWeight r e < (d : ℚ) / (r i : ℚ)
structure PairedData where
  positive_n : 0 < n
  s : ℕ
  positive_s : 0 < s
  r : Fin n → ℕ
  u : Fin n → ℕ
  v : Fin n → ℕ
  positive_r : ∀ i, 0 < r i
  degree_split : ∀ i, u i + v i = r i * s
  beta : Fin n → K
  allowed_weights : AllowedWeights beta
  phi : Fin n → PolynomialRing K n
  a : Fin n → PolynomialRing K n
  b : Fin n → PolynomialRing K n
  highest_phi : ∀ i, HasHighestPower r (phi i) i (r i)
  highest_a : ∀ i, HasHighestPower r (a i) i (u i)
  highest_b : ∀ i, HasHighestPower r (b i) i (v i)
end
section
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {n : ℕ}
def ordinaryMomentIdeal (x : Fin n → A) (β : Fin n → K) (G : Polynomial K) : Ideal A := Ideal.span (Set.range fun k : Fin n ↦ moment x
  (fun i ↦ algebraMap K A (β i) * Polynomial.aeval (x i) G) k)
end
section
variable {K : Type*} [CommRing K] {n : ℕ}
def separatedOrdinaryIdeal (β : Fin n → K) (G : Polynomial K)
    (φ : Fin n → Polynomial K) : Ideal (MvPolynomial (Fin n) K) :=
  let x := fun i ↦ Polynomial.aeval (MvPolynomial.X i) (φ i)
  ordinaryMomentIdeal x β G
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion.Endpoint
section
open Polynomial
variable {R : Type*} [CommRing R]
def CoefficientBound (p : R[X]) (h : ℕ) : Prop := ∀ j : ℕ, h ≤ j → p.coeff j = 0
end
section
open Polynomial
variable {K ι : Type*} [Field K]
local notation "P" => MvPolynomial ι K
def HomogeneousPolynomial (w : ι → ℕ) (W H : ℕ) (p : Polynomial P) : Prop := (∀ j ≤ H, (p.coeff j).IsWeightedHomogeneous w (W * (H -
  j))) ∧ CoefficientBound p (H + 1)
theorem HomogeneousPolynomial.eval {w : ι → ℕ} {W H : ℕ} {p : Polynomial P} (hp : HomogeneousPolynomial w W H p) (y : P) (hy :
  y.IsWeightedHomogeneous w W) : (p.eval y).IsWeightedHomogeneous w (W * H) := by sorry
end
end PaperVerification.Fermion.Endpoint
namespace PaperVerification.Fermion.Universal
section
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
inductive Kind
  | phi
  | left
  | right
  deriving DecidableEq, Fintype
end
section
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
variable {K : Type*} [CommRing K] {n : ℕ}
def degree (d : PairedData (K := K) (n := n)) : Kind → Fin n → ℕ
  | .phi,i => d.r i
  | .left,i => d.u i
  | .right,i => d.v i
def input (d : PairedData (K := K) (n := n)) : Kind → Fin n → PolynomialRing K n
  | .phi,i => d.phi i
  | .left,i => d.a i
  | .right,i => d.b i
def lowerSupport (d : PairedData (K := K) (n := n)) (k : Kind) (i : Fin n) :
    Finset (Fin n →₀ ℕ) := by
  classical
  exact (input d k i).support.erase (Finsupp.single i (degree d k i))
abbrev Variables (d : PairedData (K := K) (n := n)) := Fin n ⊕ (Σ k : Kind, Σ i : Fin n, {a : Fin n →₀ ℕ // a ∈ lowerSupport d k i})
abbrev Coefficients (d : PairedData (K := K) (n := n)) := MvPolynomial (Variables d) ℤ
def beta (d : PairedData (K := K) (n := n)) (i : Fin n) : Coefficients d := X (.inl i)
end
end PaperVerification.Fermion.Universal
namespace PaperVerification.Fermion
section
open MvPolynomial
variable {R : Type*} [CommRing R] {n : ℕ}
theorem highestPower_X_pow (r : Fin n → ℕ) (i : Fin n) (e : ℕ) : HasHighestPower r (X i^e : PolynomialRing R n) i e := by sorry
end
section
open scoped TensorProduct
variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B]
theorem ringCon_le_ker_of_kills (I : TwoSidedIdeal A) (f : A →ₐ[R] B) (hf : ∀ a ∈ I, f a = 0) : I.ringCon ≤ RingCon.ker f.toRingHom :=
  by sorry
theorem quotientMk_eq_zero_of_mem (I : TwoSidedIdeal A) (a : A) (ha : a ∈ I) : I.ringCon.mkₐ R a = 0 := by sorry
theorem twoSided_map_killed (I : TwoSidedIdeal A) (f : A →+* B) (g : B →+* C) (h : ∀ a ∈ I, g (f a) = 0) : ∀ b ∈ TwoSidedIdeal.map f I,
  g b = 0 := by sorry
end
section
open scoped TensorProduct
variable (R S A : Type*) [CommRing R] [CommRing S] [Ring A]
  [Algebra R S] [Algebra R A]
section
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}
instance superQuotientTensorRing (I : TwoSidedIdeal (SuperRing R n)) :
    Ring (S ⊗[R] I.ringCon.Quotient) := by
  exact Algebra.TensorProduct.instRing (R := R) (A := S) (B := I.ringCon.Quotient)
theorem superQuotientTensorRing_formula (I : TwoSidedIdeal (SuperRing R n)) :
    superQuotientTensorRing R S I = Algebra.TensorProduct.instRing (R := R) (A := S) (B := I.ringCon.Quotient) := by sorry
instance superQuotientTensorAlgebra (I : TwoSidedIdeal (SuperRing R n)) :
    Algebra S (S ⊗[R] I.ringCon.Quotient) := by
  exact Algebra.TensorProduct.leftAlgebra (R := R) (S := S) (A := S) (B := I.ringCon.Quotient)
theorem superQuotientTensorAlgebra_formula (I : TwoSidedIdeal (SuperRing R n)) :
    superQuotientTensorAlgebra R S I = Algebra.TensorProduct.leftAlgebra (R := R) (S := S) (A := S) (B := I.ringCon.Quotient) := by sorry
end
def tensorTwoSidedIdeal (I : TwoSidedIdeal A) : TwoSidedIdeal (S ⊗[R] A) := TwoSidedIdeal.map (Algebra.TensorProduct.includeRight : A
  →ₐ[R] S ⊗[R] A).toRingHom I
abbrev TensorTwoSidedQuotient (I : TwoSidedIdeal A) := (tensorTwoSidedIdeal R S A I).ringCon.Quotient
end
section
open scoped TensorProduct
variable (R S A : Type*) [CommRing R] [CommRing S] [Ring A]
  [Algebra R S] [Algebra R A]
variable {R S A}
def tensorQuotientRight (I : TwoSidedIdeal A) :
    I.ringCon.Quotient →ₐ[R] TensorTwoSidedQuotient R S A I := by
  let f : A →ₐ[R] TensorTwoSidedQuotient R S A I :=
    (((tensorTwoSidedIdeal R S A I).ringCon.mkₐ S).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)
  exact I.ringCon.liftₐ f (ringCon_le_ker_of_kills I f (by
    intro a ha
    change (tensorTwoSidedIdeal R S A I).ringCon.mkₐ S (1 ⊗ₜ[R] a)=0
    exact quotientMk_eq_zero_of_mem (R := S) (tensorTwoSidedIdeal R S A I) _
      (TwoSidedIdeal.subset_span ⟨a,ha,rfl⟩)))
def tensorQuotientForward (I : TwoSidedIdeal A) : S ⊗[R] I.ringCon.Quotient →ₐ[S] TensorTwoSidedQuotient R S A I :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (tensorQuotientRight I) (fun s a ↦ Algebra.commutes s _)
@[simp] theorem tensorQuotientForward_tmul_mk (I : TwoSidedIdeal A)
    (s : S) (a : A) :
    tensorQuotientForward (R := R) (S := S) I (s ⊗ₜ[R] I.ringCon.mkₐ R a) =
      (tensorTwoSidedIdeal R S A I).ringCon.mkₐ S (s ⊗ₜ[R] a) := by sorry
def tensorQuotientRawBackward (I : TwoSidedIdeal A) : S ⊗[R] A →ₐ[S] S ⊗[R] I.ringCon.Quotient := Algebra.TensorProduct.map (AlgHom.id
  S S) (I.ringCon.mkₐ R)
def tensorQuotientBackward (I : TwoSidedIdeal A) :
    TensorTwoSidedQuotient R S A I →ₐ[S] S ⊗[R] I.ringCon.Quotient :=
  (tensorTwoSidedIdeal R S A I).ringCon.liftₐ (tensorQuotientRawBackward I)
    (ringCon_le_ker_of_kills _ _ <|
      twoSided_map_killed I
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
        (tensorQuotientRawBackward I).toRingHom fun a ha ↦ by
          simp [tensorQuotientRawBackward, quotientMk_eq_zero_of_mem I a ha])
@[simp] theorem tensorQuotientBackward_mk_tmul (I : TwoSidedIdeal A)
    (s : S) (a : A) :
    tensorQuotientBackward (R := R) (S := S) I
      ((tensorTwoSidedIdeal R S A I).ringCon.mkₐ S (s ⊗ₜ[R] a)) =
      s ⊗ₜ[R] I.ringCon.mkₐ R a := by sorry
def tensorTwoSidedQuotientEquiv (I : TwoSidedIdeal A) :
    S ⊗[R] I.ringCon.Quotient ≃ₐ[S] TensorTwoSidedQuotient R S A I :=
  AlgEquiv.ofAlgHom (tensorQuotientForward I) (tensorQuotientBackward I)
    (by
      apply RingCon.Quotient.hom_extₐ
      apply Algebra.TensorProduct.ext'
      intro s a
      change tensorQuotientForward I
        (tensorQuotientBackward I ((tensorTwoSidedIdeal R S A I).ringCon.mkₐ S (s ⊗ₜ[R] a)))=
          (tensorTwoSidedIdeal R S A I).ringCon.mkₐ S (s ⊗ₜ[R] a)
      rw [tensorQuotientBackward_mk_tmul,tensorQuotientForward_tmul_mk])
    (by
      apply Algebra.TensorProduct.ext'
      intro s q
      obtain ⟨a, rfl⟩ := I.ringCon.mk'_surjective q
      change tensorQuotientBackward I
        (tensorQuotientForward I (s ⊗ₜ[R] I.ringCon.mkₐ R a))=s ⊗ₜ[R] I.ringCon.mkₐ R a
      rw [tensorQuotientForward_tmul_mk,tensorQuotientBackward_mk_tmul])
end
section
open scoped Classical
variable {A ι : Type*} [CommRing A]
def exteriorGenerator (i : ι) : ExteriorAlgebra A (ι → A) := ExteriorAlgebra.ι A (Pi.single i 1)
abbrev ClusterExterior (A : Type*) [CommRing A] (ι : Type*) := ExteriorAlgebra A ((ι ⊕ ι) → A)
def clusterTheta (i : ι) : ClusterExterior A ι := exteriorGenerator (Sum.inl i)
def clusterXi (i : ι) : ClusterExterior A ι := exteriorGenerator (Sum.inr i)
end
section
open scoped TensorProduct Classical
def exteriorLinearEquiv {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (e : M ≃ₗ[R] N) : ExteriorAlgebra R M ≃ₐ[R] ExteriorAlgebra R N :=
  AlgEquiv.ofAlgHom (ExteriorAlgebra.map e.toLinearMap)
    (ExteriorAlgebra.map e.symm.toLinearMap)
    (by
      rw [ExteriorAlgebra.map_comp_map]
      have h : e.toLinearMap.comp e.symm.toLinearMap=LinearMap.id := by
        ext x
        exact e.apply_symm_apply x
      rw [h,ExteriorAlgebra.map_id])
    (by
      rw [ExteriorAlgebra.map_comp_map]
      have h : e.symm.toLinearMap.comp e.toLinearMap=LinearMap.id := by
        ext x
        exact e.symm_apply_apply x
      rw [h,ExteriorAlgebra.map_id])
def finiteExteriorBaseChange (R S ι : Type*) [CommRing R] [CommRing S] [Algebra R S] [Fintype ι] : S ⊗[R] ExteriorAlgebra R (ι → R)
  ≃ₐ[S] ExteriorAlgebra S (ι → S) := (ExteriorAlgebra.baseChangeEquiv R (ι → R) S).trans (exteriorLinearEquiv
  (TensorProduct.piScalarRight R S S ι))
def noncommCancelBaseChange (R P S E : Type*) [CommRing R] [CommRing P]
    [CommRing S] [Ring E] [Algebra R P] [Algebra R S] [Algebra P S]
    [IsScalarTower R P S] [Algebra R E] :
    S ⊗[P] (P ⊗[R] E) ≃ₐ[S] S ⊗[R] E :=
  AlgEquiv.symm <| AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R P S S E).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))
def scalarExteriorBaseChange (R P S ι : Type*) [CommRing R] [CommRing P] [CommRing S] [Algebra R P] [Algebra R S] [Algebra P S]
  [IsScalarTower R P S] [Fintype ι] : S ⊗[P] (P ⊗[R] ExteriorAlgebra R (ι → R)) ≃ₐ[S] ExteriorAlgebra S (ι → S) :=
  (noncommCancelBaseChange R P S _).trans (finiteExteriorBaseChange R S ι)
def twoSidedQuotientEquivOfEq {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    {I J : TwoSidedIdeal A} (h : I=J) : I.ringCon.Quotient ≃ₐ[R] J.ringCon.Quotient := by
  subst J
  exact AlgEquiv.refl
end
section
variable {R M ι Γ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ]
def basisDegreePart (b : Module.Basis ι R M) (degree : ι → Γ) (n : Γ) :
    Submodule R M :=
  Submodule.span R (b '' {i | degree i=n})
theorem basisDegreePart_iSup_eq_top (b : Module.Basis ι R M) (degree : ι → Γ) : (⨆ n,basisDegreePart b degree n)=⊤ := by sorry
theorem basisDegreePart_independent (b : Module.Basis ι R M) (degree : ι → Γ) : iSupIndep (basisDegreePart b degree) := by sorry
def basisDegreeDecomposition (b : Module.Basis ι R M) (degree : ι → Γ) : DirectSum.Decomposition (basisDegreePart b degree) :=
  (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (basisDegreePart_independent b degree) (basisDegreePart_iSup_eq_top b
  degree)).chooseDecomposition
end
section
variable {R M ι Γ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ]
variable {A : Type*} [Ring A] [Algebra R A] [AddMonoid Γ]
def basisDegreeGradedAlgebra (b : Module.Basis ι R A) (degree : ι → Γ)
    (hone : (1 : A)∈basisDegreePart b degree 0)
    (hmul : ∀ i j,b i*b j∈basisDegreePart b degree (degree i+degree j)) :
    GradedAlgebra (basisDegreePart b degree) where
  toDecomposition := basisDegreeDecomposition b degree
  one_mem := hone
  mul_mem := by
    intro m n x y hx hy
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i,hi,rfl⟩ := hx
        change degree i=m at hi
        induction hy using Submodule.span_induction with
        | mem y hy =>
            obtain ⟨j,hj,rfl⟩ := hy
            change degree j=n at hj
            simpa only [hi,hj] using hmul i j
        | zero =>
            simpa only [mul_zero] using (basisDegreePart b degree (m+n)).zero_mem
        | add y z hy hz ihy ihz =>
            rw [mul_add]
            exact (basisDegreePart b degree (m+n)).add_mem ihy ihz
        | smul r y hy ih =>
            rw [Algebra.mul_smul_comm]
            exact (basisDegreePart b degree (m+n)).smul_mem r ih
    | zero =>
        simpa only [zero_mul] using (basisDegreePart b degree (m+n)).zero_mem
    | add x z hx hz ihx ihz =>
        rw [add_mul]
        exact (basisDegreePart b degree (m+n)).add_mem ihx ihz
    | smul r x hx ih =>
        rw [Algebra.smul_mul_assoc]
        exact (basisDegreePart b degree (m+n)).smul_mem r ih
end
section
open scoped Classical
variable {A ι Γ : Type*} [CommRing A] [Fintype ι] [LinearOrder ι]
  [AddCommMonoid Γ] [DecidableEq Γ]
def exteriorWordDegree (w : ι → Γ) (T : Finset ι) : Γ := ∑ i∈T,w i
def exteriorWeightedPart (w : ι → Γ) (g : Γ) : Submodule A (ExteriorAlgebra A (ι → A)) := basisDegreePart (Pi.basisFun A
  ι).ExteriorAlgebra (exteriorWordDegree w) g
theorem exteriorWeightedPart_one (w : ι → Γ) : (1 : ExteriorAlgebra A (ι → A))∈exteriorWeightedPart w 0 := by sorry
theorem exteriorWeightedPart_basis_mul (w : ι → Γ) (S T : Finset ι) : (Pi.basisFun A ι).ExteriorAlgebra S*(Pi.basisFun A
  ι).ExteriorAlgebra T∈ exteriorWeightedPart w (exteriorWordDegree w S+exteriorWordDegree w T) := by sorry
def exteriorWeightedGrading (w : ι → Γ) : GradedAlgebra (exteriorWeightedPart (A := A) w) := basisDegreeGradedAlgebra (Pi.basisFun A
  ι).ExteriorAlgebra (exteriorWordDegree w) (exteriorWeightedPart_one w) (exteriorWeightedPart_basis_mul w)
end
section
open DirectSum
variable {R A B Γ : Type*} [AddMonoid Γ] [DecidableEq Γ] [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]
variable (part : Γ → Submodule R A) [GradedAlgebra part] (q : A →ₐ[R] B)
def gradedImagePart (n : Γ) : Submodule R B := (part n).map q.toLinearMap
def gradedImageComponent (n : Γ) : part n →ₗ[R] gradedImagePart part q n := (q.toLinearMap.comp (part n).subtype).codRestrict _ (fun a
  ↦ ⟨a,a.property,rfl⟩)
def gradedImageDecomposeSource : A →ₗ[R] ⨁ n,gradedImagePart part q n := (DirectSum.lmap (gradedImageComponent part q)).comp
  (DirectSum.decomposeLinearEquiv part).toLinearMap
@[simp] theorem gradedImageDecomposeSource_coe (n : Γ) (a : part n) :
    gradedImageDecomposeSource part q (a : A)=
      DirectSum.lof R Γ (gradedImagePart part q ·) n
        (gradedImageComponent part q n a) := by sorry
theorem gradedImageDecomposeSource_recompose (a : A) : DirectSum.coeLinearMap (gradedImagePart part q) (gradedImageDecomposeSource part
  q a)=q a := by sorry
end
section
open DirectSum
variable {R A B Γ : Type*} [AddMonoid Γ] [DecidableEq Γ] [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]
variable (part : Γ → Submodule R A) [GradedAlgebra part] (q : A →ₐ[R] B)
variable (hq : Function.Surjective q)
variable (hker : ∀ n a,q a=0 → q (GradedAlgebra.proj part n a)=0)
include hker
theorem gradedImageDecomposeSource_ker : LinearMap.ker q.toLinearMap ≤ LinearMap.ker (gradedImageDecomposeSource part q) := by sorry
end
section
open DirectSum
variable {R A B Γ : Type*} [AddMonoid Γ] [DecidableEq Γ] [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]
variable (part : Γ → Submodule R A) [GradedAlgebra part] (q : A →ₐ[R] B)
variable (hq : Function.Surjective q)
variable (hker : ∀ n a,q a=0 → q (GradedAlgebra.proj part n a)=0)
set_option maxHeartbeats 800000
def gradedImageDecompose (hq : Function.Surjective q)
    (hker : ∀ n a, q a = 0 → q (GradedAlgebra.proj part n a) = 0) :
    B →ₗ[R] ⨁ n, gradedImagePart part q n := by
  let descended : (A ⧸ LinearMap.ker q.toLinearMap) →ₗ[R]
      (⨁ n, gradedImagePart part q n) :=
    (LinearMap.ker q.toLinearMap).liftQ
      (R₂ := R) (M₂ := ⨁ n, gradedImagePart part q n) (τ₁₂ := RingHom.id R)
      (gradedImageDecomposeSource part q)
      (gradedImageDecomposeSource_ker part q hker)
  let quotientEquiv : (A ⧸ LinearMap.ker q.toLinearMap) ≃ₗ[R] B :=
    q.toLinearMap.quotKerEquivOfSurjective hq
  exact descended.comp quotientEquiv.symm.toLinearMap
end
section
open DirectSum
variable {R A B Γ : Type*} [AddMonoid Γ] [DecidableEq Γ] [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]
variable (part : Γ → Submodule R A) [GradedAlgebra part] (q : A →ₐ[R] B)
variable (hq : Function.Surjective q)
variable (hker : ∀ n a,q a=0 → q (GradedAlgebra.proj part n a)=0)
@[simp] theorem gradedImageDecompose_q (a : A) :
    gradedImageDecompose part q hq hker (q a)=gradedImageDecomposeSource part q a := by sorry
def gradedImageDecomposition (hq : Function.Surjective q)
    (hker : ∀ n a, q a = 0 → q (GradedAlgebra.proj part n a) = 0) :
    DirectSum.Decomposition (gradedImagePart part q) := by
  exact DirectSum.Decomposition.ofLinearMap (gradedImagePart part q)
    (gradedImageDecompose part q hq hker)
    (by
      apply LinearMap.ext
      intro b
      obtain ⟨a,rfl⟩ := hq b
      simp only [LinearMap.comp_apply,gradedImageDecompose_q,
        gradedImageDecomposeSource_recompose,LinearMap.id_apply])
    (by
      apply DirectSum.linearMap_ext
      intro n
      apply LinearMap.ext
      rintro ⟨b,hb⟩
      obtain ⟨a,ha,rfl⟩ := hb
      simp only [LinearMap.comp_apply,DirectSum.coeLinearMap_lof,LinearMap.id_apply]
      change gradedImageDecompose part q hq hker (q a) =
        DirectSum.lof R Γ (gradedImagePart part q ·) n
          (gradedImageComponent part q n ⟨a,ha⟩)
      rw [gradedImageDecompose_q]
      exact gradedImageDecomposeSource_coe part q n ⟨a,ha⟩)
instance gradedImageGradedMonoid :
    SetLike.GradedMonoid (gradedImagePart part q) where
  one_mem := ⟨1,SetLike.one_mem_graded part,map_one q⟩
  mul_mem := by
    intro i j a b ha hb
    obtain ⟨x,hx,rfl⟩ := ha
    obtain ⟨y,hy,rfl⟩ := hb
    exact ⟨x*y,SetLike.mul_mem_graded hx hy,map_mul q x y⟩
def gradedImageAlgebra (hq : Function.Surjective q)
    (hker : ∀ n a, q a = 0 → q (GradedAlgebra.proj part n a) = 0) :
    GradedAlgebra (gradedImagePart part q) where
  toGradedMonoid := gradedImageGradedMonoid part q
  toDecomposition := gradedImageDecomposition part q hq hker
end
section
open DirectSum
variable {R A B Γ : Type*} [AddMonoid Γ] [DecidableEq Γ] [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B]
variable (part : Γ → Submodule R A) [GradedAlgebra part] (q : A →ₐ[R] B)
variable (hq : Function.Surjective q)
variable (hker : ∀ n a,q a=0 → q (GradedAlgebra.proj part n a)=0)
variable {S C : Type*} [CommRing S] [Ring C] [Algebra R S]
  [Algebra S C] [Algebra R C] [IsScalarTower R S C]
variable (piece : Γ → Submodule S C) [GradedAlgebra piece]
def restrictGradedPart (n : Γ) : Submodule R C := (piece n).restrictScalars R
def restrictGradedAlgebra : GradedAlgebra (restrictGradedPart (R := R) piece) := inferInstanceAs (GradedAlgebra (fun n ↦ (piece
  n).restrictScalars R))
end
section
variable {R A Γ : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddMonoid Γ] [DecidableEq Γ]
variable (part : Γ → Submodule R A) [GradedAlgebra part]
theorem twoSided_span_multihomogeneous (generators : Set A) (hgen : ∀ g∈generators,∃ n,g∈part n) : ∀ a∈TwoSidedIdeal.span generators,∀
  n, GradedAlgebra.proj part n a∈TwoSidedIdeal.span generators := by sorry
def multihomogeneousTwoSidedQuotientGrading (generators : Set A)
    (hgen : ∀ g∈generators,∃ n,g∈part n) :
    GradedAlgebra
      (gradedImagePart part ((TwoSidedIdeal.span generators).ringCon.mkₐ R)) :=
  gradedImageAlgebra part ((TwoSidedIdeal.span generators).ringCon.mkₐ R)
    (RingCon.mkₐ_surjective (α := R) _) (by
      intro n a ha
      have hamem : a∈TwoSidedIdeal.span generators := by
        change ((a : A) : (TwoSidedIdeal.span generators).ringCon.Quotient)=
          ((0 : A) : (TwoSidedIdeal.span generators).ringCon.Quotient) at ha
        exact Quotient.exact ha
      exact quotientMk_eq_zero_of_mem _ _
        (twoSided_span_multihomogeneous part generators hgen a hamem n))
end
section
variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
theorem residueAlgHom_surjective (f : A →ₐ[F] F) : Function.Surjective f := by sorry
end
section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Classical
variable {F : Type*} [Field F] {n : ℕ}
structure SeparatedOrdinaryData (F : Type*) [Field F] (n : ℕ) where
  beta : Fin n → F
  G : Polynomial F
  phi : Fin n → Polynomial F
  beta_units : ∀ U : Finset (Fin n),U.Nonempty → IsUnit (∑ i∈U,beta i)
  G_monic : G.Monic
  G_pos : 0<G.natDegree
  phi_monic : ∀ i,(phi i).Monic
  phi_pos : ∀ i,0<(phi i).natDegree
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion.SeparatedOrdinaryData
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Classical
variable {F : Type*} [Field F] {n : ℕ}
variable (d : SeparatedOrdinaryData F n)
abbrev Ordinary := MvPolynomial (Fin n) F ⧸ separatedOrdinaryIdeal d.beta d.G d.phi
abbrev SupportPoint := {rho : Fin n → F // ∀ i,d.G.eval ((d.phi i).eval (rho i))=0}
def pointEval (rho : d.SupportPoint) : MvPolynomial (Fin n) F →ₐ[F] F := MvPolynomial.aeval rho.1
theorem pointEval_kills (rho : d.SupportPoint) : separatedOrdinaryIdeal d.beta d.G d.phi ≤ RingHom.ker (d.pointEval rho).toRingHom :=
  by sorry
def pointResidue (rho : d.SupportPoint) : d.Ordinary →ₐ[F] F := Ideal.Quotient.liftₐ (separatedOrdinaryIdeal d.beta d.G d.phi)
  (d.pointEval rho) (fun p hp ↦ d.pointEval_kills rho hp)
def pointMaximal (rho : d.SupportPoint) : Ideal d.Ordinary := RingHom.ker (d.pointResidue rho).toRingHom
instance pointMaximal_isMaximal (rho : d.SupportPoint) : (d.pointMaximal rho).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (d.pointResidue rho).toRingHom
    (residueAlgHom_surjective (d.pointResidue rho))
abbrev LocalOrdinary (rho : d.SupportPoint) := Localization.AtPrime (d.pointMaximal rho)
instance localOrdinary_localRing (rho : d.SupportPoint) : IsLocalRing (d.LocalOrdinary rho) :=
  IsLocalization.AtPrime.isLocalRing _ (d.pointMaximal rho)
end PaperVerification.Fermion.SeparatedOrdinaryData
namespace PaperVerification.Fermion
open scoped Classical
variable {R ι κ : Type*} [CommRing R] [Fintype ι]
def clusterPowerMoment (beta : ι → R) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) (c : κ) (k : ℕ) : MvPolynomial ι R := ∑ i : {i : ι //
  cluster i=c}, MvPolynomial.C (beta i.1)*MvPolynomial.X i.1^(r i.1*(s c+k))
def clusterPowerIdeal (beta : ι → R) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) : Ideal (MvPolynomial ι R) := Ideal.span (Set.range (fun
  p : κ×ℕ ↦ clusterPowerMoment beta cluster r s p.1 p.2))
abbrev ClusterOrdinary (beta : ι → R) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) := MvPolynomial ι R ⧸ clusterPowerIdeal beta cluster r
  s
def clusterZ (beta : ι → R) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) (i : ι) : ClusterOrdinary beta cluster r s := Ideal.Quotient.mk _
  (MvPolynomial.X i)
end PaperVerification.Fermion
namespace PaperVerification.Fermion.SeparatedOrdinaryData
section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Classical
variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedOrdinaryData F n) (rho : d.SupportPoint)
abbrev PointCluster := Set.range (fun i : Fin n ↦ (d.phi i).eval (rho.1 i))
end
section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Classical
variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedOrdinaryData F n) (rho : d.SupportPoint)
local instance FermionLocalCoordinates_clusterDecidableEq : DecidableEq (d.PointCluster rho) :=
  fun a b ↦ Classical.propDecidable (a=b)
def pointCluster (i : Fin n) : d.PointCluster rho := ⟨(d.phi i).eval (rho.1 i),i,rfl⟩
def ramificationOrder (i : Fin n) : ℕ := (d.phi i-C ((d.phi i).eval (rho.1 i))).rootMultiplicity (rho.1 i)
def clusterMultiplicity (c : d.PointCluster rho) : ℕ := d.G.rootMultiplicity c.1
theorem ramificationOrder_pos (i : Fin n) : 0<d.ramificationOrder rho i := by sorry
theorem clusterMultiplicity_pos (c : d.PointCluster rho) : 0<d.clusterMultiplicity rho c := by sorry
end
end PaperVerification.Fermion.SeparatedOrdinaryData
namespace PaperVerification.Fermion
section
open scoped Classical
inductive LocalOddFamily
  | theta
  | xi
  | mixed
  deriving DecidableEq
end
section
open scoped Classical
variable {A B ι κ : Type*} [CommRing A] [Ring B] [Algebra A B]
  [Fintype ι] [Fintype κ]
def clusterOddCurrent (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ)
    (family : LocalOddFamily) (c : κ) (k : ℕ) : ClusterExterior A ι :=
  match family with
  | .theta => ∑ i : {i : ι // cluster i=c},
      z i.1^(r i.1*k) • (z i.1^v i.1 • clusterTheta i.1)
  | .xi => ∑ i : {i : ι // cluster i=c},
      z i.1^(r i.1*k) • ((beta i.1*z i.1^u i.1) • clusterXi i.1)
  | .mixed => ∑ i : {i : ι // cluster i=c},
      z i.1^(r i.1*k) • (clusterTheta i.1*clusterXi i.1)
def clusterOddIdeal (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) : TwoSidedIdeal (ClusterExterior A ι) := TwoSidedIdeal.span
  (Set.range (fun p : κ×(LocalOddFamily×ℕ) ↦ clusterOddCurrent cluster z beta r u v p.2.1 p.1 p.2.2))
abbrev ClusterOddQuotient (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) := (clusterOddIdeal cluster z beta r u v).ringCon.Quotient
end
section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Classical
structure SeparatedPairedData (F : Type*) [Field F] (n : ℕ)
    extends SeparatedOrdinaryData F n where
  a : Fin n → Polynomial F
  b : Fin n → Polynomial F
  a_monic : ∀ i,(a i).Monic
  b_monic : ∀ i,(b i).Monic
  paired_product : ∀ i,a i*b i=G.comp (phi i)
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion.SeparatedPairedData
section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Classical
variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedPairedData F n)
variable (rho : d.toSeparatedOrdinaryData.SupportPoint)
abbrev O := d.toSeparatedOrdinaryData
def thetaOrder (i : Fin n) : ℕ := (d.a i).rootMultiplicity (rho.1 i)
def xiOrder (i : Fin n) : ℕ := (d.b i).rootMultiplicity (rho.1 i)
theorem local_exponent_balance (i : Fin n) : d.thetaOrder rho i+d.xiOrder rho i= d.O.ramificationOrder rho i* d.O.clusterMultiplicity
  rho (d.O.pointCluster rho i) := by sorry
end
section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct Classical
variable {F : Type*} [Field F] {n : ℕ}
variable (d : SeparatedPairedData F n)
def phiPolynomial (i : Fin n) : PolynomialRing F n := Polynomial.aeval (MvPolynomial.X i) (d.phi i)
def aPolynomial (i : Fin n) : PolynomialRing F n := Polynomial.aeval (MvPolynomial.X i) (d.a i)
def bPolynomial (i : Fin n) : PolynomialRing F n := Polynomial.aeval (MvPolynomial.X i) (d.b i)
abbrev superIdeal := pairedIdeal d.beta d.phiPolynomial d.aPolynomial d.bPolynomial
def SuperQuotient := PairedQuotient d.beta d.phiPolynomial d.aPolynomial d.bPolynomial
instance superQuotientRing : Ring d.SuperQuotient :=
  inferInstanceAs (Ring (PairedQuotient d.beta d.phiPolynomial d.aPolynomial d.bPolynomial))
instance superQuotientFieldAlgebra : Algebra F d.SuperQuotient :=
  inferInstanceAs (Algebra F (PairedQuotient d.beta d.phiPolynomial d.aPolynomial d.bPolynomial))
@[reducible] instance superQuotientFieldModule : Module F d.SuperQuotient :=
  @Algebra.toModule _ _ _ _ d.superQuotientFieldAlgebra
def superMk : SuperRing F n →ₐ[F] d.SuperQuotient := d.superIdeal.ringCon.mkₐ F
attribute [local instance 2450] AddMonoidAlgebra.instModule in
theorem ordinary_scalar_ideal_mem (p : PolynomialRing F n) (hp : p∈separatedOrdinaryIdeal d.beta d.G d.phi) :
  (Algebra.TensorProduct.includeLeft : PolynomialRing F n →ₐ[F] SuperRing F n) p ∈d.superIdeal := by sorry
def ordinaryToSuper : d.toSeparatedOrdinaryData.Ordinary →ₐ[F] d.SuperQuotient := Ideal.Quotient.liftₐ (separatedOrdinaryIdeal d.beta
  d.G d.phi) (d.superMk.comp Algebra.TensorProduct.includeLeft) (fun p hp ↦ quotientMk_eq_zero_of_mem (R := F) d.superIdeal _
  (d.ordinary_scalar_ideal_mem p hp))
instance polynomialSuperAlgebra : Algebra (PolynomialRing F n) d.SuperQuotient :=
  inferInstanceAs (Algebra (PolynomialRing F n) d.superIdeal.ringCon.Quotient)
@[reducible] instance polynomialSuperModule : Module (PolynomialRing F n) d.SuperQuotient :=
  @Algebra.toModule _ _ _ _ d.polynomialSuperAlgebra
instance fieldPolynomialSuperTower :
    IsScalarTower F (PolynomialRing F n) d.SuperQuotient :=
  inferInstanceAs (IsScalarTower F (PolynomialRing F n)
    (PairedQuotient d.beta d.phiPolynomial d.aPolynomial d.bPolynomial))
instance ordinarySuperAlgebra : Algebra d.toSeparatedOrdinaryData.Ordinary d.SuperQuotient :=
  d.ordinaryToSuper.toRingHom.toAlgebra' (by
    intro c x
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨a,rfl⟩ := RingCon.mkₐ_surjective (α := F) d.superIdeal.ringCon x
    change d.superMk ((Algebra.TensorProduct.includeLeft :
      PolynomialRing F n →ₐ[F] SuperRing F n) p) * d.superMk a =
      d.superMk a * d.superMk ((Algebra.TensorProduct.includeLeft :
        PolynomialRing F n →ₐ[F] SuperRing F n) p)
    rw [←map_mul,←map_mul]
    apply congrArg d.superMk
    exact Algebra.commutes p a)
@[reducible] instance ordinarySuperModule : Module d.toSeparatedOrdinaryData.Ordinary d.SuperQuotient :=
  @Algebra.toModule _ _ _ _ d.ordinarySuperAlgebra
instance polynomialOrdinarySuperTower :
    IsScalarTower (PolynomialRing F n) d.toSeparatedOrdinaryData.Ordinary d.SuperQuotient :=
  IsScalarTower.of_algebraMap_eq (R := PolynomialRing F n)
    (S := d.toSeparatedOrdinaryData.Ordinary) (A := d.SuperQuotient) (fun p ↦ rfl)
instance fieldOrdinarySuperTower :
    IsScalarTower F d.toSeparatedOrdinaryData.Ordinary d.SuperQuotient :=
  IsScalarTower.of_algebraMap_eq (R := F)
    (S := d.toSeparatedOrdinaryData.Ordinary) (A := d.SuperQuotient)
    (fun c ↦ (d.ordinaryToSuper.commutes c).symm)
end
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion
section
open scoped Classical
def oddBidegree {ι : Type*} : ι ⊕ ι → ℕ×ℕ := Sum.elim (fun _ ↦ (1,0)) (fun _ ↦ (0,1))
def oddFamilyBidegree : LocalOddFamily → ℕ×ℕ
  | .theta => (1,0)
  | .xi => (0,1)
  | .mixed => (1,1)
def oddFamilyDegree : LocalOddFamily → ℕ
  | .theta => 1
  | .xi => 1
  | .mixed => 2
end
section
open scoped Classical
variable {A ι κ : Type*} [CommRing A] [Fintype ι] [Fintype κ]
  [LinearOrder (ι⊕ι)]
abbrev exteriorBigradedPart : ℕ×ℕ → Submodule A (ClusterExterior A ι) := exteriorWeightedPart (A := A) (oddBidegree (ι := ι))
abbrev exteriorTotalPart : ℕ → Submodule A (ClusterExterior A ι) := exteriorWeightedPart (A := A) (fun _ : ι⊕ι ↦ 1)
theorem clusterOddCurrent_bidegree (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) (family : LocalOddFamily) (c : κ) (k : ℕ) :
  clusterOddCurrent cluster z beta r u v family c k∈ exteriorBigradedPart (oddFamilyBidegree family) := by sorry
theorem clusterOddCurrent_degree (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) (family : LocalOddFamily) (c : κ) (k : ℕ) :
  clusterOddCurrent cluster z beta r u v family c k∈ exteriorTotalPart (oddFamilyDegree family) := by sorry
def clusterOddBigradedPart (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) : ℕ×ℕ → Submodule A (ClusterOddQuotient cluster z beta r
  u v) := gradedImagePart exteriorBigradedPart ((clusterOddIdeal cluster z beta r u v).ringCon.mkₐ A)
def clusterOddTotalPart (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) : ℕ → Submodule A (ClusterOddQuotient cluster z beta r u v)
  := gradedImagePart exteriorTotalPart ((clusterOddIdeal cluster z beta r u v).ringCon.mkₐ A)
def clusterOddBigrading (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) :
    GradedAlgebra (clusterOddBigradedPart cluster z beta r u v) := by
  letI := exteriorWeightedGrading (A := A) (oddBidegree (ι := ι))
  exact multihomogeneousTwoSidedQuotientGrading exteriorBigradedPart
    (Set.range fun p : κ×(LocalOddFamily×ℕ) ↦
      clusterOddCurrent cluster z beta r u v p.2.1 p.1 p.2.2) (by
        rintro g ⟨⟨c,family,k⟩,rfl⟩
        exact ⟨oddFamilyBidegree family,clusterOddCurrent_bidegree cluster z beta r u v family c k⟩)
def clusterOddTotalGrading (cluster : ι → κ) (z beta : ι → A) (r u v : ι → ℕ) :
    GradedAlgebra (clusterOddTotalPart cluster z beta r u v) := by
  letI := exteriorWeightedGrading (A := A) (fun _ : ι⊕ι ↦ (1:ℕ))
  exact multihomogeneousTwoSidedQuotientGrading exteriorTotalPart
    (Set.range fun p : κ×(LocalOddFamily×ℕ) ↦
      clusterOddCurrent cluster z beta r u v p.2.1 p.1 p.2.2) (by
        rintro g ⟨⟨c,family,k⟩,rfl⟩
        exact ⟨oddFamilyDegree family,clusterOddCurrent_degree cluster z beta r u v family c k⟩)
end
section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
variable {F ι κ : Type*} [Field F] [CharZero F] [Fintype ι] [Fintype κ]
abbrev HomogeneousClusterAlgebra (beta : ι → F) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ) := ClusterOddQuotient cluster
  (clusterZ beta cluster r s) (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v
end
section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
variable {F ι κ : Type*} [Field F] [CharZero F] [Fintype ι] [Fintype κ]
  [LinearOrder (ι⊕ι)]
  (beta : ι → F) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ)
def homogeneousClusterPart : ℕ → Submodule F (HomogeneousClusterAlgebra beta cluster r s u v) := restrictGradedPart (R := F)
  (clusterOddTotalPart cluster (clusterZ beta cluster r s) (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v)
def homogeneousClusterGrading :
    GradedAlgebra (homogeneousClusterPart beta cluster r s u v) := by
  letI := clusterOddTotalGrading cluster (clusterZ beta cluster r s)
    (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v
  exact restrictGradedAlgebra _
end
section
open scoped TensorProduct
universe u
variable (F : Type u) [Field F]
structure NGradedAlgebra where
  Carrier : Type u
  [ring : Ring Carrier]
  [algebra : Algebra F Carrier]
  part : ℕ → Submodule F Carrier
  [graded : GradedAlgebra part]
attribute [instance] NGradedAlgebra.ring NGradedAlgebra.algebra NGradedAlgebra.graded
end
section
set_option backward.isDefEq.respectTransparency false
open scoped Classical TensorProduct
universe u
def finiteIndexLinearOrder (ι : Type u) [Fintype ι] : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin
  ι).injective
structure ClusterFamilyData (F : Type u) [Field F] (m : ℕ) where
  Index : Fin m → Type u
  [finite : ∀ c,Fintype (Index c)]
  beta : ∀ c,Index c → F
  r : ∀ c,Index c → ℕ
  s : Fin m → ℕ
  u : ∀ c,Index c → ℕ
  v : ∀ c,Index c → ℕ
attribute [instance] ClusterFamilyData.finite
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion.ClusterFamilyData
set_option backward.isDefEq.respectTransparency false
open scoped Classical TensorProduct
universe u
variable {F : Type u} [Field F] [CharZero F] {m : ℕ}
  (d : ClusterFamilyData F m)
local instance FermionIndependentClusterTensor_factorOddOrder (c : Fin m) : LinearOrder (d.Index c⊕d.Index c) :=
  finiteIndexLinearOrder _
local instance FermionIndependentClusterTensor_wholeOddOrder :
    LinearOrder ((Σ c,d.Index c)⊕(Σ c,d.Index c)) :=
  finiteIndexLinearOrder _
def factor (c : Fin m) : NGradedAlgebra F where
  Carrier := HomogeneousClusterAlgebra (d.beta c) (fun _ ↦ ()) (d.r c)
    (fun _ ↦ d.s c) (d.u c) (d.v c)
  ring := inferInstance
  algebra := inferInstance
  part := homogeneousClusterPart (d.beta c) (fun _ ↦ ()) (d.r c)
    (fun _ ↦ d.s c) (d.u c) (d.v c)
  graded := homogeneousClusterGrading (d.beta c) (fun _ ↦ ()) (d.r c)
    (fun _ ↦ d.s c) (d.u c) (d.v c)
end PaperVerification.Fermion.ClusterFamilyData
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open scoped Classical TensorProduct
def totalBidegree : (ℕ×ℕ) →+ ℕ where
  toFun g := g.1+g.2
  map_zero' := rfl
  map_add' g h := by change (g.1+h.1)+(g.2+h.2)=(g.1+g.2)+(h.1+h.2); omega
end PaperVerification.Fermion
namespace PaperVerification.Fermion.NGradedAlgebra
set_option backward.isDefEq.respectTransparency false
open scoped Classical TensorProduct
universe u
variable {F : Type u} [Field F]
structure Bigrading (A : NGradedAlgebra F) where
  part : (ℕ×ℕ) → Submodule F A.Carrier
  [graded : GradedAlgebra part]
  total : ∀ g,part g≤A.part (totalBidegree g)
attribute [instance] Bigrading.graded
end PaperVerification.Fermion.NGradedAlgebra
namespace PaperVerification.Fermion
open scoped Classical
variable {F ι κ : Type*} [Field F] [CharZero F] [Fintype ι] [Fintype κ]
  [LinearOrder (ι⊕ι)]
  (beta : ι → F) (cluster : ι → κ) (r : ι → ℕ) (s : κ → ℕ) (u v : ι → ℕ)
def homogeneousClusterBigradedPart : (ℕ×ℕ) → Submodule F (HomogeneousClusterAlgebra beta cluster r s u v) := restrictGradedPart (R :=
  F) (clusterOddBigradedPart cluster (clusterZ beta cluster r s) (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u
  v)
def homogeneousClusterBigrading :
    GradedAlgebra (homogeneousClusterBigradedPart beta cluster r s u v) := by
  letI := clusterOddBigrading cluster (clusterZ beta cluster r s)
    (fun i ↦ algebraMap F (ClusterOrdinary beta cluster r s) (beta i)) r u v
  exact restrictGradedAlgebra _
theorem homogeneousCluster_bigraded_total (g : ℕ×ℕ) : homogeneousClusterBigradedPart beta cluster r s u v g≤ homogeneousClusterPart
  beta cluster r s u v (totalBidegree g) := by sorry
end PaperVerification.Fermion
namespace PaperVerification.Fermion.ClusterFamilyData
open scoped Classical
universe u
variable {F : Type u} [Field F] [CharZero F] {m : ℕ}
  (d : ClusterFamilyData F m)
local instance FermionIndependentClusterBigraded_factorOddOrder (c : Fin m) : LinearOrder (d.Index c⊕d.Index c) :=
  finiteIndexLinearOrder _
local instance FermionIndependentClusterBigraded_wholeOddOrder :
    LinearOrder ((Σ c,d.Index c)⊕(Σ c,d.Index c)) := finiteIndexLinearOrder _
def factorBigrading (c : Fin m) : NGradedAlgebra.Bigrading (d.factor c) where
  part := homogeneousClusterBigradedPart (d.beta c) (fun _ ↦ ()) (d.r c)
    (fun _ ↦ d.s c) (d.u c) (d.v c)
  graded := homogeneousClusterBigrading _ _ _ _ _ _
  total := homogeneousCluster_bigraded_total _ _ _ _ _ _
end PaperVerification.Fermion.ClusterFamilyData
namespace PaperVerification.Fermion.SeparatedPairedData
section
open scoped Classical TensorProduct
variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)
local instance FermionLocalTensorAssembly_sourceOddOrder : LinearOrder (Fin n⊕Fin n) := finiteIndexLinearOrder _
def localClusterLabels : d.O.PointCluster rho ≃ Fin (Fintype.card (d.O.PointCluster rho)) := Fintype.equivFin _
def localClusterFamily : ClusterFamilyData F (Fintype.card (d.O.PointCluster rho)) where
  Index c := {i : Fin n // d.O.pointCluster rho i=(d.localClusterLabels rho).symm c}
  finite _ := inferInstance
  beta c i := d.beta i.1
  r c i := d.O.ramificationOrder rho i.1
  s c := d.O.clusterMultiplicity rho ((d.localClusterLabels rho).symm c)
  u c i := d.thetaOrder rho i.1
  v c i := d.xiOrder rho i.1
end
section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct Classical
variable {F : Type*} [Field F] {n : ℕ} (d : SeparatedPairedData F n)
local instance (priority := 2250) palomarSelfActionglobalSuperPolynomialBaseEquiv : DistribMulAction d.toSeparatedOrdinaryData.Ordinary d.toSeparatedOrdinaryData.Ordinary := (Semiring.toModule (R := d.toSeparatedOrdinaryData.Ordinary)).toDistribMulAction
def globalSuperPolynomialBaseEquiv :
    d.SuperQuotient ≃ₐ[d.O.Ordinary] d.O.Ordinary ⊗[PolynomialRing F n] d.SuperQuotient := by
  letI : TensorProduct.CompatibleSMul (PolynomialRing F n) d.O.Ordinary
      d.O.Ordinary d.SuperQuotient :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (R := PolynomialRing F n) (A := d.O.Ordinary) d.O.Ordinary d.SuperQuotient
      (show Function.Surjective (algebraMap (PolynomialRing F n) d.O.Ordinary)
        from Ideal.Quotient.mk_surjective)
  exact (Algebra.TensorProduct.lid d.O.Ordinary d.SuperQuotient).symm.trans
    (Algebra.TensorProduct.equivOfCompatibleSMul (PolynomialRing F n)
      d.O.Ordinary d.O.Ordinary d.O.Ordinary d.SuperQuotient)
def ordinaryAmbientEquiv : d.O.Ordinary ⊗[PolynomialRing F n] SuperRing F n ≃ₐ[d.O.Ordinary] ClusterExterior d.O.Ordinary (Fin n) :=
  scalarExteriorBaseChange F (PolynomialRing F n) d.O.Ordinary (OddIndex n)
def ordinaryTensorIdeal := tensorTwoSidedIdeal (PolynomialRing F n) (d.O.Ordinary) (SuperRing F n) d.superIdeal
end
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open scoped Classical
variable {F : Type*} [Field F] {n : ℕ}
  (beta : Fin n → F)
  (hbeta : ∀ U : Finset (Fin n),U.Nonempty → IsUnit (∑ i∈U,beta i))
  (r : Fin n → ℕ) (hr : ∀ i,0<r i) (s : ℕ) (hs : 0<s)
  (u v : Fin n → ℕ) (huv : ∀ i,u i+v i=r i*s)
def powerSeparatedData : SeparatedPairedData F n where
  beta := beta
  G := Polynomial.X^s
  phi i := Polynomial.X^r i
  beta_units := hbeta
  G_monic := Polynomial.monic_X_pow s
  G_pos := by simpa only [Polynomial.natDegree_X_pow] using hs
  phi_monic i := Polynomial.monic_X_pow (r i)
  phi_pos i := by simpa only [Polynomial.natDegree_X_pow] using hr i
  a i := Polynomial.X^u i
  b i := Polynomial.X^v i
  a_monic i := Polynomial.monic_X_pow (u i)
  b_monic i := Polynomial.monic_X_pow (v i)
  paired_product i := by
    rw [←pow_add,huv,Polynomial.X_pow_comp,pow_mul]
end PaperVerification.Fermion
namespace PaperVerification.Fermion.SeparatedPairedData
section
open scoped Classical
variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)
  (c : Fin (Fintype.card (d.O.PointCluster rho)))
abbrev LocalFactorIndex := (d.localClusterFamily rho).Index c
def localFactorIndex : Fin (Fintype.card (d.LocalFactorIndex rho c)) → Fin n := fun j ↦ ((Fintype.equivFin (d.LocalFactorIndex rho
  c)).symm j).1
theorem localFactorIndex_cluster (j : Fin (Fintype.card (d.LocalFactorIndex rho c))) : d.O.pointCluster rho (d.localFactorIndex rho c
  j)=(d.localClusterLabels rho).symm c := by sorry
theorem localFactor_card_pos : 0<Fintype.card (d.LocalFactorIndex rho c) := by sorry
theorem localFactor_subset_units (U : Finset (Fin (Fintype.card (d.LocalFactorIndex rho c)))) (hU : U.Nonempty) : IsUnit (∑ j∈U,d.beta
  (d.localFactorIndex rho c j)) := by sorry
def localFactorPairedData :
    PairedData (K := F) (n := Fintype.card (d.LocalFactorIndex rho c)) where
  positive_n := d.localFactor_card_pos rho c
  s := (d.localClusterFamily rho).s c
  positive_s := d.O.clusterMultiplicity_pos rho ((d.localClusterLabels rho).symm c)
  r j := d.O.ramificationOrder rho (d.localFactorIndex rho c j)
  u j := d.thetaOrder rho (d.localFactorIndex rho c j)
  v j := d.xiOrder rho (d.localFactorIndex rho c j)
  positive_r j := d.O.ramificationOrder_pos rho (d.localFactorIndex rho c j)
  degree_split j := by
    change d.thetaOrder rho (d.localFactorIndex rho c j)+
        d.xiOrder rho (d.localFactorIndex rho c j)=
      d.O.ramificationOrder rho (d.localFactorIndex rho c j)*
        d.O.clusterMultiplicity rho ((d.localClusterLabels rho).symm c)
    rw [←d.localFactorIndex_cluster rho c j]
    exact d.local_exponent_balance rho (d.localFactorIndex rho c j)
  beta j := d.beta (d.localFactorIndex rho c j)
  allowed_weights := ⟨isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    d.localFactor_subset_units rho c⟩
  phi j := MvPolynomial.X j^d.O.ramificationOrder rho (d.localFactorIndex rho c j)
  a j := MvPolynomial.X j^d.thetaOrder rho (d.localFactorIndex rho c j)
  b j := MvPolynomial.X j^d.xiOrder rho (d.localFactorIndex rho c j)
  highest_phi j := highestPower_X_pow _ j _
  highest_a j := highestPower_X_pow _ j _
  highest_b j := highestPower_X_pow _ j _
end
section
set_option backward.isDefEq.respectTransparency false
open scoped Classical TensorProduct
variable {F : Type*} [Field F] {n : ℕ} (d : SeparatedPairedData F n)
local instance FermionGlobalBigrading_oddOrder : LinearOrder (Fin n⊕Fin n) := finiteIndexLinearOrder _
def globalSuperExteriorLift : ClusterExterior (d.O.Ordinary) (Fin n) →ₐ[d.O.Ordinary] d.SuperQuotient :=
  (d.globalSuperPolynomialBaseEquiv).symm.toAlgHom.comp ((tensorTwoSidedQuotientEquiv (R := PolynomialRing F n) (S := d.O.Ordinary)
  d.superIdeal).symm.toAlgHom.comp (((d.ordinaryTensorIdeal).ringCon.mkₐ (d.O.Ordinary)).comp (d.ordinaryAmbientEquiv).symm.toAlgHom))
def globalSuperBigradedPart (g : ℕ×ℕ) : Submodule (d.O.Ordinary) (d.SuperQuotient) := (exteriorBigradedPart g).map
  (d.globalSuperExteriorLift).toLinearMap
end
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion
set_option backward.isDefEq.respectTransparency false
open scoped Classical
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
  (beta : Fin n → F)
  (hbeta : ∀ U : Finset (Fin n),U.Nonempty → IsUnit (∑ i∈U,beta i))
  (r : Fin n → ℕ) (hr : ∀ i,0<r i) (s : ℕ) (hs : 0<s)
  (u v : Fin n → ℕ) (huv : ∀ i,u i+v i=r i*s)
local instance FermionSingleClusterBigraded_powerOddOrder : LinearOrder (Fin n⊕Fin n) := finiteIndexLinearOrder _
def pairedPowerOriginalEquiv :
    (powerSeparatedData beta hbeta r hr s hs u v huv).SuperQuotient ≃ₐ[F]
      PairedQuotient beta (fun i ↦ MvPolynomial.X i^r i)
        (fun i ↦ MvPolynomial.X i^u i) (fun i ↦ MvPolynomial.X i^v i) := by
  let d := powerSeparatedData beta hbeta r hr s hs u v huv
  have hphi : d.phiPolynomial = (fun i ↦ MvPolynomial.X i^r i) := by
    funext i
    change Polynomial.aeval (MvPolynomial.X i) (Polynomial.X^r i) = _
    exact Polynomial.aeval_X_pow _
  have hpa : d.aPolynomial = (fun i ↦ MvPolynomial.X i^u i) := by
    funext i
    change Polynomial.aeval (MvPolynomial.X i) (Polynomial.X^u i) = _
    exact Polynomial.aeval_X_pow _
  have hpb : d.bPolynomial = (fun i ↦ MvPolynomial.X i^v i) := by
    funext i
    change Polynomial.aeval (MvPolynomial.X i) (Polynomial.X^v i) = _
    exact Polynomial.aeval_X_pow _
  exact twoSidedQuotientEquivOfEq (R := F) (show d.superIdeal=
    pairedIdeal beta (fun i ↦ MvPolynomial.X i^r i)
      (fun i ↦ MvPolynomial.X i^u i) (fun i ↦ MvPolynomial.X i^v i) from by
        change pairedIdeal d.beta d.phiPolynomial d.aPolynomial d.bPolynomial=_
        rw [hphi,hpa,hpb]
        rfl)
def pairedPowerBigradedPart (g : ℕ×ℕ) : Submodule F (PairedQuotient beta (fun i ↦ MvPolynomial.X i^r i) (fun i ↦ MvPolynomial.X i^u i)
  (fun i ↦ MvPolynomial.X i^v i)) := (((powerSeparatedData beta hbeta r hr s hs u v huv).globalSuperBigradedPart g).restrictScalars
  F).map (pairedPowerOriginalEquiv beta hbeta r hr s hs u v huv).toLinearMap
end PaperVerification.Fermion
namespace PaperVerification.Fermion.SeparatedPairedData
open scoped Classical
variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)
  (c : Fin (Fintype.card (d.O.PointCluster rho)))
local instance FermionLocalFactorBigraded_factorOddOrder :
    LinearOrder (d.LocalFactorIndex rho c⊕d.LocalFactorIndex rho c) := finiteIndexLinearOrder _
local instance FermionLocalFactorBigraded_originalOddOrder :
    LinearOrder (Fin (Fintype.card (d.LocalFactorIndex rho c))⊕
      Fin (Fintype.card (d.LocalFactorIndex rho c))) := finiteIndexLinearOrder _
def localFactorPairedBigradedPart (g : ℕ×ℕ) :
    Submodule F (PairedQuotient (d.localFactorPairedData rho c).beta
      (d.localFactorPairedData rho c).phi
      (d.localFactorPairedData rho c).a
      (d.localFactorPairedData rho c).b) :=
  let p := d.localFactorPairedData rho c
  pairedPowerBigradedPart p.beta p.allowed_weights.2 p.r p.positive_r p.s p.positive_s
    p.u p.v p.degree_split g
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion
open scoped Classical
theorem localFactorPresentation {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ} (d : SeparatedPairedData F n) : ∀ (rho :
  d.O.SupportPoint) (c : Fin (Fintype.card (d.O.PointCluster rho))), ∃ e : ((d.localClusterFamily rho).factor c).Carrier ≃ₐ[F]
  PairedQuotient (d.localFactorPairedData rho c).beta (d.localFactorPairedData rho c).phi (d.localFactorPairedData rho c).a
  (d.localFactorPairedData rho c).b, ∀ g x,e x∈d.localFactorPairedBigradedPart rho c g ↔ x∈((d.localClusterFamily rho).factorBigrading
  c).part g := by sorry
end PaperVerification.Fermion
