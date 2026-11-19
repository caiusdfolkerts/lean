module
public import Mathlib

/-! Dimensions of the local factors and exterior components of separated two-fermion quotients. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace PaperVerification.Fermion.BasisFiltered
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped BigOperators
variable {R M I J E : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis I R M) (w : I → ℕ)
def Homogeneous (d : ℕ) (x : M) : Prop := ∀ i, b.repr x i ≠ 0 → w i = d
end
end PaperVerification.Fermion.BasisFiltered
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped BigOperators
open Polynomial
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {n : ℕ}
def moment (x : Fin n → R) (v : Fin n → M) (k : ℕ) : M :=
  ∑ i, x i ^ k • v i
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped BigOperators
open Polynomial
variable {R : Type*} [CommRing R]
variable {n : ℕ}
variable {A : Type*} [Ring A] [Algebra R A]
def momentIdeal {κ : Type*} (x : Fin n → R) (v : κ → Fin n → A) : TwoSidedIdeal A :=
  TwoSidedIdeal.span (Set.range fun p : κ × ℕ ↦ moment x (v p.1) p.2)
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped BigOperators TensorProduct
universe u
variable (K : Type u) [CommRing K] (n : ℕ)
abbrev PolynomialRing := MvPolynomial (Fin n) K
abbrev OddIndex := Fin n ⊕ Fin n
abbrev OddModule := OddIndex n → K
abbrev SuperRing := PolynomialRing K n ⊗[K] ExteriorAlgebra K (OddModule K n)
noncomputable def theta (i : Fin n) : SuperRing K n :=
  Algebra.TensorProduct.includeRight
    (ExteriorAlgebra.ι K (Pi.single (Sum.inl i) 1))
noncomputable def xi (i : Fin n) : SuperRing K n :=
  Algebra.TensorProduct.includeRight
    (ExteriorAlgebra.ι K (Pi.single (Sum.inr i) 1))
inductive MomentKind
  | polynomial | theta | xi | mixed
  deriving DecidableEq
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped BigOperators TensorProduct
universe u
variable (K : Type u) [CommRing K] (n : ℕ)
variable {K n}
noncomputable def pairedCoefficients (β : Fin n → K)
    (a b : Fin n → PolynomialRing K n) : MomentKind → Fin n → SuperRing K n
  | .polynomial, i => (MvPolynomial.C (β i) * a i * b i) • (1 : SuperRing K n)
  | .theta, i => b i • theta K n i
  | .xi, i => (MvPolynomial.C (β i) * a i) • xi K n i
  | .mixed, i => theta K n i * xi K n i
noncomputable abbrev pairedIdeal (β : Fin n → K)
    (φ a b : Fin n → PolynomialRing K n) : TwoSidedIdeal (SuperRing K n) :=
  momentIdeal φ (pairedCoefficients β a b)
abbrev PairedQuotient (β : Fin n → K) (φ a b : Fin n → PolynomialRing K n) :=
  (pairedIdeal β φ a b).ringCon.Quotient
def AllowedWeights (β : Fin n → K) : Prop :=
  IsUnit (n.factorial : K) ∧
    ∀ U : Finset (Fin n), U.Nonempty → IsUnit (∑ i ∈ U, β i)
def monomialWeight (r : Fin n → ℕ) (e : Fin n →₀ ℕ) : ℚ :=
  ∑ i, (e i : ℚ) / (r i : ℚ)
def HasHighestPower (r : Fin n → ℕ) (p : PolynomialRing K n)
    (i : Fin n) (d : ℕ) : Prop :=
  p.coeff (Finsupp.single i d) = 1 ∧
    ∀ e ∈ p.support, e ≠ Finsupp.single i d →
      monomialWeight r e < (d : ℚ) / (r i : ℚ)
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
end PaperVerification.Fermion
namespace PaperVerification.Fermion.Exterior
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped BigOperators
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {n : ℕ}
def modeRank : Fin n ⊕ Fin n → ℕ
  | .inl i => i.val
  | .inr i => n + i.val
theorem modeRank_injective : Function.Injective (modeRank (n := n)) := by sorry
end
end PaperVerification.Fermion.Exterior
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped BigOperators
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A] {n : ℕ}
def ordinaryMomentIdeal (x : Fin n → A) (β : Fin n → K) (G : Polynomial K) : Ideal A :=
  Ideal.span (Set.range fun k : Fin n ↦
    moment x (fun i ↦ algebraMap K A (β i) * Polynomial.aeval (x i) G) k)
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped BigOperators
variable {K : Type*} [CommRing K] {n : ℕ}
def separatedOrdinaryIdeal (β : Fin n → K) (G : Polynomial K)
    (φ : Fin n → Polynomial K) : Ideal (MvPolynomial (Fin n) K) :=
  let x := fun i ↦ Polynomial.aeval (MvPolynomial.X i) (φ i)
  ordinaryMomentIdeal x β G
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion.Endpoint
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped BigOperators
open Polynomial
variable {R : Type*} [CommRing R]
def CoefficientBound (p : R[X]) (h : ℕ) : Prop :=
  ∀ j : ℕ, h ≤ j → p.coeff j = 0
end
end PaperVerification.Fermion.Endpoint
namespace PaperVerification.Fermion.Endpoint
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped BigOperators
open Polynomial
variable {K ι : Type*} [Field K]
local notation "P" => MvPolynomial ι K
def HomogeneousPolynomial (w : ι → ℕ) (W H : ℕ) (p : Polynomial P) : Prop :=
  (∀ j ≤ H, (p.coeff j).IsWeightedHomogeneous w (W * (H - j))) ∧
    CoefficientBound p (H + 1)
theorem HomogeneousPolynomial.eval {w : ι → ℕ} {W H : ℕ} {p : Polynomial P}
    (hp : HomogeneousPolynomial w W H p) (y : P)
    (hy : y.IsWeightedHomogeneous w W) :
    (p.eval y).IsWeightedHomogeneous w (W * H) := by sorry
end
end PaperVerification.Fermion.Endpoint
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open MvPolynomial
open scoped BigOperators TensorProduct
variable {K : Type*} [CommRing K] {n : ℕ} [LinearOrder (OddIndex n)]
abbrev SuperMonomialIndex (n : ℕ) := (Fin n →₀ ℕ) × Finset (OddIndex n)
def superMonomialBasis : Module.Basis (SuperMonomialIndex n) K (SuperRing K n) :=
  (basisMonomials (Fin n) K).tensorProduct (Pi.basisFun K (OddIndex n)).ExteriorAlgebra
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion.Universal
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
open scoped BigOperators
inductive Kind
  | phi
  | left
  | right
  deriving DecidableEq, Fintype
end
end PaperVerification.Fermion.Universal
namespace PaperVerification.Fermion.Universal
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MvPolynomial
open scoped BigOperators
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
abbrev Variables (d : PairedData (K := K) (n := n)) :=
  Fin n ⊕ (Σ k : Kind, Σ i : Fin n, {a : Fin n →₀ ℕ // a ∈ lowerSupport d k i})
abbrev Coefficients (d : PairedData (K := K) (n := n)) := MvPolynomial (Variables d) ℤ
def beta (d : PairedData (K := K) (n := n)) (i : Fin n) : Coefficients d := X (.inl i)
end
end PaperVerification.Fermion.Universal
namespace PaperVerification.Fermion.BasisFiltered
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped BigOperators
variable {R M Q I E : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup Q] [Module R Q]
  (b : Module.Basis I R M) (w : I → ℕ)
def homogeneousPiece (d : ℕ) : Submodule R M where
  carrier := {x | Homogeneous b w d x}
  zero_mem' := by intro i hi; exact (hi (by simp)).elim
  add_mem' := by
    intro x y hx hy i hi
    by_cases hxi : b.repr x i=0
    · apply hy i
      simpa only [map_add,Finsupp.add_apply,hxi,zero_add] using hi
    · exact hx i hxi
  smul_mem' := by
    intro c x hx i hi
    apply hx i
    intro hz
    exact hi (by simp only [map_smul,Finsupp.smul_apply,hz,smul_zero])
end
end PaperVerification.Fermion.BasisFiltered
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped TensorProduct
variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
  [Algebra R A] [Algebra R B]
theorem ringCon_le_ker_of_kills (I : TwoSidedIdeal A) (f : A →ₐ[R] B)
    (hf : ∀ a ∈ I, f a = 0) : I.ringCon ≤ RingCon.ker f.toRingHom := by sorry
theorem quotientMk_eq_zero_of_mem (I : TwoSidedIdeal A) (a : A) (ha : a ∈ I) :
    I.ringCon.mkₐ R a = 0 := by sorry
theorem twoSided_map_killed (I : TwoSidedIdeal A) (f : A →+* B)
    (g : B →+* C) (h : ∀ a ∈ I, g (f a) = 0) :
    ∀ b ∈ TwoSidedIdeal.map f I, g b = 0 := by sorry
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped TensorProduct
variable (R S A : Type*) [CommRing R] [CommRing S] [Ring A]
  [Algebra R S] [Algebra R A]
def tensorTwoSidedIdeal (I : TwoSidedIdeal A) : TwoSidedIdeal (S ⊗[R] A) :=
  TwoSidedIdeal.map
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom I
abbrev TensorTwoSidedQuotient (I : TwoSidedIdeal A) :=
  (tensorTwoSidedIdeal R S A I).ringCon.Quotient
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
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
def tensorQuotientForward (I : TwoSidedIdeal A) :
    S ⊗[R] I.ringCon.Quotient →ₐ[S] TensorTwoSidedQuotient R S A I :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (tensorQuotientRight I)
    (fun s a ↦ Algebra.commutes s _)
@[simp] theorem tensorQuotientForward_tmul_mk (I : TwoSidedIdeal A)
    (s : S) (a : A) :
    tensorQuotientForward (R := R) (S := S) I (s ⊗ₜ[R] I.ringCon.mkₐ R a) =
      (tensorTwoSidedIdeal R S A I).ringCon.mkₐ S (s ⊗ₜ[R] a) := by sorry
def tensorQuotientRawBackward (I : TwoSidedIdeal A) :
    S ⊗[R] A →ₐ[S] S ⊗[R] I.ringCon.Quotient :=
  Algebra.TensorProduct.map (AlgHom.id S S) (I.ringCon.mkₐ R)
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
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped Classical
variable {A ι : Type*} [CommRing A]
abbrev ClusterExterior (A : Type*) [CommRing A] (ι : Type*) :=
  ExteriorAlgebra A ((ι ⊕ ι) → A)
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
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
def finiteExteriorBaseChange (R S ι : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Fintype ι] :
    S ⊗[R] ExteriorAlgebra R (ι → R) ≃ₐ[S] ExteriorAlgebra S (ι → S) :=
  (ExteriorAlgebra.baseChangeEquiv R (ι → R) S).trans
    (exteriorLinearEquiv (TensorProduct.piScalarRight R S S ι))
def noncommCancelBaseChange (R P S E : Type*) [CommRing R] [CommRing P]
    [CommRing S] [Ring E] [Algebra R P] [Algebra R S] [Algebra P S]
    [IsScalarTower R P S] [Algebra R E] :
    S ⊗[P] (P ⊗[R] E) ≃ₐ[S] S ⊗[R] E :=
  AlgEquiv.symm <| AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R P S S E).symm
    (by simp [Algebra.TensorProduct.one_def])
    (LinearMap.map_mul_of_map_mul_tmul (fun _ _ _ _ ↦ by simp))
def scalarExteriorBaseChange (R P S ι : Type*) [CommRing R] [CommRing P]
    [CommRing S] [Algebra R P] [Algebra R S] [Algebra P S]
    [IsScalarTower R P S] [Fintype ι] :
    S ⊗[P] (P ⊗[R] ExteriorAlgebra R (ι → R)) ≃ₐ[S]
      ExteriorAlgebra S (ι → S) :=
  (noncommCancelBaseChange R P S _).trans (finiteExteriorBaseChange R S ι)
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
variable {R M ι Γ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [DecidableEq Γ]
def basisDegreePart (b : Module.Basis ι R M) (degree : ι → Γ) (n : Γ) :
    Submodule R M :=
  Submodule.span R (b '' {i | degree i=n})
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped Classical BigOperators
variable {A ι Γ : Type*} [CommRing A] [Fintype ι] [LinearOrder ι]
  [AddCommMonoid Γ] [DecidableEq Γ]
def exteriorWordDegree (w : ι → Γ) (T : Finset ι) : Γ := ∑ i∈T,w i
def exteriorWeightedPart (w : ι → Γ) (g : Γ) :
    Submodule A (ExteriorAlgebra A (ι → A)) :=
  basisDegreePart (Pi.basisFun A ι).ExteriorAlgebra (exteriorWordDegree w) g
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
theorem residueAlgHom_surjective (f : A →ₐ[F] F) : Function.Surjective f := by sorry
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators Classical
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
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators Classical
variable {F : Type*} [Field F] {n : ℕ}
variable (d : SeparatedOrdinaryData F n)
abbrev Ordinary := MvPolynomial (Fin n) F ⧸ separatedOrdinaryIdeal d.beta d.G d.phi
abbrev SupportPoint :=
  {rho : Fin n → F // ∀ i,d.G.eval ((d.phi i).eval (rho i))=0}
def pointEval (rho : d.SupportPoint) : MvPolynomial (Fin n) F →ₐ[F] F :=
  MvPolynomial.aeval rho.1
theorem pointEval_kills (rho : d.SupportPoint) :
    separatedOrdinaryIdeal d.beta d.G d.phi ≤ RingHom.ker (d.pointEval rho).toRingHom := by sorry
def pointResidue (rho : d.SupportPoint) : d.Ordinary →ₐ[F] F :=
  Ideal.Quotient.liftₐ (separatedOrdinaryIdeal d.beta d.G d.phi)
    (d.pointEval rho) (fun p hp ↦ d.pointEval_kills rho hp)
def pointMaximal (rho : d.SupportPoint) : Ideal d.Ordinary :=
  RingHom.ker (d.pointResidue rho).toRingHom
instance pointMaximal_isMaximal (rho : d.SupportPoint) : (d.pointMaximal rho).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (d.pointResidue rho).toRingHom
    (residueAlgHom_surjective (d.pointResidue rho))
abbrev LocalOrdinary (rho : d.SupportPoint) := Localization.AtPrime (d.pointMaximal rho)
instance localOrdinary_localRing (rho : d.SupportPoint) : IsLocalRing (d.LocalOrdinary rho) :=
  IsLocalization.AtPrime.isLocalRing _ (d.pointMaximal rho)
end
end PaperVerification.Fermion.SeparatedOrdinaryData
namespace PaperVerification.Fermion.SeparatedOrdinaryData
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators Classical
variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedOrdinaryData F n) (rho : d.SupportPoint)
abbrev PointCluster := Set.range (fun i : Fin n ↦ (d.phi i).eval (rho.1 i))
end
end PaperVerification.Fermion.SeparatedOrdinaryData
namespace PaperVerification.Fermion.SeparatedOrdinaryData
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators Classical
variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedOrdinaryData F n) (rho : d.SupportPoint)
local instance FermionLocalCoordinates_clusterDecidableEq : DecidableEq (d.PointCluster rho) :=
  fun a b ↦ Classical.propDecidable (a=b)
def pointCluster (i : Fin n) : d.PointCluster rho :=
  ⟨(d.phi i).eval (rho.1 i),i,rfl⟩
def ramificationOrder (i : Fin n) : ℕ :=
  (d.phi i-C ((d.phi i).eval (rho.1 i))).rootMultiplicity (rho.1 i)
def clusterMultiplicity (c : d.PointCluster rho) : ℕ :=
  d.G.rootMultiplicity c.1
end
end PaperVerification.Fermion.SeparatedOrdinaryData
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Classical BigOperators
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
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped Classical BigOperators
variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedPairedData F n)
variable (rho : d.toSeparatedOrdinaryData.SupportPoint)
abbrev O := d.toSeparatedOrdinaryData
def thetaOrder (i : Fin n) : ℕ := (d.a i).rootMultiplicity (rho.1 i)
def xiOrder (i : Fin n) : ℕ := (d.b i).rootMultiplicity (rho.1 i)
end
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion.SeparatedPairedData
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct BigOperators Classical
variable {F : Type*} [Field F] {n : ℕ}
variable (d : SeparatedPairedData F n)
def phiPolynomial (i : Fin n) : PolynomialRing F n :=
  Polynomial.aeval (MvPolynomial.X i) (d.phi i)
def aPolynomial (i : Fin n) : PolynomialRing F n :=
  Polynomial.aeval (MvPolynomial.X i) (d.a i)
def bPolynomial (i : Fin n) : PolynomialRing F n :=
  Polynomial.aeval (MvPolynomial.X i) (d.b i)
abbrev superIdeal := pairedIdeal d.beta d.phiPolynomial d.aPolynomial d.bPolynomial
def SuperQuotient := PairedQuotient d.beta d.phiPolynomial d.aPolynomial d.bPolynomial
instance superQuotientRing : Ring d.SuperQuotient :=
  inferInstanceAs (Ring (PairedQuotient d.beta d.phiPolynomial d.aPolynomial d.bPolynomial))
instance superQuotientFieldAlgebra : Algebra F d.SuperQuotient :=
  inferInstanceAs (Algebra F (PairedQuotient d.beta d.phiPolynomial d.aPolynomial d.bPolynomial))
@[reducible] instance superQuotientFieldModule : Module F d.SuperQuotient :=
  @Algebra.toModule _ _ _ _ d.superQuotientFieldAlgebra
def superMk : SuperRing F n →ₐ[F] d.SuperQuotient := d.superIdeal.ringCon.mkₐ F
theorem ordinary_scalar_ideal_mem
    (p : PolynomialRing F n)
    (hp : p∈separatedOrdinaryIdeal d.beta d.G d.phi) :
    (Algebra.TensorProduct.includeLeft : PolynomialRing F n →ₐ[F] SuperRing F n) p
      ∈d.superIdeal := by sorry
def ordinaryToSuper : d.toSeparatedOrdinaryData.Ordinary →ₐ[F] d.SuperQuotient :=
  Ideal.Quotient.liftₐ (separatedOrdinaryIdeal d.beta d.G d.phi)
    (d.superMk.comp Algebra.TensorProduct.includeLeft)
    (fun p hp ↦ quotientMk_eq_zero_of_mem (R := F) d.superIdeal _
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
instance ordinarySuperTensorRing (A : Type*) [CommRing A]
    [Algebra d.toSeparatedOrdinaryData.Ordinary A] :
    Ring (A ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient) :=
  Algebra.TensorProduct.instRing (R := d.toSeparatedOrdinaryData.Ordinary)
    (A := A) (B := d.SuperQuotient)
instance polynomialSuperTensorRing (A : Type*) [CommRing A]
    [Algebra (PolynomialRing F n) A] : Ring (A ⊗[PolynomialRing F n] d.SuperQuotient) :=
  Algebra.TensorProduct.instRing (R := PolynomialRing F n) (A := A) (B := d.SuperQuotient)
instance polynomialOrdinarySuperTower :
    IsScalarTower (PolynomialRing F n) d.toSeparatedOrdinaryData.Ordinary d.SuperQuotient :=
  IsScalarTower.of_algebraMap_eq (R := PolynomialRing F n)
    (S := d.toSeparatedOrdinaryData.Ordinary) (A := d.SuperQuotient) (fun p ↦ rfl)
instance fieldOrdinarySuperTower :
    IsScalarTower F d.toSeparatedOrdinaryData.Ordinary d.SuperQuotient :=
  IsScalarTower.of_algebraMap_eq (R := F)
    (S := d.toSeparatedOrdinaryData.Ordinary) (A := d.SuperQuotient)
    (fun c ↦ (d.ordinaryToSuper.commutes c).symm)
local instance (priority := 2250) palomarOrdinarySelfAction : DistribMulAction d.toSeparatedOrdinaryData.Ordinary d.toSeparatedOrdinaryData.Ordinary := (Semiring.toModule (R := d.toSeparatedOrdinaryData.Ordinary)).toDistribMulAction
def LocalSuper (rho : d.toSeparatedOrdinaryData.SupportPoint) :=
  d.toSeparatedOrdinaryData.LocalOrdinary rho ⊗[d.toSeparatedOrdinaryData.Ordinary]
    d.SuperQuotient
instance localSuperRing (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Ring (d.LocalSuper rho) :=
  d.ordinarySuperTensorRing (d.toSeparatedOrdinaryData.LocalOrdinary rho)
instance localSuperLocalAlgebra (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Algebra (d.toSeparatedOrdinaryData.LocalOrdinary rho) (d.LocalSuper rho) :=
  inferInstanceAs (Algebra (d.toSeparatedOrdinaryData.LocalOrdinary rho)
    (d.toSeparatedOrdinaryData.LocalOrdinary rho
      ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient))
@[reducible] instance localSuperLocalModule (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Module (d.toSeparatedOrdinaryData.LocalOrdinary rho) (d.LocalSuper rho) :=
  @Algebra.toModule _ _ _ _ (d.localSuperLocalAlgebra rho)
instance localSuperOrdinaryAlgebra (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Algebra d.toSeparatedOrdinaryData.Ordinary (d.LocalSuper rho) :=
  inferInstanceAs (Algebra d.toSeparatedOrdinaryData.Ordinary
    (d.toSeparatedOrdinaryData.LocalOrdinary rho
      ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient))
@[reducible] instance localSuperOrdinaryModule (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Module d.toSeparatedOrdinaryData.Ordinary (d.LocalSuper rho) :=
  @Algebra.toModule _ _ _ _ (d.localSuperOrdinaryAlgebra rho)
instance localSuperFieldAlgebra (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Algebra F (d.LocalSuper rho) :=
  inferInstanceAs (Algebra F (d.toSeparatedOrdinaryData.LocalOrdinary rho
    ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient))
@[reducible] instance localSuperFieldModule (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    Module F (d.LocalSuper rho) :=
  @Algebra.toModule _ _ _ _ (d.localSuperFieldAlgebra rho)
instance localSuperFieldOrdinaryTower (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    IsScalarTower F d.toSeparatedOrdinaryData.Ordinary (d.LocalSuper rho) :=
  inferInstanceAs (IsScalarTower F d.toSeparatedOrdinaryData.Ordinary
    (d.toSeparatedOrdinaryData.LocalOrdinary rho
      ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient))
instance localSuperFieldLocalTower (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    IsScalarTower F (d.toSeparatedOrdinaryData.LocalOrdinary rho) (d.LocalSuper rho) :=
  inferInstanceAs (IsScalarTower F (d.toSeparatedOrdinaryData.LocalOrdinary rho)
    (d.toSeparatedOrdinaryData.LocalOrdinary rho
      ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient))
instance localSuperOrdinaryLocalTower (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    IsScalarTower d.toSeparatedOrdinaryData.Ordinary
      (d.toSeparatedOrdinaryData.LocalOrdinary rho) (d.LocalSuper rho) :=
  inferInstanceAs (IsScalarTower d.toSeparatedOrdinaryData.Ordinary
    (d.toSeparatedOrdinaryData.LocalOrdinary rho)
    (d.toSeparatedOrdinaryData.LocalOrdinary rho
      ⊗[d.toSeparatedOrdinaryData.Ordinary] d.SuperQuotient))
def localSuperPolynomialBaseEquiv (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    d.LocalSuper rho ≃ₐ[d.toSeparatedOrdinaryData.LocalOrdinary rho]
      d.toSeparatedOrdinaryData.LocalOrdinary rho ⊗[PolynomialRing F n] d.SuperQuotient := by
  letI : TensorProduct.CompatibleSMul (PolynomialRing F n)
      d.toSeparatedOrdinaryData.Ordinary
      (d.toSeparatedOrdinaryData.LocalOrdinary rho) d.SuperQuotient :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective
      (R := PolynomialRing F n) (A := d.toSeparatedOrdinaryData.Ordinary)
      (d.toSeparatedOrdinaryData.LocalOrdinary rho) d.SuperQuotient
      (show Function.Surjective (algebraMap (PolynomialRing F n)
        d.toSeparatedOrdinaryData.Ordinary) from Ideal.Quotient.mk_surjective)
  exact Algebra.TensorProduct.equivOfCompatibleSMul (PolynomialRing F n)
    d.toSeparatedOrdinaryData.Ordinary (d.toSeparatedOrdinaryData.LocalOrdinary rho)
    (d.toSeparatedOrdinaryData.LocalOrdinary rho) d.SuperQuotient
def localAmbientEquiv (rho : d.toSeparatedOrdinaryData.SupportPoint) :
    d.toSeparatedOrdinaryData.LocalOrdinary rho ⊗[PolynomialRing F n] SuperRing F n ≃ₐ[
      d.toSeparatedOrdinaryData.LocalOrdinary rho]
        ClusterExterior (d.toSeparatedOrdinaryData.LocalOrdinary rho) (Fin n) :=
  scalarExteriorBaseChange F (PolynomialRing F n)
    (d.toSeparatedOrdinaryData.LocalOrdinary rho) (OddIndex n)
end
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion.SeparatedPairedData
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct BigOperators Classical
variable {F : Type*} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
variable (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)
def localTensorIdeal :=
  tensorTwoSidedIdeal (PolynomialRing F n) (d.O.LocalOrdinary rho) (SuperRing F n) d.superIdeal
end
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped Classical BigOperators
variable {A ι κ : Type*} [CommRing A] [Fintype ι] [Fintype κ]
  [LinearOrder (ι⊕ι)]
abbrev exteriorTotalPart : ℕ → Submodule A (ClusterExterior A ι) :=
  exteriorWeightedPart (A := A) (fun _ : ι⊕ι ↦ 1)
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators TensorProduct
universe u
def finiteIndexLinearOrder (ι : Type u) [Fintype ι] : LinearOrder ι :=
  LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
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
namespace PaperVerification.Fermion.SeparatedPairedData
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped Classical TensorProduct
variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)
local instance FermionLocalTensorAssembly_sourceOddOrder : LinearOrder (Fin n⊕Fin n) := finiteIndexLinearOrder _
def localClusterLabels :
    d.O.PointCluster rho ≃ Fin (Fintype.card (d.O.PointCluster rho)) :=
  Fintype.equivFin _
def localClusterFamily : ClusterFamilyData F (Fintype.card (d.O.PointCluster rho)) where
  Index c := {i : Fin n // d.O.pointCluster rho i=(d.localClusterLabels rho).symm c}
  finite _ := inferInstance
  beta c i := d.beta i.1
  r c i := d.O.ramificationOrder rho i.1
  s c := d.O.clusterMultiplicity rho ((d.localClusterLabels rho).symm c)
  u c i := d.thetaOrder rho i.1
  v c i := d.xiOrder rho i.1
end
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion.SeparatedPairedData
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical TensorProduct
variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)
local instance FermionLocalTensorBigraded_oddOrder : LinearOrder (Fin n⊕Fin n) := finiteIndexLinearOrder _
local instance FermionLocalTensorBigraded_wholeOddOrder : LinearOrder
    (((Σ c,(d.localClusterFamily rho).Index c))⊕((Σ c,(d.localClusterFamily rho).Index c))) :=
  finiteIndexLinearOrder _
def localSuperExteriorLift :
    ClusterExterior (d.O.LocalOrdinary rho) (Fin n) →ₐ[d.O.LocalOrdinary rho]
      d.LocalSuper rho :=
  (d.localSuperPolynomialBaseEquiv rho).symm.toAlgHom.comp
    ((tensorTwoSidedQuotientEquiv (R := PolynomialRing F n)
      (S := d.O.LocalOrdinary rho) d.superIdeal).symm.toAlgHom.comp
      (((d.localTensorIdeal rho).ringCon.mkₐ (d.O.LocalOrdinary rho)).comp
        (d.localAmbientEquiv rho).symm.toAlgHom))
end
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion.SeparatedPairedData
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped Classical BigOperators
variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)
  (c : Fin (Fintype.card (d.O.PointCluster rho)))
abbrev LocalFactorIndex := (d.localClusterFamily rho).Index c
end
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
open scoped Classical BigOperators
theorem localProductOverSupport {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
    (d : SeparatedPairedData F n) :
    Finite d.O.SupportPoint ∧ (∀ rho : d.O.SupportPoint, Nontrivial (d.LocalSuper rho)) ∧
      Nonempty (d.SuperQuotient ≃ₐ[F] ∀ rho : d.O.SupportPoint, d.LocalSuper rho) := by sorry
end
end PaperVerification.Fermion
namespace PaperVerification.Fermion.SeparatedPairedData
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators TensorProduct
variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)
theorem localSuper_finrank :
    Module.finrank F (d.LocalSuper rho)=
      2^n*(∏ i,d.O.ramificationOrder rho i)*
        ∏ c : Fin (Fintype.card (d.O.PointCluster rho)),
          ((d.localClusterFamily rho).s c).ascFactorial
            (Fintype.card (d.LocalFactorIndex rho c)) := by sorry
end
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion.SeparatedPairedData
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators TensorProduct
variable {F : Type} [Field F] [CharZero F] [IsAlgClosed F] {n : ℕ}
  (d : SeparatedPairedData F n) (rho : d.O.SupportPoint)
local instance FermionLocalHilbert_originalOddOrder : LinearOrder (Fin n⊕Fin n) := finiteIndexLinearOrder _
def localSuperExteriorTotalPart (k : ℕ) : Submodule F (d.LocalSuper rho) :=
  ((exteriorTotalPart (A := d.O.LocalOrdinary rho) (ι := Fin n) k).map
    (d.localSuperExteriorLift rho).toLinearMap).restrictScalars F
theorem localSuper_exterior_hilbert_coefficient (k : ℕ) :
    Module.finrank F (d.localSuperExteriorTotalPart rho k)=
      (Polynomial.C ((∏ i,d.O.ramificationOrder rho i)*
          ∏ c : Fin (Fintype.card (d.O.PointCluster rho)),
            ((d.localClusterFamily rho).s c).ascFactorial
              (Fintype.card (d.LocalFactorIndex rho c)))*
        (1+Polynomial.X)^n : Polynomial ℕ).coeff k := by sorry
end
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion.SeparatedPairedData
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
  (d : SeparatedPairedData F n)
theorem globalSuper_finrank_closed (hn : 0<n) :
    Module.finrank F d.SuperQuotient=
      2^n*(∏ i,(d.phi i).natDegree)*d.G.natDegree.ascFactorial n := by sorry
end
end PaperVerification.Fermion.SeparatedPairedData
namespace PaperVerification.Fermion.SeparatedPairedData
section
set_option maxErrors 1000
set_option Elab.async true
set_option linter.all false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}
  (d : SeparatedPairedData F n)
local instance FermionSeparatedGlobalFormulas_globalExteriorPaperOrder : LinearOrder (OddIndex n) :=
  LinearOrder.lift' Exterior.modeRank Exterior.modeRank_injective
def globalSuperExteriorTotalPart (k : ℕ) : Submodule F d.SuperQuotient :=
  (BasisFiltered.homogeneousPiece (superMonomialBasis (K := F))
    (fun z ↦ z.2.card) k).map d.superMk.toLinearMap
theorem globalSuper_exterior_hilbert_coefficient (hn : 0<n) (k : ℕ) :
    Module.finrank F (d.globalSuperExteriorTotalPart k)=
      (Polynomial.C ((∏ i,(d.phi i).natDegree)*d.G.natDegree.ascFactorial n)*
        (1+Polynomial.X)^n : Polynomial ℕ).coeff k := by sorry
end
end PaperVerification.Fermion.SeparatedPairedData
