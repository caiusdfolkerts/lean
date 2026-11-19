module

public import PaperVerification.AlternatingFormsKoszulHilbert
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# The polynomial action and its actual tensor Koszul complex

The polynomial variables act by multiplication by the given exterior
two-forms.  Evaluation is constructed through the centre of the exterior
algebra.  A componentwise tensor isomorphism then identifies the tensor of
the polynomial free resolution with the displayed exterior Koszul complex.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PaperVerification.AlternatingForms

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

section Restriction

variable {K R A B : Type u} [Field K] [CommRing R] [Algebra K R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [Module K B] [IsScalarTower K R B]

/-- Scalar restriction on the source of a linear equivalence, using the
specified compatible coefficient-field action on its target. -/
def restrictDomainLinearEquiv (e : A ≃ₗ[R] B) :
    ((ModuleCat.restrictScalars (algebraMap K R)).obj (ModuleCat.of R A)) ≃ₗ[K] B where
  toFun := e
  invFun := e.symm
  left_inv := e.left_inv
  right_inv := e.right_inv
  map_add' := e.map_add
  map_smul' c a := by
    change e (algebraMap K R c • (show A from a)) = c • e (show A from a)
    exact (e.map_smul (algebraMap K R c) (show A from a)).trans
      (algebraMap_smul R c (e (show A from a)))

@[simp] theorem restrictDomainLinearEquiv_apply (e : A ≃ₗ[R] B) (a : A) :
    restrictDomainLinearEquiv (K := K) e a = e a := rfl

end Restriction

section Action

variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

def centralTwoForm (f : ⋀[K]^2 M) : Subalgebra.center K (ExteriorAlgebra K M) :=
  ⟨f, (Subalgebra.mem_center_iff).mpr (fun a => (twoForm_commute f a).eq.symm)⟩

/-- Genuine polynomial evaluation `u ↦ f`, `v ↦ g` into the exterior algebra. -/
def quadraticPolynomialEvaluation (f g : ⋀[K]^2 M) :
    PairPolynomial K →ₐ[K] ExteriorAlgebra K M :=
  (Subalgebra.center K (ExteriorAlgebra K M)).val.comp
    (MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then centralTwoForm f else centralTwoForm g))

@[simp] theorem quadraticPolynomialEvaluation_X_zero (f g : ⋀[K]^2 M) :
    quadraticPolynomialEvaluation f g (MvPolynomial.X 0) = (f : ExteriorAlgebra K M) := by
  simp [quadraticPolynomialEvaluation, centralTwoForm]

@[simp] theorem quadraticPolynomialEvaluation_X_one (f g : ⋀[K]^2 M) :
    quadraticPolynomialEvaluation f g (MvPolynomial.X 1) = (g : ExteriorAlgebra K M) := by
  simp [quadraticPolynomialEvaluation, centralTwoForm]

/-- A type synonym records which pair determines the polynomial-module
structure.  Its elements are exactly the original exterior-algebra elements. -/
def ExteriorPairModule (f g : ⋀[K]^2 M) := ExteriorAlgebra K M

instance (f g : ⋀[K]^2 M) : AddCommGroup (ExteriorPairModule f g) :=
  inferInstanceAs (AddCommGroup (ExteriorAlgebra K M))

instance (f g : ⋀[K]^2 M) : Module K (ExteriorPairModule f g) :=
  inferInstanceAs (Module K (ExteriorAlgebra K M))

def exteriorPairModuleEquiv (f g : ⋀[K]^2 M) :
    ExteriorPairModule f g ≃ₗ[K] ExteriorAlgebra K M :=
  LinearEquiv.refl K (ExteriorAlgebra K M)

instance (f g : ⋀[K]^2 M) : Module (PairPolynomial K) (ExteriorPairModule f g) :=
  Module.compHom (ExteriorAlgebra K M) (quadraticPolynomialEvaluation f g).toRingHom

theorem exteriorPair_smul (f g : ⋀[K]^2 M) (p : PairPolynomial K)
    (a : ExteriorPairModule f g) :
    p • a = (quadraticPolynomialEvaluation f g p) * (exteriorPairModuleEquiv f g a) := rfl

instance (f g : ⋀[K]^2 M) : IsScalarTower K (PairPolynomial K) (ExteriorPairModule f g) where
  smul_assoc c p a := by
    change quadraticPolynomialEvaluation f g (c • p) * (exteriorPairModuleEquiv f g a) =
      c • (quadraticPolynomialEvaluation f g p * (exteriorPairModuleEquiv f g a))
    rw [map_smul, smul_mul_assoc]

instance (f g : ⋀[K]^2 M) : SMulCommClass K (PairPolynomial K) (ExteriorPairModule f g) where
  smul_comm c p a := by
    change c • (quadraticPolynomialEvaluation f g p * (exteriorPairModuleEquiv f g a)) =
      quadraticPolynomialEvaluation f g p * (c • (exteriorPairModuleEquiv f g a))
    exact (mul_smul_comm _ _ _).symm

@[simp] theorem exteriorPair_X_zero_smul (f g : ⋀[K]^2 M) (a : ExteriorPairModule f g) :
    MvPolynomial.X (R := K) (0 : Fin 2) • a =
      (f : ExteriorAlgebra K M) * (exteriorPairModuleEquiv f g a) := by
  rw [exteriorPair_smul, quadraticPolynomialEvaluation_X_zero]

@[simp] theorem exteriorPair_X_one_smul (f g : ⋀[K]^2 M) (a : ExteriorPairModule f g) :
    MvPolynomial.X (R := K) (1 : Fin 2) • a =
      (g : ExteriorAlgebra K M) * (exteriorPairModuleEquiv f g a) := by
  rw [exteriorPair_smul, quadraticPolynomialEvaluation_X_one]

def exteriorPolynomialTensorComplex (f g : ⋀[K]^2 M) :
    ChainComplex (ModuleCat (PairPolynomial K)) ℕ :=
  ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat (PairPolynomial K))).obj
    (ModuleCat.of (PairPolynomial K) (ExteriorPairModule f g))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (pairPolynomialResolution K).complex)

def exteriorPolynomialTensorComplexOverK (f g : ⋀[K]^2 M) :
    ChainComplex (ModuleCat K) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap K (PairPolynomial K))).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (exteriorPolynomialTensorComplex f g)

def exteriorPairComplex (f g : ⋀[K]^2 M) : ChainComplex (ModuleCat K) ℕ :=
  pairComplex (twoFormMultiplication f) (twoFormMultiplication g)
    (twoFormMultiplication_commute f g)

instance exteriorPairTerm_subsingleton (f g : ⋀[K]^2 M) (n : ℕ) :
    Subsingleton ((exteriorPairComplex f g).X (n+3)) := by
  change Subsingleton (⊥ : Submodule K (ExteriorAlgebra K M))
  infer_instance

instance exteriorTensorTerm_subsingleton (f g : ⋀[K]^2 M) (n : ℕ) :
    Subsingleton ((exteriorPolynomialTensorComplexOverK f g).X (n+3)) := by
  change Subsingleton (ExteriorPairModule f g ⊗[PairPolynomial K]
    (⊥ : Submodule (PairPolynomial K) (PairPolynomial K)))
  infer_instance

def exteriorTensorTermEquiv (f g : ⋀[K]^2 M) : (n : ℕ) →
    (exteriorPolynomialTensorComplexOverK f g).X n ≃ₗ[K] (exteriorPairComplex f g).X n
  | 0 => (restrictDomainLinearEquiv (K := K)
      (TensorProduct.rid (PairPolynomial K) (ExteriorPairModule f g))).trans
        (exteriorPairModuleEquiv f g)
  | 1 => (restrictDomainLinearEquiv (K := K)
      ((TensorProduct.prodRight (PairPolynomial K) (PairPolynomial K)
        (ExteriorPairModule f g) (PairPolynomial K) (PairPolynomial K)).trans
          ((TensorProduct.rid (PairPolynomial K) (ExteriorPairModule f g)).prodCongr
            (TensorProduct.rid (PairPolynomial K) (ExteriorPairModule f g))))).trans
        ((exteriorPairModuleEquiv f g).prodCongr (exteriorPairModuleEquiv f g))
  | 2 => (restrictDomainLinearEquiv (K := K)
      (TensorProduct.rid (PairPolynomial K) (ExteriorPairModule f g))).trans
        (exteriorPairModuleEquiv f g)
  | _ + 3 => LinearEquiv.ofSubsingleton _ _

@[simp] theorem exteriorTensorTermEquiv_zero_tmul (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (p : PairPolynomial K) :
    exteriorTensorTermEquiv f g 0 (a ⊗ₜ[PairPolynomial K] p) = p • a := rfl

@[simp] theorem exteriorTensorTermEquiv_one_tmul (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (p : PairPolynomial K × PairPolynomial K) :
    exteriorTensorTermEquiv f g 1 (a ⊗ₜ[PairPolynomial K] p) = (p.1 • a, p.2 • a) := rfl

@[simp] theorem exteriorTensorTermEquiv_two_tmul (f g : ⋀[K]^2 M)
    (a : ExteriorPairModule f g) (p : PairPolynomial K) :
    exteriorTensorTermEquiv f g 2 (a ⊗ₜ[PairPolynomial K] p) = p • a := rfl

theorem exteriorTensorTermEquiv_comm (f g : ⋀[K]^2 M) (n : ℕ) :
    (exteriorTensorTermEquiv f g (n + 1)).toModuleIso.hom ≫
        (exteriorPairComplex f g).d (n + 1) n =
      (exteriorPolynomialTensorComplexOverK f g).d (n + 1) n ≫
        (exteriorTensorTermEquiv f g n).toModuleIso.hom := by
  cases n with
  | zero =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    refine TensorProduct.inductionOn (R := PairPolynomial K) (M := ExteriorPairModule f g)
      (N := PairPolynomial K × PairPolynomial K) z ?_ ?_
    · intro a p
      change (f : ExteriorAlgebra K M) * exteriorPairModuleEquiv f g (p.1 • a) +
          (g : ExteriorAlgebra K M) * exteriorPairModuleEquiv f g (p.2 • a) =
        exteriorPairModuleEquiv f g ((MvPolynomial.X 0 * p.1 + MvPolynomial.X 1 * p.2) • a)
      simp only [add_smul, mul_smul, map_add,
        exteriorPair_X_zero_smul, exteriorPair_X_one_smul,
        exteriorPairModuleEquiv, LinearEquiv.refl_apply] <;> rfl
    · intro x y hx hy
      rw [map_add,map_add,hx,hy]
  | succ n =>
    cases n with
    | zero =>
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      refine TensorProduct.inductionOn (R := PairPolynomial K) (M := ExteriorPairModule f g)
        (N := PairPolynomial K) z ?_ ?_
      · intro a p
        change (-((g : ExteriorAlgebra K M) * exteriorPairModuleEquiv f g (p • a)),
            (f : ExteriorAlgebra K M) * exteriorPairModuleEquiv f g (p • a)) =
          (exteriorPairModuleEquiv f g (-(MvPolynomial.X 1 * p) • a),
            exteriorPairModuleEquiv f g ((MvPolynomial.X 0 * p) • a))
        simp only [neg_smul, mul_smul, map_neg,
          exteriorPair_X_one_smul, exteriorPair_X_zero_smul,
          exteriorPairModuleEquiv, LinearEquiv.refl_apply] <;> rfl
      · intro x y hx hy
        rw [map_add,map_add,hx,hy]
    | succ n =>
      have hz : IsZero ((exteriorPolynomialTensorComplexOverK f g).X (n + 3)) :=
        ModuleCat.isZero_of_subsingleton _
      exact hz.eq_of_src _ _

/-- The tensor of the actual polynomial free resolution is isomorphic to
the actual exterior two-form Koszul complex, with every differential checked. -/
def exteriorTensorComplexIso (f g : ⋀[K]^2 M) :
    exteriorPolynomialTensorComplexOverK f g ≅ exteriorPairComplex f g :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (exteriorTensorTermEquiv f g n).toModuleIso) (by
      intro i j hij
      change j + 1 = i at hij
      subst i
      exact exteriorTensorTermEquiv_comm f g j)

/-- Coefficient-field restriction commutes with homology because it is an
exact functor on the genuine module category. -/
def exteriorTensorHomologyRestrictionIso (f g : ⋀[K]^2 M) (i : ℕ) :
    (exteriorPolynomialTensorComplexOverK f g).homology i ≅
      (ModuleCat.restrictScalars (algebraMap K (PairPolynomial K))).obj
        ((exteriorPolynomialTensorComplex f g).homology i) :=
  ((exteriorPolynomialTensorComplex f g).sc i).mapHomologyIso
    (ModuleCat.restrictScalars (algebraMap K (PairPolynomial K)))

/-- The actual derived tensor vector space, with coefficient scalars
restricted along the inclusion `K → K[u,v]`. -/
def exteriorPolynomialTor (f g : ⋀[K]^2 M) (i : ℕ) : ModuleCat K :=
  (ModuleCat.restrictScalars (algebraMap K (PairPolynomial K))).obj
    (((Tor (ModuleCat (PairPolynomial K)) i).obj
      (ModuleCat.of (PairPolynomial K) (ExteriorPairModule f g))).obj
        (ModuleCat.of (PairPolynomial K) (PairResidue K)))

/-- The derived-functor comparison is now specialized to the literal action
by the two exterior forms; the isomorphism introduces no homology assumption. -/
def exteriorPolynomialTorIso (f g : ⋀[K]^2 M) (i : ℕ) :
    exteriorPolynomialTor f g i ≅ (exteriorPairComplex f g).homology i :=
  (ModuleCat.restrictScalars (algebraMap K (PairPolynomial K))).mapIso
      (pairPolynomialTorIso K (ModuleCat.of (PairPolynomial K) (ExteriorPairModule f g)) i) ≪≫
    (exteriorTensorHomologyRestrictionIso f g i).symm ≪≫
    HomologicalComplex.homologyMapIso (exteriorTensorComplexIso f g) i

theorem exteriorPolynomialTor_isZero_above (f g : ⋀[K]^2 M) {i : ℕ} (hi : 2 < i) :
    IsZero (exteriorPolynomialTor f g i) :=
  (pairComplex_isZero_homology _ _ _ hi).of_iso (exteriorPolynomialTorIso f g i)

end Action

end PaperVerification.AlternatingForms
