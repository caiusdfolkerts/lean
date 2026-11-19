module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# The actual two-variable Koszul resolution

The resolution in this file is over the genuine polynomial ring `K[u,v]`.
Its terms and maps are explicit.  The middle exactness proof uses primality
of the variable `u`; no homological assertion is introduced as an axiom.
The resulting `ProjectiveResolution` computes Mathlib's derived tensor
functor, and therefore supplies the comparison required to call the
homology in Proposition 5.4 graded Betti spaces.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.AlternatingForms

open CategoryTheory CategoryTheory.Limits

section PairComplex

universe u v

variable {R : Type u} [Ring R] {A : Type v} [AddCommGroup A] [Module R A]

/-- The first differential for two commuting operators. -/
def pairFirstDifferential (F G : Module.End R A) : A × A →ₗ[R] A :=
  F.coprod G

/-- The second differential, with the usual Koszul sign. -/
def pairSecondDifferential (F G : Module.End R A) : A →ₗ[R] A × A :=
  (-G).prod F

@[simp] theorem pairFirstDifferential_apply (F G : Module.End R A) (a : A × A) :
    pairFirstDifferential F G a = F a.1 + G a.2 := rfl

@[simp] theorem pairSecondDifferential_apply (F G : Module.End R A) (a : A) :
    pairSecondDifferential F G a = (-G a, F a) := rfl

theorem pairDifferentials_comp (F G : Module.End R A) (hFG : Commute F G) :
    (pairFirstDifferential F G).comp (pairSecondDifferential F G) = 0 := by
  ext a
  have h := congrArg (fun T : Module.End R A => T a) hFG.eq
  change F (G a) = G (F a) at h
  change F (-G a) + G (F a) = 0
  rw [map_neg, h, neg_add_cancel]

/-- Terms of a length-two complex, with an actual zero module thereafter. -/
def pairTerm (R : Type u) [Ring R] (A : Type v) [AddCommGroup A] [Module R A] :
    ℕ → ModuleCat.{v} R
  | 0 => ModuleCat.of R A
  | 1 => ModuleCat.of R (A × A)
  | 2 => ModuleCat.of R A
  | _ + 3 => ModuleCat.of R (⊥ : Submodule R A)

def pairDifferential (F G : Module.End R A) :
    (n : ℕ) → pairTerm R A (n + 1) ⟶ pairTerm R A n
  | 0 => ModuleCat.ofHom (pairFirstDifferential F G)
  | 1 => ModuleCat.ofHom (pairSecondDifferential F G)
  | _ + 2 => 0

theorem pairDifferential_comp (F G : Module.End R A) (hFG : Commute F G) (n : ℕ) :
    pairDifferential F G (n + 1) ≫ pairDifferential F G n = 0 := by
  cases n with
  | zero => exact ModuleCat.hom_ext (pairDifferentials_comp F G hFG)
  | succ n =>
    change (0 : pairTerm R A (n+3) ⟶ pairTerm R A (n+2)) ≫
      pairDifferential F G (n+1)=0
    exact CategoryTheory.Limits.zero_comp

/-- The literal Koszul complex of two commuting operators. -/
def pairComplex (F G : Module.End R A) (hFG : Commute F G) :
    ChainComplex (ModuleCat.{v} R) ℕ :=
  ChainComplex.of (pairTerm R A) (pairDifferential F G)
    (pairDifferential_comp F G hFG)

@[simp] theorem pairComplex_X (F G : Module.End R A) (hFG : Commute F G) (n : ℕ) :
    (pairComplex F G hFG).X n = pairTerm R A n := rfl

@[simp] theorem pairComplex_d (F G : Module.End R A) (hFG : Commute F G) (n : ℕ) :
    (pairComplex F G hFG).d (n + 1) n = pairDifferential F G n := by
  simp [pairComplex]

theorem pairComplex_isZero_X (F G : Module.End R A) (hFG : Commute F G)
    {n : ℕ} (hn : 2 < n) : IsZero ((pairComplex F G hFG).X n) := by
  have hn' : n = (n - 3) + 3 := by omega
  rw [hn']
  change IsZero (ModuleCat.of R (⊥ : Submodule R A))
  exact ModuleCat.isZero_of_subsingleton _

theorem pairComplex_isZero_homology (F G : Module.End R A) (hFG : Commute F G)
    {n : ℕ} (hn : 2 < n) : IsZero ((pairComplex F G hFG).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero (pairComplex_isZero_X F G hFG hn)).isZero_homology

end PairComplex

section PolynomialResolution

universe u

variable (K : Type u) [Field K]

abbrev PairPolynomial := MvPolynomial (Fin 2) K

def pairPolynomialFirst : Module.End (PairPolynomial K) (PairPolynomial K) :=
  LinearMap.mulLeft (PairPolynomial K) (MvPolynomial.X 0)

def pairPolynomialSecond : Module.End (PairPolynomial K) (PairPolynomial K) :=
  LinearMap.mulLeft (PairPolynomial K) (MvPolynomial.X 1)

theorem pairPolynomial_commute : Commute (pairPolynomialFirst K) (pairPolynomialSecond K) := by
  change pairPolynomialFirst K * pairPolynomialSecond K =
    pairPolynomialSecond K * pairPolynomialFirst K
  apply LinearMap.ext
  intro p
  change MvPolynomial.X 0 * (MvPolynomial.X 1 * p) =
    MvPolynomial.X 1 * (MvPolynomial.X 0 * p)
  ring

/-- The maximal ideal `(u,v)` of the polynomial ring, not an abstract residue field. -/
def pairResidueIdeal : Ideal (PairPolynomial K) :=
  Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1}

abbrev PairResidue := PairPolynomial K ⧸ pairResidueIdeal K

theorem pairResidueIdeal_eq_ker_constantCoeff :
    pairResidueIdeal K = RingHom.ker (MvPolynomial.constantCoeff : PairPolynomial K →+* K) := by
  classical
  have hset : ({MvPolynomial.X 0, MvPolynomial.X 1} : Set (PairPolynomial K)) =
      MvPolynomial.X '' (Set.univ : Set (Fin 2)) := by
    ext p
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, Set.mem_univ _, rfl⟩
      · exact ⟨1, Set.mem_univ _, rfl⟩
    · rintro ⟨i, _, rfl⟩
      fin_cases i <;> simp
  unfold pairResidueIdeal
  rw [hset, MvPolynomial.span_X_image_eq_ker_aeval_ite_mem]
  ext p
  simp only [RingHom.mem_ker, Set.compl_univ, Set.mem_empty_iff_false, if_false,
    MvPolynomial.aeval_zero', MvPolynomial.algebraMap_eq, MvPolynomial.C_eq_zero]

/-- The residue in the displayed resolution is precisely the coefficient
field with both variables acting as zero. -/
def pairConstantCoefficient : PairPolynomial K →ₐ[K] K :=
  { MvPolynomial.constantCoeff with
    commutes' := fun c => MvPolynomial.constantCoeff_C _ c }

theorem pairConstantCoefficient_surjective :
    Function.Surjective (pairConstantCoefficient K) := by
  intro c
  exact ⟨MvPolynomial.C c, by simp [pairConstantCoefficient]⟩

theorem pairResidueIdeal_eq_ker_pairConstantCoefficient :
    pairResidueIdeal K=RingHom.ker (pairConstantCoefficient K) :=
  pairResidueIdeal_eq_ker_constantCoeff K

noncomputable def pairResidueEquivField : PairResidue K ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K (pairResidueIdeal_eq_ker_pairConstantCoefficient K)).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := pairConstantCoefficient K) (pairConstantCoefficient_surjective K))

@[simp] theorem pairResidueEquivField_mk (p : PairPolynomial K) :
    pairResidueEquivField K (Ideal.Quotient.mk (pairResidueIdeal K) p) =
      MvPolynomial.constantCoeff p := by
  rfl

/-- The coefficient field equipped with the actual origin action of the
polynomial ring. The synonym records this particular polynomial-module
structure without replacing the underlying field. -/
def PairOriginModule := K

instance : AddCommGroup (PairOriginModule K) :=
  inferInstanceAs (AddCommGroup K)

instance : Module (PairPolynomial K) (PairOriginModule K) :=
  Module.compHom K (pairConstantCoefficient K).toRingHom

def pairOriginValue (a : PairOriginModule K) : K := a

@[simp] theorem pairOriginValue_smul (p : PairPolynomial K) (a : PairOriginModule K) :
    pairOriginValue K (p • a) = MvPolynomial.constantCoeff p * pairOriginValue K a := rfl

/-- The augmentation quotient and the coefficient field are isomorphic as
modules over the original polynomial ring, with its origin action. -/
def pairResidueOriginEquiv : PairResidue K ≃ₗ[PairPolynomial K] PairOriginModule K where
  toFun := pairResidueEquivField K
  invFun := (pairResidueEquivField K).symm
  left_inv := (pairResidueEquivField K).left_inv
  right_inv := (pairResidueEquivField K).right_inv
  map_add' := (pairResidueEquivField K).map_add
  map_smul' p x := by
    change pairResidueEquivField K (Ideal.Quotient.mk (pairResidueIdeal K) p * x) =
      pairConstantCoefficient K p * pairResidueEquivField K x
    rw [map_mul, pairResidueEquivField_mk]
    rfl

@[simp] theorem pairResidueOriginEquiv_mk (p : PairPolynomial K) :
    pairResidueOriginEquiv K (Ideal.Quotient.mk (pairResidueIdeal K) p) =
      ((MvPolynomial.constantCoeff : PairPolynomial K →+* K) p : PairOriginModule K) :=
  pairResidueEquivField_mk K p

def pairPolynomialComplex : ChainComplex (ModuleCat (PairPolynomial K)) ℕ :=
  pairComplex (pairPolynomialFirst K) (pairPolynomialSecond K) (pairPolynomial_commute K)

theorem pairPolynomial_range_first :
    LinearMap.range
      (pairFirstDifferential (pairPolynomialFirst K) (pairPolynomialSecond K)) =
      pairResidueIdeal K := by
  ext p
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    apply Ideal.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    change a * MvPolynomial.X 0 + b * MvPolynomial.X 1 =
      MvPolynomial.X 0 * a + MvPolynomial.X 1 * b
    ring
  · intro hp
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hp
    refine ⟨(a, b), ?_⟩
    change MvPolynomial.X 0 * a + MvPolynomial.X 1 * b = p
    rw [← hab]
    ring

/-- Exactness of `P → P² → P` for the independent variables of `P=K[u,v]`. -/
theorem pairPolynomial_exact :
    Function.Exact
      (pairSecondDifferential (pairPolynomialFirst K) (pairPolynomialSecond K))
      (pairFirstDifferential (pairPolynomialFirst K) (pairPolynomialSecond K)) := by
  intro a
  constructor
  · intro ha
    change MvPolynomial.X 0 * a.1 + MvPolynomial.X 1 * a.2 = 0 at ha
    have hu : (MvPolynomial.X (R := K) (0 : Fin 2)) ≠ 0 := MvPolynomial.X_ne_zero 0
    have hdiv : (MvPolynomial.X (R := K) (0 : Fin 2)) ∣ MvPolynomial.X 1 * a.2 := by
      refine ⟨-a.1, ?_⟩
      linear_combination ha
    have hb : (MvPolynomial.X (R := K) (0 : Fin 2)) ∣ a.2 := by
      rcases (MvPolynomial.prime_X (R := K) (i := (0 : Fin 2))).dvd_or_dvd hdiv with h | h
      · exact False.elim (by simpa using h)
      · exact h
    obtain ⟨c, hc⟩ := hb
    have hac : a.1 = -(MvPolynomial.X 1 * c) := by
      apply mul_left_cancel₀ hu
      rw [hc] at ha
      linear_combination ha
    refine ⟨c, ?_⟩
    apply Prod.ext
    · exact hac.symm
    · exact hc.symm
  · rintro ⟨c, rfl⟩
    exact congrArg (fun T : PairPolynomial K →ₗ[PairPolynomial K] PairPolynomial K => T c)
      (pairDifferentials_comp _ _ (pairPolynomial_commute K))

theorem pairPolynomial_second_injective :
    Function.Injective
      (pairSecondDifferential (pairPolynomialFirst K) (pairPolynomialSecond K)) := by
  intro a b hab
  have h := congrArg Prod.snd hab
  exact mul_left_cancel₀ (MvPolynomial.X_ne_zero (R := K) (0 : Fin 2)) h

theorem pairPolynomial_exactAt_succ (n : ℕ) :
    (pairPolynomialComplex K).ExactAt (n + 1) := by
  cases n with
  | zero =>
    rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range
      (pairSecondDifferential (pairPolynomialFirst K) (pairPolynomialSecond K)) =
      LinearMap.ker (pairFirstDifferential (pairPolynomialFirst K) (pairPolynomialSecond K))
    exact (LinearMap.exact_iff.mp (pairPolynomial_exact K)).symm
  | succ n =>
    cases n with
    | zero =>
      rw [HomologicalComplex.exactAt_iff' _ 3 2 1 (by simp) (by simp),
        ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
      intro a
      constructor
      · intro ha
        have ha0 : a = 0 := pairPolynomial_second_injective K
          (ha.trans (map_zero _).symm)
        exact ⟨0, ha0.symm⟩
      · rintro ⟨b, rfl⟩
        exact map_zero _
    | succ n =>
      exact HomologicalComplex.ExactAt.of_isZero
        (pairComplex_isZero_X _ _ _ (by omega))

def pairPolynomialAugmentation :
    (pairPolynomialComplex K).X 0 ⟶ ModuleCat.of (PairPolynomial K) (PairResidue K) :=
  ModuleCat.ofHom (pairResidueIdeal K).mkQ

theorem pairPolynomial_d_augmentation :
    (pairPolynomialComplex K).d 1 0 ≫ pairPolynomialAugmentation K = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.range_le_ker_iff.mp
  change LinearMap.range
    (pairFirstDifferential (pairPolynomialFirst K) (pairPolynomialSecond K)) ≤
      LinearMap.ker (pairResidueIdeal K).mkQ
  rw [Submodule.ker_mkQ]
  exact le_of_eq (pairPolynomial_range_first K)

theorem pairPolynomial_augmentation_exact :
    (ShortComplex.mk _ _ (pairPolynomial_d_augmentation K)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range
      (pairFirstDifferential (pairPolynomialFirst K) (pairPolynomialSecond K)) =
    LinearMap.ker (pairResidueIdeal K).mkQ
  rw [Submodule.ker_mkQ, pairPolynomial_range_first]

instance pairPolynomial_augmentation_epi : Epi (pairPolynomialAugmentation K) :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

/-- A genuine free resolution of `K[u,v]/(u,v)` with exactly three nonzero terms. -/
noncomputable def pairPolynomialResolution :
    ProjectiveResolution (ModuleCat.of (PairPolynomial K) (PairResidue K)) where
  complex := pairPolynomialComplex K
  projective n := by
    cases n with
    | zero =>
      change Projective (ModuleCat.of (PairPolynomial K) (PairPolynomial K))
      infer_instance
    | succ n =>
      cases n with
      | zero =>
        change Projective (ModuleCat.of (PairPolynomial K) (PairPolynomial K × PairPolynomial K))
        infer_instance
      | succ n =>
        cases n with
        | zero =>
          change Projective (ModuleCat.of (PairPolynomial K) (PairPolynomial K))
          infer_instance
        | succ n => exact (pairComplex_isZero_X _ _ _ (by omega)).projective
  π := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨pairPolynomialAugmentation K, pairPolynomial_d_augmentation K⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk _ _ (pairPolynomial_d_augmentation K)).Exact ∧
          Epi (pairPolynomialAugmentation K)
        exact ⟨pairPolynomial_augmentation_exact K, inferInstance⟩
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact pairPolynomial_exactAt_succ K n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- Derived tensor is computed by the displayed free resolution.  The target
is the actual homology of `E ⊗_P K(u,v)`, not a stipulated Betti dimension. -/
noncomputable def pairPolynomialTorIso (E : ModuleCat (PairPolynomial K)) (i : ℕ) :
    (((Tor (ModuleCat (PairPolynomial K)) i).obj E).obj
        (ModuleCat.of (PairPolynomial K) (PairResidue K))) ≅
      ((((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat (PairPolynomial K))).obj E).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (pairPolynomialResolution K).complex).homology i :=
  (pairPolynomialResolution K).isoLeftDerivedObj _ i

/-- There are no later derived tensor terms for any polynomial module,
because the actual displayed free resolution stops in degree two. -/
theorem pairPolynomialTor_isZero_above (E : ModuleCat (PairPolynomial K))
    {i : ℕ} (hi : 2 < i) :
    IsZero ((((Tor (ModuleCat (PairPolynomial K)) i).obj E).obj
      (ModuleCat.of (PairPolynomial K) (PairResidue K)))) := by
  let F := (CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat (PairPolynomial K))).obj E
  have hterm : IsZero (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (pairPolynomialResolution K).complex).X i) :=
    F.map_isZero (pairComplex_isZero_X (pairPolynomialFirst K)
      (pairPolynomialSecond K) (pairPolynomial_commute K) hi)
  exact (HomologicalComplex.ExactAt.of_isZero hterm).isZero_homology.of_iso
    (pairPolynomialTorIso K E i)

end PolynomialResolution

end PaperVerification.AlternatingForms
