module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# Triangular polynomial coordinates

A change of coordinates `X i ↦ X i + p i` is an actual polynomial algebra
isomorphism when every variable occurring in `p i` has smaller natural-number
weight. Its inverse is constructed by well-founded recursion, rather than
assumed from a Jacobian condition. Consequently, any subset of these
coordinates cuts out an affine space, with its full scheme-theoretic ideal.

This is the algebraic elimination step needed for positive-weight attracting
charts. No assertion about an attracting chart or its smoothness is included
in the hypotheses by definition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.TriangularPolynomialCoordinates

open MvPolynomial

variable {R σ : Type*} [CommRing R]

local instance : DecidableEq σ := Classical.decEq σ

lemma aeval_eq_of_eq_on_vars {A : Type*} [CommRing A] [Algebra R A]
    (p : MvPolynomial σ R) {g h : σ → A}
    (hh : ∀ i ∈ p.vars, g i = h i) : aeval g p = aeval h p :=
  eval₂Hom_congr' rfl (fun i hi _ => hh i hi) rfl

/-- Recursive inverse coordinates. Only smaller weights are evaluated
recursively; values on all other variables are irrelevant under triangularity. -/
def inverseCoordinate (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (i : σ) : MvPolynomial σ R :=
  X i - aeval (fun j => if h : w j < w i then inverseCoordinate w p j else 0) (p i)
termination_by w i

/-- The forward substitution associated to a triangular family. -/
def substitution (p : σ → MvPolynomial σ R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval (fun i => X i + p i)

@[simp] theorem substitution_X (p : σ → MvPolynomial σ R) (i : σ) :
    substitution p (X i) = X i + p i := by simp [substitution]

theorem substitution_inverseCoordinate (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (hp : ∀ i j, j ∈ (p i).vars → w j < w i) (i : σ) :
    substitution p (inverseCoordinate w p i) = X i := by
  induction h : w i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [inverseCoordinate, map_sub, substitution_X, comp_aeval_apply]
    have he : aeval
        (fun j => substitution p (if h : w j < w i then inverseCoordinate w p j else 0))
        (p i) = p i := by
      calc
        _ = aeval (fun j => X j) (p i) := by
          apply aeval_eq_of_eq_on_vars
          intro j hj
          rw [dite_eq_left (hp i j hj)]
          exact ih (w j) (h ▸ hp i j hj) j rfl
        _ = p i := aeval_X_left_apply (p i)
    rw [he]
    ring

theorem inverseCoordinate_substitution (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (hp : ∀ i j, j ∈ (p i).vars → w j < w i) (i : σ) :
    aeval (inverseCoordinate w p) (substitution p (X i)) = X i := by
  rw [substitution_X, map_add, aeval_X, inverseCoordinate]
  have he : aeval
      (fun j => if h : w j < w i then inverseCoordinate w p j else 0) (p i) =
      aeval (inverseCoordinate w p) (p i) := by
    apply aeval_eq_of_eq_on_vars
    intro j hj
    rw [dite_eq_left (hp i j hj)]
  rw [he]
  ring

/-- An actual polynomial algebra automorphism, including both inverse laws. -/
def triangularEquiv (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (hp : ∀ i j, j ∈ (p i).vars → w j < w i) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (substitution p) (aeval (inverseCoordinate w p))
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simpa only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply] using
        substitution_inverseCoordinate w p hp i)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
        inverseCoordinate_substitution w p hp i)

@[simp] theorem triangularEquiv_X (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (hp : ∀ i j, j ∈ (p i).vars → w j < w i) (i : σ) :
    triangularEquiv w p hp (X i) = X i + p i := by
  exact substitution_X p i

/-- Set the coordinates in `s` equal to zero and retain the others. -/
def eraseCoordinates (s : Set σ) :
    MvPolynomial σ R →ₐ[R] MvPolynomial {i // i ∉ s} R := by
  classical
  exact aeval (fun i => if h : i ∉ s then X ⟨i,h⟩ else 0)

@[simp] theorem eraseCoordinates_rename (s : Set σ)
    (q : MvPolynomial {i // i ∉ s} R) :
    eraseCoordinates s (rename Subtype.val q) = q := by
  classical
  have h : (eraseCoordinates (R := R) s).comp (rename Subtype.val) = AlgHom.id R _ := by
    ext i
    simp [eraseCoordinates, i.property]
  exact DFunLike.congr_fun h q

theorem eraseCoordinates_surjective (s : Set σ) :
    Function.Surjective (eraseCoordinates (R := R) s) :=
  fun q => ⟨rename Subtype.val q, eraseCoordinates_rename s q⟩

theorem ker_eraseCoordinates (s : Set σ) :
    RingHom.ker (eraseCoordinates (R := R) s).toRingHom =
      Ideal.span (X '' s : Set (MvPolynomial σ R)) := by
  classical
  rw [span_X_image_eq_ker_aeval_ite_mem]
  ext q
  rw [RingHom.mem_ker, RingHom.mem_ker]
  have he : (rename Subtype.val : MvPolynomial {i // i ∉ s} R →ₐ[R] MvPolynomial σ R)
      (eraseCoordinates s q) = aeval (fun i => if i ∈ sᶜ then X i else 0) q := by
    have h : (rename Subtype.val).comp (eraseCoordinates (R := R) s) =
        aeval (fun i => if i ∈ sᶜ then X i else 0) := by
      ext i
      simp only [AlgHom.comp_apply, eraseCoordinates, aeval_X]
      split_ifs <;> simp_all
    exact DFunLike.congr_fun h q
  rw [← he]
  constructor
  · intro hz
    change eraseCoordinates s q = 0 at hz
    rw [hz,map_zero]
  · intro hz
    change eraseCoordinates s q = 0
    apply rename_injective Subtype.val Subtype.val_injective
    simpa only [map_zero] using hz

/-- The coordinate ideal has the expected polynomial quotient, over any
commutative coefficient ring. -/
def coordinateQuotientEquiv (s : Set σ) :
    (MvPolynomial σ R ⧸ Ideal.span (X '' s : Set (MvPolynomial σ R))) ≃ₐ[R]
      MvPolynomial {i // i ∉ s} R :=
  (Ideal.quotientEquivAlgOfEq R (ker_eraseCoordinates (R := R) s).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (eraseCoordinates_surjective (R := R) s))

/-- Triangular equations cut out a genuine affine coordinate ring: the
ideal here is literally generated by `X i + p i` for `i ∈ s`. -/
def triangularQuotientEquiv (w : σ → ℕ) (p : σ → MvPolynomial σ R)
    (hp : ∀ i j, j ∈ (p i).vars → w j < w i) (s : Set σ) :
    (MvPolynomial σ R ⧸ Ideal.span ((fun i => X i + p i) '' s)) ≃ₐ[R]
      MvPolynomial {i // i ∉ s} R := by
  let e := triangularEquiv w p hp
  have heval : e.toRingHom ∘ X = (fun i => X i + p i) := by
    funext i
    exact triangularEquiv_X w p hp i
  have he : Ideal.span ((fun i => X i + p i) '' s) =
      (Ideal.span (X '' s)).map e.toRingHom := by
    rw [Ideal.map_span,Set.image_image]
    change Ideal.span ((fun i => X i + p i) '' s) = Ideal.span ((e.toRingHom ∘ X) '' s)
    rw [heval]
  exact (Ideal.quotientEquivAlg _ _ e he).symm.trans (coordinateQuotientEquiv s)

/-- A positive weighted homogeneous polynomial with zero linear part uses
only variables of strictly smaller weight than its degree. -/
theorem vars_lt_weight_of_no_linear_terms (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (f : MvPolynomial σ R) (d : ℕ) (hf : f.IsWeightedHomogeneous w d)
    (hlin : ∀ i, f.coeff (Finsupp.single i 1) = 0)
    (j : σ) (hj : j ∈ f.vars) : w j < d := by
  classical
  letI : Finsupp.NonTorsionWeight ℕ w :=
    Finsupp.nonTorsionWeight_of ℕ w (fun i => ne_of_gt (hw i))
  obtain ⟨a,ha,hja⟩ := (mem_vars_iff_mem_support (p := f) j).mp hj
  have haj : a j ≠ 0 := Finsupp.mem_support_iff.mp hja
  have hdegree : Finsupp.weight w a = d := hf (mem_support_iff.mp ha)
  have hne : a ≠ Finsupp.single j 1 := by
    intro he
    exact (mem_support_iff.mp ha) (by simpa only [he] using hlin j)
  have hres : a - Finsupp.single j 1 ≠ 0 := by
    intro hz
    apply hne
    have hh := Finsupp.sub_add_single_one_cancel haj
    rw [hz, zero_add] at hh
    exact hh.symm
  have hpos : 0 < Finsupp.weight w (a - Finsupp.single j 1) :=
    Nat.pos_of_ne_zero (fun hz => hres ((Finsupp.weight_eq_zero_iff_eq_zero w).mp hz))
  have hh := Finsupp.weight_sub_single_add (w := w) haj
  rw [hdegree] at hh
  omega

/-- The nonlinear remainders of positive weighted homogeneous equations
with normalized independent linear terms satisfy the triangular condition. -/
theorem normalized_homogeneous_triangular (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (F : σ → MvPolynomial σ R)
    (hF : ∀ i, (F i).IsWeightedHomogeneous w (w i))
    (hlin : ∀ i j, (F i).coeff (Finsupp.single j 1) = if j = i then 1 else 0) :
    ∀ i j, j ∈ (F i - X i).vars → w j < w i := by
  classical
  intro i j hj
  apply vars_lt_weight_of_no_linear_terms w hw (F i - X i) (w i)
    ((hF i).sub (isWeightedHomogeneous_X R w i)) _ j hj
  intro q
  simp [hlin, coeff_single_X, eq_comm]

/-- A normalized positive weighted homogeneous family is a polynomial
coordinate system. This is stronger than a set-theoretic parametrization. -/
def homogeneousCoordinateEquiv (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (F : σ → MvPolynomial σ R)
    (hF : ∀ i, (F i).IsWeightedHomogeneous w (w i))
    (hlin : ∀ i j, (F i).coeff (Finsupp.single j 1) = if j = i then 1 else 0) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  triangularEquiv w (fun i => F i - X i)
    (normalized_homogeneous_triangular w hw F hF hlin)

@[simp] theorem homogeneousCoordinateEquiv_X (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (F : σ → MvPolynomial σ R)
    (hF : ∀ i, (F i).IsWeightedHomogeneous w (w i))
    (hlin : ∀ i j, (F i).coeff (Finsupp.single j 1) = if j = i then 1 else 0)
    (i : σ) : homogeneousCoordinateEquiv w hw F hF hlin (X i) = F i := by
  simp [homogeneousCoordinateEquiv]

end PaperVerification.TriangularPolynomialCoordinates
