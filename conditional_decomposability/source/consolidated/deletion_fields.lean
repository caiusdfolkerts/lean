module
public import consolidated.deletion_geometry
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic.Ring

set_option Elab.async false

section BundlePart0
/- Source: Papers/FacetSupport.lean -/





@[expose] public section

/-!
# Supporting affine forms of actual facets

The extremality used here is a consequence of the ordinary geometric face
dimension.  No dual polytope or extra assumption about a cone of normals
is built into the definitions.  The final coefficient lemma is the sign
step needed when restoring a vertex beyond a simplex facet.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def affineFormEvaluation (x : E d) : (E d →ᵃ[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem affineForm_sum_apply {ι : Type*} (s : Finset ι)
    (f : ι → E d →ᵃ[ℝ] ℝ) (x : E d) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  exact map_sum (affineFormEvaluation x) f s

def IsFacet (P : ConvexPolytope d) (F : Set (E d)) : Prop :=
  P.IsFace F ∧ faceDim F + 1 = P.dim

def SupportsFace (P : ConvexPolytope d) (F : Set (E d))
    (f : E d →ᵃ[ℝ] ℝ) : Prop :=
  (∀ x ∈ P.toSet, 0 ≤ f x) ∧ F = {x ∈ P.toSet | f x = 0}

theorem SupportsFace.mem_iff {P : ConvexPolytope d} {F : Set (E d)}
    {f : E d →ᵃ[ℝ] ℝ} (hf : SupportsFace P F f) (x : E d) :
    x ∈ F ↔ x ∈ P.toSet ∧ f x = 0 := by rw [hf.2]; rfl

theorem SupportsFace.eq_zero {P : ConvexPolytope d} {F : Set (E d)}
    {f : E d →ᵃ[ℝ] ℝ} (hf : SupportsFace P F f) {x : E d} (hx : x ∈ F) :
    f x = 0 := ((hf.mem_iff x).mp hx).2

theorem exists_supportsFace (P : ConvexPolytope d) {F : Set (E d)}
    (hF : P.IsFace F) : ∃ f : E d →ᵃ[ℝ] ℝ, SupportsFace P F f := by
  obtain ⟨l, hl⟩ := hF.1 hF.2
  obtain ⟨p, hp⟩ := hF.2
  have hp' := hp
  rw [hl] at hp'
  refine ⟨AffineMap.const ℝ (E d) (l p) - l.toLinearMap.toAffineMap, ?_, ?_⟩
  · intro x hx
    change 0 ≤ l p - l x
    exact sub_nonneg.mpr (hp'.2 x hx)
  · ext x
    rw [hl]
    change (x ∈ P.toSet ∧ ∀ y ∈ P.toSet, l y ≤ l x) ↔
      x ∈ P.toSet ∧ l p - l x = 0
    constructor
    · rintro ⟨hx, hmax⟩
      exact ⟨hx, sub_eq_zero.mpr (le_antisymm (hmax p hp'.1) (hp'.2 x hx))⟩
    · rintro ⟨hx, heq⟩
      exact ⟨hx, fun y hy => (hp'.2 y hy).trans_eq (sub_eq_zero.mp heq)⟩

theorem IsFacet.ne_toSet {P : ConvexPolytope d} {F : Set (E d)}
    (hF : IsFacet P F) : F ≠ P.toSet := by
  intro heq
  have h := hF.2
  rw [heq] at h
  change P.dim + 1 = P.dim at h
  omega

theorem IsFacet.eq_of_subset {P : ConvexPolytope d} {F G : Set (E d)}
    (hF : IsFacet P F) (hG : P.IsFace G) (hproper : G ≠ P.toSet)
    (hsub : F ⊆ G) : F = G := by
  by_contra hne
  have hFG : F ⊂ G := (Set.ssubset_iff_subset_ne).mpr ⟨hsub, hne⟩
  have hGP : G ⊂ P.toSet := (Set.ssubset_iff_subset_ne).mpr
    ⟨face_subset_toSet P hG, hproper⟩
  have h₁ := faceDim_lt_of_ssubset P hF.1 hG hFG
  have h₂ := faceDim_lt_of_ssubset P hG (toSet_isFace P) hGP
  change faceDim G < P.dim at h₂
  have h₃ := hF.2
  omega

theorem IsFacet.support_ne_zero {P : ConvexPolytope d} {F : Set (E d)}
    (hF : IsFacet P F) {f : E d →ᵃ[ℝ] ℝ} (hf : SupportsFace P F f) : f ≠ 0 := by
  intro heq
  apply hF.ne_toSet
  rw [hf.2, heq]
  ext x
  simp

/-- In a nonnegative linear combination exposing a facet, every positive
summand exposes that same facet.  This is proved from actual face
inclusion and strict growth of dimension. -/
theorem positive_support_summand_same_facet
    {ι : Type*} [Fintype ι] (P : ConvexPolytope d)
    (F : ι → Set (E d)) (f : ι → E d →ᵃ[ℝ] ℝ)
    (hF : ∀ i, IsFacet P (F i)) (hf : ∀ i, SupportsFace P (F i) (f i))
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (heq : ∑ i, c i • f i = g) (i : ι) (hi : 0 < c i) : G = F i := by
  apply hG.eq_of_subset (hF i).1 (hF i).ne_toSet
  intro x hx
  have hxP : x ∈ P.toSet := face_subset_toSet P hG.1 hx
  have hsum : ∑ j, c j * f j x = 0 := by
    have h := congrArg (fun a : E d →ᵃ[ℝ] ℝ => a x) heq
    simpa only [affineForm_sum_apply, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul,
      hg.eq_zero hx] using h
  have hle : c i * f i x ≤ ∑ j, c j * f j x :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hc j) ((hf j).1 x hxP))
      (Finset.mem_univ i)
  have hfi : f i x = 0 := by
    rw [hsum] at hle
    have hn := (hf i).1 x hxP
    nlinarith
  exact ((hf i).mem_iff x).mpr ⟨hxP, hfi⟩

/-- A facet different from all facets in a basis cannot have a
nonnegative expansion in their supporting forms. -/
theorem facet_support_not_all_coordinates_nonneg
    {ι : Type*} [Fintype ι] (P : ConvexPolytope d)
    (F : ι → Set (E d)) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (hF : ∀ i, IsFacet P (F i)) (hb : ∀ i, SupportsFace P (F i) (b i))
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (hne : ∀ i, G ≠ F i) : ¬∀ i, 0 ≤ b.repr g i := by
  intro hc
  have hz : ∀ i, b.repr g i = 0 := by
    intro i
    by_contra hi
    have hpos : 0 < b.repr g i := lt_of_le_of_ne (hc i) (Ne.symm hi)
    exact hne i (positive_support_summand_same_facet P F b hF hb G g hG hg
      (fun j => b.repr g j) hc (b.sum_repr g) i hpos)
  have hg0 : g = 0 := by
    apply b.repr.injective
    ext i
    simp only [map_zero, Finsupp.zero_apply, hz i]
  exact hG.support_ne_zero hg hg0

/-- At a simplex facet all other coordinates of another facet form are
nonnegative, by evaluation on the simplex vertices.  Its remaining
coordinate is therefore strictly negative. -/
theorem facet_support_distinguished_coordinate_neg
    {ι : Type*} [Fintype ι] (P : ConvexPolytope d)
    (F : ι → Set (E d)) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (hF : ∀ i, IsFacet P (F i)) (hb : ∀ i, SupportsFace P (F i) (b i))
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (hne : ∀ i, G ≠ F i) (i₀ : ι)
    (hc : ∀ i, i ≠ i₀ → 0 ≤ b.repr g i) : b.repr g i₀ < 0 := by
  by_contra h
  have h₀ : 0 ≤ b.repr g i₀ := le_of_not_gt h
  apply facet_support_not_all_coordinates_nonneg P F b hF hb G g hG hg hne
  intro i
  by_cases hi : i = i₀
  · simpa only [hi] using h₀
  · exact hc i hi

end Papers.Polytopes

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/AffineHomogeneousValues.lean -/






@[expose] public section

/-!
# Homogeneous points specified by affine forms

An ordinary homogeneous vector `(x,t)` evaluates an affine form `f` as
`f.linear x + t * f 0`.  In finite dimension this identifies homogeneous
vectors with the dual of the space of affine forms.  Consequently a basis
of affine forms can be assigned arbitrary values over the same field.
The identification is explicit and does not assume an affine chart is
already available.
-/

noncomputable section
namespace Papers.AffineCoordinates

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def linearToAffine : (V →ₗ[K] K) →ₗ[K] (V →ᵃ[K] K) where
  toFun f := f.toAffineMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem linearToAffine_apply (f : V →ₗ[K] K) (x : V) :
    linearToAffine f x = f x := rfl

theorem affine_decomposition (f : V →ᵃ[K] K) :
    f = linearToAffine f.linear + f 0 • AffineMap.const K V (1 : K) := by
  ext x
  have h := f.map_vadd (0 : V) x
  simpa only [vadd_eq_add, add_zero, AffineMap.coe_add, Pi.add_apply,
    linearToAffine_apply, AffineMap.coe_smul, Pi.smul_apply,
    AffineMap.coe_const, Function.const_apply, smul_eq_mul, mul_one] using h

def homogeneousEvaluation : (V × K) →ₗ[K] Module.Dual K (V →ᵃ[K] K) where
  toFun z :=
    { toFun := fun f => f.linear z.1 + z.2 * f 0
      map_add' := by
        intro f g
        simp only [AffineMap.add_linear, LinearMap.add_apply, AffineMap.coe_add,
          Pi.add_apply, mul_add]
        ring
      map_smul' := by
        intro c f
        simp only [AffineMap.smul_linear, LinearMap.smul_apply, AffineMap.coe_smul,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  map_add' := by
    intro z w
    apply LinearMap.ext
    intro f
    change f.linear (z.1 + w.1) + (z.2 + w.2) * f 0 =
      (f.linear z.1 + z.2 * f 0) + (f.linear w.1 + w.2 * f 0)
    rw [map_add]
    ring
  map_smul' := by
    intro c z
    apply LinearMap.ext
    intro f
    change f.linear (c • z.1) + (c * z.2) * f 0 =
      c * (f.linear z.1 + z.2 * f 0)
    rw [map_smul, smul_eq_mul]
    ring

@[simp] theorem homogeneousEvaluation_apply (z : V × K) (f : V →ᵃ[K] K) :
    homogeneousEvaluation z f = f.linear z.1 + z.2 * f 0 := rfl

@[simp] theorem homogeneousEvaluation_homogenize (x : V) (f : V →ᵃ[K] K) :
    homogeneousEvaluation (x, (1 : K)) f = f x := by
  have h := f.map_vadd (0 : V) x
  simpa only [homogeneousEvaluation_apply, vadd_eq_add, add_zero, one_mul] using h.symm

@[simp] theorem homogeneousEvaluation_const (z : V × K) (c : K) :
    homogeneousEvaluation z (AffineMap.const K V c) = z.2 * c := by
  simp [homogeneousEvaluation]

@[simp] theorem homogeneousEvaluation_linear (z : V × K) (f : V →ₗ[K] K) :
    homogeneousEvaluation z (linearToAffine f) = f z.1 := by
  change f z.1 + z.2 * f 0 = f z.1
  rw [map_zero, mul_zero, add_zero]

variable [FiniteDimensional K V]

theorem homogeneousEvaluation_injective :
    Function.Injective (homogeneousEvaluation (K := K) (V := V)) := by
  intro z w heq
  apply Prod.ext
  · apply (Module.evalEquiv K V).injective
    ext f
    have h := congrArg (fun a : Module.Dual K (V →ᵃ[K] K) => a (linearToAffine f)) heq
    simpa only [Module.evalEquiv_apply, Module.Dual.eval_apply,
      homogeneousEvaluation_linear] using h
  · have h := congrArg
      (fun a : Module.Dual K (V →ᵃ[K] K) => a (AffineMap.const K V (1 : K))) heq
    simpa only [homogeneousEvaluation_const, mul_one] using h

theorem homogeneousEvaluation_surjective :
    Function.Surjective (homogeneousEvaluation (K := K) (V := V)) := by
  intro a
  let x : V := (Module.evalEquiv K V).symm (a.comp linearToAffine)
  let t : K := a (AffineMap.const K V (1 : K))
  refine ⟨(x, t), ?_⟩
  ext f
  have hx : f.linear x = a (linearToAffine f.linear) := by
    simpa only [x, LinearMap.comp_apply] using
      Module.apply_evalEquiv_symm_apply K V f.linear (a.comp linearToAffine)
  calc
    homogeneousEvaluation (x, t) f = a (linearToAffine f.linear) +
        a (AffineMap.const K V (1 : K)) * f 0 := by rw [homogeneousEvaluation_apply, hx]
    _ = a (linearToAffine f.linear + f 0 • AffineMap.const K V (1 : K)) := by
      rw [map_add, map_smul, smul_eq_mul]
      ring
    _ = a f := congrArg a (affine_decomposition f).symm

def homogeneousEvaluationEquiv :
    (V × K) ≃ₗ[K] Module.Dual K (V →ᵃ[K] K) :=
  LinearEquiv.ofBijective homogeneousEvaluation
    ⟨homogeneousEvaluation_injective, homogeneousEvaluation_surjective⟩

variable {ι : Type*}

def realizeAffineValues (b : Basis ι K (V →ᵃ[K] K)) (r : ι → K) : V × K :=
  homogeneousEvaluationEquiv.symm (b.constr K r)

@[simp] theorem realizeAffineValues_evaluation
    (b : Basis ι K (V →ᵃ[K] K)) (r : ι → K) (f : V →ᵃ[K] K) :
    homogeneousEvaluation (realizeAffineValues b r) f = b.constr K r f := by
  have h := homogeneousEvaluationEquiv.apply_symm_apply (b.constr K r)
  exact congrArg (fun a : Module.Dual K (V →ᵃ[K] K) => a f) h

@[simp] theorem realizeAffineValues_basis
    (b : Basis ι K (V →ᵃ[K] K)) (r : ι → K) (i : ι) :
    homogeneousEvaluation (realizeAffineValues b r) (b i) = r i := by
  rw [realizeAffineValues_evaluation, Basis.constr_basis]

theorem homogeneousEvaluation_expansion [Fintype ι]
    (b : Basis ι K (V →ᵃ[K] K)) (z : V × K) (f : V →ᵃ[K] K) :
    homogeneousEvaluation z f =
      ∑ i, b.repr f i * homogeneousEvaluation z (b i) := by
  conv_lhs => rw [← b.sum_repr f]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

theorem realizeAffineValues_expansion [Fintype ι]
    (b : Basis ι K (V →ᵃ[K] K)) (r : ι → K) (f : V →ᵃ[K] K) :
    homogeneousEvaluation (realizeAffineValues b r) f = ∑ i, b.repr f i * r i := by
  rw [homogeneousEvaluation_expansion b]
  simp only [realizeAffineValues_basis]

def affineLift (f : V →ᵃ[K] K) : (V × K) →ₗ[K] K where
  toFun z := homogeneousEvaluation z f
  map_add' z w := by
    exact congrArg (fun a : Module.Dual K (V →ᵃ[K] K) => a f)
      (homogeneousEvaluation.map_add z w)
  map_smul' c z := by
    exact congrArg (fun a : Module.Dual K (V →ᵃ[K] K) => a f)
      (homogeneousEvaluation.map_smul c z)

def affineDehomogenize (l : (V × K) →ₗ[K] K) : V →ᵃ[K] K where
  toFun x := l (x, 1)
  linear := l.comp (LinearMap.inl K V K)
  map_vadd' p v := by
    change l (v + p, (1 : K)) = l (v, 0) + l (p, 1)
    rw [← map_add]
    exact congrArg l (Prod.ext rfl (zero_add (1 : K)).symm)

@[simp] theorem affineLift_apply (f : V →ᵃ[K] K) (z : V × K) :
    affineLift f z = homogeneousEvaluation z f := rfl

@[simp] theorem affineDehomogenize_apply (l : (V × K) →ₗ[K] K) (x : V) :
    affineDehomogenize l x = l (x, 1) := rfl

@[simp] theorem affineDehomogenize_affineLift (f : V →ᵃ[K] K) :
    affineDehomogenize (affineLift f) = f := by
  ext x
  exact homogeneousEvaluation_homogenize x f

@[simp] theorem affineLift_affineDehomogenize (l : (V × K) →ₗ[K] K) :
    affineLift (affineDehomogenize l) = l := by
  apply LinearMap.ext
  intro z
  change l (z.1, 0) + z.2 * l (0, 1) = l z
  calc
    l (z.1, 0) + z.2 * l (0, 1) = l ((z.1, 0) + z.2 • (0, 1)) := by
      rw [map_add, map_smul, smul_eq_mul]
    _ = l z := congrArg l (by
      apply Prod.ext
      · simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul, mul_one, zero_add])

variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

def projectiveTransportAffine (L : (V × K) ≃ₗ[K] (W × K)) (f : V →ᵃ[K] K) :
    W →ᵃ[K] K := affineDehomogenize ((affineLift f).comp L.symm.toLinearMap)

@[simp] theorem projectiveTransportAffine_apply
    (L : (V × K) ≃ₗ[K] (W × K)) (f : V →ᵃ[K] K) (x : W) :
    projectiveTransportAffine L f x = homogeneousEvaluation (L.symm (x, 1)) f := rfl

theorem projectiveTransportAffine_scaled
    (L : (V × K) ≃ₗ[K] (W × K)) (f : V →ᵃ[K] K)
    (x : V) (y : W) (h : K) (heq : L (x, 1) = h • (y, 1)) :
    f x = h * projectiveTransportAffine L f y := by
  have hpre : (x, (1 : K)) = h • L.symm (y, 1) := by
    have h' := congrArg L.symm heq
    simpa only [L.symm_apply_apply, map_smul] using h'
  calc
    f x = affineLift f (x, 1) := (homogeneousEvaluation_homogenize x f).symm
    _ = affineLift f (h • L.symm (y, 1)) := congrArg (affineLift f) hpre
    _ = h * projectiveTransportAffine L f y := by
      change affineLift f (h • L.symm (y, 1)) = h * affineLift f (L.symm (y, 1))
      rw [map_smul, smul_eq_mul]

theorem projectiveTransportAffine_inverse
    (L : (V × K) ≃ₗ[K] (W × K)) (f : V →ᵃ[K] K) :
    projectiveTransportAffine L.symm (projectiveTransportAffine L f) = f := by
  unfold projectiveTransportAffine
  rw [affineLift_affineDehomogenize]
  have hcomp : ((affineLift f).comp L.symm.toLinearMap).comp
      L.symm.symm.toLinearMap = affineLift f := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm,
      LinearEquiv.symm_apply_apply]
  rw [hcomp, affineDehomogenize_affineLift]

end Papers.AffineCoordinates

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/SimplexFacetCoordinates.lean -/





@[expose] public section

/-!
# Coordinates dual to a simplex facet and its neighboring facets

The triangular evaluation pattern at the simplex vertices proves that the
supporting affine forms are a basis.  The coefficient sign argument then
constructs a homogeneous restoration point which is beyond the simplex
facet, on a prescribed subset of its neighboring hyperplanes, and strictly
inside every other facet halfspace.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

def simplexSupportFamily (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ) :
    Option ι → E d →ᵃ[ℝ] ℝ := fun i => i.elim f₀ f

@[simp] theorem simplexSupportFamily_none (f₀ : E d →ᵃ[ℝ] ℝ)
    (f : ι → E d →ᵃ[ℝ] ℝ) : simplexSupportFamily f₀ f none = f₀ := rfl

@[simp] theorem simplexSupportFamily_some (f₀ : E d →ᵃ[ℝ] ℝ)
    (f : ι → E d →ᵃ[ℝ] ℝ) (i : ι) : simplexSupportFamily f₀ f (some i) = f i := rfl

theorem simplexSupportFamily_linearIndependent
    (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ)
    (p : ι → E d) (q : E d)
    (h₀ : ∀ i, f₀ (p i) = 0) (hq : f₀ q ≠ 0)
    (hdiag : ∀ i, f i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → f i (p j) = 0) :
    LinearIndependent ℝ (simplexSupportFamily f₀ f) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c heq i
  have hc : ∀ j, c (some j) = 0 := by
    intro j
    have h := congrArg (affineFormEvaluation (p j)) heq
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h
    change (∑ k, c k * simplexSupportFamily f₀ f k (p j)) = 0 at h
    simp only [Fintype.sum_option, simplexSupportFamily_none,
      simplexSupportFamily_some, h₀ j, mul_zero, zero_add] at h
    have hsum : (∑ k, c (some k) * f k (p j)) = c (some j) * f j (p j) := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [hoff k j hkj, mul_zero]
      · intro hj
        exact False.elim (hj (Finset.mem_univ _))
    rw [hsum] at h
    exact (mul_eq_zero.mp h).resolve_right (hdiag j)
  cases i with
  | some j => exact hc j
  | none =>
    have h := congrArg (affineFormEvaluation q) heq
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h
    change (∑ k, c k * simplexSupportFamily f₀ f k q) = 0 at h
    simp only [Fintype.sum_option, simplexSupportFamily_none,
      simplexSupportFamily_some, hc, zero_mul, Finset.sum_const_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_right hq

def simplexSupportBasis
    (hcard : Fintype.card ι = d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ)
    (p : ι → E d) (q : E d)
    (h₀ : ∀ i, f₀ (p i) = 0) (hq : f₀ q ≠ 0)
    (hdiag : ∀ i, f i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → f i (p j) = 0) :
    Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (simplexSupportFamily f₀ f)
    (simplexSupportFamily_linearIndependent f₀ f p q h₀ hq hdiag hoff)
    (by simp [AffineMap.finrank_eq, hcard])

@[simp] theorem simplexSupportBasis_apply
    (hcard : Fintype.card ι = d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ)
    (p : ι → E d) (q : E d)
    (h₀ : ∀ i, f₀ (p i) = 0) (hq : f₀ q ≠ 0)
    (hdiag : ∀ i, f i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → f i (p j) = 0) (i : Option ι) :
    simplexSupportBasis hcard f₀ f p q h₀ hq hdiag hoff i =
      simplexSupportFamily f₀ f i := by
  simp only [simplexSupportBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

theorem basis_repr_at_simplex_vertex
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (p : ι → E d)
    (h₀ : ∀ i, b none (p i) = 0)
    (hoff : ∀ i j, i ≠ j → b (some i) (p j) = 0)
    (g : E d →ᵃ[ℝ] ℝ) (i : ι) :
    b.repr g (some i) * b (some i) (p i) = g (p i) := by
  have h := congrArg (affineFormEvaluation (p i)) (b.sum_repr g)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  change (∑ j, b.repr g j * b j (p i)) = g (p i) at h
  simp only [Fintype.sum_option, h₀ i, mul_zero, zero_add] at h
  have hsum : (∑ j, b.repr g (some j) * b (some j) (p i)) =
      b.repr g (some i) * b (some i) (p i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hoff j i hji, mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ _))
  rwa [hsum] at h

theorem basis_repr_some_nonneg
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (p : ι → E d)
    (h₀ : ∀ i, b none (p i) = 0)
    (hdiag : ∀ i, 0 < b (some i) (p i))
    (hoff : ∀ i j, i ≠ j → b (some i) (p j) = 0)
    (g : E d →ᵃ[ℝ] ℝ) (hg : ∀ i, 0 ≤ g (p i)) (i : ι) :
    0 ≤ b.repr g (some i) := by
  have heq := basis_repr_at_simplex_vertex b p h₀ hoff g i
  have hnonneg : 0 ≤ b.repr g (some i) * b (some i) (p i) := heq.symm ▸ hg i
  exact (mul_nonneg_iff_of_pos_right (hdiag i)).mp hnonneg

/-- The coefficient with respect to the simplex facet is negative for
every other genuine facet.  All hypotheses refer to ordinary geometric
facets and their vertex evaluations. -/
theorem simplexFacet_other_coefficient_neg
    (P : ConvexPolytope d) (F : Option ι → Set (E d))
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (p : ι → E d)
    (hF : ∀ i, IsFacet P (F i)) (hb : ∀ i, SupportsFace P (F i) (b i))
    (hp : ∀ i, p i ∈ P.toSet)
    (h₀ : ∀ i, b none (p i) = 0)
    (hdiag : ∀ i, 0 < b (some i) (p i))
    (hoff : ∀ i j, i ≠ j → b (some i) (p j) = 0)
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (hne : ∀ i, G ≠ F i) : b.repr g none < 0 := by
  apply facet_support_distinguished_coordinate_neg P F b hF hb G g hG hg hne none
  intro i hi
  cases i with
  | none => exact False.elim (hi rfl)
  | some j =>
    exact basis_repr_some_nonneg b p h₀ hdiag hoff g (fun k => hg.1 _ (hp k)) j

def restorationValues (t : ι → ℝ) : Option ι → ℝ := fun i => i.elim (-1) t

def restorationVector
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (t : ι → ℝ) : E d × ℝ :=
  realizeAffineValues b (restorationValues t)

@[simp] theorem restorationVector_none
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (t : ι → ℝ) :
    homogeneousEvaluation (restorationVector b t) (b none) = -1 := by
  change homogeneousEvaluation (realizeAffineValues b (restorationValues t)) (b none) = -1
  exact realizeAffineValues_basis b (restorationValues t) none

@[simp] theorem restorationVector_some
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (t : ι → ℝ) (i : ι) :
    homogeneousEvaluation (restorationVector b t) (b (some i)) = t i := by
  change homogeneousEvaluation (realizeAffineValues b (restorationValues t)) (b (some i)) = t i
  exact realizeAffineValues_basis b (restorationValues t) (some i)

theorem restorationVector_other_facet_pos
    (P : ConvexPolytope d) (F : Option ι → Set (E d))
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (p : ι → E d)
    (hF : ∀ i, IsFacet P (F i)) (hb : ∀ i, SupportsFace P (F i) (b i))
    (hp : ∀ i, p i ∈ P.toSet)
    (h₀ : ∀ i, b none (p i) = 0)
    (hdiag : ∀ i, 0 < b (some i) (p i))
    (hoff : ∀ i j, i ≠ j → b (some i) (p j) = 0)
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (hne : ∀ i, G ≠ F i) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    0 < homogeneousEvaluation (restorationVector b t) g := by
  have hn := simplexFacet_other_coefficient_neg P F b p hF hb hp h₀ hdiag hoff G g hG hg hne
  have hc := basis_repr_some_nonneg b p h₀ hdiag hoff g (fun i => hg.1 _ (hp i))
  rw [homogeneousEvaluation_expansion b, Fintype.sum_option]
  simp only [restorationVector_none, restorationVector_some, mul_neg_one]
  exact add_pos_of_pos_of_nonneg (neg_pos.mpr hn)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hc i) (ht i)))

end Papers.Polytopes

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/FacetHalfspaces.lean -/






@[expose] public section

/-!
# A full-dimensional finite polytope is the intersection of its facet halfspaces

The proof enlarges a separating exposed face while keeping the separated
point strictly outside.  Each enlargement is a finite minimum-ratio pivot.
This avoids assuming a polyhedral duality theorem or a halfspace
representation as part of the polytope datatype.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem affine_form_apply (f : E d →ᵃ[ℝ] ℝ) (x : E d) :
    f x = f.linear x + f 0 := by
  simpa only [vadd_eq_add, add_zero] using f.map_vadd (0 : E d) x

theorem affine_nonneg_on_hull (s : Finset (E d)) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) : ∀ x ∈ convexHull ℝ (s : Set (E d)), 0 ≤ f x := by
  let l := f.linear.toContinuousLinearMap
  have hlin : ∀ x ∈ s, -f 0 ≤ l x := by
    intro x hx
    have h := hf x hx
    rw [affine_form_apply f x] at h
    change -f 0 ≤ f.linear x
    linarith
  intro x hx
  have h := linear_lower_bound_on_hull s l (-f 0) hlin x hx
  change -f 0 ≤ f.linear x at h
  rw [affine_form_apply f x]
  linarith

def affineZeroFace (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ) : Set (E d) :=
  {x ∈ P.toSet | f x = 0}

theorem affineZeroFace_isFace (P : ConvexPolytope d) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ P.toSet, 0 ≤ f x) (hne : (affineZeroFace P f).Nonempty) :
    P.IsFace (affineZeroFace P f) := by
  refine ⟨?_, hne⟩
  intro _
  let l := f.linear.toContinuousLinearMap
  refine ⟨-l, ?_⟩
  obtain ⟨p, hpP, hpf⟩ := hne
  ext x
  change (x ∈ P.toSet ∧ f x = 0) ↔
    x ∈ P.toSet ∧ ∀ y ∈ P.toSet, -l y ≤ -l x
  constructor
  · rintro ⟨hxP, hxf⟩
    refine ⟨hxP, ?_⟩
    intro y hy
    have hfy := hf y hy
    rw [affine_form_apply f x] at hxf
    rw [affine_form_apply f y] at hfy
    change -f.linear y ≤ -f.linear x
    linarith
  · rintro ⟨hxP, hmax⟩
    refine ⟨hxP, ?_⟩
    have hlx := hmax p hpP
    change -f.linear p ≤ -f.linear x at hlx
    have hfx := hf x hxP
    rw [affine_form_apply f p] at hpf
    rw [affine_form_apply f x] at hfx ⊢
    linarith

theorem fullDim_affineSpan_body (P : ConvexPolytope d) (hP : P.IsFullDim) :
    affineSpan ℝ P.toSet = ⊤ := by
  have hspan : vectorSpan ℝ P.toSet = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change finrank ℝ (vectorSpan ℝ P.toSet) = d at hP
    simpa only [finrank_euclideanSpace_fin] using hP
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ?_).mp
  · rw [direction_affineSpan, hspan]
  · obtain ⟨x, hx⟩ := (toSet_isFace P).2
    exact ⟨x, subset_affineSpan ℝ _ hx⟩

theorem fullDim_affineSpan_vertices (P : ConvexPolytope d) (hP : P.IsFullDim) :
    affineSpan ℝ (P.vertices : Set (E d)) = ⊤ := by
  rw [← affineSpan_convexHull]
  exact fullDim_affineSpan_body P hP

theorem affine_eq_zero_of_body (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.toSet, f x = 0) : f = 0 := by
  have heq : Set.EqOn (⇑f) (⇑(0 : E d →ᵃ[ℝ] ℝ)) P.toSet := hf
  have heq' := AffineMap.eqOn_affineSpan (k := ℝ) heq
  rw [fullDim_affineSpan_body P hP] at heq'
  ext x
  exact heq' (by simp)

theorem affine_eq_zero_of_vertices (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.vertices, f x = 0) : f = 0 := by
  have heq : Set.EqOn (⇑f) (⇑(0 : E d →ᵃ[ℝ] ℝ)) (P.vertices : Set (E d)) := hf
  have heq' := AffineMap.eqOn_affineSpan (k := ℝ) heq
  rw [fullDim_affineSpan_vertices P hP] at heq'
  ext x
  exact heq' (by simp)

theorem affineZeroFace_ne_body_of_ne_zero (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d →ᵃ[ℝ] ℝ) (x : E d) (hx : f x ≠ 0) :
    affineZeroFace P f ≠ P.toSet := by
  intro heq
  have hf := affine_eq_zero_of_body P hP f (by
    intro y hy
    have h : y ∈ affineZeroFace P f := heq.symm ▸ hy
    exact h.2)
  exact hx (congrArg (fun a : E d →ᵃ[ℝ] ℝ => a x) hf)

theorem affineZeroFace_ne_body_of_negative (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d →ᵃ[ℝ] ℝ) (x : E d) (hx : f x < 0) :
    affineZeroFace P f ≠ P.toSet :=
  affineZeroFace_ne_body_of_ne_zero P hP f x (ne_of_lt hx)

/-- A face of codimension at least two and one extra point lie in the
zero set of a nonzero affine form. -/
theorem affine_form_vanishing_on_face_and_point
    (F : Set (E d)) (x : E d) (hgap : faceDim F + 2 ≤ d) :
    ∃ h : E d →ᵃ[ℝ] ℝ, h ≠ 0 ∧ h x = 0 ∧ ∀ y ∈ F, h y = 0 := by
  let U := vectorSpan ℝ (insert x F)
  have hdim : finrank ℝ U < finrank ℝ (E d) := by
    have hi := finrank_vectorSpan_insert_le_set (k := ℝ) F x
    rw [finrank_euclideanSpace_fin]
    change finrank ℝ (vectorSpan ℝ (insert x F)) < d
    change finrank ℝ (vectorSpan ℝ F) + 2 ≤ d at hgap
    omega
  obtain ⟨v, hv⟩ : ∃ v : E d, v ∉ U := by
    by_contra hall
    push_neg at hall
    have htop : U = ⊤ := SetLike.ext fun y => by simp [hall y]
    rw [htop, finrank_top] at hdim
    exact (lt_irrefl _) hdim
  obtain ⟨l, hlv, hU⟩ := Submodule.exists_le_ker_of_notMem hv
  let h : E d →ᵃ[ℝ] ℝ := l.toAffineMap - AffineMap.const ℝ (E d) (l x)
  have happly (y : E d) : h y = l (y - x) := by
    change l y - l x = l (y - x)
    rw [map_sub]
  refine ⟨h, ?_, ?_, ?_⟩
  · intro hz
    have hzero := congrArg (fun f : E d →ᵃ[ℝ] ℝ => f (v + x)) hz
    rw [happly] at hzero
    simp only [add_sub_cancel_right, AffineMap.coe_zero, Pi.zero_apply] at hzero
    exact hlv hzero
  · rw [happly, sub_self, map_zero]
  · intro y hy
    rw [happly]
    exact hU (vsub_mem_vectorSpan ℝ (Set.mem_insert_of_mem x hy) (Set.mem_insert x F))

theorem positive_vanishing_pivot_form
    (P : ConvexPolytope d) (hP : P.IsFullDim) (F : Set (E d)) (x : E d)
    (hgap : faceDim F + 2 ≤ d) :
    ∃ h : E d →ᵃ[ℝ] ℝ, h x = 0 ∧ (∀ y ∈ F, h y = 0) ∧
      ∃ v ∈ P.vertices, 0 < h v := by
  obtain ⟨h, hn, hx, hF⟩ := affine_form_vanishing_on_face_and_point F x hgap
  obtain ⟨v, hv, hnv⟩ : ∃ v ∈ P.vertices, h v ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hn (affine_eq_zero_of_vertices P hP h hall)
  rcases lt_or_gt_of_ne hnv with hneg | hpos
  · refine ⟨-h, ?_, ?_, v, hv, ?_⟩
    · change -h x = 0
      rw [hx, neg_zero]
    · intro y hy
      change -h y = 0
      rw [hF y hy, neg_zero]
    · exact neg_pos.mpr hneg
  · exact ⟨h, hx, hF, v, hv, hpos⟩

/-- A finite ratio pivot enlarges the exposed zero face and keeps the
chosen exterior point strictly on the negative side. -/
theorem enlarge_supported_face
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : P.IsFace F) (f : E d →ᵃ[ℝ] ℝ)
    (hf : SupportsFace P F f) (x : E d) (hx : f x ≠ 0)
    (hgap : faceDim F + 2 ≤ d) :
    ∃ G : Set (E d), ∃ g : E d →ᵃ[ℝ] ℝ,
      P.IsFace G ∧ SupportsFace P G g ∧ F ⊂ G ∧ G ≠ P.toSet ∧ g x = f x := by
  classical
  obtain ⟨h, hx0, hF0, v, hv, hvpos⟩ := positive_vanishing_pivot_form P hP F x hgap
  let S := P.vertices.filter (fun y => 0 < h y)
  have hS : S.Nonempty := ⟨v, Finset.mem_filter.mpr ⟨hv, hvpos⟩⟩
  let r : E d → ℝ := fun y => f y / h y
  have hr : ∀ y ∈ S, 0 < r y := by
    intro y hy
    obtain ⟨hyP, hyp⟩ := Finset.mem_filter.mp hy
    have hbody : y ∈ P.toSet := subset_convexHull ℝ _ hyP
    have hfy : 0 < f y := by
      rcases lt_or_eq_of_le (hf.1 y hbody) with ht | he
      · exact ht
      · have hyF := (hf.mem_iff y).mpr ⟨hbody, he.symm⟩
        rw [hF0 y hyF] at hyp
        exact False.elim ((lt_irrefl _) hyp)
    exact div_pos hfy hyp
  let R := S.image r
  have hR : R.Nonempty := hS.image r
  let τ := R.min' hR
  have hτmem : τ ∈ R := Finset.min'_mem R hR
  obtain ⟨w, hwS, hwτ⟩ := Finset.mem_image.mp hτmem
  have hτ : 0 < τ := hwτ ▸ hr w hwS
  let g : E d →ᵃ[ℝ] ℝ := f - τ • h
  have gapply (y : E d) : g y = f y - τ * h y := rfl
  have hgV : ∀ y ∈ P.vertices, 0 ≤ g y := by
    intro y hy
    have hfy := hf.1 y (subset_convexHull ℝ _ hy)
    rw [gapply]
    by_cases hhy : 0 < h y
    · have hyS : y ∈ S := Finset.mem_filter.mpr ⟨hy, hhy⟩
      have hle : τ ≤ r y := Finset.min'_le R (r y) (Finset.mem_image_of_mem r hyS)
      have hm : τ * h y ≤ f y := (le_div_iff₀ hhy).mp hle
      exact sub_nonneg.mpr hm
    · have hm : τ * h y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ.le (le_of_not_gt hhy)
      linarith
  have hgP : ∀ y ∈ P.toSet, 0 ≤ g y := affine_nonneg_on_hull P.vertices g hgV
  have hgF : ∀ y ∈ F, g y = 0 := by
    intro y hy
    rw [gapply, hf.eq_zero hy, hF0 y hy, mul_zero, sub_zero]
  have hgx : g x = f x := by rw [gapply, hx0, mul_zero, sub_zero]
  let G := affineZeroFace P g
  have hsub : F ⊆ G := fun y hy => ⟨face_subset_toSet P hF hy, hgF y hy⟩
  have hneG : G.Nonempty := hF.2.mono hsub
  have hG : P.IsFace G := affineZeroFace_isFace P g hgP hneG
  have hwP : w ∈ P.vertices := (Finset.mem_filter.mp hwS).1
  have hwp : 0 < h w := (Finset.mem_filter.mp hwS).2
  have hwg : g w = 0 := by
    rw [gapply, ← hwτ]
    dsimp only [r]
    rw [div_mul_cancel₀ _ (ne_of_gt hwp), sub_self]
  have hwF : w ∉ F := by
    intro hw
    rw [hF0 w hw] at hwp
    exact (lt_irrefl _) hwp
  refine ⟨G, g, hG, ⟨hgP, rfl⟩, ?_,
    affineZeroFace_ne_body_of_ne_zero P hP g x (hgx.trans_ne hx), hgx⟩
  apply Set.ssubset_iff_subset_ne.mpr
  refine ⟨hsub, ?_⟩
  intro heq
  apply hwF
  rw [heq]
  exact ⟨subset_convexHull ℝ _ hwP, hwg⟩

theorem facet_containing_preserving_value
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : P.IsFace F) (f : E d →ᵃ[ℝ] ℝ)
    (hf : SupportsFace P F f) (x : E d) (hx : f x ≠ 0) :
    ∃ G : Set (E d), ∃ g : E d →ᵃ[ℝ] ℝ,
      IsFacet P G ∧ SupportsFace P G g ∧ F ⊆ G ∧ g x = f x := by
  suffices H : ∀ k : ℕ, ∀ (F : Set (E d)) (f : E d →ᵃ[ℝ] ℝ),
      P.IsFace F → SupportsFace P F f → f x ≠ 0 →
      d - 1 - faceDim F ≤ k →
      ∃ G : Set (E d), ∃ g : E d →ᵃ[ℝ] ℝ,
        IsFacet P G ∧ SupportsFace P G g ∧ F ⊆ G ∧ g x = f x by
    exact H (d - 1 - faceDim F) F f hF hf hx le_rfl
  intro k
  induction k with
  | zero =>
    intro F f hF hf hx hk
    have hproper : F ≠ P.toSet := by
      rw [hf.2]
      exact affineZeroFace_ne_body_of_ne_zero P hP f x hx
    have hlt := faceDim_lt_of_ssubset P hF (toSet_isFace P)
      (Set.ssubset_iff_subset_ne.mpr ⟨face_subset_toSet P hF, hproper⟩)
    change faceDim F < P.dim at hlt
    have hd : faceDim F + 1 = P.dim := by rw [hP] at hlt ⊢; omega
    exact ⟨F, f, ⟨hF, hd⟩, hf, Set.Subset.rfl, rfl⟩
  | succ k ih =>
    intro F f hF hf hx hk
    by_cases heq : faceDim F + 1 = P.dim
    · exact ⟨F, f, ⟨hF, heq⟩, hf, Set.Subset.rfl, rfl⟩
    have hproper : F ≠ P.toSet := by
      rw [hf.2]
      exact affineZeroFace_ne_body_of_ne_zero P hP f x hx
    have hlt := faceDim_lt_of_ssubset P hF (toSet_isFace P)
      (Set.ssubset_iff_subset_ne.mpr ⟨face_subset_toSet P hF, hproper⟩)
    change faceDim F < P.dim at hlt
    have hgap : faceDim F + 2 ≤ d := by rw [hP] at hlt heq; omega
    obtain ⟨G, g, hG, hg, hFG, _, hgx⟩ := enlarge_supported_face P hP F hF f hf x hx hgap
    have hdim := faceDim_lt_of_ssubset P hF hG hFG
    obtain ⟨H, k, hH, hk, hGH, hkx⟩ := ih G g hG hg (hgx.trans_ne hx) (by omega)
    exact ⟨H, k, hH, hk, hFG.1.trans hGH, hkx.trans hgx⟩

theorem separating_facet_of_separating_face
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : P.IsFace F) (f : E d →ᵃ[ℝ] ℝ)
    (hf : SupportsFace P F f) (x : E d) (hx : f x < 0) :
    ∃ G : Set (E d), ∃ g : E d →ᵃ[ℝ] ℝ,
      IsFacet P G ∧ SupportsFace P G g ∧ g x < 0 := by
  obtain ⟨G, g, hG, hg, _, hval⟩ :=
    facet_containing_preserving_value P hP F hF f hf x (ne_of_lt hx)
  exact ⟨G, g, hG, hg, hval.trans_lt hx⟩

theorem exists_facet_containing_not_mem
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : P.IsFace F)
    (x : E d) (hx : x ∈ P.toSet) (hxF : x ∉ F) :
    ∃ G : Set (E d), IsFacet P G ∧ F ⊆ G ∧ x ∉ G := by
  obtain ⟨f, hf⟩ := exists_supportsFace P hF
  have hfx : f x ≠ 0 := fun heq => hxF ((hf.mem_iff x).mpr ⟨hx, heq⟩)
  obtain ⟨G, g, hG, hg, hFG, hval⟩ :=
    facet_containing_preserving_value P hP F hF f hf x hfx
  exact ⟨G, hG, hFG, fun hxG => hfx (hval.symm.trans (hg.eq_zero hxG))⟩

/-- Every nonempty geometric face is the intersection, inside the body,
of the facets containing it.  The statement includes the whole body. -/
theorem face_eq_inter_facets (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : P.IsFace F) :
    F = {x ∈ P.toSet | ∀ G : Set (E d), IsFacet P G → F ⊆ G → x ∈ G} := by
  ext x
  constructor
  · intro hx
    exact ⟨face_subset_toSet P hF hx, fun _ _ hFG => hFG hx⟩
  · rintro ⟨hx, hall⟩
    by_contra hxF
    obtain ⟨G, hG, hFG, hxG⟩ := exists_facet_containing_not_mem P hP F hF x hx hxF
    exact hxG (hall G hG hFG)

theorem exists_separating_facet (P : ConvexPolytope d) (hP : P.IsFullDim)
    (x : E d) (hx : x ∉ P.toSet) :
    ∃ F : Set (E d), ∃ f : E d →ᵃ[ℝ] ℝ,
      IsFacet P F ∧ SupportsFace P F f ∧ f x < 0 := by
  obtain ⟨l, c, hbound, hcx⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (P.vertices : Set (E d)))
    (P.vertices.finite_toSet.isClosed_convexHull ℝ) hx
  obtain ⟨v, hv, hmax⟩ := P.vertices.exists_max_image l P.vertices_nonempty
  let f : E d →ᵃ[ℝ] ℝ := AffineMap.const ℝ (E d) (l v) - l.toLinearMap.toAffineMap
  have hf : ∀ y ∈ P.toSet, 0 ≤ f y := by
    intro y hy
    have hm := le_su_toSet P l hmax y hy
    change 0 ≤ l v - l y
    linarith
  have hne : (affineZeroFace P f).Nonempty := by
    refine ⟨v, subset_convexHull ℝ _ hv, ?_⟩
    change l v - l v = 0
    exact sub_self _
  have hfx : f x < 0 := by
    have hvlt := hbound v (subset_convexHull ℝ _ hv)
    change l v - l x < 0
    linarith
  exact separating_facet_of_separating_face P hP (affineZeroFace P f)
    (affineZeroFace_isFace P f hf hne) f ⟨hf, rfl⟩ x hfx

/-- The geometric halfspace representation is derived from the finite
convex hull, and includes every point of the ambient space. -/
theorem mem_body_iff_facet_supports_nonneg (P : ConvexPolytope d) (hP : P.IsFullDim)
    (x : E d) :
    x ∈ P.toSet ↔ ∀ (F : Set (E d)) (f : E d →ᵃ[ℝ] ℝ),
      IsFacet P F → SupportsFace P F f → 0 ≤ f x := by
  constructor
  · intro hx F f _ hf
    exact hf.1 x hx
  · intro h
    by_contra hx
    obtain ⟨F, f, hF, hf, hfx⟩ := exists_separating_facet P hP x hx
    exact (not_lt_of_ge (h F f hF hf)) hfx

end Papers.Polytopes

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/FieldCoordinates.lean -/







@[expose] public section

/-!
# Field changes and homogeneous coordinates

Finite coordinate matrices have the same linear-dependence relations after
an embedding of fields. The proof extends an independent rectangular family
to a square basis, then uses the determinant and its functoriality. This
supplies the field-of-definition step in the projective reconstruction.
-/

noncomputable section

namespace Papers.Coordinates

section Homogeneous

variable {K V ι : Type*} [CommRing K] [AddCommGroup V] [Module K V]

def homogenize (p : V) : V × K := (p, 1)

theorem linearIndependent_homogenize_iff (p : ι → V) :
    LinearIndependent K (fun i => homogenize (K := K) (p i)) ↔ AffineIndependent K p := by
  rw [linearIndependent_iff', affineIndependent_iff]
  constructor
  · intro h s w hw hsum i hi
    apply h s w ?_ i hi
    apply Prod.ext
    · simpa only [Prod.fst_sum, Prod.smul_fst, homogenize, Prod.fst_zero] using hsum
    · simpa only [Prod.snd_sum, Prod.smul_snd, homogenize, smul_eq_mul, mul_one,
        Prod.snd_zero] using hw
  · intro h s w hsum i hi
    have hw := congrArg Prod.snd hsum
    have hp := congrArg Prod.fst hsum
    simp only [Prod.snd_sum, Prod.smul_snd, homogenize, smul_eq_mul, mul_one,
      Prod.snd_zero] at hw
    simp only [Prod.fst_sum, Prod.smul_fst, homogenize, Prod.fst_zero] at hp
    exact h s w hw hp i hi

end Homogeneous

section FieldEmbedding

variable {K L : Type*} [Field K] [Field L]

theorem linearIndependent_coordinate_map {m n : ℕ} (σ : K →+* L)
    (p : Fin m → Fin n → K) (hp : LinearIndependent K p) :
    LinearIndependent L (fun i j => σ (p i j)) := by
  have step : ∀ k m, ∀ p : Fin m → Fin n → K, n - m = k → LinearIndependent K p →
      LinearIndependent L (fun i j => σ (p i j)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m p hnm hp
      have hle : m ≤ n := by simpa using hp.fintype_card_le_finrank
      rcases lt_or_eq_of_le hle with hlt | heq
      · obtain ⟨w, hw⟩ := exists_linearIndependent_snoc_of_lt_finrank hp
          (by simpa using hlt)
        have hcast := ih (n - (m + 1)) (by omega) (m + 1) (Fin.snoc p w) rfl hw
        change LinearIndependent L
          ((fun x : Fin n → K => fun j => σ (x j)) ∘ Fin.snoc p w) at hcast
        rw [Fin.comp_snoc] at hcast
        exact (linearIndependent_finSnoc.mp hcast).1
      · subst m
        have hdet : Matrix.det (Matrix.of p) ≠ 0 := Matrix.nonsingular_iff_det_ne_zero.mp
          (Matrix.Nonsingular.of_linearIndependent_row hp)
        apply Matrix.linearIndependent_rows_of_det_ne_zero (A := σ.mapMatrix (Matrix.of p))
        rw [← σ.map_det]
        intro hzero
        exact hdet (σ.injective (by simpa using hzero))
  exact step (n - m) m p rfl hp

theorem linearIndependent_of_coordinate_map {m n : ℕ} (σ : K →+* L)
    (p : Fin m → Fin n → K) (hp : LinearIndependent L (fun i j => σ (p i j))) :
    LinearIndependent K p := by
  rw [linearIndependent_iff']
  intro s w hsum i hi
  have hmap : ∑ j ∈ s, σ (w j) • (fun k => σ (p j k)) = (0 : Fin n → L) := by
    ext k
    have h := congrArg σ (congrFun hsum k)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
      map_sum, map_mul, map_zero] using h
  have hzero := (linearIndependent_iff'.mp hp) s (fun j => σ (w j)) hmap i hi
  exact σ.injective (by simpa using hzero)

/-- Both directions are needed: real geometric dependence can be transported
back to the field in which the coordinate entries lie. -/
theorem linearIndependent_coordinate_map_iff {m n : ℕ} (σ : K →+* L)
    (p : Fin m → Fin n → K) :
    LinearIndependent L (fun i j => σ (p i j)) ↔ LinearIndependent K p :=
  ⟨linearIndependent_of_coordinate_map σ p, linearIndependent_coordinate_map σ p⟩

end FieldEmbedding

end Papers.Coordinates

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/HomogeneousSpan.lean -/



@[expose] public section

/-! The exact relation between affine dimension and homogeneous linear rank. -/

noncomputable section
namespace Papers.Coordinates
open Set
open scoped Pointwise

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def homogeneousSpan (S : Set V) : Submodule K (V × K) :=
  Submodule.span K (homogenize (K := K) '' S)

theorem homogenize_mem_span {S : Set V} {p : V} (hp : p ∈ S) :
    homogenize (K := K) p ∈ homogeneousSpan (K := K) S :=
  Submodule.subset_span (Set.mem_image_of_mem _ hp)

theorem direction_lift_mem_homogeneousSpan {S : Set V} {v : V}
    (hv : v ∈ vectorSpan K S) : (v, (0 : K)) ∈ homogeneousSpan (K := K) S := by
  rw [vectorSpan_def] at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨p, hp, q, hq, rfl⟩ := Set.mem_vsub.mp hv
    have h := (homogeneousSpan (K := K) S).sub_mem
      (homogenize_mem_span hp) (homogenize_mem_span hq)
    simpa only [homogenize, Prod.mk_sub_mk, sub_self, vsub_eq_sub] using h
  | zero => exact (homogeneousSpan (K := K) S).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [Prod.mk_add_mk, add_zero] using
      (homogeneousSpan (K := K) S).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [Prod.smul_mk, smul_zero] using
      (homogeneousSpan (K := K) S).smul_mem c ih

def homogeneousParam (S : Set V) (p₀ : V) :
    (vectorSpan K S × K) →ₗ[K] (V × K) where
  toFun z := (z.1.val + z.2 • p₀, z.2)
  map_add' x y := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
      module
    · rfl
  map_smul' c x := by
    apply Prod.ext
    · simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, smul_smul]
      rfl
    · rfl

theorem homogeneousParam_injective (S : Set V) (p₀ : V) :
    Function.Injective (homogeneousParam (K := K) S p₀) := by
  rintro ⟨v, c⟩ ⟨w, d⟩ heq
  have hcd : c = d := congrArg Prod.snd heq
  subst d
  apply Prod.ext
  · apply Subtype.ext
    exact add_right_cancel (show v.val + c • p₀ = w.val + c • p₀ from
      congrArg Prod.fst heq)
  · rfl

theorem homogeneousSpan_eq_range {S : Set V} {p₀ : V} (hp₀ : p₀ ∈ S) :
    homogeneousSpan (K := K) S = (homogeneousParam (K := K) S p₀).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨(⟨p - p₀, ?_⟩, 1), ?_⟩
    · exact vsub_mem_vectorSpan K hp hp₀
    · simp [homogeneousParam, homogenize]
  · rintro _ ⟨⟨v, c⟩, rfl⟩
    have h₁ := direction_lift_mem_homogeneousSpan (K := K) v.property
    have h₂ := (homogeneousSpan (K := K) S).smul_mem c (homogenize_mem_span hp₀)
    simpa [homogeneousParam, homogenize] using (homogeneousSpan (K := K) S).add_mem h₁ h₂

/-- A homogeneous vector of last coordinate one is in the homogeneous span
exactly when its affine point is in the original affine span. -/
theorem homogenize_mem_span_iff {S : Set V} (hS : S.Nonempty) (p : V) :
    homogenize (K := K) p ∈ homogeneousSpan (K := K) S ↔ p ∈ affineSpan K S := by
  obtain ⟨p₀, hp₀⟩ := hS
  constructor
  · intro hp
    rw [homogeneousSpan_eq_range hp₀] at hp
    obtain ⟨⟨v, c⟩, hv⟩ := hp
    have hc : c = 1 := congrArg Prod.snd hv
    subst c
    apply (mem_affineSpan_iff_exists K).mpr
    refine ⟨p₀, hp₀, v.val, v.property, ?_⟩
    have hv' := congrArg Prod.fst hv
    simpa [homogeneousParam, homogenize] using hv'.symm
  · intro hp
    obtain ⟨q, hq, v, hv, rfl⟩ := (mem_affineSpan_iff_exists K).mp hp
    have h₁ := direction_lift_mem_homogeneousSpan (K := K) hv
    have h₂ := homogenize_mem_span (K := K) hq
    simpa [homogenize, vadd_eq_add] using (homogeneousSpan (K := K) S).add_mem h₁ h₂

/-- Nonempty affine sets gain exactly one dimension on homogenization. -/
theorem finrank_homogeneousSpan [FiniteDimensional K V] {S : Set V}
    (hS : S.Nonempty) :
    Module.finrank K (homogeneousSpan (K := K) S) =
      Module.finrank K (vectorSpan K S) + 1 := by
  obtain ⟨p₀, hp₀⟩ := hS
  rw [homogeneousSpan_eq_range hp₀,
    LinearMap.finrank_range_of_inj (homogeneousParam_injective S p₀),
    Module.finrank_prod]
  simp

end Papers.Coordinates

end
end
end BundlePart5

section BundlePart6
/- Source: Papers/FacetNormalization.lean -/






@[expose] public section

/-!
# Uniqueness of an oriented facet form

The homogeneous span of a facet is exactly the kernel of any nonzero
supporting form.  Consequently two inward forms for the same actual facet
are positive scalar multiples.  A single chosen form for each facet is
therefore a complete halfspace representation of the polytope.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem linear_form_eq_scalar_of_ker_le
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f g : V →ₗ[K] K) (z : V) (hz : g z ≠ 0) (hker : g.ker ≤ f.ker) :
    f = (f z / g z) • g := by
  ext x
  have hmem : x - (g x / g z) • z ∈ g.ker := by
    change g (x - (g x / g z) • z) = 0
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hz, sub_self]
  have h := hker hmem
  change f (x - (g x / g z) • z) = 0 at h
  rw [map_sub, map_smul, smul_eq_mul] at h
  change f x = (f z / g z) * g x
  calc
    f x = (g x / g z) * f z := sub_eq_zero.mp h
    _ = (f z / g z) * g x := by ring

theorem affineLift_surjective {f : E d →ᵃ[ℝ] ℝ} (hf : f ≠ 0) :
    Function.Surjective (affineLift f) := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hf
    ext x
    exact h x
  intro t
  refine ⟨(t / f x) • (x, (1 : ℝ)), ?_⟩
  rw [map_smul, smul_eq_mul, affineLift_apply, homogeneousEvaluation_homogenize,
    div_mul_cancel₀ _ hx]

theorem homogeneousSpan_facet_eq_ker
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : IsFacet P F)
    (f : E d →ᵃ[ℝ] ℝ) (hf : SupportsFace P F f) :
    homogeneousSpan (K := ℝ) F = (affineLift f).ker := by
  have hle : homogeneousSpan (K := ℝ) F ≤ (affineLift f).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    change homogeneousEvaluation (x, (1 : ℝ)) f = 0
    rw [homogeneousEvaluation_homogenize, hf.eq_zero hx]
  have hdimF : finrank ℝ (homogeneousSpan (K := ℝ) F) = d := by
    rw [finrank_homogeneousSpan hF.1.2]
    change faceDim F + 1 = d
    exact hF.2.trans hP
  have hrange : (affineLift f).range = ⊤ :=
    LinearMap.range_eq_top.mpr (affineLift_surjective (hF.support_ne_zero hf))
  have hdim := (affineLift f).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, finrank_self, finrank_prod,
    finrank_euclideanSpace_fin, finrank_self] at hdim
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [hdimF]
  omega

theorem supportsFacet_positive_proportional
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : IsFacet P F)
    (f g : E d →ᵃ[ℝ] ℝ) (hf : SupportsFace P F f) (hg : SupportsFace P F g) :
    ∃ c : ℝ, 0 < c ∧ f = c • g := by
  obtain ⟨x, hxP, hxF⟩ : ∃ x, x ∈ P.toSet ∧ x ∉ F := by
    by_contra h
    push_neg at h
    exact hF.ne_toSet (Set.Subset.antisymm (face_subset_toSet P hF.1) h)
  have hfx : 0 < f x := lt_of_le_of_ne (hf.1 x hxP)
    (fun hz => hxF ((hf.mem_iff x).mpr ⟨hxP, hz.symm⟩))
  have hgx : 0 < g x := lt_of_le_of_ne (hg.1 x hxP)
    (fun hz => hxF ((hg.mem_iff x).mpr ⟨hxP, hz.symm⟩))
  have hker : (affineLift g).ker ≤ (affineLift f).ker := by
    rw [← homogeneousSpan_facet_eq_ker P hP F hF g hg,
      ← homogeneousSpan_facet_eq_ker P hP F hF f hf]
  have heq := linear_form_eq_scalar_of_ker_le
    (affineLift f) (affineLift g) (x, (1 : ℝ))
    (by simpa only [affineLift_apply, homogeneousEvaluation_homogenize] using ne_of_gt hgx)
    hker
  refine ⟨f x / g x, div_pos hfx hgx, ?_⟩
  ext y
  have h := congrArg (fun l : (E d × ℝ) →ₗ[ℝ] ℝ => l (y, 1)) heq
  simpa only [LinearMap.smul_apply, affineLift_apply, homogeneousEvaluation_homogenize,
    smul_eq_mul, AffineMap.coe_smul, Pi.smul_apply] using h

def FacetType (P : ConvexPolytope d) := {F : FaceType P // IsFacet P F.val}

instance facetTypeFintype (P : ConvexPolytope d) : Fintype (FacetType P) :=
  inferInstanceAs (Fintype {F : FaceType P // IsFacet P F.val})

def chosenFacetForm (P : ConvexPolytope d) (F : FacetType P) : E d →ᵃ[ℝ] ℝ :=
  Classical.choose (exists_supportsFace P F.val.property)

theorem chosenFacetForm_supports (P : ConvexPolytope d) (F : FacetType P) :
    SupportsFace P F.val.val (chosenFacetForm P F) :=
  Classical.choose_spec (exists_supportsFace P F.val.property)

theorem mem_body_iff_chosenFacetForms_nonneg
    (P : ConvexPolytope d) (hP : P.IsFullDim) (x : E d) :
    x ∈ P.toSet ↔ ∀ F : FacetType P, 0 ≤ chosenFacetForm P F x := by
  constructor
  · intro hx F
    exact (chosenFacetForm_supports P F).1 x hx
  · intro h
    apply (mem_body_iff_facet_supports_nonneg P hP x).mpr
    intro F f hF hf
    let F' : FacetType P := ⟨⟨F, hF.1⟩, hF⟩
    obtain ⟨c, hc, hfc⟩ := supportsFacet_positive_proportional P hP F hF f
      (chosenFacetForm P F') hf (chosenFacetForm_supports P F')
    rw [hfc]
    change 0 ≤ c * chosenFacetForm P F' x
    exact mul_nonneg hc.le (h F')

end Papers.Polytopes

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/RestorationCone.lean -/




@[expose] public section

/-!
# The cone over a simplex facet

The supporting forms through a proposed new vertex have a diagonal
evaluation matrix on the old simplex vertices.  This produces an actual
basis of edge vectors.  The cone cut on the exterior side of the simplex
hyperplane is exactly the convex hull of the new vertex and the simplex.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

def restorationConeForm (f₀ : E d →ᵃ[ℝ] ℝ)
    (f : ι → E d →ᵃ[ℝ] ℝ) (a : E d) (i : ι) : E d →ᵃ[ℝ] ℝ :=
  f i - (f i a / f₀ a) • f₀

theorem restorationConeForm_at_apex (f₀ : E d →ᵃ[ℝ] ℝ)
    (f : ι → E d →ᵃ[ℝ] ℝ) (a : E d) (ha : f₀ a ≠ 0) (i : ι) :
    restorationConeForm f₀ f a i a = 0 := by
  change f i a - (f i a / f₀ a) * f₀ a = 0
  rw [div_mul_cancel₀ _ ha, sub_self]

theorem restorationConeForm_on_hyperplane (f₀ : E d →ᵃ[ℝ] ℝ)
    (f : ι → E d →ᵃ[ℝ] ℝ) (a x : E d) (hx : f₀ x = 0) (i : ι) :
    restorationConeForm f₀ f a i x = f i x := by
  change f i x - (f i a / f₀ a) * f₀ x = f i x
  rw [hx, mul_zero, sub_zero]

theorem restorationConeForm_nonneg
    (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ)
    (a x : E d) (ha : f₀ a < 0) (hax : ∀ i, 0 ≤ f i a)
    (hx₀ : 0 ≤ f₀ x) (hx : ∀ i, 0 ≤ f i x) (i : ι) :
    0 ≤ restorationConeForm f₀ f a i x := by
  change 0 ≤ f i x - (f i a / f₀ a) * f₀ x
  have hc : f i a / f₀ a ≤ 0 := div_nonpos_of_nonneg_of_nonpos (hax i) ha.le
  exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hc hx₀).trans (hx i))

theorem diagonal_edge_family_independent
    (a : E d) (p : ι → E d) (g : ι → E d →ᵃ[ℝ] ℝ)
    (ha : ∀ i, g i a = 0)
    (hdiag : ∀ i, g i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0) :
    LinearIndependent ℝ (fun i => p i - a) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (g i).linear hc
  simp only [map_sum, map_smul, smul_eq_mul, map_zero,
    ← vsub_eq_sub, AffineMap.linear_apply_vsub, ha i] at h
  simp only [vsub_eq_sub, sub_zero] at h
  have hsum : (∑ j, c j * g i (p j)) = c i * g i (p i) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hoff i j hji.symm, mul_zero]
    · intro hi
      exact False.elim (hi (Finset.mem_univ _))
  rw [hsum] at h
  exact (mul_eq_zero.mp h).resolve_right (hdiag i)

def diagonalEdgeBasis (hcard : Fintype.card ι = d)
    (a : E d) (p : ι → E d) (g : ι → E d →ᵃ[ℝ] ℝ)
    (ha : ∀ i, g i a = 0)
    (hdiag : ∀ i, g i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0) : Basis ι ℝ (E d) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (fun i => p i - a)
    (diagonal_edge_family_independent a p g ha hdiag hoff)
    (by simpa only [finrank_euclideanSpace_fin] using hcard)

@[simp] theorem diagonalEdgeBasis_apply (hcard : Fintype.card ι = d)
    (a : E d) (p : ι → E d) (g : ι → E d →ᵃ[ℝ] ℝ)
    (ha : ∀ i, g i a = 0)
    (hdiag : ∀ i, g i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0) (i : ι) :
    diagonalEdgeBasis hcard a p g ha hdiag hoff i = p i - a := by
  simp only [diagonalEdgeBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

theorem diagonal_form_coordinate
    (a : E d) (p : ι → E d) (g : ι → E d →ᵃ[ℝ] ℝ)
    (b : Basis ι ℝ (E d)) (hb : ∀ i, b i = p i - a)
    (ha : ∀ i, g i a = 0)
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0) (x : E d) (i : ι) :
    g i x = b.repr (x - a) i * g i (p i) := by
  have h := congrArg (g i).linear (b.sum_repr (x - a))
  simp only [map_sum, map_smul, smul_eq_mul, hb,
    ← vsub_eq_sub, AffineMap.linear_apply_vsub, ha i] at h
  simp only [vsub_eq_sub, sub_zero] at h
  rw [← h]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [hoff i j hji.symm, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ _))

theorem affine_height_of_edge_coordinates
    (a : E d) (p : ι → E d) (b : Basis ι ℝ (E d))
    (hb : ∀ i, b i = p i - a) (f₀ : E d →ᵃ[ℝ] ℝ)
    (hp : ∀ i, f₀ (p i) = 0) (x : E d) :
    f₀ x = f₀ a * (1 - ∑ i, b.repr (x - a) i) := by
  have h := congrArg f₀.linear (b.sum_repr (x - a))
  simp only [map_sum, map_smul, smul_eq_mul, hb,
    ← vsub_eq_sub, AffineMap.linear_apply_vsub, hp] at h
  simp only [vsub_eq_sub, zero_sub,
    mul_neg, Finset.sum_neg_distrib, ← Finset.sum_mul] at h
  nlinarith

theorem diagonal_cone_cut_mem_simplex
    (a : E d) (p : ι → E d) (g : ι → E d →ᵃ[ℝ] ℝ)
    (b : Basis ι ℝ (E d)) (hb : ∀ i, b i = p i - a)
    (ha : ∀ i, g i a = 0) (hdiag : ∀ i, 0 < g i (p i))
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀a : f₀ a < 0) (hp₀ : ∀ i, f₀ (p i) = 0)
    (x : E d) (hx : ∀ i, 0 ≤ g i x) (hx₀ : f₀ x ≤ 0) :
    x ∈ convexHull ℝ (insert a (Set.range p)) := by
  let c : ι → ℝ := fun i => b.repr (x - a) i
  have hc : ∀ i, 0 ≤ c i := by
    intro i
    have h := hx i
    rw [diagonal_form_coordinate a p g b hb ha hoff x i] at h
    exact (mul_nonneg_iff_of_pos_right (hdiag i)).mp h
  have hsum : ∑ i, c i ≤ 1 := by
    have h := affine_height_of_edge_coordinates a p b hb f₀ hp₀ x
    change f₀ x = f₀ a * (1 - ∑ i, c i) at h
    nlinarith
  let z : Option ι → E d := fun i => i.elim a p
  let w : Option ι → ℝ := fun i => i.elim (1 - ∑ i, c i) c
  have hw : ∀ i ∈ (Finset.univ : Finset (Option ι)), 0 ≤ w i := by
    intro i _
    cases i with
    | none => exact sub_nonneg.mpr hsum
    | some j => exact hc j
  have htotal : ∑ i : Option ι, w i = 1 := by
    simp only [Fintype.sum_option, w, Option.elim_none, Option.elim_some]
    ring
  have hz : ∀ i ∈ (Finset.univ : Finset (Option ι)),
      z i ∈ convexHull ℝ (insert a (Set.range p)) := by
    intro i _
    apply subset_convexHull ℝ _
    cases i with
    | none => exact Set.mem_insert _ _
    | some j => exact Set.mem_insert_of_mem _ ⟨j, rfl⟩
  have hconv := (convex_convexHull ℝ (insert a (Set.range p))).sum_mem hw htotal hz
  have hrep : (∑ i : Option ι, w i • z i) = x := by
    simp only [Fintype.sum_option, w, z, Option.elim_none, Option.elim_some]
    have h := b.sum_repr (x - a)
    simp only [hb, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul] at h
    change (∑ i, c i • p i) - (∑ i, c i) • a = x - a at h
    calc
      (1 - ∑ i, c i) • a + ∑ i, c i • p i =
          a + ((∑ i, c i • p i) - (∑ i, c i) • a) := by module
      _ = a + (x - a) := by rw [h]
      _ = x := by module
  exact hrep ▸ hconv

end Papers.Polytopes

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/VertexAddition.lean -/



@[expose] public section

/-!
# Adjoining an exterior point while retaining all old vertices

The new point has an explicit strict separating affine form.  For every
old vertex, a supporting form which is positive at the new point can be
added to its old exposing form.  This proves that the displayed generators
are exactly the extreme vertices of the enlarged convex hull.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem polytope_eq_of_vertices_eq {P Q : ConvexPolytope d}
    (h : P.vertices = Q.vertices) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

theorem exterior_point_not_mem_vertices (P : ConvexPolytope d) (a : E d)
    (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ P.toSet, 0 ≤ f x) (ha : f a < 0) :
    a ∉ P.vertices := by
  intro h
  exact (not_lt_of_ge (hf a (subset_convexHull ℝ _ h))) ha

theorem exposing_form_after_addition (P : ConvexPolytope d) (a : E d)
    (v : VertexType P) (g : E d →ᵃ[ℝ] ℝ)
    (hg : ∀ x ∈ P.toSet, 0 ≤ g x) (hgv : g v.val = 0) (hga : 0 < g a) :
    ∃ f : E d →ᵃ[ℝ] ℝ, f v.val = 0 ∧ 0 < f a ∧
      ∀ w ∈ P.vertices, w ≠ v.val → 0 < f w := by
  obtain ⟨f, hf⟩ := exists_supportsFace P (vertex_isFace P v.property)
  have hfv : f v.val = 0 := hf.eq_zero (Set.mem_singleton _)
  let t : ℝ := (|f a| + 1) / g a
  have ht : 0 < t := div_pos (by positivity) hga
  refine ⟨f + t • g, ?_, ?_, ?_⟩
  · change f v.val + t * g v.val = 0
    rw [hfv, hgv, mul_zero, add_zero]
  · change 0 < f a + t * g a
    have hmul : t * g a = |f a| + 1 := div_mul_cancel₀ _ (ne_of_gt hga)
    rw [hmul]
    have h := neg_abs_le (f a)
    linarith
  · intro w hw hwv
    have hwP : w ∈ P.toSet := subset_convexHull ℝ _ hw
    have hfw : 0 < f w := by
      rcases lt_or_eq_of_le (hf.1 w hwP) with hp | he
      · exact hp
      · have hmem := (hf.mem_iff w).mpr ⟨hwP, he.symm⟩
        exact False.elim (hwv hmem)
    change 0 < f w + t * g w
    exact add_pos_of_pos_of_nonneg hfw (mul_nonneg ht.le (hg w hwP))

/-- Actual convex-hull extension.  The preservation premise asks only for
supporting affine forms and is discharged combinatorially in restoration. -/
def addExteriorVertex (P : ConvexPolytope d) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a) : ConvexPolytope d := by
  classical
  apply polytopeOfStrictMinima (insert a P.vertices) ⟨a, Finset.mem_insert_self _ _⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with hxa | hx
  · subst x
    refine ⟨f₀.linear.toContinuousLinearMap, ?_⟩
    intro y hy hya
    have hyP := (Finset.mem_insert.mp hy).resolve_left hya
    have hfy := hf₀ y (subset_convexHull ℝ _ hyP)
    have hfa := ha
    rw [affine_form_apply f₀ a] at hfa
    rw [affine_form_apply f₀ y] at hfy
    change f₀.linear a < f₀.linear y
    linarith
  · let v : VertexType P := ⟨x, hx⟩
    obtain ⟨g, hg, hgv, hga⟩ := hretain v
    obtain ⟨f, hfv, hfa, hfw⟩ := exposing_form_after_addition P a v g hg hgv hga
    refine ⟨f.linear.toContinuousLinearMap, ?_⟩
    intro y hy hyx
    have hfy : 0 < f y := by
      rcases Finset.mem_insert.mp hy with rfl | hyP
      · exact hfa
      · exact hfw y hyP hyx
    rw [affine_form_apply f v.val] at hfv
    rw [affine_form_apply f y] at hfy
    change f.linear x < f.linear y
    change f.linear x + f 0 = 0 at hfv
    linarith

@[simp] theorem addExteriorVertex_vertices (P : ConvexPolytope d) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a) :
    (addExteriorVertex P a f₀ hf₀ ha hretain).vertices = insert a P.vertices := rfl

theorem body_subset_addExteriorVertex (P : ConvexPolytope d) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a) :
    P.toSet ⊆ (addExteriorVertex P a f₀ hf₀ ha hretain).toSet :=
  convexHull_mono (fun _ hx => Finset.mem_insert_of_mem hx)

theorem addExteriorVertex_fullDim (P : ConvexPolytope d) (hP : P.IsFullDim) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a) :
    (addExteriorVertex P a f₀ hf₀ ha hretain).IsFullDim := by
  let Q := addExteriorVertex P a f₀ hf₀ ha hretain
  have hle : P.dim ≤ Q.dim := Submodule.finrank_mono
    (vectorSpan_mono ℝ (body_subset_addExteriorVertex P a f₀ hf₀ ha hretain))
  have hupper : Q.dim ≤ d := by
    change finrank ℝ (vectorSpan ℝ Q.toSet) ≤ d
    simpa only [finrank_euclideanSpace_fin] using
      (Submodule.finrank_le (vectorSpan ℝ Q.toSet))
  change Q.dim = d
  have heq : P.dim = d := hP
  exact le_antisymm hupper (le_trans heq.ge hle)

theorem addExteriorVertex_card (P : ConvexPolytope d) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a) :
    (addExteriorVertex P a f₀ hf₀ ha hretain).vertices.card = P.vertices.card + 1 := by
  rw [addExteriorVertex_vertices, Finset.card_insert_of_notMem
    (exterior_point_not_mem_vertices P a f₀ hf₀ ha)]

theorem addExteriorVertex_delete (P : ConvexPolytope d) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a)
    (hne : ((addExteriorVertex P a f₀ hf₀ ha hretain).vertices.erase a).Nonempty) :
    deleteVertex (addExteriorVertex P a f₀ hf₀ ha hretain) a hne = P := by
  apply polytope_eq_of_vertices_eq
  rw [deleteVertex_vertices, addExteriorVertex_vertices,
    Finset.erase_insert (exterior_point_not_mem_vertices P a f₀ hf₀ ha)]

theorem addExteriorVertex_coordinates (P : ConvexPolytope d) (a : E d)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : ∀ x ∈ P.toSet, 0 ≤ f₀ x) (ha : f₀ a < 0)
    (hretain : ∀ v : VertexType P, ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ P.toSet, 0 ≤ g x) ∧ g v.val = 0 ∧ 0 < g a)
    (K : Subfield ℝ) (hPK : CoordinatesIn K P) (haK : ∀ i, a i ∈ K) :
    CoordinatesIn K (addExteriorVertex P a f₀ hf₀ ha hretain) := by
  intro x hx i
  rcases Finset.mem_insert.mp hx with rfl | hxP
  · exact haK i
  · exact hPK x hxP i

end Papers.Polytopes

end
end
end BundlePart8

section BundlePart9
/- Source: Papers/ExtensionHalfspaces.lean -/




@[expose] public section

/-!
# The exact halfspaces after extension beyond a simplex facet

The old nonvisible facets and the cone facets give the whole enlarged
convex hull.  The proof treats the two sides of the simplex hyperplane
separately and uses the explicit barycentric cone calculation outside.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

def ExtensionFacetIndex (Q : ConvexPolytope d) (T : Set (E d)) (ι : Type*) :=
  Sum {F : FacetType Q // F.val.val ≠ T} ι

instance extensionFacetIndexFintype (Q : ConvexPolytope d) (T : Set (E d)) :
    Fintype (ExtensionFacetIndex Q T ι) :=
  inferInstanceAs (Fintype (Sum {F : FacetType Q // F.val.val ≠ T} ι))

def extensionFacetForm (Q : ConvexPolytope d) (T : Set (E d))
    (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ) (a : E d) :
    ExtensionFacetIndex Q T ι → E d →ᵃ[ℝ] ℝ :=
  Sum.elim (fun F => chosenFacetForm Q F.val) (restorationConeForm f₀ f a)

theorem old_body_subset_extension (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) : Q.toSet ⊆ R.toSet := by
  change convexHull ℝ (Q.vertices : Set (E d)) ⊆ convexHull ℝ (R.vertices : Set (E d))
  rw [hvertices]
  exact convexHull_mono (fun _ hx => Finset.mem_insert_of_mem hx)

theorem extension_fullDim (Q R : ConvexPolytope d) (hQ : Q.IsFullDim) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) : R.IsFullDim := by
  have hle : Q.dim ≤ R.dim := Submodule.finrank_mono
    (vectorSpan_mono ℝ (old_body_subset_extension Q R a hvertices))
  have hupper : R.dim ≤ d := by
    change finrank ℝ (vectorSpan ℝ R.toSet) ≤ d
    simpa only [finrank_euclideanSpace_fin] using
      (Submodule.finrank_le (vectorSpan ℝ R.toSet))
  have heq : Q.dim = d := hQ
  have hlower : d ≤ R.dim := le_trans heq.ge hle
  exact le_antisymm hupper hlower

theorem affine_nonneg_on_extension (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (g : E d →ᵃ[ℝ] ℝ)
    (hgQ : ∀ x ∈ Q.toSet, 0 ≤ g x) (hga : 0 ≤ g a) :
    ∀ x ∈ R.toSet, 0 ≤ g x := by
  apply affine_nonneg_on_hull R.vertices g
  intro x hx
  rw [hvertices] at hx
  rcases Finset.mem_insert.mp hx with rfl | hxQ
  · exact hga
  · exact hgQ x (subset_convexHull ℝ _ hxQ)

theorem simplex_hull_subset_extension
    (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (p : ι → E d) (hp : ∀ i, p i ∈ Q.vertices) :
    convexHull ℝ (insert a (Set.range p)) ⊆ R.toSet := by
  apply convexHull_mono
  intro x hx
  rw [hvertices]
  rcases Set.mem_insert_iff.mp hx with rfl | ⟨i, rfl⟩
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hp i)

theorem extensionFacetForms_nonneg
    (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (T : Set (E d)) (f₀ : E d →ᵃ[ℝ] ℝ) (f : ι → E d →ᵃ[ℝ] ℝ)
    (hf₀ : ∀ x ∈ Q.toSet, 0 ≤ f₀ x)
    (hf : ∀ i x, x ∈ Q.toSet → 0 ≤ f i x)
    (ha₀ : f₀ a < 0) (ha : ∀ i, 0 ≤ f i a)
    (hother : ∀ F : FacetType Q, F.val.val ≠ T → 0 ≤ chosenFacetForm Q F a) :
    ∀ i : ExtensionFacetIndex Q T ι, ∀ x ∈ R.toSet,
      0 ≤ extensionFacetForm Q T f₀ f a i x := by
  intro i
  cases i with
  | inl F =>
    exact affine_nonneg_on_extension Q R a hvertices (chosenFacetForm Q F.val)
      (chosenFacetForm_supports Q F.val).1 (hother F.val F.property)
  | inr i =>
    apply affine_nonneg_on_extension Q R a hvertices (restorationConeForm f₀ f a i)
    · intro x hx
      exact restorationConeForm_nonneg f₀ f a x ha₀ ha (hf₀ x hx) (fun j => hf j x hx) i
    · exact (restorationConeForm_at_apex f₀ f a (ne_of_lt ha₀) i).symm.le

/-- This is equality of subsets of the entire ambient Euclidean space,
not only equality on a prescribed list of generators. -/
theorem extension_body_iff_halfspaces
    (Q R : ConvexPolytope d) (hQ : Q.IsFullDim)
    (a : E d) (hvertices : R.vertices = insert a Q.vertices)
    (T : Set (E d)) (hT : IsFacet Q T)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : SupportsFace Q T f₀)
    (f : ι → E d →ᵃ[ℝ] ℝ)
    (hf : ∀ i x, x ∈ Q.toSet → 0 ≤ f i x)
    (p : ι → E d) (hp : ∀ i, p i ∈ Q.vertices)
    (hp₀ : ∀ i, f₀ (p i) = 0)
    (hdiag : ∀ i, 0 < f i (p i))
    (hoff : ∀ i j, i ≠ j → f i (p j) = 0)
    (hcard : Fintype.card ι = d)
    (ha₀ : f₀ a < 0) (ha : ∀ i, 0 ≤ f i a)
    (hother : ∀ F : FacetType Q, F.val.val ≠ T → 0 ≤ chosenFacetForm Q F a)
    (x : E d) :
    x ∈ R.toSet ↔ ∀ i : ExtensionFacetIndex Q T ι,
      0 ≤ extensionFacetForm Q T f₀ f a i x := by
  constructor
  · intro hx i
    exact extensionFacetForms_nonneg Q R a hvertices T f₀ f hf₀.1 hf ha₀ ha hother i x hx
  · intro hx
    by_cases hx₀ : 0 ≤ f₀ x
    · apply old_body_subset_extension Q R a hvertices
      apply (mem_body_iff_chosenFacetForms_nonneg Q hQ x).mpr
      intro F
      by_cases hFT : F.val.val = T
      · obtain ⟨c, hc, heq⟩ := supportsFacet_positive_proportional Q hQ T hT
          (chosenFacetForm Q F) f₀ (hFT ▸ chosenFacetForm_supports Q F) hf₀
        rw [heq]
        exact mul_nonneg hc.le hx₀
      · exact hx (Sum.inl ⟨F, hFT⟩)
    · let g := restorationConeForm f₀ f a
      have hga : ∀ i, g i a = 0 := restorationConeForm_at_apex f₀ f a (ne_of_lt ha₀)
      have hgdiag : ∀ i, 0 < g i (p i) := by
        intro i
        rw [show g i (p i) = f i (p i) from
          restorationConeForm_on_hyperplane f₀ f a (p i) (hp₀ i) i]
        exact hdiag i
      have hgoff : ∀ i j, i ≠ j → g i (p j) = 0 := by
        intro i j hij
        rw [show g i (p j) = f i (p j) from
          restorationConeForm_on_hyperplane f₀ f a (p j) (hp₀ j) i]
        exact hoff i j hij
      let b := diagonalEdgeBasis hcard a p g hga (fun i => ne_of_gt (hgdiag i)) hgoff
      have hb : ∀ i, b i = p i - a :=
        diagonalEdgeBasis_apply hcard a p g hga (fun i => ne_of_gt (hgdiag i)) hgoff
      have hcone := diagonal_cone_cut_mem_simplex a p g b hb hga hgdiag hgoff
        f₀ ha₀ hp₀ x (fun i => hx (Sum.inr i)) (le_of_not_ge hx₀)
      exact simplex_hull_subset_extension Q R a hvertices p hp hcone

end Papers.Polytopes

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/SimplexFacetChart.lean -/



@[expose] public section

/-!
# A positive chart for simplex-facet restoration

A common affine chart is proved to exist on the finite old vertex set and
the proposed homogeneous restoration point.  The exceptional simplex
case is kept explicit: either some neighboring support is positive at the
new point, or there is a further facet.  No chart existence hypothesis is
silently introduced into the restoration argument.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem affine_basis_not_all_zero
    (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ)) (x : E d) : ¬∀ i, b i x = 0 := by
  intro hz
  have h := congrArg (fun a : E d →ᵃ[ℝ] ℝ => a x)
    (b.sum_repr (AffineMap.const ℝ (E d) (1 : ℝ)))
  simp only [affineForm_sum_apply, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul,
    hz, mul_zero, Finset.sum_const_zero, AffineMap.coe_const, Function.const_apply] at h
  exact zero_ne_one h

theorem positive_weighted_affine_basis
    (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ)) (x : E d)
    (hx : ∀ i, 0 ≤ b i x) (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    0 < (∑ i, w i • b i) x := by
  simp only [affineForm_sum_apply, AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  have hn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i * b i x :=
    fun i _ => mul_nonneg (hw i).le (hx i)
  have hsum := Finset.sum_nonneg hn
  by_contra hnot
  have heq : ∑ i, w i * b i x = 0 := le_antisymm (le_of_not_gt hnot) hsum
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp heq
  apply affine_basis_not_all_zero b x
  intro i
  exact (mul_eq_zero.mp (hz i (Finset.mem_univ _))).resolve_left (ne_of_gt (hw i))

/-- A finite set of strict positive inequalities permits a common small
positive perturbation.  The proof takes a finite minimum of admissible
positive parameters through induction. -/
theorem finite_positive_perturbation {α : Type*} (S : Finset α) (f h : α → ℝ)
    (hf : ∀ x ∈ S, 0 < f x) (hh : ∀ x ∈ S, 0 ≤ h x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ S, ε * h x < f x := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert x S hxS ih =>
    obtain ⟨ε₀, hε₀, hS⟩ := ih
      (fun y hy => hf y (Finset.mem_insert_of_mem hy))
      (fun y hy => hh y (Finset.mem_insert_of_mem hy))
    obtain ⟨ε₁, hε₁, h₁⟩ := exists_pos_mul_lt (hf x (Finset.mem_insert_self _ _)) (h x)
    refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      calc
        min ε₀ ε₁ * h x ≤ ε₁ * h x :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (hh x (Finset.mem_insert_self _ _))
        _ < f x := by simpa only [mul_comm] using h₁
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
        (hh y (Finset.mem_insert_of_mem hy))).trans_lt (hS y hy)

def positiveRestorationChart
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (ε : ℝ) : E d →ᵃ[ℝ] ℝ :=
  ε • b none + ∑ i, b (some i)

def negativeRestorationChart
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (ε : ℝ) : E d →ᵃ[ℝ] ℝ :=
  ∑ i, b (some i) - ε • b none

theorem restoration_positive_chart_of_some_positive
    (P : ConvexPolytope d) (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ))
    (hb : ∀ i x, x ∈ P.toSet → 0 ≤ b i x)
    (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (hpos : ∃ i, 0 < t i) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ x ∈ P.toSet, 0 < positiveRestorationChart b ε x) ∧
      0 < homogeneousEvaluation (restorationVector b t) (positiveRestorationChart b ε) := by
  have hs : 0 < ∑ i, t i := by
    obtain ⟨i, hi⟩ := hpos
    exact lt_of_lt_of_le hi (Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ _))
  let ε : ℝ := (∑ i, t i) / 2
  have hε : 0 < ε := half_pos hs
  refine ⟨ε, hε, ?_, ?_⟩
  · intro x hx
    let w : Option ι → ℝ := fun i => i.elim ε (fun _ => 1)
    have hw : ∀ i, 0 < w i := by
      intro i
      cases i with
      | none => exact hε
      | some _ => exact zero_lt_one
    have h := positive_weighted_affine_basis b x (fun i => hb i x hx) w hw
    simpa only [Fintype.sum_option, w, Option.elim_none, Option.elim_some,
      one_smul, positiveRestorationChart] using h
  · rw [positiveRestorationChart, map_add, map_smul, map_sum]
    simp only [restorationVector_none, restorationVector_some, smul_eq_mul, mul_neg_one]
    dsimp only [ε]
    linarith

theorem neighbor_support_sum_pos_of_other_facet
    (P : ConvexPolytope d) (F : Option ι → Set (E d))
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (p : ι → E d)
    (hF : ∀ i, IsFacet P (F i)) (hb : ∀ i, SupportsFace P (F i) (b i))
    (hp : ∀ i, p i ∈ P.toSet)
    (h₀ : ∀ i, b none (p i) = 0)
    (hdiag : ∀ i, 0 < b (some i) (p i))
    (hoff : ∀ i j, i ≠ j → b (some i) (p j) = 0)
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (hne : ∀ i, G ≠ F i) (x : E d) (hx : x ∈ P.toSet) :
    0 < ∑ i, b (some i) x := by
  have hnonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ b (some i) x :=
    fun i _ => (hb (some i)).1 x hx
  have hsum := Finset.sum_nonneg hnonneg
  by_contra hnot
  have hz : ∑ i, b (some i) x = 0 := le_antisymm (le_of_not_gt hnot) hsum
  have hzero : ∀ i, b (some i) x = 0 :=
    fun i => (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz i (Finset.mem_univ _)
  have hrepr := homogeneousEvaluation_expansion b (x, (1 : ℝ)) g
  simp only [homogeneousEvaluation_homogenize, Fintype.sum_option, hzero,
    mul_zero, Finset.sum_const_zero, add_zero] at hrepr
  have ha := simplexFacet_other_coefficient_neg P F b p hF hb hp h₀ hdiag hoff G g hG hg hne
  have hnx := (hb none).1 x hx
  have hgx := hg.1 x hx
  have hnone : b none x = 0 := by nlinarith
  apply affine_basis_not_all_zero b x
  intro i
  cases i with
  | none => exact hnone
  | some j => exact hzero j

theorem restoration_positive_chart_of_other_facet
    (P : ConvexPolytope d) (F : Option ι → Set (E d))
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (p : ι → E d)
    (hF : ∀ i, IsFacet P (F i)) (hb : ∀ i, SupportsFace P (F i) (b i))
    (hp : ∀ i, p i ∈ P.toSet)
    (h₀ : ∀ i, b none (p i) = 0)
    (hdiag : ∀ i, 0 < b (some i) (p i))
    (hoff : ∀ i j, i ≠ j → b (some i) (p j) = 0)
    (G : Set (E d)) (g : E d →ᵃ[ℝ] ℝ)
    (hG : IsFacet P G) (hg : SupportsFace P G g)
    (hne : ∀ i, G ≠ F i) (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ x ∈ P.vertices, 0 < negativeRestorationChart b ε x) ∧
      0 < homogeneousEvaluation (restorationVector b t) (negativeRestorationChart b ε) := by
  obtain ⟨ε, hε, hbound⟩ := finite_positive_perturbation P.vertices
    (fun x => ∑ i, b (some i) x) (b none)
    (fun x hx => neighbor_support_sum_pos_of_other_facet P F b p hF hb hp h₀ hdiag hoff
      G g hG hg hne x (subset_convexHull ℝ _ hx))
    (fun x hx => (hb none).1 x (subset_convexHull ℝ _ hx))
  refine ⟨ε, hε, ?_, ?_⟩
  · intro x hx
    change 0 < (∑ i, b (some i)) x - ε * b none x
    rw [affineForm_sum_apply]
    exact sub_pos.mpr (hbound x hx)
  · rw [negativeRestorationChart, map_sub, map_sum, map_smul]
    simp only [restorationVector_none, restorationVector_some, smul_eq_mul, mul_neg_one]
    have hsum : 0 ≤ ∑ i, t i := Finset.sum_nonneg (fun i _ => ht i)
    linarith

end Papers.Polytopes

end
end
end BundlePart10

section BundlePart11
/- Source: Papers/FiniteHalfspaceFacets.lean -/




@[expose] public section

/-!
# Facet completeness for a finite halfspace description

The average of all vertices of a face detects every supporting form
vanishing on the face.  If every defining inequality were strict there,+a small explicit displacement would leave the polytope through the face
while still satisfying all the defining inequalities.  This proves
completeness of the displayed geometric facet list.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def finitePointAverage (S : Finset (E d)) : E d :=
  (S.card : ℝ)⁻¹ • ∑ x ∈ S, x

theorem finitePointAverage_mem (S : Finset (E d)) (hS : S.Nonempty) :
    finitePointAverage S ∈ convexHull ℝ (S : Set (E d)) := by
  have hn : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have h := S.centerMass_mem_convexHull
    (s := (S : Set (E d))) (w := fun _ => (1 : ℝ)) (z := id)
    (fun _ _ => zero_le_one) (by simpa using hn) (fun _ hx => hx)
  simpa [Finset.centerMass, finitePointAverage] using h

theorem affine_apply_finitePointAverage (S : Finset (E d)) (hS : S.Nonempty)
    (f : E d →ᵃ[ℝ] ℝ) :
    f (finitePointAverage S) = (S.card : ℝ)⁻¹ * ∑ x ∈ S, f x := by
  have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  rw [affine_form_apply f, finitePointAverage, map_smul, map_sum, smul_eq_mul]
  have hsum : (∑ x ∈ S, f x) = ∑ x ∈ S, (f.linear x + f 0) :=
    Finset.sum_congr rfl (fun x _ => affine_form_apply f x)
  rw [hsum]
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul]
  field_simp <;> ring

theorem affine_zero_on_hull (S : Finset (E d)) (f : E d →ᵃ[ℝ] ℝ)
    (hf : ∀ x ∈ S, f x = 0) :
    ∀ x ∈ convexHull ℝ (S : Set (E d)), f x = 0 := by
  intro x hx
  have hn := affine_nonneg_on_hull S f (fun y hy => (hf y hy).symm.le) x hx
  have hp := affine_nonneg_on_hull S (-f)
    (fun y hy => by change 0 ≤ -f y; rw [hf y hy, neg_zero]) x hx
  change 0 ≤ -f x at hp
  linarith

theorem affine_average_zero_iff (S : Finset (E d)) (hS : S.Nonempty)
    (f : E d →ᵃ[ℝ] ℝ) (hf : ∀ x ∈ S, 0 ≤ f x) :
    f (finitePointAverage S) = 0 ↔ ∀ x ∈ S, f x = 0 := by
  have hn : (S.card : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hS.card_pos.ne')
  rw [affine_apply_finitePointAverage S hS f, mul_eq_zero, or_iff_right hn]
  exact Finset.sum_eq_zero_iff_of_nonneg hf

theorem proper_face_has_active_halfspace
    {ι : Type*} [Fintype ι] (P : ConvexPolytope d)
    (f : ι → E d →ᵃ[ℝ] ℝ)
    (hbody : ∀ x, x ∈ P.toSet ↔ ∀ i, 0 ≤ f i x)
    (F : Set (E d)) (hF : P.IsFace F) (hproper : F ≠ P.toSet) :
    ∃ i, ∀ x ∈ F, f i x = 0 := by
  let S := P.vertices.filter (· ∈ F)
  have hS : S.Nonempty := (facePolytope P hF).vertices_nonempty
  let p := finitePointAverage S
  have hpF : p ∈ F := by
    rw [face_eq_hull_vertices P hF]
    exact finitePointAverage_mem S hS
  have hpP : p ∈ P.toSet := face_subset_toSet P hF hpF
  by_cases hz : ∃ i, f i p = 0
  · obtain ⟨i, hi⟩ := hz
    refine ⟨i, ?_⟩
    have hzero : ∀ x ∈ S, f i x = 0 :=
      (affine_average_zero_iff S hS (f i)
        (fun x hx => (hbody x).mp
          (subset_convexHull ℝ _ (Finset.mem_filter.mp hx).1) i)).mp hi
    intro x hx
    rw [face_eq_hull_vertices P hF] at hx
    exact affine_zero_on_hull S (f i) hzero x hx
  · have hpos : ∀ i, 0 < f i p := by
      intro i
      exact lt_of_le_of_ne ((hbody p).mp hpP i) (fun hi => hz ⟨i, hi.symm⟩)
    obtain ⟨g, hg⟩ := exists_supportsFace P hF
    obtain ⟨y, hyP, hyF⟩ : ∃ y, y ∈ P.toSet ∧ y ∉ F := by
      by_contra hy
      push_neg at hy
      exact hproper (Set.Subset.antisymm (face_subset_toSet P hF) hy)
    have hgp : g p = 0 := hg.eq_zero hpF
    have hgy : 0 < g y := by
      have hn := hg.1 y hyP
      exact lt_of_le_of_ne hn (fun hz => hyF ((hg.mem_iff y).mpr ⟨hyP, hz.symm⟩))
    let u : E d := p - y
    obtain ⟨ε, hε, hbound⟩ := finite_positive_perturbation
      (Finset.univ : Finset ι) (fun i => f i p) (fun i => |(f i).linear u|)
      (fun i _ => hpos i) (fun i _ => abs_nonneg _)
    let x := p + ε • u
    have hfx (i : ι) : f i x = f i p + ε * (f i).linear u := by
      rw [affine_form_apply (f i) x, affine_form_apply (f i) p]
      dsimp only [x]
      rw [map_add, map_smul, smul_eq_mul]
      ring
    have hxP : x ∈ P.toSet := by
      apply (hbody x).mpr
      intro i
      rw [hfx i]
      have hb := hbound i (Finset.mem_univ _)
      have hneg := mul_le_mul_of_nonneg_left (neg_abs_le ((f i).linear u)) hε.le
      linarith
    have hgu : g.linear u = -g y := by
      rw [affine_form_apply g p] at hgp
      rw [affine_form_apply g y]
      dsimp only [u]
      rw [map_sub]
      linarith
    have hgx : g x = -ε * g y := by
      rw [affine_form_apply g x]
      dsimp only [x]
      rw [map_add, map_smul, smul_eq_mul, hgu]
      have h := hgp
      rw [affine_form_apply g p] at h
      nlinarith
    have hn := hg.1 x hxP
    rw [hgx] at hn
    have hp := mul_pos hε hgy
    nlinarith

/-- A finite halfspace description whose zero sets are genuine facets
contains every facet of the polytope. -/
theorem facets_exhausted_by_halfspaces
    {ι : Type*} [Fintype ι] (P : ConvexPolytope d)
    (f : ι → E d →ᵃ[ℝ] ℝ)
    (hbody : ∀ x, x ∈ P.toSet ↔ ∀ i, 0 ≤ f i x)
    (hfacet : ∀ i, IsFacet P (affineZeroFace P (f i)))
    (F : Set (E d)) (hF : IsFacet P F) :
    ∃ i, F = affineZeroFace P (f i) := by
  obtain ⟨i, hi⟩ := proper_face_has_active_halfspace P f hbody F hF.1 hF.ne_toSet
  refine ⟨i, hF.eq_of_subset (hfacet i).1 (hfacet i).ne_toSet ?_⟩
  intro x hx
  exact ⟨face_subset_toSet P hF.1 hx, hi x hx⟩

end Papers.Polytopes

end
end
end BundlePart11

section BundlePart12
/- Source: Papers/ExtensionFacets.lean -/




@[expose] public section

/-!
# Every facet of a simplex-facet extension

Old nonvisible facets keep their dimension.  The cone forms are genuine
facets because their zero sets contain the apex and a full codimension-one
family of basis directions.  The exact halfspace representation proves
that these are all facets.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem old_facet_survives_extension
    (Q R : ConvexPolytope d) (hQ : Q.IsFullDim) (hR : R.IsFullDim)
    (hQR : Q.toSet ⊆ R.toSet)
    (F : Set (E d)) (hF : IsFacet Q F)
    (f : E d →ᵃ[ℝ] ℝ) (hf : SupportsFace Q F f)
    (hnonneg : ∀ x ∈ R.toSet, 0 ≤ f x) :
    IsFacet R (affineZeroFace R f) := by
  have hsub : F ⊆ affineZeroFace R f := by
    intro x hx
    exact ⟨hQR (face_subset_toSet Q hF.1 hx), hf.eq_zero hx⟩
  have hG : R.IsFace (affineZeroFace R f) :=
    affineZeroFace_isFace R f hnonneg (hF.1.2.mono hsub)
  have hproper : affineZeroFace R f ≠ R.toSet := by
    intro heq
    apply hF.support_ne_zero hf
    apply affine_eq_zero_of_body R hR f
    intro x hx
    exact (show x ∈ affineZeroFace R f from heq.symm ▸ hx).2
  have hlow : faceDim F ≤ faceDim (affineZeroFace R f) :=
    Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
  have hhigh := faceDim_lt_of_ssubset R hG (toSet_isFace R)
    (Set.ssubset_iff_subset_ne.mpr ⟨face_subset_toSet R hG, hproper⟩)
  have hdF := hF.2
  change faceDim (affineZeroFace R f) < R.dim at hhigh
  refine ⟨hG, ?_⟩
  rw [hQ] at hdF
  rw [hR] at hhigh ⊢
  omega

theorem diagonal_zeroFace_direction
    (R : ConvexPolytope d) (a : E d) (p : ι → E d)
    (haR : a ∈ R.toSet) (hpR : ∀ i, p i ∈ R.toSet)
    (b : Basis ι ℝ (E d)) (hb : ∀ i, b i = p i - a)
    (g : ι → E d →ᵃ[ℝ] ℝ) (ha : ∀ i, g i a = 0)
    (hdiag : ∀ i, g i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0) (i : ι) :
    vectorSpan ℝ (affineZeroFace R (g i)) = (b.coord i).ker := by
  have hzero {x : E d} (hx : g i x = 0) : b.coord i (x - a) = 0 := by
    rw [diagonal_form_coordinate a p g b hb ha hoff x i] at hx
    exact (mul_eq_zero.mp hx).resolve_right (hdiag i)
  apply le_antisymm
  · rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_vsub.mp hz
    have hx0 := hzero hx.2
    have hy0 := hzero hy.2
    change b.coord i (x - y) = 0
    rw [map_sub] at hx0 hy0 ⊢
    linarith
  · intro z hz
    change b.coord i z = 0 at hz
    rw [← b.sum_repr z]
    apply Submodule.sum_mem
    intro j _
    by_cases hji : j = i
    · subst j
      have hrepr : b.repr z i = 0 := hz
      rw [hrepr, zero_smul]
      exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      rw [hb j]
      exact vsub_mem_vectorSpan ℝ
        (show p j ∈ affineZeroFace R (g i) from ⟨hpR j, hoff i j (Ne.symm hji)⟩)
        (show a ∈ affineZeroFace R (g i) from ⟨haR, ha i⟩)

theorem diagonal_zeroFace_isFacet
    (R : ConvexPolytope d) (hR : R.IsFullDim)
    (a : E d) (p : ι → E d)
    (haR : a ∈ R.toSet) (hpR : ∀ i, p i ∈ R.toSet)
    (b : Basis ι ℝ (E d)) (hb : ∀ i, b i = p i - a)
    (g : ι → E d →ᵃ[ℝ] ℝ) (ha : ∀ i, g i a = 0)
    (hdiag : ∀ i, g i (p i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → g i (p j) = 0)
    (hnonneg : ∀ i x, x ∈ R.toSet → 0 ≤ g i x) (i : ι) :
    IsFacet R (affineZeroFace R (g i)) := by
  have hG := affineZeroFace_isFace R (g i) (hnonneg i) ⟨a, haR, ha i⟩
  have hsur : Function.Surjective (b.coord i) := by
    intro t
    refine ⟨t • b i, ?_⟩
    simp only [map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
      if_pos rfl, if_true, smul_eq_mul, mul_one]
  have hrange : (b.coord i).range = ⊤ := LinearMap.range_eq_top.mpr hsur
  have hdim := (b.coord i).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, finrank_self, finrank_euclideanSpace_fin] at hdim
  refine ⟨hG, ?_⟩
  change finrank ℝ (vectorSpan ℝ (affineZeroFace R (g i))) + 1 = R.dim
  rw [diagonal_zeroFace_direction R a p haR hpR b hb g ha hdiag hoff i, hR]
  omega

theorem extensionFacetForms_are_facets
    (Q R : ConvexPolytope d) (hQ : Q.IsFullDim)
    (a : E d) (hvertices : R.vertices = insert a Q.vertices)
    (T : Set (E d)) (f₀ : E d →ᵃ[ℝ] ℝ)
    (hf₀ : ∀ x ∈ Q.toSet, 0 ≤ f₀ x)
    (f : ι → E d →ᵃ[ℝ] ℝ)
    (hf : ∀ i x, x ∈ Q.toSet → 0 ≤ f i x)
    (p : ι → E d) (hp : ∀ i, p i ∈ Q.vertices)
    (hp₀ : ∀ i, f₀ (p i) = 0)
    (hdiag : ∀ i, 0 < f i (p i))
    (hoff : ∀ i j, i ≠ j → f i (p j) = 0)
    (hcard : Fintype.card ι = d)
    (ha₀ : f₀ a < 0) (ha : ∀ i, 0 ≤ f i a)
    (hother : ∀ F : FacetType Q, F.val.val ≠ T → 0 ≤ chosenFacetForm Q F a) :
    ∀ i : ExtensionFacetIndex Q T ι,
      IsFacet R (affineZeroFace R (extensionFacetForm Q T f₀ f a i)) := by
  have hR := extension_fullDim Q R hQ a hvertices
  have hQR := old_body_subset_extension Q R a hvertices
  have hnonneg := extensionFacetForms_nonneg Q R a hvertices T f₀ f hf₀ hf ha₀ ha hother
  have haR : a ∈ R.toSet := subset_convexHull ℝ _ (by rw [hvertices]; exact Finset.mem_insert_self _ _)
  have hpR : ∀ i, p i ∈ R.toSet :=
    fun i => hQR (subset_convexHull ℝ _ (hp i))
  intro i
  cases i with
  | inl F =>
    exact old_facet_survives_extension Q R hQ hR hQR F.val.val.val F.val.property
      (chosenFacetForm Q F.val) (chosenFacetForm_supports Q F.val) (hnonneg (Sum.inl F))
  | inr i =>
    let g := restorationConeForm f₀ f a
    have hga : ∀ j, g j a = 0 := restorationConeForm_at_apex f₀ f a (ne_of_lt ha₀)
    have hgdiag : ∀ j, g j (p j) ≠ 0 := by
      intro j
      rw [show g j (p j) = f j (p j) from
        restorationConeForm_on_hyperplane f₀ f a (p j) (hp₀ j) j]
      exact ne_of_gt (hdiag j)
    have hgoff : ∀ j k, j ≠ k → g j (p k) = 0 := by
      intro j k hjk
      rw [show g j (p k) = f j (p k) from
        restorationConeForm_on_hyperplane f₀ f a (p k) (hp₀ k) j]
      exact hoff j k hjk
    let b := diagonalEdgeBasis hcard a p g hga hgdiag hgoff
    have hb : ∀ j, b j = p j - a := diagonalEdgeBasis_apply hcard a p g hga hgdiag hgoff
    exact diagonal_zeroFace_isFacet R hR a p haR hpR b hb g hga hgdiag hgoff
      (fun j => hnonneg (Sum.inr j)) i

theorem extension_facets_complete
    (Q R : ConvexPolytope d) (hQ : Q.IsFullDim)
    (a : E d) (hvertices : R.vertices = insert a Q.vertices)
    (T : Set (E d)) (hT : IsFacet Q T)
    (f₀ : E d →ᵃ[ℝ] ℝ) (hf₀ : SupportsFace Q T f₀)
    (f : ι → E d →ᵃ[ℝ] ℝ)
    (hf : ∀ i x, x ∈ Q.toSet → 0 ≤ f i x)
    (p : ι → E d) (hp : ∀ i, p i ∈ Q.vertices)
    (hp₀ : ∀ i, f₀ (p i) = 0)
    (hdiag : ∀ i, 0 < f i (p i))
    (hoff : ∀ i j, i ≠ j → f i (p j) = 0)
    (hcard : Fintype.card ι = d)
    (ha₀ : f₀ a < 0) (ha : ∀ i, 0 ≤ f i a)
    (hother : ∀ F : FacetType Q, F.val.val ≠ T → 0 ≤ chosenFacetForm Q F a)
    (F : Set (E d)) (hF : IsFacet R F) :
    ∃ i : ExtensionFacetIndex Q T ι,
      F = affineZeroFace R (extensionFacetForm Q T f₀ f a i) := by
  apply facets_exhausted_by_halfspaces R (extensionFacetForm Q T f₀ f a)
    (extension_body_iff_halfspaces Q R hQ a hvertices T hT f₀ hf₀ f hf p hp hp₀
      hdiag hoff hcard ha₀ ha hother)
    (extensionFacetForms_are_facets Q R hQ a hvertices T f₀ hf₀.1 f hf p hp hp₀
      hdiag hoff hcard ha₀ ha hother) F hF

end Papers.Polytopes

end
end
end BundlePart12

section BundlePart13
/- Source: Papers/FacetVertexDictionary.lean -/




@[expose] public section

/-!
# Recovering all faces from facet--vertex incidences

Finite intersections of geometric faces are exposed by sums of supporting
affine forms.  The facet-intersection theorem then upgrades a bijection of
vertices preserving the two complete facet families to an ordinary face
order isomorphism.  No abstract incidence object replaces the convex body.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ}

def indexedFaceIntersection {ι : Type*} (P : ConvexPolytope d)
    (S : Finset ι) (F : ι → FaceType P) : Set (E d) :=
  {x ∈ P.toSet | ∀ i ∈ S, x ∈ (F i).val}

theorem indexedFaceIntersection_isFace {ι : Type*} (P : ConvexPolytope d)
    (S : Finset ι) (F : ι → FaceType P)
    (hne : (indexedFaceIntersection P S F).Nonempty) :
    P.IsFace (indexedFaceIntersection P S F) := by
  let f : ι → E d →ᵃ[ℝ] ℝ := fun i => Classical.choose
    (exists_supportsFace P (F i).property)
  have hf (i : ι) : SupportsFace P (F i).val (f i) :=
    Classical.choose_spec (exists_supportsFace P (F i).property)
  let g : E d →ᵃ[ℝ] ℝ := ∑ i ∈ S, f i
  have hg : ∀ x ∈ P.toSet, 0 ≤ g x := by
    intro x hx
    rw [show g x = ∑ i ∈ S, f i x from affineForm_sum_apply S f x]
    exact Finset.sum_nonneg (fun i _ => (hf i).1 x hx)
  have heq : indexedFaceIntersection P S F = affineZeroFace P g := by
    ext x
    change (x ∈ P.toSet ∧ ∀ i ∈ S, x ∈ (F i).val) ↔
      x ∈ P.toSet ∧ g x = 0
    constructor
    · rintro ⟨hx, hall⟩
      refine ⟨hx, ?_⟩
      rw [show g x = ∑ i ∈ S, f i x from affineForm_sum_apply S f x]
      exact Finset.sum_eq_zero (fun i hi => (hf i).eq_zero (hall i hi))
    · rintro ⟨hx, hz⟩
      rw [show g x = ∑ i ∈ S, f i x from affineForm_sum_apply S f x] at hz
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i (_ : i ∈ S) => (hf i).1 x hx)).mp hz
      exact ⟨hx, fun i hi => ((hf i).mem_iff x).mpr ⟨hx, hall i hi⟩⟩
  rw [heq]
  exact affineZeroFace_isFace P g hg (heq ▸ hne)

theorem face_forward_of_facet_incidence
    (P : ConvexPolytope d) (hP : P.IsFullDim) (Q : ConvexPolytope e)
    (b : VertexType P ≃ VertexType Q)
    (hfacets : ∀ F : FaceType P, IsFacet P F.val →
      ∃ G : FaceType Q, IsFacet Q G.val ∧
        ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val)
    (F : FaceType P) :
    ∃ G : FaceType Q, ∀ v : VertexType P,
      (b v).val ∈ G.val ↔ v.val ∈ F.val := by
  let S : Finset (FaceType P) := Finset.univ.filter
    (fun H => IsFacet P H.val ∧ F.val ⊆ H.val)
  let g : FaceType P → FaceType Q := fun H =>
    if hH : IsFacet P H.val then Classical.choose (hfacets H hH)
    else ⟨Q.toSet, toSet_isFace Q⟩
  have hg (H : FaceType P) (hH : IsFacet P H.val) (v : VertexType P) :
      (b v).val ∈ (g H).val ↔ v.val ∈ H.val := by
    dsimp only [g]
    rw [dif_pos hH]
    exact (Classical.choose_spec (hfacets H hH)).2 v
  have hS (H : FaceType P) : H ∈ S ↔ IsFacet P H.val ∧ F.val ⊆ H.val := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hne : (indexedFaceIntersection Q S g).Nonempty := by
    obtain ⟨x, hx⟩ := (facePolytope P F.property).vertices_nonempty
    obtain ⟨hxP, hxF⟩ := Finset.mem_filter.mp hx
    let v : VertexType P := ⟨x, hxP⟩
    refine ⟨(b v).val, subset_convexHull ℝ _ (b v).property, ?_⟩
    intro H hH
    obtain ⟨hfacet, hFH⟩ := (hS H).mp hH
    exact (hg H hfacet v).mpr (hFH hxF)
  refine ⟨⟨indexedFaceIntersection Q S g,
    indexedFaceIntersection_isFace Q S g hne⟩, ?_⟩
  intro v
  change ((b v).val ∈ Q.toSet ∧ ∀ H ∈ S, (b v).val ∈ (g H).val) ↔ v.val ∈ F.val
  constructor
  · rintro ⟨_, hall⟩
    rw [face_eq_inter_facets P hP F.val F.property]
    refine ⟨subset_convexHull ℝ _ v.property, ?_⟩
    intro H hH hFH
    let H' : FaceType P := ⟨H, hH.1⟩
    exact (hg H' hH v).mp (hall H' ((hS H').mpr ⟨hH, hFH⟩))
  · intro hv
    refine ⟨subset_convexHull ℝ _ (b v).property, ?_⟩
    intro H hH
    obtain ⟨hfacet, hFH⟩ := (hS H).mp hH
    exact (hg H hfacet v).mpr (hFH hv)

/-- Two-way coverage of actual facets, with all vertex incidences,
determines the full ordinary geometric face order. -/
def faceOrderIsoOfFacetIncidence
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (Q : ConvexPolytope e) (hQ : Q.IsFullDim)
    (b : VertexType P ≃ VertexType Q)
    (hforward : ∀ F : FaceType P, IsFacet P F.val →
      ∃ G : FaceType Q, IsFacet Q G.val ∧
        ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val)
    (hbackward : ∀ G : FaceType Q, IsFacet Q G.val →
      ∃ F : FaceType P, IsFacet P F.val ∧
        ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val) :
    FaceType P ≃o FaceType Q := by
  apply faceOrderIsoOfVertexIncidence P Q b
    (face_forward_of_facet_incidence P hP Q b hforward)
  intro G
  have hback : ∀ H : FaceType Q, IsFacet Q H.val →
      ∃ F : FaceType P, IsFacet P F.val ∧
        ∀ w : VertexType Q, (b.symm w).val ∈ F.val ↔ w.val ∈ H.val := by
    intro H hH
    obtain ⟨F, hF, hinc⟩ := hbackward H hH
    refine ⟨F, hF, ?_⟩
    intro w
    simpa only [b.apply_symm_apply] using (hinc (b.symm w)).symm
  obtain ⟨F, hF⟩ := face_forward_of_facet_incidence Q hQ P b.symm hback G
  refine ⟨F, ?_⟩
  intro v
  simpa only [b.symm_apply_apply] using (hF (b v)).symm

end Papers.Polytopes

end
end
end BundlePart13

section BundlePart14
/- Source: Papers/SimplexFacetPresentation.lean -/




@[expose] public section

/-!
# Geometric data at a simplex facet

This structure records actual vertices, actual facets and their supporting
forms.  Its later instances are derived from ordinary face isomorphisms.
The finite diagonal evaluation pattern supplies the affine-form basis;
strict positivity on all other facets is a theorem, not stored data.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

structure SimplexFacetPresentation (Q : ConvexPolytope d) (ι : Type*) [Fintype ι] where
  fullDim : Q.IsFullDim
  index_card : Fintype.card ι = d
  facet : Option ι → FacetType Q
  form : Option ι → E d →ᵃ[ℝ] ℝ
  supports : ∀ i, SupportsFace Q (facet i).val.val (form i)
  vertex : ι → VertexType Q
  at_base : ∀ i, form none (vertex i).val = 0
  diagonal : ∀ i, 0 < form (some i) (vertex i).val
  off_diagonal : ∀ i j, i ≠ j → form (some i) (vertex j).val = 0

namespace SimplexFacetPresentation

variable {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q ι)

def base : Set (E d) := (D.facet none).val.val

theorem base_isFacet : IsFacet Q D.base := (D.facet none).property

theorem exists_outside_base : ∃ q : VertexType Q, D.form none q.val ≠ 0 := by
  by_contra h
  push_neg at h
  apply D.base_isFacet.support_ne_zero (D.supports none)
  apply affine_eq_zero_of_vertices Q D.fullDim (D.form none)
  intro x hx
  exact h ⟨x, hx⟩

def outsideVertex : VertexType Q := Classical.choose D.exists_outside_base

theorem outsideVertex_form_ne : D.form none D.outsideVertex.val ≠ 0 :=
  Classical.choose_spec D.exists_outside_base

def basis : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ) :=
  simplexSupportBasis D.index_card (D.form none) (fun i => D.form (some i))
    (fun i => (D.vertex i).val) D.outsideVertex.val D.at_base D.outsideVertex_form_ne
    (fun i => ne_of_gt (D.diagonal i)) D.off_diagonal

@[simp] theorem basis_apply (i : Option ι) : D.basis i = D.form i := by
  rw [basis, simplexSupportBasis_apply]
  cases i <;> rfl

theorem form_nonneg (i : Option ι) (x : E d) (hx : x ∈ Q.toSet) :
    0 ≤ D.form i x := (D.supports i).1 x hx

theorem facet_injective : Function.Injective D.facet := by
  intro i j heq
  by_contra hij
  cases i with
  | none =>
    cases j with
    | none => exact hij rfl
    | some j =>
      have hp : (D.vertex j).val ∈ (D.facet none).val.val :=
        ((D.supports none).mem_iff _).mpr
          ⟨subset_convexHull ℝ _ (D.vertex j).property, D.at_base j⟩
      rw [heq] at hp
      have hz := (D.supports (some j)).eq_zero hp
      exact (ne_of_gt (D.diagonal j)) hz
  | some i =>
    cases j with
    | none =>
      have hp : (D.vertex i).val ∈ (D.facet none).val.val :=
        ((D.supports none).mem_iff _).mpr
          ⟨subset_convexHull ℝ _ (D.vertex i).property, D.at_base i⟩
      rw [← heq] at hp
      exact (ne_of_gt (D.diagonal i)) ((D.supports (some i)).eq_zero hp)
    | some j =>
      have hne : j ≠ i := fun h => hij (congrArg Option.some h.symm)
      have hp : (D.vertex i).val ∈ (D.facet (some j)).val.val :=
        ((D.supports (some j)).mem_iff _).mpr
          ⟨subset_convexHull ℝ _ (D.vertex i).property, D.off_diagonal j i hne⟩
      rw [← heq] at hp
      exact (ne_of_gt (D.diagonal i)) ((D.supports (some i)).eq_zero hp)

theorem facet_set_injective : Function.Injective (fun i => (D.facet i).val.val) := by
  intro i j heq
  apply D.facet_injective
  apply Subtype.ext
  exact Subtype.ext heq

def AdmissiblePoint (a : E d) : Prop :=
  D.form none a < 0 ∧ ∀ i, 0 ≤ D.form (some i) a

theorem other_facet_positive
    (a : E d) (ha : D.AdmissiblePoint a)
    (G : FacetType Q) (hne : ∀ i, G ≠ D.facet i) :
    0 < chosenFacetForm Q G a := by
  let g := chosenFacetForm Q G
  have hne' : ∀ i, G.val.val ≠ (D.facet i).val.val := by
    intro i hi
    exact hne i (Subtype.ext (Subtype.ext hi))
  have hneg := simplexFacet_other_coefficient_neg Q
    (fun i => (D.facet i).val.val) D.basis (fun i => (D.vertex i).val)
    (fun i => (D.facet i).property)
    (fun i => by simpa only [D.basis_apply] using D.supports i)
    (fun i => subset_convexHull ℝ _ (D.vertex i).property)
    (by simpa only [D.basis_apply] using D.at_base)
    (by simpa only [D.basis_apply] using D.diagonal)
    (by simpa only [D.basis_apply] using D.off_diagonal)
    G.val.val g G.property (chosenFacetForm_supports Q G) hne'
  have hcoeff := basis_repr_some_nonneg D.basis (fun i => (D.vertex i).val)
    (by simpa only [D.basis_apply] using D.at_base)
    (by simpa only [D.basis_apply] using D.diagonal)
    (by simpa only [D.basis_apply] using D.off_diagonal)
    g (fun i => (chosenFacetForm_supports Q G).1 _
      (subset_convexHull ℝ _ (D.vertex i).property))
  have heq := homogeneousEvaluation_expansion D.basis (a, (1 : ℝ)) g
  simp only [homogeneousEvaluation_homogenize, Fintype.sum_option, D.basis_apply] at heq
  rw [heq]
  exact add_pos_of_pos_of_nonneg (mul_pos_of_neg_of_neg hneg ha.1)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hcoeff i) (ha.2 i)))

theorem nonbase_facet_nonneg
    (a : E d) (ha : D.AdmissiblePoint a)
    (G : FacetType Q) (hne : G.val.val ≠ D.base) :
    0 ≤ chosenFacetForm Q G a := by
  by_cases hG : ∃ i, G = D.facet (some i)
  · obtain ⟨i, rfl⟩ := hG
    obtain ⟨c, hc, hform⟩ := supportsFacet_positive_proportional Q D.fullDim
      (D.facet (some i)).val.val (D.facet (some i)).property
      (chosenFacetForm Q (D.facet (some i))) (D.form (some i))
      (chosenFacetForm_supports Q (D.facet (some i))) (D.supports (some i))
    rw [hform]
    exact mul_nonneg hc.le (ha.2 i)
  · apply (D.other_facet_positive a ha G ?_).le
    intro i hi
    cases i with
    | none => exact hne (congrArg (fun F : FacetType Q => F.val.val) hi)
    | some j => exact hG ⟨j, hi⟩

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart14

section BundlePart15
/- Source: Papers/SimpleDeletionPresentation.lean -/




@[expose] public section

/-!
# The simplex-facet data come from simple deletion

The neighboring facets are obtained by geometric facet separation of the
proper simplex faces.  Every facet visible from the original vertex is
proved to be the new simplex facet.  Thus the original vertex satisfies
the restoration sign conditions without an extra incidence assumption.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem two_le_dimension_of_simple_deletion
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card) : 2 ≤ d := by
  letI := neighborIndex_nonempty_of_vertex_count P hP v hs hcard
  let u : NeighborIndex P v := Classical.choice inferInstance
  obtain ⟨x, hxP, hxv, hxnot⟩ := exists_vertex_outside_corner P hP v hs hcard
  have huv : u.val.val ≠ v.val :=
    ((adj_iff_generalVertexStep P v u.val).mp u.property).2.1.symm
  have hxu : x ≠ u.val.val := by
    intro h
    apply hxnot
    rw [h]
    exact (adj_iff_generalVertexStep P v u.val).mp u.property
  have hnc := vertices_not_collinear P v.property u.val.property hxP huv.symm hxv.symm hxu.symm
  by_contra hd
  apply hnc
  rw [collinear_iff_finrank_le_one]
  have hle := Submodule.finrank_le (vectorSpan ℝ ({v.val, u.val.val, x} : Set (E d)))
  rw [finrank_euclideanSpace_fin] at hle
  omega

theorem deletionFacetSet_isFacet
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) :
    IsFacet (deleteVertex P v.val hne) (deletionFacetSet P v) := by
  refine ⟨deletionFacetSet_isFace P hP v hs hcard hne, ?_⟩
  rw [deleteVertex_fullDim_of_simple P hP v hs hcard hne]
  exact deletionFacetSet_dimension P hP v hs hcard

theorem negative_deletion_facet_eq_new_facet
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty)
    (F : Set (E d)) (hF : IsFacet (deleteVertex P v.val hne) F)
    (f : E d →ᵃ[ℝ] ℝ) (hf : SupportsFace (deleteVertex P v.val hne) F f)
    (hv : f v.val < 0) : F = deletionFacetSet P v := by
  let Q := deleteVertex P v.val hne
  let l : E d →L[ℝ] ℝ := -f.linear.toContinuousLinearMap
  have hneighbors : ∀ u : NeighborIndex P v, l u.val.val ≤ f 0 := by
    intro u
    have h := hf.1 _ (neighbor_mem_deletion P v hne u)
    rw [affine_form_apply f u.val.val] at h
    change -f.linear u.val.val ≤ f 0
    linarith
  have hlv : f 0 < l v.val := by
    rw [affine_form_apply f v.val] at hv
    change f 0 < -f.linear v.val
    linarith
  have hsub : F ⊆ deletionFacetSet P v := by
    rw [face_eq_hull_vertices Q hF.1]
    apply convexHull_mono
    intro x hx
    obtain ⟨hxQ, hxF⟩ := Finset.mem_filter.mp hx
    have hxP : x ∈ P.vertices := Finset.mem_of_mem_erase hxQ
    have hxv : x ≠ v.val := Finset.ne_of_mem_erase hxQ
    have hstep : GeneralVertexStep P v.val x := by
      by_contra hnot
      have hlt := nonneighbor_strict_bound P hP v hs l (f 0) hneighbors hlv hxP hxv hnot
      have hz := hf.eq_zero hxF
      rw [affine_form_apply f x] at hz
      change -f.linear x < f 0 at hlt
      linarith
    let u : NeighborIndex P v :=
      ⟨⟨x, hxP⟩, (adj_iff_generalVertexStep P v ⟨x, hxP⟩).mpr hstep⟩
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have hT := deletionFacetSet_isFacet P hP v hs hcard hne
  exact hF.eq_of_subset hT.1 hT.ne_toSet hsub

theorem deleted_vertex_not_mem_body
    (P : ConvexPolytope d) (v : VertexType P)
    (hne : (P.vertices.erase v.val).Nonempty) :
    v.val ∉ (deleteVertex P v.val hne).toSet := by
  intro hv
  have h := (vertex_mem_hull_vertexSubset_iff P (P.vertices.erase v.val)
    (Finset.erase_subset _ _) v).mp hv
  exact Finset.notMem_erase _ _ h

theorem new_facet_support_negative_at_deleted_vertex
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty)
    (f : E d →ᵃ[ℝ] ℝ)
    (hf : SupportsFace (deleteVertex P v.val hne) (deletionFacetSet P v) f) :
    f v.val < 0 := by
  let Q := deleteVertex P v.val hne
  have hQ := deleteVertex_fullDim_of_simple P hP v hs hcard hne
  obtain ⟨F, g, hF, hg, hgv⟩ := exists_separating_facet Q hQ v.val
    (deleted_vertex_not_mem_body P v hne)
  have hFT := negative_deletion_facet_eq_new_facet P hP v hs hcard hne F hF g hg hgv
  obtain ⟨c, hc, heq⟩ := supportsFacet_positive_proportional Q hQ (deletionFacetSet P v)
    (deletionFacetSet_isFacet P hP v hs hcard hne) f g hf (hFT ▸ hg)
  rw [heq]
  exact mul_neg_of_pos_of_neg hc hgv

def deletionNeighborVertex (P : ConvexPolytope d) (v : VertexType P)
    (hne : (P.vertices.erase v.val).Nonempty) (i : NeighborIndex P v) :
    VertexType (deleteVertex P v.val hne) :=
  ⟨i.val.val, Finset.mem_erase.mpr
    ⟨((adj_iff_generalVertexStep P v i.val).mp i.property).2.1.symm, i.val.property⟩⟩

theorem exists_deletion_simplexFacetPresentation
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) :
    ∃ D : SimplexFacetPresentation (deleteVertex P v.val hne) (NeighborIndex P v),
      D.base = deletionFacetSet P v ∧
      (∀ i, D.vertex i = deletionNeighborVertex P v hne i) ∧ D.AdmissiblePoint v.val := by
  let Q := deleteVertex P v.val hne
  let N := NeighborIndex P v
  let p : N → VertexType Q := deletionNeighborVertex P v hne
  have hd := two_le_dimension_of_simple_deletion P hP v hs hcard
  have hQ := deleteVertex_fullDim_of_simple P hP v hs hcard hne
  have hT := deletionFacetSet_isFacet P hP v hs hcard hne
  let T : FacetType Q := ⟨⟨deletionFacetSet P v, hT.1⟩, hT⟩
  have hfacets (i : N) : ∃ G : FacetType Q,
      (p i).val ∉ G.val.val ∧ ∀ j : N, j ≠ i → (p j).val ∈ G.val.val := by
    let S := (neighborVertices P v).erase (p i).val
    have hiN : (p i).val ∈ neighborVertices P v :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hS : S.Nonempty := by
      apply Finset.card_pos.mp
      change 0 < ((neighborVertices P v).erase (p i).val).card
      rw [Finset.card_erase_of_mem hiN, neighborVertices_card P hP v hs]
      omega
    have hSface := neighbor_subset_isFace P hP v hs hcard hne S hS (Finset.erase_subset _ _)
    have hip : (p i).val ∉ convexHull ℝ (S : Set (E d)) := by
      intro hi
      have hmem := (vertex_mem_hull_vertexSubset_iff P S
        (fun x hx => by
          obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hx)
          exact u.val.property) i.val).mp hi
      exact (Finset.mem_erase.mp hmem).1 rfl
    obtain ⟨G, hG, hSG, hiG⟩ := exists_facet_containing_not_mem Q hQ
      (convexHull ℝ (S : Set (E d))) hSface (p i).val
      (subset_convexHull ℝ _ (p i).property) hip
    refine ⟨⟨⟨G, hG.1⟩, hG⟩, hiG, ?_⟩
    intro j hji
    apply hSG
    apply subset_convexHull ℝ _
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
    intro heq
    exact hji (Subtype.ext (Subtype.ext heq))
  let G : N → FacetType Q := fun i => Classical.choose (hfacets i)
  have hGi (i : N) : (p i).val ∉ (G i).val.val ∧
      ∀ j : N, j ≠ i → (p j).val ∈ (G i).val.val := Classical.choose_spec (hfacets i)
  let F : Option N → FacetType Q := fun i => i.elim T G
  let form : Option N → E d →ᵃ[ℝ] ℝ := fun i => chosenFacetForm Q (F i)
  have hsupp : ∀ i, SupportsFace Q (F i).val.val (form i) :=
    fun i => chosenFacetForm_supports Q (F i)
  have hpT (i : N) : (p i).val ∈ T.val.val :=
    subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let D : SimplexFacetPresentation Q N := {
    fullDim := hQ
    index_card := by simpa only [finrank_euclideanSpace_fin] using card_neighbors_of_simple P hP v hs
    facet := F
    form := form
    supports := hsupp
    vertex := p
    at_base := fun i => (hsupp none).eq_zero (hpT i)
    diagonal := by
      intro i
      exact lt_of_le_of_ne ((hsupp (some i)).1 _ (subset_convexHull ℝ _ (p i).property))
        (fun hz => (hGi i).1 (((hsupp (some i)).mem_iff _).mpr
          ⟨subset_convexHull ℝ _ (p i).property, hz.symm⟩))
    off_diagonal := by
      intro i j hij
      exact (hsupp (some i)).eq_zero ((hGi i).2 j hij.symm) }
  refine ⟨D, rfl, fun _ => rfl, ?_, ?_⟩
  · exact new_facet_support_negative_at_deleted_vertex P hP v hs hcard hne
      (form none) (hsupp none)
  · intro i
    by_contra hi
    have hneg : form (some i) v.val < 0 := lt_of_not_ge hi
    have hGT := negative_deletion_facet_eq_new_facet P hP v hs hcard hne
      (G i).val.val (G i).property (form (some i)) (hsupp (some i)) hneg
    exact (hGi i).1 (hGT.symm ▸ hpT i)

end Papers.Polytopes

end
end
end BundlePart15

section BundlePart16
/- Source: Papers/ProjectivePolytope.lean -/





@[expose] public section

/-!
# Positive projective transformations of finite convex polytopes

The homogeneous linear isomorphism and positive normalizing factors are
explicit.  All target generators are proved to be extreme points, and
every exposed face is transported in both directions.  Thus the resulting
equivalence is an ordinary face-poset isomorphism, with no additional
combinatorial incidence hypothesis.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ}

theorem positive_projective_labels_injective
    (P : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ))
    (q : VertexType P → E e) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) : Function.Injective q := by
  intro v w hq
  have hcross : h w • (v.val, (1 : ℝ)) = h v • (w.val, (1 : ℝ)) := by
    apply L.injective
    rw [map_smul, map_smul, hL v, hL w, hq]
    simp only [smul_smul, mul_comm]
  have hscale : h w = h v := by
    have hs := congrArg Prod.snd hcross
    simpa only [Prod.smul_snd, smul_eq_mul, mul_one] using hs
  have hvalue := congrArg Prod.fst hcross
  simp only [Prod.smul_fst, hscale] at hvalue
  exact Subtype.ext (smul_right_injective _ (ne_of_gt (hh v)) hvalue)

theorem projective_support_nonneg
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (f : E d →ᵃ[ℝ] ℝ)
    (x : E d) (y : E e) (h : ℝ) (hh : 0 < h)
    (hL : L (x, 1) = h • (y, 1)) (hf : 0 ≤ f x) :
    0 ≤ projectiveTransportAffine L f y := by
  have heq := projectiveTransportAffine_scaled L f x y h hL
  rw [heq] at hf
  exact (mul_nonneg_iff_of_pos_left hh).mp hf

theorem projective_support_zero_iff
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (f : E d →ᵃ[ℝ] ℝ)
    (x : E d) (y : E e) (h : ℝ) (hh : h ≠ 0)
    (hL : L (x, 1) = h • (y, 1)) :
    projectiveTransportAffine L f y = 0 ↔ f x = 0 := by
  rw [projectiveTransportAffine_scaled L f x y h hL]
  exact (mul_eq_zero.trans (or_iff_right hh)).symm

def projectivePolytope
    (P : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ))
    (q : VertexType P → E e) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) : ConvexPolytope e := by
  classical
  let s := Finset.univ.image q
  have hs : s.Nonempty := by
    obtain ⟨x, hx⟩ := P.vertices_nonempty
    exact ⟨q ⟨x, hx⟩, Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩⟩
  apply polytopeOfStrictMinima s hs
  intro x hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨f, hf⟩ := exists_supportsFace P (vertex_isFace P v.property)
  let g := projectiveTransportAffine L f
  have hgv : g (q v) = 0 :=
    (projective_support_zero_iff L f v.val (q v) (h v) (ne_of_gt (hh v)) (hL v)).mpr
      (hf.eq_zero (Set.mem_singleton _))
  refine ⟨g.linear.toContinuousLinearMap, ?_⟩
  intro y hy hyne
  obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hy
  have hwv : w ≠ v := fun heq => hyne (congrArg q heq)
  have hfw : 0 < f w.val := by
    have hfn := hf.1 w.val (subset_convexHull ℝ _ w.property)
    rcases lt_or_eq_of_le hfn with hp | he
    · exact hp
    · have hw : w.val ∈ ({v.val} : Set (E d)) :=
        (hf.mem_iff w.val).mpr ⟨subset_convexHull ℝ _ w.property, he.symm⟩
      exact False.elim (hwv (Subtype.ext hw))
  have hscale := projectiveTransportAffine_scaled L f w.val (q w) (h w) (hL w)
  have hgw : 0 < g (q w) := by
    change 0 < projectiveTransportAffine L f (q w)
    rw [hscale] at hfw
    exact (mul_pos_iff_of_pos_left (hh w)).mp hfw
  change g.linear (q v) < g.linear (q w)
  rw [affine_form_apply g (q v)] at hgv
  rw [affine_form_apply g (q w)] at hgw
  linarith

@[simp] theorem projectivePolytope_vertices
    (P : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ))
    (q : VertexType P → E e) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) :
    (projectivePolytope P L q h hh hL).vertices = Finset.univ.image q := rfl

def projectiveVertexEquiv
    (P : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ))
    (q : VertexType P → E e) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) :
    VertexType P ≃ VertexType (projectivePolytope P L q h hh hL) := by
  classical
  let f : VertexType P → VertexType (projectivePolytope P L q h hh hL) :=
    fun v => ⟨q v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro v w heq
    exact positive_projective_labels_injective P L q h hh hL (congrArg Subtype.val heq)
  · rintro ⟨x, hx⟩
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨v, rfl⟩

@[simp] theorem projectiveVertexEquiv_apply_val
    (P : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ))
    (q : VertexType P → E e) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) (v : VertexType P) :
    (projectiveVertexEquiv P L q h hh hL v).val = q v := rfl

theorem positive_projective_face_forward
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (b : VertexType P ≃ VertexType Q)
    (h : VertexType P → ℝ) (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1))
    (F : FaceType P) : ∃ G : FaceType Q,
      ∀ v : VertexType P, (b v).val ∈ G.val ↔ v.val ∈ F.val := by
  obtain ⟨f, hf⟩ := exists_supportsFace P F.property
  let g := projectiveTransportAffine L f
  have hgV : ∀ y ∈ Q.vertices, 0 ≤ g y := by
    intro y hy
    obtain ⟨v, hv⟩ := b.surjective ⟨y, hy⟩
    have hby : (b v).val = y := congrArg Subtype.val hv
    rw [← hby]
    exact projective_support_nonneg L f v.val (b v).val (h v) (hh v) (hL v)
      (hf.1 v.val (subset_convexHull ℝ _ v.property))
  have hgP : ∀ y ∈ Q.toSet, 0 ≤ g y := affine_nonneg_on_hull Q.vertices g hgV
  obtain ⟨x, hx⟩ := (facePolytope P F.property).vertices_nonempty
  have hxP : x ∈ P.vertices := (Finset.mem_filter.mp hx).1
  have hxF : x ∈ F.val := (Finset.mem_filter.mp hx).2
  let v : VertexType P := ⟨x, hxP⟩
  have hgv : g (b v).val = 0 :=
    (projective_support_zero_iff L f v.val (b v).val (h v) (ne_of_gt (hh v)) (hL v)).mpr
      (hf.eq_zero hxF)
  have hne : (affineZeroFace Q g).Nonempty :=
    ⟨(b v).val, subset_convexHull ℝ _ (b v).property, hgv⟩
  let G : FaceType Q := ⟨affineZeroFace Q g, affineZeroFace_isFace Q g hgP hne⟩
  refine ⟨G, ?_⟩
  intro w
  have hbwQ : (b w).val ∈ Q.toSet := subset_convexHull ℝ _ (b w).property
  have hwP : w.val ∈ P.toSet := subset_convexHull ℝ _ w.property
  change ((b w).val ∈ Q.toSet ∧ g (b w).val = 0) ↔ w.val ∈ F.val
  rw [and_iff_right hbwQ]
  rw [projective_support_zero_iff L f w.val (b w).val (h w) (ne_of_gt (hh w)) (hL w)]
  exact ((hf.mem_iff w.val).trans (and_iff_right hwP)).symm

def positiveProjectiveFaceOrderIso
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (b : VertexType P ≃ VertexType Q)
    (h : VertexType P → ℝ) (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1)) :
    FaceType P ≃o FaceType Q := by
  apply faceOrderIsoOfVertexIncidence P Q b
    (positive_projective_face_forward P Q L b h hh hL)
  intro G
  let h' : VertexType Q → ℝ := fun w => (h (b.symm w))⁻¹
  have hh' : ∀ w, 0 < h' w := fun w => inv_pos.mpr (hh (b.symm w))
  have hL' : ∀ w, L.symm (w.val, 1) = h' w • ((b.symm w).val, 1) := by
    intro w
    have heq := congrArg L.symm (hL (b.symm w))
    simp only [L.symm_apply_apply, b.apply_symm_apply, map_smul] at heq
    rw [heq]
    simp only [h', smul_smul, inv_mul_cancel₀ (ne_of_gt (hh (b.symm w))), one_smul]
  obtain ⟨F, hF⟩ := positive_projective_face_forward Q P L.symm b.symm h' hh' hL' G
  refine ⟨F, ?_⟩
  intro v
  simpa only [b.symm_apply_apply] using (hF (b v)).symm

def projectivePolytopeFaceOrderIso
    (P : ConvexPolytope d) (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ))
    (q : VertexType P → E e) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) :
    FaceType P ≃o FaceType (projectivePolytope P L q h hh hL) :=
  positiveProjectiveFaceOrderIso P _ L (projectiveVertexEquiv P L q h hh hL) h hh hL

end Papers.Polytopes

end
end
end BundlePart16

section BundlePart17
/- Source: Papers/SimplexFacetTransport.lean -/



@[expose] public section

/-!
# Transport of simplex-facet data through the ordinary face order

Facet dimensions and vertex incidences are recovered from the order
isomorphism.  Supporting forms are selected afresh in the target
realization.  Their numerical coefficients need not agree; only the
proved geometric incidence pattern is used.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ} {ι : Type*} [Fintype ι]

theorem imageFace_isFacet_iff {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (F : FaceType P) :
    IsFacet Q (φ F).val ↔ IsFacet P F.val := by
  change (Q.IsFace (φ F).val ∧ faceDim (φ F).val + 1 = Q.dim) ↔
    P.IsFace F.val ∧ faceDim F.val + 1 = P.dim
  rw [faceOrderIso_dimension φ F, faceOrderIso_polytope_dim φ]
  simp only [(φ F).property, F.property, true_and]

def facetEquivOfFaceOrder {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) : FacetType P ≃ FacetType Q where
  toFun F := ⟨φ F.val, (imageFace_isFacet_iff φ F.val).mpr F.property⟩
  invFun G := ⟨φ.symm G.val, (imageFace_isFacet_iff φ.symm G.val).mpr G.property⟩
  left_inv F := by
    apply Subtype.ext
    exact φ.symm_apply_apply F.val
  right_inv G := by
    apply Subtype.ext
    exact φ.apply_symm_apply G.val

@[simp] theorem facetEquivOfFaceOrder_apply_val {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (F : FacetType P) :
    (facetEquivOfFaceOrder φ F).val = φ F.val := rfl

namespace SimplexFacetPresentation

variable {P Q : ConvexPolytope d}

def transport (D : SimplexFacetPresentation P ι) (φ : FaceType P ≃o FaceType Q) :
    SimplexFacetPresentation Q ι where
  fullDim := (faceOrderIso_polytope_dim φ).trans D.fullDim
  index_card := D.index_card
  facet := fun i => facetEquivOfFaceOrder φ (D.facet i)
  form := fun i => chosenFacetForm Q (facetEquivOfFaceOrder φ (D.facet i))
  supports := fun i => chosenFacetForm_supports Q (facetEquivOfFaceOrder φ (D.facet i))
  vertex := fun i => imageVertex φ (D.vertex i)
  at_base := by
    intro i
    apply (chosenFacetForm_supports Q (facetEquivOfFaceOrder φ (D.facet none))).eq_zero
    apply (imageVertex_mem_iff φ (D.vertex i) (D.facet none).val).mpr
    exact ((D.supports none).mem_iff _).mpr
      ⟨subset_convexHull ℝ _ (D.vertex i).property, D.at_base i⟩
  diagonal := by
    intro i
    let w := imageVertex φ (D.vertex i)
    let F := facetEquivOfFaceOrder φ (D.facet (some i))
    have hw : w.val ∈ Q.toSet := subset_convexHull ℝ _ w.property
    apply lt_of_le_of_ne ((chosenFacetForm_supports Q F).1 w.val hw)
    intro hz
    have hwF := ((chosenFacetForm_supports Q F).mem_iff w.val).mpr ⟨hw, hz.symm⟩
    have hpF := (imageVertex_mem_iff φ (D.vertex i) (D.facet (some i)).val).mp hwF
    exact (ne_of_gt (D.diagonal i)) ((D.supports (some i)).eq_zero hpF)
  off_diagonal := by
    intro i j hij
    apply (chosenFacetForm_supports Q (facetEquivOfFaceOrder φ (D.facet (some i)))).eq_zero
    apply (imageVertex_mem_iff φ (D.vertex j) (D.facet (some i)).val).mpr
    exact ((D.supports (some i)).mem_iff _).mpr
      ⟨subset_convexHull ℝ _ (D.vertex j).property, D.off_diagonal i j hij⟩

/-- Replace the supporting forms by any other proved inward forms for the
same facets.  This permits forms with coefficients in a specified field. -/
def withForms (D : SimplexFacetPresentation P ι)
    (f : Option ι → E d →ᵃ[ℝ] ℝ)
    (hf : ∀ i, SupportsFace P (D.facet i).val.val (f i)) :
    SimplexFacetPresentation P ι where
  fullDim := D.fullDim
  index_card := D.index_card
  facet := D.facet
  form := f
  supports := hf
  vertex := D.vertex
  at_base := fun i => (hf none).eq_zero
    (((D.supports none).mem_iff _).mpr
      ⟨subset_convexHull ℝ _ (D.vertex i).property, D.at_base i⟩)
  diagonal := by
    intro i
    apply lt_of_le_of_ne ((hf (some i)).1 _ (subset_convexHull ℝ _ (D.vertex i).property))
    intro hz
    have hp := ((hf (some i)).mem_iff _).mpr
      ⟨subset_convexHull ℝ _ (D.vertex i).property, hz.symm⟩
    exact (ne_of_gt (D.diagonal i)) ((D.supports (some i)).eq_zero hp)
  off_diagonal := fun i j hij => (hf (some i)).eq_zero
    (((D.supports (some i)).mem_iff _).mpr
      ⟨subset_convexHull ℝ _ (D.vertex j).property, D.off_diagonal i j hij⟩)

def Aligned (D : SimplexFacetPresentation P ι) (D₂ : SimplexFacetPresentation Q ι)
    (φ : FaceType P ≃o FaceType Q) : Prop :=
  (∀ i, D₂.facet i = facetEquivOfFaceOrder φ (D.facet i)) ∧
    ∀ i, D₂.vertex i = imageVertex φ (D.vertex i)

theorem transport_aligned (D : SimplexFacetPresentation P ι)
    (φ : FaceType P ≃o FaceType Q) : D.Aligned (D.transport φ) φ :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem chosen_form_zero_iff (D : SimplexFacetPresentation P ι)
    (i : Option ι) (a : E d) :
    chosenFacetForm P (D.facet i) a = 0 ↔ D.form i a = 0 := by
  obtain ⟨c, hc, heq⟩ := supportsFacet_positive_proportional P D.fullDim
    (D.facet i).val.val (D.facet i).property
    (chosenFacetForm P (D.facet i)) (D.form i)
    (chosenFacetForm_supports P (D.facet i)) (D.supports i)
  rw [heq]
  change c * D.form i a = 0 ↔ D.form i a = 0
  exact mul_eq_zero.trans (or_iff_right (ne_of_gt hc))

def SameCoplanar (D : SimplexFacetPresentation P ι) (a : E d)
    (D₂ : SimplexFacetPresentation Q ι) (a' : E d) : Prop :=
  ∀ i, D.form (some i) a = 0 ↔ D₂.form (some i) a' = 0

theorem nonbase_zero_preserved
    (D : SimplexFacetPresentation P ι) (D₂ : SimplexFacetPresentation Q ι)
    (φ : FaceType P ≃o FaceType Q) (hDE : D.Aligned D₂ φ)
    (a a' : E d) (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (hsame : D.SameCoplanar a D₂ a')
    (F : FacetType P) (hF : F.val.val ≠ D.base) :
    chosenFacetForm P F a = 0 ↔
      chosenFacetForm Q (facetEquivOfFaceOrder φ F) a' = 0 := by
  by_cases hFi : ∃ i, F = D.facet (some i)
  · obtain ⟨i, rfl⟩ := hFi
    rw [← hDE.1 (some i), D.chosen_form_zero_iff, D₂.chosen_form_zero_iff]
    exact hsame i
  · have hne : ∀ i, F ≠ D.facet i := by
      intro i hi
      cases i with
      | none => exact hF (congrArg (fun G : FacetType P => G.val.val) hi)
      | some j => exact hFi ⟨j, hi⟩
    have hne' : ∀ i, facetEquivOfFaceOrder φ F ≠ D₂.facet i := by
      intro i hi
      rw [hDE.1 i] at hi
      exact hne i ((facetEquivOfFaceOrder φ).injective hi)
    have hpos := D.other_facet_positive a ha F hne
    have hpos' := D₂.other_facet_positive a' ha' (facetEquivOfFaceOrder φ F) hne'
    exact iff_of_false (ne_of_gt hpos) (ne_of_gt hpos')

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart17

section BundlePart18
/- Source: Papers/ProjectiveFaceSupport.lean -/




@[expose] public section

/-!
# The vertex and support dictionaries of the projective face isomorphism

The induced vertex map is proved to be the explicit projective vertex
map.  Supporting affine forms consequently transport to the exact image
face, so their signs can be used in restoration without an additional
compatibility hypothesis.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ}

theorem imageVertex_eq_of_face_incidence
    {P : ConvexPolytope d} {Q : ConvexPolytope e}
    (φ : FaceType P ≃o FaceType Q) (b : VertexType P ≃ VertexType Q)
    (hinc : ∀ (F : FaceType P) (v : VertexType P),
      (b v).val ∈ (φ F).val ↔ v.val ∈ F.val)
    (v : VertexType P) : imageVertex φ v = b v := by
  have hm := (hinc (vertexFace P v) v).mpr (Set.mem_singleton _)
  rw [← imageVertex_face φ v] at hm
  exact Subtype.ext (show (imageVertex φ v).val = (b v).val from hm.symm)

theorem positiveProjectiveFaceOrderIso_incidence
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (b : VertexType P ≃ VertexType Q)
    (h : VertexType P → ℝ) (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1))
    (F : FaceType P) (v : VertexType P) :
    (b v).val ∈ (positiveProjectiveFaceOrderIso P Q L b h hh hL F).val ↔ v.val ∈ F.val := by
  change (b v).val ∈ (Classical.choose
    (positive_projective_face_forward P Q L b h hh hL F)).val ↔ v.val ∈ F.val
  exact Classical.choose_spec (positive_projective_face_forward P Q L b h hh hL F) v

theorem positiveProjectiveFaceOrderIso_vertex
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (b : VertexType P ≃ VertexType Q)
    (h : VertexType P → ℝ) (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1)) (v : VertexType P) :
    imageVertex (positiveProjectiveFaceOrderIso P Q L b h hh hL) v = b v :=
  imageVertex_eq_of_face_incidence _ b
    (positiveProjectiveFaceOrderIso_incidence P Q L b h hh hL) v

theorem positiveProjectiveFaceOrderIso_supports
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E e × ℝ)) (b : VertexType P ≃ VertexType Q)
    (h : VertexType P → ℝ) (hh : ∀ v, 0 < h v)
    (hL : ∀ v, L (v.val, 1) = h v • ((b v).val, 1))
    (F : FaceType P) (f : E d →ᵃ[ℝ] ℝ) (hf : SupportsFace P F.val f) :
    SupportsFace Q (positiveProjectiveFaceOrderIso P Q L b h hh hL F).val
      (projectiveTransportAffine L f) := by
  let g := projectiveTransportAffine L f
  let φ := positiveProjectiveFaceOrderIso P Q L b h hh hL
  have hgV : ∀ x ∈ Q.vertices, 0 ≤ g x := by
    intro x hx
    obtain ⟨v, hv⟩ := b.surjective ⟨x, hx⟩
    have hval : (b v).val = x := congrArg Subtype.val hv
    rw [← hval]
    exact projective_support_nonneg L f v.val (b v).val (h v) (hh v) (hL v)
      (hf.1 v.val (subset_convexHull ℝ _ v.property))
  have hg : ∀ x ∈ Q.toSet, 0 ≤ g x := affine_nonneg_on_hull Q.vertices g hgV
  have hinc (v : VertexType P) : (b v).val ∈ affineZeroFace Q g ↔ v.val ∈ F.val := by
    have hbvQ : (b v).val ∈ Q.toSet := subset_convexHull ℝ _ (b v).property
    have hvP : v.val ∈ P.toSet := subset_convexHull ℝ _ v.property
    change ((b v).val ∈ Q.toSet ∧ g (b v).val = 0) ↔ v.val ∈ F.val
    rw [and_iff_right hbvQ]
    rw [projective_support_zero_iff L f v.val (b v).val (h v) (ne_of_gt (hh v)) (hL v)]
    exact ((hf.mem_iff v.val).trans
      (and_iff_right hvP)).symm
  have hne : (affineZeroFace Q g).Nonempty := by
    obtain ⟨x, hx⟩ := (facePolytope P F.property).vertices_nonempty
    obtain ⟨hxP, hxF⟩ := Finset.mem_filter.mp hx
    exact ⟨(b ⟨x, hxP⟩).val, (hinc ⟨x, hxP⟩).mpr hxF⟩
  let G : FaceType Q := ⟨affineZeroFace Q g, affineZeroFace_isFace Q g hg hne⟩
  have heq : φ F = G := by
    apply face_eq_of_vertex_incidence Q
    intro w
    obtain ⟨v, rfl⟩ := b.surjective w
    exact (positiveProjectiveFaceOrderIso_incidence P Q L b h hh hL F v).trans (hinc v).symm
  exact ⟨hg, congrArg Subtype.val heq⟩

end Papers.Polytopes

end
end
end BundlePart18

section BundlePart19
/- Source: Papers/PresentedExtension.lean -/



@[expose] public section

/-!
# Complete facets and vertex retention for a presented extension

All assertions here concern an existing actual convex polytope with the
displayed old and new vertices.  The retention witness is extracted from
its ordinary facets.  This witness will be transported to construct a new
extension, avoiding a circular assumption that the construction has kept
the old vertices extreme.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

def extensionVertexLabels (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : a ∉ Q.vertices) :
    Option (VertexType Q) ≃ VertexType R := by
  let f : Option (VertexType Q) → VertexType R := fun u =>
    u.elim ⟨a, by rw [hvertices]; exact Finset.mem_insert_self _ _⟩
      (fun v => ⟨v.val, by rw [hvertices]; exact Finset.mem_insert_of_mem v.property⟩)
  apply Equiv.ofBijective f
  constructor
  · intro u v heq
    have hval := congrArg Subtype.val heq
    cases u with
    | none =>
      cases v with
      | none => rfl
      | some v =>
        have hv : a = v.val := hval
        exact False.elim (ha (hv.symm ▸ v.property))
    | some u =>
      cases v with
      | none =>
        have hu : u.val = a := hval
        exact False.elim (ha (hu ▸ u.property))
      | some v => exact congrArg Option.some (Subtype.ext hval)
  · intro v
    have hv : v.val ∈ insert a Q.vertices :=
      (congrArg (fun s : Finset (E d) => v.val ∈ s) hvertices).mp v.property
    rcases Finset.mem_insert.mp hv with hv | hv
    · refine ⟨none, ?_⟩
      exact Subtype.ext hv.symm
    · refine ⟨some ⟨v.val, hv⟩, ?_⟩
      rfl

@[simp] theorem extensionVertexLabels_none (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : a ∉ Q.vertices) :
    (extensionVertexLabels Q R a hvertices ha none).val = a := rfl

@[simp] theorem extensionVertexLabels_some (Q R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : a ∉ Q.vertices)
    (v : VertexType Q) :
    (extensionVertexLabels Q R a hvertices ha (some v)).val = v.val := rfl

namespace SimplexFacetPresentation

variable {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q ι)

def extensionForm (a : E d) : ExtensionFacetIndex Q D.base ι → E d →ᵃ[ℝ] ℝ :=
  extensionFacetForm Q D.base (D.form none) (fun i => D.form (some i)) a

theorem apex_not_mem_vertices (a : E d) (ha : D.AdmissiblePoint a) : a ∉ Q.vertices :=
  exterior_point_not_mem_vertices Q a (D.form none) (D.supports none).1 ha.1

theorem extension_form_nonneg (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : D.AdmissiblePoint a) :
    ∀ i, ∀ x ∈ R.toSet, 0 ≤ D.extensionForm a i x :=
  extensionFacetForms_nonneg Q R a hvertices D.base (D.form none)
    (fun i => D.form (some i)) (D.supports none).1
    (fun i => (D.supports (some i)).1) ha.1 ha.2 (D.nonbase_facet_nonneg a ha)

theorem extension_form_isFacet (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : D.AdmissiblePoint a) :
    ∀ i, IsFacet R (affineZeroFace R (D.extensionForm a i)) :=
  extensionFacetForms_are_facets Q R D.fullDim a hvertices D.base (D.form none)
    (D.supports none).1 (fun i => D.form (some i))
    (fun i => (D.supports (some i)).1) (fun i => (D.vertex i).val)
    (fun i => (D.vertex i).property) D.at_base D.diagonal D.off_diagonal
    D.index_card ha.1 ha.2 (D.nonbase_facet_nonneg a ha)

theorem extension_facets (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : D.AdmissiblePoint a)
    (F : Set (E d)) (hF : IsFacet R F) :
    ∃ i, F = affineZeroFace R (D.extensionForm a i) :=
  extension_facets_complete Q R D.fullDim a hvertices D.base D.base_isFacet
    (D.form none) (D.supports none) (fun i => D.form (some i))
    (fun i => (D.supports (some i)).1) (fun i => (D.vertex i).val)
    (fun i => (D.vertex i).property) D.at_base D.diagonal D.off_diagonal
    D.index_card ha.1 ha.2 (D.nonbase_facet_nonneg a ha) F hF

theorem cone_form_zero_iff (a : E d) (ha : D.AdmissiblePoint a)
    (i : ι) (x : E d) (hx : x ∈ Q.toSet) :
    D.extensionForm a (Sum.inr i) x = 0 ↔
      D.form (some i) x = 0 ∧ (D.form (some i) a = 0 ∨ D.form none x = 0) := by
  change D.form (some i) x -
    (D.form (some i) a / D.form none a) * D.form none x = 0 ↔ _
  by_cases hai : D.form (some i) a = 0
  · simp only [hai, zero_div, zero_mul, sub_zero, true_or, and_true]
  · have hp : 0 < D.form (some i) a := lt_of_le_of_ne (ha.2 i) (Ne.symm hai)
    have hc : D.form (some i) a / D.form none a < 0 := div_neg_of_pos_of_neg hp ha.1
    have hix := D.form_nonneg (some i) x hx
    have h₀x := D.form_nonneg none x hx
    simp only [hai, false_or]
    constructor
    · intro hzero
      constructor <;> nlinarith
    · rintro ⟨hi, h₀⟩
      rw [hi, h₀, mul_zero, sub_zero]

/-- Every old actual vertex lies on an old nonbase facet that is strictly
inside at the apex.  This is proved from the existing extension, not
assumed in the construction of another realization. -/
theorem retention_facet (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : D.AdmissiblePoint a)
    (v : VertexType Q) :
    ∃ F : FacetType Q, F.val.val ≠ D.base ∧ v.val ∈ F.val.val ∧
      0 < chosenFacetForm Q F a := by
  have hR := extension_fullDim Q R D.fullDim a hvertices
  have hvR : v.val ∈ R.vertices := by rw [hvertices]; exact Finset.mem_insert_of_mem v.property
  have haR : a ∈ R.toSet := subset_convexHull ℝ _ (by rw [hvertices]; exact Finset.mem_insert_self _ _)
  have hav : a ≠ v.val := fun h => D.apex_not_mem_vertices a ha (h.symm ▸ v.property)
  obtain ⟨H, hH, hvH, haH⟩ := exists_facet_containing_not_mem R hR
    ({v.val} : Set (E d)) (vertex_isFace R hvR) a haR hav
  obtain ⟨i, hi⟩ := D.extension_facets R a hvertices ha H hH
  cases i with
  | inl F =>
    have hzv : chosenFacetForm Q F.val v.val = 0 := by
      have hmem := hvH (Set.mem_singleton _)
      rw [hi] at hmem
      exact hmem.2
    have hza : chosenFacetForm Q F.val a ≠ 0 := by
      intro hz
      apply haH
      rw [hi]
      exact ⟨haR, hz⟩
    exact ⟨F.val, F.property,
      ((chosenFacetForm_supports Q F.val).mem_iff _).mpr
        ⟨subset_convexHull ℝ _ v.property, hzv⟩,
      lt_of_le_of_ne (D.nonbase_facet_nonneg a ha F.val F.property) (Ne.symm hza)⟩
  | inr i =>
    apply False.elim
    apply haH
    rw [hi]
    exact ⟨haR, restorationConeForm_at_apex (D.form none)
      (fun i => D.form (some i)) a (ne_of_lt ha.1) i⟩

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart19

section BundlePart20
/- Source: Papers/EquivalentExtensions.lean -/





@[expose] public section

/-!
# The face lattice of an extension depends on the prescribed coplanar facets

The ordinary face isomorphism of the old polytopes transports the full
facet list.  The new point is specified by the base facet and the zero
pattern on its neighboring facets.  The proof includes retention of every
old vertex and constructs the ordinary face order of the enlarged hulls.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

def extensionLabelPoint {Q : ConvexPolytope d} (a : E d) : Option (VertexType Q) → E d :=
  fun u => u.elim a Subtype.val

namespace SimplexFacetPresentation

variable {Q Q' : ConvexPolytope d}

theorem aligned_base_eq_iff
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ) (F : FacetType Q) :
    F.val.val = D.base ↔ (facetEquivOfFaceOrder φ F).val.val = D₂.base := by
  constructor
  · intro h
    have hF : F = D.facet none := Subtype.ext (Subtype.ext h)
    rw [hF, ← hDE.1 none]
    rfl
  · intro h
    have hF : facetEquivOfFaceOrder φ F = D₂.facet none := Subtype.ext (Subtype.ext h)
    rw [hDE.1 none] at hF
    exact congrArg (fun F : FacetType Q => F.val.val)
      ((facetEquivOfFaceOrder φ).injective hF)

def nonbaseFacetEquiv
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ) :
    {F : FacetType Q // F.val.val ≠ D.base} ≃
      {F : FacetType Q' // F.val.val ≠ D₂.base} :=
  (facetEquivOfFaceOrder φ).subtypeEquiv
    (fun F => not_congr (D.aligned_base_eq_iff D₂ φ hDE F))

def extensionIndexEquiv
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ) :
    ExtensionFacetIndex Q D.base ι ≃ ExtensionFacetIndex Q' D₂.base ι :=
  Equiv.sumCongr (D.nonbaseFacetEquiv D₂ φ hDE) (Equiv.refl ι)

theorem form_zero_at_old_vertex_preserved
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ)
    (i : Option ι) (v : VertexType Q) :
    D.form i v.val = 0 ↔ D₂.form i (imageVertex φ v).val = 0 := by
  have hvQ : v.val ∈ Q.toSet := subset_convexHull ℝ _ v.property
  have hvQ' : (imageVertex φ v).val ∈ Q'.toSet :=
    subset_convexHull ℝ _ (imageVertex φ v).property
  have hleft := (D.supports i).mem_iff v.val
  have hright := (D₂.supports i).mem_iff (imageVertex φ v).val
  rw [and_iff_right hvQ] at hleft
  rw [and_iff_right hvQ'] at hright
  rw [← hleft, ← hright, hDE.1 i]
  exact (imageVertex_mem_iff φ v (D.facet i).val).symm

theorem extension_zero_incidence_preserved
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ)
    (a a' : E d) (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (hsame : D.SameCoplanar a D₂ a')
    (i : ExtensionFacetIndex Q D.base ι) (u : Option (VertexType Q)) :
    D.extensionForm a i (extensionLabelPoint a u) = 0 ↔
      D₂.extensionForm a' (D.extensionIndexEquiv D₂ φ hDE i)
        (extensionLabelPoint a' (Equiv.optionCongr (vertexEquivOfFaceOrder φ) u)) = 0 := by
  cases i with
  | inl F =>
    cases u with
    | none =>
      exact D.nonbase_zero_preserved D₂ φ hDE a a' ha ha' hsame F.val F.property
    | some v =>
      change chosenFacetForm Q F.val v.val = 0 ↔
        chosenFacetForm Q' (facetEquivOfFaceOrder φ F.val) (imageVertex φ v).val = 0
      have hleft := (chosenFacetForm_supports Q F.val).mem_iff v.val
      have hright := (chosenFacetForm_supports Q' (facetEquivOfFaceOrder φ F.val)).mem_iff
        (imageVertex φ v).val
      have hvQ : v.val ∈ Q.toSet := subset_convexHull ℝ _ v.property
      have hvQ' : (imageVertex φ v).val ∈ Q'.toSet :=
        subset_convexHull ℝ _ (imageVertex φ v).property
      rw [and_iff_right hvQ] at hleft
      rw [and_iff_right hvQ'] at hright
      rw [← hleft, ← hright]
      exact (imageVertex_mem_iff φ v F.val.val).symm
  | inr i =>
    cases u with
    | none =>
      have h := restorationConeForm_at_apex (D.form none) (fun i => D.form (some i))
        a (ne_of_lt ha.1) i
      have h' := restorationConeForm_at_apex (D₂.form none) (fun i => D₂.form (some i))
        a' (ne_of_lt ha'.1) i
      exact iff_of_true h h'
    | some v =>
      change D.extensionForm a (Sum.inr i) v.val = 0 ↔
        D₂.extensionForm a' (Sum.inr i) (imageVertex φ v).val = 0
      rw [D.cone_form_zero_iff a ha i v.val (subset_convexHull ℝ _ v.property),
        D₂.cone_form_zero_iff a' ha' i (imageVertex φ v).val
          (subset_convexHull ℝ _ (imageVertex φ v).property),
        D.form_zero_at_old_vertex_preserved D₂ φ hDE (some i) v,
        D.form_zero_at_old_vertex_preserved D₂ φ hDE none v,
        hsame i]

theorem transferred_retention
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ)
    (R : ConvexPolytope d) (a a' : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (hsame : D.SameCoplanar a D₂ a') :
    ∀ v' : VertexType Q', ∃ g : E d →ᵃ[ℝ] ℝ,
      (∀ x ∈ Q'.toSet, 0 ≤ g x) ∧ g v'.val = 0 ∧ 0 < g a' := by
  intro v'
  obtain ⟨v, rfl⟩ := (vertexEquivOfFaceOrder φ).surjective v'
  obtain ⟨F, hFT, hvF, hFa⟩ := D.retention_facet R a hvertices ha v
  let F' := facetEquivOfFaceOrder φ F
  have hF'T : F'.val.val ≠ D₂.base :=
    (not_congr (D.aligned_base_eq_iff D₂ φ hDE F)).mp hFT
  have hvF' : (imageVertex φ v).val ∈ F'.val.val :=
    (imageVertex_mem_iff φ v F.val).mpr hvF
  have hFa' : chosenFacetForm Q' F' a' ≠ 0 := by
    intro hz
    exact (ne_of_gt hFa) ((D.nonbase_zero_preserved D₂ φ hDE a a' ha ha' hsame F hFT).mpr hz)
  exact ⟨chosenFacetForm Q' F', (chosenFacetForm_supports Q' F').1,
    (chosenFacetForm_supports Q' F').eq_zero hvF',
    lt_of_le_of_ne (D₂.nonbase_facet_nonneg a' ha' F' hF'T) (Ne.symm hFa')⟩

def extensionVertexEquiv
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q')
    (R R' : ConvexPolytope d) (a a' : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (hvertices' : R'.vertices = insert a' Q'.vertices)
    (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a') :
    VertexType R ≃ VertexType R' :=
  (extensionVertexLabels Q R a hvertices (D.apex_not_mem_vertices a ha)).symm.trans
    ((Equiv.optionCongr (vertexEquivOfFaceOrder φ)).trans
      (extensionVertexLabels Q' R' a' hvertices' (D₂.apex_not_mem_vertices a' ha')))

def extensionFaceOrderIso
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ)
    (R R' : ConvexPolytope d) (a a' : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (hvertices' : R'.vertices = insert a' Q'.vertices)
    (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (hsame : D.SameCoplanar a D₂ a') : FaceType R ≃o FaceType R' := by
  let b := D.extensionVertexEquiv D₂ φ R R' a a' hvertices hvertices' ha ha'
  let e := D.extensionIndexEquiv D₂ φ hDE
  have hinc (i : ExtensionFacetIndex Q D.base ι) (v : VertexType R) :
      (b v).val ∈ affineZeroFace R' (D₂.extensionForm a' (e i)) ↔
        v.val ∈ affineZeroFace R (D.extensionForm a i) := by
    have hvR : v.val ∈ R.toSet := subset_convexHull ℝ _ v.property
    have hbvR' : (b v).val ∈ R'.toSet := subset_convexHull ℝ _ (b v).property
    obtain ⟨u, rfl⟩ :=
      (extensionVertexLabels Q R a hvertices (D.apex_not_mem_vertices a ha)).surjective v
    change ((b _).val ∈ R'.toSet ∧ D₂.extensionForm a' (e i) (b _).val = 0) ↔
      (_ ∈ R.toSet ∧ D.extensionForm a i _ = 0)
    rw [and_iff_right hbvR', and_iff_right hvR]
    have hlabel : (b (extensionVertexLabels Q R a hvertices
        (D.apex_not_mem_vertices a ha) u)).val =
        extensionLabelPoint a' (Equiv.optionCongr (vertexEquivOfFaceOrder φ) u) := by
      dsimp only [b, extensionVertexEquiv, Equiv.trans_apply]
      rw [Equiv.symm_apply_apply]
      cases (Equiv.optionCongr (vertexEquivOfFaceOrder φ) u) <;> rfl
    have hlabel' : (extensionVertexLabels Q R a hvertices
        (D.apex_not_mem_vertices a ha) u).val = extensionLabelPoint a u := by
      cases u <;> rfl
    rw [hlabel, hlabel']
    exact (D.extension_zero_incidence_preserved D₂ φ hDE a a' ha ha' hsame i u).symm
  apply faceOrderIsoOfFacetIncidence R (extension_fullDim Q R D.fullDim a hvertices)
    R' (extension_fullDim Q' R' D₂.fullDim a' hvertices') b
  · intro F hF
    obtain ⟨i, hi⟩ := D.extension_facets R a hvertices ha F.val hF
    refine ⟨⟨_, (D₂.extension_form_isFacet R' a' hvertices' ha' (e i)).1⟩,
      D₂.extension_form_isFacet R' a' hvertices' ha' (e i), ?_⟩
    intro v
    rw [hi]
    exact hinc i v
  · intro G hG
    obtain ⟨j, hj⟩ := D₂.extension_facets R' a' hvertices' ha' G.val hG
    obtain ⟨i, rfl⟩ := e.surjective j
    refine ⟨⟨_, (D.extension_form_isFacet R a hvertices ha i).1⟩,
      D.extension_form_isFacet R a hvertices ha i, ?_⟩
    intro v
    rw [hj]
    exact hinc i v

/-- Whenever a same-type core admits a point with the prescribed signs,
the resulting convex hull is an actual realization of the original
extension.  Existence of that point over each field is a separate,
constructive homogeneous-coordinate theorem. -/
theorem realize_extension_from_admissible_point
    (D : SimplexFacetPresentation Q ι) (D₂ : SimplexFacetPresentation Q' ι)
    (φ : FaceType Q ≃o FaceType Q') (hDE : D.Aligned D₂ φ)
    (R : ConvexPolytope d) (a a' : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (ha : D.AdmissiblePoint a) (ha' : D₂.AdmissiblePoint a')
    (hsame : D.SameCoplanar a D₂ a') :
    ∃ R' : ConvexPolytope d, R'.vertices = insert a' Q'.vertices ∧
      Nonempty (FaceType R ≃o FaceType R') := by
  let hr := D.transferred_retention D₂ φ hDE R a a' hvertices ha ha' hsame
  let R' := addExteriorVertex Q' a' (D₂.form none) (D₂.supports none).1 ha'.1 hr
  have hv : R'.vertices = insert a' Q'.vertices := rfl
  exact ⟨R', hv, ⟨D.extensionFaceOrderIso D₂ φ hDE R R' a a' hvertices hv ha ha' hsame⟩⟩

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart20

section BundlePart21
/- Source: Papers/FieldSpan.lean -/



@[expose] public section

/-!
# Spans under an embedding of coordinate fields

These lemmas compare linear spans over the two different fields, rather than
restricting scalars on the larger vector space. In particular the dimension
statement is equality, not just monotonicity under an injective linear map.
-/

noncomputable section
namespace Papers.Coordinates

open Set

variable {K L : Type*} [Field K] [Field L]

def coordinateMap (σ : K →+* L) (n : ℕ) : (Fin n → K) →ₛₗ[σ] (Fin n → L) where
  toFun x j := σ (x j)
  map_add' x y := by ext j; exact σ.map_add _ _
  map_smul' c x := by ext j; exact σ.map_mul _ _

@[simp] theorem coordinateMap_apply (σ : K →+* L) (n : ℕ)
    (x : Fin n → K) (j : Fin n) : coordinateMap σ n x j = σ (x j) := rfl

theorem coordinateMap_mem_span (σ : K →+* L) {n : ℕ}
    {S : Set (Fin n → K)} {x : Fin n → K} (hx : x ∈ Submodule.span K S) :
    coordinateMap σ n x ∈ Submodule.span L (coordinateMap σ n '' S) := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (Set.mem_image_of_mem _ hx)
  | zero => simpa only [map_zero] using (Submodule.span L (coordinateMap σ n '' S)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (Submodule.span L (coordinateMap σ n '' S)).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smulₛₗ] using
      (Submodule.span L (coordinateMap σ n '' S)).smul_mem (σ c) ih

theorem span_coordinateMap_span (σ : K →+* L) {n : ℕ} (S : Set (Fin n → K)) :
    Submodule.span L (coordinateMap σ n '' (Submodule.span K S : Set (Fin n → K))) =
      Submodule.span L (coordinateMap σ n '' S) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact coordinateMap_mem_span σ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/-- The rank of a coordinate span is unchanged by a field embedding. -/
theorem finrank_span_coordinateMap (σ : K →+* L) {n : ℕ} (S : Set (Fin n → K)) :
    Module.finrank L (Submodule.span L (coordinateMap σ n '' S)) =
      Module.finrank K (Submodule.span K S) := by
  let W := Submodule.span K S
  let b := Module.finBasis K W
  let q : Fin (Module.finrank K W) → Fin n → K := W.subtype ∘ b
  have hq : LinearIndependent K q :=
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hspan : Submodule.span K (Set.range q) = W := by
    dsimp only [q]
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have himage : Submodule.span L (coordinateMap σ n '' S) =
      Submodule.span L (Set.range (fun i => coordinateMap σ n (q i))) := by
    calc
      _ = Submodule.span L (coordinateMap σ n '' (W : Set (Fin n → K))) :=
        (span_coordinateMap_span σ S).symm
      _ = Submodule.span L
          (coordinateMap σ n '' (Submodule.span K (Set.range q) : Set (Fin n → K))) := by
        rw [hspan]
      _ = Submodule.span L (coordinateMap σ n '' Set.range q) :=
        span_coordinateMap_span σ (Set.range q)
      _ = _ := by rw [← Set.range_comp]; rfl
  rw [himage]
  change Module.finrank L (Submodule.span L (Set.range (fun i j => σ (q i j)))) =
    Module.finrank K W
  simpa only [Fintype.card_fin] using
    finrank_span_eq_card (linearIndependent_coordinate_map σ q hq)

/-- Linear membership also reflects back to the smaller field. -/
theorem coordinateMap_mem_span_iff (σ : K →+* L) {n : ℕ}
    (S : Set (Fin n → K)) (x : Fin n → K) :
    coordinateMap σ n x ∈ Submodule.span L (coordinateMap σ n '' S) ↔
      x ∈ Submodule.span K S := by
  constructor
  · intro hx
    have hm : Submodule.span L (coordinateMap σ n '' insert x S) =
        Submodule.span L (coordinateMap σ n '' S) := by
      rw [Set.image_insert_eq, Submodule.span_insert_eq_span hx]
    have hd : Module.finrank K (Submodule.span K S) =
        Module.finrank K (Submodule.span K (insert x S)) := by
      rw [← finrank_span_coordinateMap σ S,
        ← finrank_span_coordinateMap σ (insert x S), hm]
    have heq := Submodule.eq_of_le_of_finrank_eq
      (Submodule.span_mono (Set.subset_insert x S)) hd
    rw [heq]
    exact Submodule.subset_span (Set.mem_insert x S)
  · exact coordinateMap_mem_span σ

end Papers.Coordinates

end
end
end BundlePart21

section BundlePart22
/- Source: Papers/SubfieldAffineForms.lean -/




@[expose] public section

/-!
# Affine forms over a real subfield

Field-valued coordinates are embedded in ordinary Euclidean space.  An
affine form over the subfield is extended by its actual coordinate
coefficients.  The evaluation identity proves that this is an extension
of scalars, without restricting real geometric dimensions to the smaller
field.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

/-- Coercion of a finite sum through the actual subfield embedding. -/
theorem subfield_coe_fintype_sum {ι : Type*} [Fintype ι]
    (K : Subfield ℝ) (f : ι → K) :
    ((∑ i, f i : K) : ℝ) = ∑ i, (f i : ℝ) := by
  simpa only [Subfield.subtype_apply] using (map_sum K.subtype f Finset.univ)

def embedFieldPoint (K : Subfield ℝ) : (Fin d → K) →ₛₗ[K.subtype] E d where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℝ))
  map_add' x y := by ext i; exact K.subtype.map_add (x i) (y i)
  map_smul' c x := by ext i; exact K.subtype.map_mul c (x i)

@[simp] theorem embedFieldPoint_apply (K : Subfield ℝ) (x : Fin d → K) (i : Fin d) :
    embedFieldPoint K x i = (x i : ℝ) := rfl

def fieldPoint (K : Subfield ℝ) (x : E d) (hx : ∀ i, x i ∈ K) : Fin d → K :=
  fun i => ⟨x i, hx i⟩

@[simp] theorem embed_fieldPoint (K : Subfield ℝ) (x : E d) (hx : ∀ i, x i ∈ K) :
    embedFieldPoint K (fieldPoint K x hx) = x := by ext i; rfl

def embedFieldHomogeneous (K : Subfield ℝ) :
    ((Fin d → K) × K) →ₛₗ[K.subtype] (E d × ℝ) where
  toFun z := (embedFieldPoint K z.1, (z.2 : ℝ))
  map_add' z w := by
    apply Prod.ext
    · exact map_add (embedFieldPoint K) z.1 w.1
    · exact K.subtype.map_add z.2 w.2
  map_smul' c z := by
    apply Prod.ext
    · exact map_smulₛₗ (embedFieldPoint K) c z.1
    · exact K.subtype.map_mul c z.2

@[simp] theorem embedFieldHomogeneous_homogenize
    (K : Subfield ℝ) (x : Fin d → K) :
    embedFieldHomogeneous K (x, (1 : K)) = (embedFieldPoint K x, (1 : ℝ)) := by
  rfl

theorem semilinear_mem_span
    {K L V W : Type*} [Field K] [Field L] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module L W] (σ : K →+* L) (f : V →ₛₗ[σ] W)
    (S : Set V) (x : V) (hx : x ∈ Submodule.span K S) :
    f x ∈ Submodule.span L (f '' S) := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (Set.mem_image_of_mem _ hy)
  | zero => simpa only [map_zero] using (Submodule.span L (f '' S)).zero_mem
  | add y z hy hz ihy ihz =>
    simpa only [map_add] using (Submodule.span L (f '' S)).add_mem ihy ihz
  | smul c y hy ih =>
    simpa only [map_smulₛₗ] using (Submodule.span L (f '' S)).smul_mem (σ c) ih

def extendFieldLinear (K : Subfield ℝ) (l : (Fin d → K) →ₗ[K] K) : E d →ₗ[ℝ] ℝ :=
  (PiLp.basisFun 2 ℝ (Fin d)).constr ℝ
    (fun i => ((l (Pi.single i 1) : K) : ℝ))

@[simp] theorem extendFieldLinear_basis (K : Subfield ℝ)
    (l : (Fin d → K) →ₗ[K] K) (i : Fin d) :
    extendFieldLinear K l (PiLp.basisFun 2 ℝ (Fin d) i) = (l (Pi.single i 1) : ℝ) := by
  exact (PiLp.basisFun 2 ℝ (Fin d)).constr_basis ℝ _ i

theorem extendFieldLinear_embed (K : Subfield ℝ)
    (l : (Fin d → K) →ₗ[K] K) (x : Fin d → K) :
    extendFieldLinear K l (embedFieldPoint K x) = (l x : ℝ) := by
  have hx : (∑ i : Fin d, x i • Pi.single i (1 : K)) = x := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    simp
  have hl := congrArg (fun y : K => (y : ℝ)) (congrArg l hx)
  simp only [map_sum, map_smul, smul_eq_mul,
    subfield_coe_fintype_sum, Subfield.coe_mul] at hl
  rw [← (PiLp.basisFun 2 ℝ (Fin d)).sum_repr (embedFieldPoint K x), map_sum]
  simp only [map_smul, smul_eq_mul, PiLp.basisFun_repr, embedFieldPoint_apply,
    extendFieldLinear_basis]
  exact hl

def extendFieldAffine (K : Subfield ℝ) (f : (Fin d → K) →ᵃ[K] K) : E d →ᵃ[ℝ] ℝ where
  toFun x := extendFieldLinear K f.linear x + (f 0 : ℝ)
  linear := extendFieldLinear K f.linear
  map_vadd' p v := by
    change extendFieldLinear K f.linear (v + p) + (f 0 : ℝ) =
      extendFieldLinear K f.linear v + (extendFieldLinear K f.linear p + (f 0 : ℝ))
    rw [map_add, add_assoc]

theorem extendFieldAffine_embed (K : Subfield ℝ)
    (f : (Fin d → K) →ᵃ[K] K) (x : Fin d → K) :
    extendFieldAffine K f (embedFieldPoint K x) = (f x : ℝ) := by
  change extendFieldLinear K f.linear (embedFieldPoint K x) + (f 0 : ℝ) = _
  rw [extendFieldLinear_embed, ← Subfield.coe_add]
  apply congrArg (fun t : K => (t : ℝ))
  simpa only [vadd_eq_add, add_zero] using (f.map_vadd (0 : Fin d → K) x).symm

@[simp] theorem extendFieldAffine_zero (K : Subfield ℝ) (f : (Fin d → K) →ᵃ[K] K) :
    extendFieldAffine K f 0 = (f 0 : ℝ) := by
  change extendFieldLinear K f.linear 0 + (f 0 : ℝ) = _
  rw [map_zero, zero_add]

theorem extendFieldAffine_homogeneous (K : Subfield ℝ)
    (f : (Fin d → K) →ᵃ[K] K) (z : (Fin d → K) × K) :
    homogeneousEvaluation (embedFieldHomogeneous K z) (extendFieldAffine K f) =
      (homogeneousEvaluation z f : ℝ) := by
  change extendFieldLinear K f.linear (embedFieldPoint K z.1) +
    (z.2 : ℝ) * extendFieldAffine K f 0 = _
  rw [extendFieldLinear_embed, extendFieldAffine_zero,
    homogeneousEvaluation_apply, Subfield.coe_add, Subfield.coe_mul]

def AffineCoefficientsIn (K : Subfield ℝ) (f : E d →ᵃ[ℝ] ℝ) : Prop :=
  f 0 ∈ K ∧ ∀ i : Fin d, f.linear (PiLp.basisFun 2 ℝ (Fin d) i) ∈ K

theorem extendFieldAffine_coefficients (K : Subfield ℝ)
    (f : (Fin d → K) →ᵃ[K] K) : AffineCoefficientsIn K (extendFieldAffine K f) := by
  constructor
  · rw [extendFieldAffine_zero]
    exact (f 0).property
  · intro i
    change extendFieldLinear K f.linear (PiLp.basisFun 2 ℝ (Fin d) i) ∈ K
    rw [extendFieldLinear_basis]
    exact (f.linear (Pi.single i 1)).property

theorem AffineCoefficientsIn.eval {K : Subfield ℝ} {f : E d →ᵃ[ℝ] ℝ}
    (hf : AffineCoefficientsIn K f) (x : E d) (hx : ∀ i, x i ∈ K) : f x ∈ K := by
  rw [affine_form_apply f x]
  apply K.add_mem _ hf.1
  rw [← (PiLp.basisFun 2 ℝ (Fin d)).sum_repr x, map_sum]
  apply K.sum_mem
  intro i _
  rw [map_smul, smul_eq_mul, PiLp.basisFun_repr]
  exact K.mul_mem (hx i) (hf.2 i)

theorem AffineCoefficientsIn.homogeneous {K : Subfield ℝ} {f : E d →ᵃ[ℝ] ℝ}
    (hf : AffineCoefficientsIn K f) (z : E d × ℝ)
    (hz : (∀ i, z.1 i ∈ K) ∧ z.2 ∈ K) : homogeneousEvaluation z f ∈ K := by
  rw [homogeneousEvaluation_apply]
  apply K.add_mem _ (K.mul_mem hz.2 hf.1)
  have h := hf.eval z.1 hz.1
  rw [affine_form_apply f z.1] at h
  exact K.sub_mem h hf.1 |> fun h => by simpa only [add_sub_cancel_right] using h

end Papers.Polytopes

end
end
end BundlePart22

section BundlePart23
/- Source: Papers/SubfieldFacetForms.lean -/




@[expose] public section

/-!
# Every facet of a field-coordinate polytope has a form over that field

A field-linear functional separates an outside vertex from the span of
the homogeneous facet vertices.  Its real extension is normalized to one
at that vertex.  The actual facet dimension then makes its kernel the
facet hyperplane, and fixes the inward orientation.  No rational normal
or determinant certificate is assumed.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem homogeneousSpan_facet_eq_ker_of_vanishes
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : IsFacet P F)
    (g : E d →ᵃ[ℝ] ℝ) (hg : ∀ x ∈ F, g x = 0) (hne : g ≠ 0) :
    homogeneousSpan (K := ℝ) F = (affineLift g).ker := by
  have hle : homogeneousSpan (K := ℝ) F ≤ (affineLift g).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    change homogeneousEvaluation (x, (1 : ℝ)) g = 0
    rw [homogeneousEvaluation_homogenize, hg x hx]
  have hdimF : finrank ℝ (homogeneousSpan (K := ℝ) F) = d := by
    rw [finrank_homogeneousSpan hF.1.2]
    exact hF.2.trans hP
  have hrange : (affineLift g).range = ⊤ := LinearMap.range_eq_top.mpr (affineLift_surjective hne)
  have hdim := (affineLift g).finrank_range_add_finrank_ker
  rw [hrange, finrank_top, finrank_self, finrank_prod,
    finrank_euclideanSpace_fin, finrank_self] at hdim
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [hdimF]
  omega

theorem supportsFace_of_vanishes_facet
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (F : Set (E d)) (hF : IsFacet P F)
    (g : E d →ᵃ[ℝ] ℝ) (hg : ∀ x ∈ F, g x = 0)
    (q : E d) (hqP : q ∈ P.toSet) (hqF : q ∉ F) (hgq : 0 < g q) :
    SupportsFace P F g := by
  obtain ⟨f, hf⟩ := exists_supportsFace P hF.1
  have hfq : 0 < f q := lt_of_le_of_ne (hf.1 q hqP)
    (fun hz => hqF ((hf.mem_iff q).mpr ⟨hqP, hz.symm⟩))
  have hgne : g ≠ 0 := by
    intro heq
    rw [heq] at hgq
    exact lt_irrefl (0 : ℝ) hgq
  have hker : (affineLift g).ker ≤ (affineLift f).ker := by
    rw [← homogeneousSpan_facet_eq_ker_of_vanishes P hP F hF g hg hgne,
      ← homogeneousSpan_facet_eq_ker P hP F hF f hf]
  have heq := linear_form_eq_scalar_of_ker_le (affineLift f) (affineLift g)
    (q, (1 : ℝ))
    (by simpa only [affineLift_apply, homogeneousEvaluation_homogenize] using ne_of_gt hgq)
    hker
  let c := f q / g q
  have hc : 0 < c := div_pos hfq hgq
  have hfg (x : E d) : f x = c * g x := by
    have h := congrArg (fun l : (E d × ℝ) →ₗ[ℝ] ℝ => l (x, 1)) heq
    simpa only [LinearMap.smul_apply, affineLift_apply, homogeneousEvaluation_homogenize,
      smul_eq_mul] using h
  constructor
  · intro x hx
    have hn := hf.1 x hx
    rw [hfg x] at hn
    exact (mul_nonneg_iff_of_pos_left hc).mp hn
  · rw [hf.2]
    ext x
    change (x ∈ P.toSet ∧ f x = 0) ↔ x ∈ P.toSet ∧ g x = 0
    rw [hfg x, mul_eq_zero, or_iff_right (ne_of_gt hc)]

theorem exists_vertex_outside_facet
    (P : ConvexPolytope d) (F : Set (E d)) (hF : IsFacet P F) :
    ∃ q : VertexType P, q.val ∉ F := by
  by_contra h
  push_neg at h
  have hPF : P.toSet ⊆ F := convexHull_min
    (fun x hx => h ⟨x, hx⟩) (hF.1.1.convex (convex_convexHull ℝ _))
  exact hF.ne_toSet (Set.Subset.antisymm (face_subset_toSet P hF.1) hPF)

theorem exists_field_facet_form
    (K : Subfield ℝ) (P : ConvexPolytope d) (hP : P.IsFullDim)
    (hPK : CoordinatesIn K P) (F : Set (E d)) (hF : IsFacet P F) :
    ∃ f : (Fin d → K) →ᵃ[K] K, SupportsFace P F (extendFieldAffine K f) := by
  let vK : VertexType P → Fin d → K :=
    fun v => fieldPoint K v.val (hPK v.val v.property)
  let h : VertexType P → (Fin d → K) × K := fun v => (vK v, 1)
  let S : Set ((Fin d → K) × K) := h '' {v : VertexType P | v.val ∈ F}
  obtain ⟨q, hqF⟩ := exists_vertex_outside_facet P F hF
  have hembed (v : VertexType P) :
      embedFieldHomogeneous K (h v) = (v.val, (1 : ℝ)) := by
    change (embedFieldPoint K (fieldPoint K v.val (hPK v.val v.property)), 1) = _
    rw [embed_fieldPoint]
  have himage : embedFieldHomogeneous K '' S ⊆
      homogenize (K := ℝ) '' F := by
    rintro z ⟨w, ⟨v, hv, rfl⟩, rfl⟩
    rw [hembed]
    exact ⟨v.val, hv, rfl⟩
  have hqspan : h q ∉ Submodule.span K S := by
    intro hmem
    have hreal := semilinear_mem_span K.subtype (embedFieldHomogeneous K) S (h q) hmem
    have hreal' : embedFieldHomogeneous K (h q) ∈ homogeneousSpan (K := ℝ) F :=
      Submodule.span_mono himage hreal
    rw [hembed] at hreal'
    have haff := (homogenize_mem_span_iff hF.1.2 q.val).mp hreal'
    exact vertex_notMem_affineSpan_face P hF.1 q.property hqF haff
  obtain ⟨l, hlq, hlS⟩ := Submodule.exists_le_ker_of_notMem hqspan
  let l' : ((Fin d → K) × K) →ₗ[K] K := (l (h q))⁻¹ • l
  let f : (Fin d → K) →ᵃ[K] K := affineDehomogenize l'
  have hfq : f (vK q) = 1 := by
    change (l (h q))⁻¹ * l (h q) = 1
    exact inv_mul_cancel₀ hlq
  have hfF (v : VertexType P) (hv : v.val ∈ F) : f (vK v) = 0 := by
    have hzero : l (h v) = 0 := hlS (Submodule.subset_span ⟨v, hv, rfl⟩)
    change (l (h q))⁻¹ * l (h v) = 0
    rw [hzero, mul_zero]
  let g := extendFieldAffine K f
  have hgv (v : VertexType P) : g v.val = (f (vK v) : ℝ) := by
    have he : embedFieldPoint K (vK v) = v.val := embed_fieldPoint K v.val (hPK v.val v.property)
    rw [← he]
    exact extendFieldAffine_embed K f (vK v)
  have hgF : ∀ x ∈ F, g x = 0 := by
    intro x hx
    rw [face_eq_hull_vertices P hF.1] at hx
    apply affine_zero_on_hull (P.vertices.filter (· ∈ F)) g ?_ x hx
    intro y hy
    obtain ⟨hyP, hyF⟩ := Finset.mem_filter.mp hy
    rw [hgv ⟨y, hyP⟩, hfF ⟨y, hyP⟩ hyF, Subfield.coe_zero]
  have hgq : 0 < g q.val := by
    rw [hgv q, hfq, Subfield.coe_one]
    exact zero_lt_one
  exact ⟨f, supportsFace_of_vanishes_facet P hP F hF g hgF q.val
    (subset_convexHull ℝ _ q.property) hqF hgq⟩

theorem exists_facet_coefficients_in
    (K : Subfield ℝ) (P : ConvexPolytope d) (hP : P.IsFullDim)
    (hPK : CoordinatesIn K P) (F : Set (E d)) (hF : IsFacet P F) :
    ∃ f : E d →ᵃ[ℝ] ℝ, SupportsFace P F f ∧ AffineCoefficientsIn K f := by
  obtain ⟨f, hf⟩ := exists_field_facet_form K P hP hPK F hF
  exact ⟨extendFieldAffine K f, hf, extendFieldAffine_coefficients K f⟩

end Papers.Polytopes

end
end
end BundlePart23

section BundlePart24
/- Source: Papers/SubfieldAffineBasis.lean -/



@[expose] public section

/-!
# Solving the restoration equations over the coordinate field

The real affine-form basis descends to a basis over the subfield when its
members are real extensions of subfield forms.  Arbitrary subfield values
therefore determine a homogeneous point over that same field.  This is an
actual linear-algebra construction, not an assumed solution of the system.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates Papers.Coordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem extendFieldLinear_add (K : Subfield ℝ)
    (f g : (Fin d → K) →ₗ[K] K) :
    extendFieldLinear K (f + g) = extendFieldLinear K f + extendFieldLinear K g := by
  apply (PiLp.basisFun 2 ℝ (Fin d)).ext
  intro i
  simp only [LinearMap.add_apply, extendFieldLinear_basis, Subfield.coe_add]

theorem extendFieldLinear_smul (K : Subfield ℝ) (c : K)
    (f : (Fin d → K) →ₗ[K] K) :
    extendFieldLinear K (c • f) = (c : ℝ) • extendFieldLinear K f := by
  apply (PiLp.basisFun 2 ℝ (Fin d)).ext
  intro i
  simp only [LinearMap.smul_apply, extendFieldLinear_basis, smul_eq_mul, Subfield.coe_mul]

def extendFieldAffineMap (K : Subfield ℝ) :
    ((Fin d → K) →ᵃ[K] K) →ₛₗ[K.subtype] (E d →ᵃ[ℝ] ℝ) where
  toFun := extendFieldAffine K
  map_add' f g := by
    ext x
    change extendFieldLinear K (f + g).linear x + ((f + g) 0 : ℝ) =
      (extendFieldLinear K f.linear x + (f 0 : ℝ)) +
        (extendFieldLinear K g.linear x + (g 0 : ℝ))
    rw [AffineMap.add_linear, extendFieldLinear_add, LinearMap.add_apply]
    change _ + ((f 0 + g 0 : K) : ℝ) = _
    rw [Subfield.coe_add]
    ring
  map_smul' c f := by
    ext x
    change extendFieldLinear K (c • f).linear x + ((c • f) 0 : ℝ) =
      (c : ℝ) * (extendFieldLinear K f.linear x + (f 0 : ℝ))
    rw [AffineMap.smul_linear, extendFieldLinear_smul, LinearMap.smul_apply, smul_eq_mul]
    change _ + ((c * f 0 : K) : ℝ) = _
    rw [Subfield.coe_mul, mul_add]

@[simp] theorem extendFieldAffineMap_apply (K : Subfield ℝ)
    (f : (Fin d → K) →ᵃ[K] K) : extendFieldAffineMap K f = extendFieldAffine K f := rfl

theorem field_forms_independent_of_real_basis
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) : LinearIndependent K f := by
  have hLI : LinearIndependent ℝ (fun i => extendFieldAffineMap K (f i)) := by
    have heq : (fun i => extendFieldAffineMap K (f i)) = (fun i => b i) :=
      funext (fun i => (hf i).symm)
    rw [heq]
    exact b.linearIndependent
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (extendFieldAffineMap K) hc
  simp only [map_sum, map_smulₛₗ, map_zero, Subfield.subtype_apply] at h
  have hi := (Fintype.linearIndependent_iff.mp hLI) (fun j => (c j : ℝ)) h i
  apply Subtype.ext
  simpa only [Subfield.coe_zero] using hi

def fieldAffineBasis
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) :
    Basis ι K ((Fin d → K) →ᵃ[K] K) :=
  basisOfLinearIndependentOfCardEqFinrank' f
    (field_forms_independent_of_real_basis K b f hf)
    (by
      rw [← Module.finrank_eq_card_basis b]
      simp [AffineMap.finrank_eq])

@[simp] theorem fieldAffineBasis_apply
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) (i : ι) :
    fieldAffineBasis K b f hf i = f i := by
  simp only [fieldAffineBasis, coe_basisOfLinearIndependentOfCardEqFinrank']

def fieldHomogeneousValues
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) (r : ι → K) : (Fin d → K) × K :=
  realizeAffineValues (fieldAffineBasis K b f hf) r

theorem fieldHomogeneousValues_evaluation
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) (r : ι → K) (i : ι) :
    homogeneousEvaluation (embedFieldHomogeneous K (fieldHomogeneousValues K b f hf r))
      (b i) = (r i : ℝ) := by
  rw [hf i, extendFieldAffine_homogeneous]
  apply congrArg (fun x : K => (x : ℝ))
  rw [← fieldAffineBasis_apply K b f hf i]
  exact realizeAffineValues_basis (fieldAffineBasis K b f hf) r i

theorem fieldHomogeneousValues_eq_real_solution
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) (r : ι → K) :
    embedFieldHomogeneous K (fieldHomogeneousValues K b f hf r) =
      realizeAffineValues b (fun i => (r i : ℝ)) := by
  apply homogeneousEvaluation_injective
  apply b.ext
  intro i
  rw [fieldHomogeneousValues_evaluation, realizeAffineValues_basis]

theorem real_solution_coordinates_in
    (K : Subfield ℝ) (b : Basis ι ℝ (E d →ᵃ[ℝ] ℝ))
    (f : ι → (Fin d → K) →ᵃ[K] K)
    (hf : ∀ i, b i = extendFieldAffine K (f i)) (r : ι → K) :
    (∀ j, (realizeAffineValues b (fun i => (r i : ℝ))).1 j ∈ K) ∧
      (realizeAffineValues b (fun i => (r i : ℝ))).2 ∈ K := by
  rw [← fieldHomogeneousValues_eq_real_solution K b f hf r]
  exact ⟨fun j => ((fieldHomogeneousValues K b f hf r).1 j).property,
    (fieldHomogeneousValues K b f hf r).2.property⟩

end Papers.Polytopes

end
end
end BundlePart24

section BundlePart25
/- Source: Papers/BasisProjectiveChart.lean -/





@[expose] public section

/-!
# An explicit projective chart from an affine-form basis

The chart replaces the distinguished coordinate by a nonzero multiple of
that coordinate plus the sum of all other coordinates.  Its inverse is
written explicitly.  The same construction works over any field; in the
real geometric application the denominator is separately proved positive
on every old vertex and the new homogeneous point.
-/

noncomputable section
namespace Papers.AffineCoordinates

open Module
open scoped Classical BigOperators

section Field
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype ι]

def basisValuesLinear (b : Basis ι K (V →ᵃ[K] K)) : (V × K) →ₗ[K] (ι → K) where
  toFun z i := homogeneousEvaluation z (b i)
  map_add' z w := by
    ext i
    exact congrArg (fun f : Module.Dual K (V →ᵃ[K] K) => f (b i))
      (homogeneousEvaluation.map_add z w)
  map_smul' c z := by
    ext i
    exact congrArg (fun f : Module.Dual K (V →ᵃ[K] K) => f (b i))
      (homogeneousEvaluation.map_smul c z)

def basisValuesEquiv (b : Basis ι K (V →ᵃ[K] K)) : (V × K) ≃ₗ[K] (ι → K) := by
  apply LinearEquiv.ofBijective (basisValuesLinear b)
  constructor
  · intro z w h
    apply homogeneousEvaluation_injective
    apply b.ext
    intro i
    exact congrFun h i
  · intro r
    refine ⟨realizeAffineValues b r, ?_⟩
    ext i
    exact realizeAffineValues_basis b r i

def optionValuesEquiv : (Option ι → K) ≃ₗ[K] ((ι → K) × K) where
  toFun r := (fun i => r (some i), r none)
  invFun z i := i.elim z.2 z.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv r := by ext i; cases i <;> rfl
  right_inv z := rfl

def chartShear (ε : K) (hε : ε ≠ 0) : ((ι → K) × K) ≃ₗ[K] ((ι → K) × K) where
  toFun z := (z.1, ε * z.2 + ∑ i, z.1 i)
  invFun z := (z.1, (z.2 - ∑ i, z.1 i) / ε)
  map_add' z w := by
    apply Prod.ext
    · rfl
    · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, Finset.sum_add_distrib]
      ring
  map_smul' c z := by
    apply Prod.ext
    · rfl
    · simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply, ← Finset.mul_sum]
      ring
  left_inv z := by
    apply Prod.ext
    · rfl
    · change (ε * z.2 + (∑ i, z.1 i) - (∑ i, z.1 i)) / ε = z.2
      rw [add_sub_cancel_right, mul_div_cancel_left₀ _ hε]
  right_inv z := by
    apply Prod.ext
    · rfl
    · change ε * ((z.2 - ∑ i, z.1 i) / ε) + (∑ i, z.1 i) = z.2
      field_simp
      ring

end Field

open LeanEval.Geometry.PlatonicClassification

variable {d : ℕ} {ι : Type*} [Fintype ι]

def euclideanReindex (e : ι ≃ Fin d) : (ι → ℝ) ≃ₗ[ℝ] E d where
  toFun x := WithLp.toLp 2 (fun i => x (e.symm i))
  invFun y i := y (e i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by ext i; simp only [Equiv.symm_apply_apply]
  right_inv y := by ext i; simp only [Equiv.apply_symm_apply]

def basisChartEquiv
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (e : ι ≃ Fin d)
    (ε : ℝ) (hε : ε ≠ 0) : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ) :=
  (basisValuesEquiv b).trans
    (optionValuesEquiv.trans ((chartShear ε hε).trans
      (LinearEquiv.prodCongr (euclideanReindex e) (LinearEquiv.refl ℝ ℝ))))

@[simp] theorem basisChartEquiv_fst
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (e : ι ≃ Fin d)
    (ε : ℝ) (hε : ε ≠ 0) (z : E d × ℝ) (i : Fin d) :
    (basisChartEquiv b e ε hε z).1 i = homogeneousEvaluation z (b (some (e.symm i))) := rfl

@[simp] theorem basisChartEquiv_snd
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (e : ι ≃ Fin d)
    (ε : ℝ) (hε : ε ≠ 0) (z : E d × ℝ) :
    (basisChartEquiv b e ε hε z).2 =
      ε * homogeneousEvaluation z (b none) + ∑ i, homogeneousEvaluation z (b (some i)) := rfl

theorem basisChartEquiv_snd_form
    (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ)) (e : ι ≃ Fin d)
    (ε : ℝ) (hε : ε ≠ 0) (z : E d × ℝ) :
    (basisChartEquiv b e ε hε z).2 =
      homogeneousEvaluation z (ε • b none + ∑ i, b (some i)) := by
  rw [basisChartEquiv_snd, map_add, map_smul, map_sum]
  rfl

def normalizedImage (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ)) (z : E d × ℝ) : E d :=
  (L z).2⁻¹ • (L z).1

theorem normalizedImage_lift (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (z : E d × ℝ) (hz : (L z).2 ≠ 0) :
    L z = (L z).2 • (normalizedImage L z, (1 : ℝ)) := by
  apply Prod.ext
  · change (L z).1 = (L z).2 • ((L z).2⁻¹ • (L z).1)
    rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
  · change (L z).2 = (L z).2 * 1
    exact (mul_one _).symm

theorem projectiveTransportAffine_homogeneous_scaled
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (f : E d →ᵃ[ℝ] ℝ) (z : E d × ℝ) (y : E d) (h : ℝ)
    (heq : L z = h • (y, 1)) :
    homogeneousEvaluation z f = h * projectiveTransportAffine L f y := by
  have hz : z = h • L.symm (y, 1) := by
    have h' := congrArg L.symm heq
    simpa only [L.symm_apply_apply, map_smul] using h'
  change affineLift f z = _
  calc
    affineLift f z = affineLift f (h • L.symm (y, 1)) := congrArg (affineLift f) hz
    _ = h * affineLift f (L.symm (y, 1)) := by rw [map_smul, smul_eq_mul]
    _ = h * projectiveTransportAffine L f y := rfl

end Papers.AffineCoordinates

end
end
end BundlePart25

section BundlePart26
/- Source: Papers/SubfieldRestorationChart.lean -/






@[expose] public section

/-!
# A positive restoration chart whose coefficients lie in the field

If some prescribed neighboring value is positive, a half-sum gives the
chart coefficient.  Otherwise a further actual facet makes the sum of
neighboring supports strictly positive on the old polytope, and a small
rational coefficient works.  The exceptional all-coplanar simplex case
is excluded by the proved retention-facet theorem for the original
extension.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

namespace SimplexFacetPresentation

variable {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q ι)

theorem other_facet_of_all_coplanar
    (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices)
    (ha : D.AdmissiblePoint a) (hzero : ∀ i, D.form (some i) a = 0) :
    ∃ G : FacetType Q, ∀ i, G ≠ D.facet i := by
  obtain ⟨x, hx⟩ := Q.vertices_nonempty
  obtain ⟨G, hGT, _, hGa⟩ := D.retention_facet R a hvertices ha ⟨x, hx⟩
  refine ⟨G, ?_⟩
  intro i hi
  cases i with
  | none => exact hGT (congrArg (fun F : FacetType Q => F.val.val) hi)
  | some j =>
    rw [hi] at hGa
    have hz := (D.chosen_form_zero_iff (some j) a).mpr (hzero j)
    exact (ne_of_gt hGa) hz

theorem exists_field_forms
    (K : Subfield ℝ) (hQK : CoordinatesIn K Q) :
    ∃ f : Option ι → (Fin d → K) →ᵃ[K] K,
      ∀ i, SupportsFace Q (D.facet i).val.val (extendFieldAffine K (f i)) := by
  have h (i : Option ι) := exists_field_facet_form K Q D.fullDim hQK
    (D.facet i).val.val (D.facet i).property
  exact ⟨fun i => Classical.choose (h i), fun i => Classical.choose_spec (h i)⟩

theorem exists_field_positive_chart
    (K : Subfield ℝ) (t : ι → K) (ht : ∀ i, 0 ≤ (t i : ℝ))
    (hcase : (∃ i, 0 < (t i : ℝ)) ∨ ∃ G : FacetType Q, ∀ i, G ≠ D.facet i) :
    ∃ ε : K, ε ≠ 0 ∧
      (∀ x ∈ Q.vertices, 0 < positiveRestorationChart D.basis (ε : ℝ) x) ∧
      0 < homogeneousEvaluation (restorationVector D.basis (fun i => (t i : ℝ)))
        (positiveRestorationChart D.basis (ε : ℝ)) := by
  rcases hcase with hpos | ⟨G, hG⟩
  · have hsum : 0 < ∑ i, (t i : ℝ) := by
      obtain ⟨i, hi⟩ := hpos
      exact lt_of_lt_of_le hi (Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ _))
    let ε : K := (∑ i, t i) / 2
    have hcast : (ε : ℝ) = (∑ i, (t i : ℝ)) / 2 := by
      have htwo : ((2 : K) : ℝ) = 2 := by
        simpa only [Subfield.subtype_apply] using (map_ofNat K.subtype 2)
      dsimp only [ε]
      rw [Subfield.coe_div, subfield_coe_fintype_sum, htwo]
    have hε : 0 < (ε : ℝ) := by rw [hcast]; exact half_pos hsum
    refine ⟨ε, ?_, ?_, ?_⟩
    · intro hz
      rw [hz, Subfield.coe_zero] at hε
      exact lt_irrefl _ hε
    · intro x hx
      let w : Option ι → ℝ := fun i => i.elim (ε : ℝ) (fun _ => 1)
      have hw : ∀ i, 0 < w i := by
        intro i
        cases i with
        | none => exact hε
        | some _ => exact zero_lt_one
      have h := positive_weighted_affine_basis D.basis x
        (fun i => by rw [D.basis_apply]; exact D.form_nonneg i x (subset_convexHull ℝ _ hx)) w hw
      simpa only [Fintype.sum_option, w, Option.elim_none, Option.elim_some,
        one_smul, positiveRestorationChart] using h
    · rw [positiveRestorationChart, map_add, map_smul, map_sum]
      simp only [restorationVector_none, restorationVector_some, smul_eq_mul, mul_neg_one]
      rw [hcast]
      linarith
  · have hGset : ∀ i, G.val.val ≠ (D.facet i).val.val := by
      intro i hi
      exact hG i (Subtype.ext (Subtype.ext hi))
    have hsumPos (x : E d) (hx : x ∈ Q.toSet) : 0 < ∑ i, D.basis (some i) x :=
      neighbor_support_sum_pos_of_other_facet Q (fun i => (D.facet i).val.val)
        D.basis (fun i => (D.vertex i).val)
        (fun i => (D.facet i).property)
        (fun i => by simpa only [D.basis_apply] using D.supports i)
        (fun i => subset_convexHull ℝ _ (D.vertex i).property)
        (by simpa only [D.basis_apply] using D.at_base)
        (by simpa only [D.basis_apply] using D.diagonal)
        (by simpa only [D.basis_apply] using D.off_diagonal)
        G.val.val (chosenFacetForm Q G) G.property (chosenFacetForm_supports Q G) hGset x hx
    obtain ⟨δ, hδ, hbound⟩ := finite_positive_perturbation Q.vertices
      (fun x => ∑ i, D.basis (some i) x) (D.basis none)
      (fun x hx => hsumPos x (subset_convexHull ℝ _ hx))
      (fun x hx => by rw [D.basis_apply]; exact D.form_nonneg none x (subset_convexHull ℝ _ hx))
    obtain ⟨q, hq0, hqδ⟩ := exists_rat_btwn hδ
    let ε : K := -(q : K)
    have hcast : (ε : ℝ) = -(q : ℝ) := by
      simp only [ε, Subfield.coe_neg, SubfieldClass.coe_ratCast]
    refine ⟨ε, ?_, ?_, ?_⟩
    · intro hz
      have hqz : -(q : ℝ) = 0 := by rw [← hcast, hz, Subfield.coe_zero]
      linarith
    · intro x hx
      change 0 < (ε : ℝ) * D.basis none x + (∑ i, D.basis (some i)) x
      rw [affineForm_sum_apply, hcast]
      have hb := hbound x hx
      have hn : 0 ≤ D.basis none x := by
        rw [D.basis_apply]
        exact D.form_nonneg none x (subset_convexHull ℝ _ hx)
      have hsmall := mul_le_mul_of_nonneg_right hqδ.le hn
      linarith
    · rw [positiveRestorationChart, map_add, map_smul, map_sum]
      simp only [restorationVector_none, restorationVector_some, smul_eq_mul, mul_neg_one]
      rw [hcast]
      have hsum : 0 ≤ ∑ i, (t i : ℝ) := Finset.sum_nonneg (fun i _ => ht i)
      linarith

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart26

section BundlePart27
/- Source: Papers/FieldProjectiveChart.lean -/




@[expose] public section

/-!
# Coordinates of the explicit projective chart

The chosen chart uses only the supporting-form coefficients and a scalar
in the coordinate field.  Its normalized coordinates therefore remain in
that field.  The statement concerns the actual extreme vertices of the
projective image polytope.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

theorem normalizedBasisChart_coordinates_in
    (K : Subfield ℝ) (b : Basis (Option ι) ℝ (E d →ᵃ[ℝ] ℝ))
    (hb : ∀ i, AffineCoefficientsIn K (b i)) (e : ι ≃ Fin d)
    (ε : ℝ) (hε : ε ≠ 0) (hεK : ε ∈ K)
    (z : E d × ℝ) (hz : (∀ j, z.1 j ∈ K) ∧ z.2 ∈ K) :
    ∀ j, normalizedImage (basisChartEquiv b e ε hε) z j ∈ K := by
  have heval (i : Option ι) : homogeneousEvaluation z (b i) ∈ K :=
    (hb i).homogeneous z hz
  have hden : (basisChartEquiv b e ε hε z).2 ∈ K := by
    rw [basisChartEquiv_snd]
    exact K.add_mem (K.mul_mem hεK (heval none))
      (K.sum_mem (fun i _ => heval (some i)))
  intro j
  change (basisChartEquiv b e ε hε z).2⁻¹ *
    (basisChartEquiv b e ε hε z).1 j ∈ K
  rw [basisChartEquiv_fst]
  exact K.mul_mem (K.inv_mem hden) (heval (some (e.symm j)))

theorem projectivePolytope_coordinates
    (K : Subfield ℝ) (P : ConvexPolytope d)
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (q : VertexType P → E d) (h : VertexType P → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • (q v, 1))
    (hq : ∀ v j, q v j ∈ K) : CoordinatesIn K (projectivePolytope P L q h hh hL) := by
  intro x hx j
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact hq v j

theorem imageVertex_trans
    {P Q R : ConvexPolytope d} (φ : FaceType P ≃o FaceType Q)
    (ψ : FaceType Q ≃o FaceType R) (v : VertexType P) :
    imageVertex (φ.trans ψ) v = imageVertex ψ (imageVertex φ v) := by
  apply vertexFace_injective R
  rw [imageVertex_face, imageVertex_face, imageVertex_face]
  rfl

theorem facetEquivOfFaceOrder_trans
    {P Q R : ConvexPolytope d} (φ : FaceType P ≃o FaceType Q)
    (ψ : FaceType Q ≃o FaceType R) (F : FacetType P) :
    facetEquivOfFaceOrder (φ.trans ψ) F =
      facetEquivOfFaceOrder ψ (facetEquivOfFaceOrder φ F) := rfl

namespace SimplexFacetPresentation

theorem Aligned.trans
    {P Q R : ConvexPolytope d}
    {D₁ : SimplexFacetPresentation P ι} {D₂ : SimplexFacetPresentation Q ι}
    {D₃ : SimplexFacetPresentation R ι}
    {φ : FaceType P ≃o FaceType Q} {ψ : FaceType Q ≃o FaceType R}
    (h₁ : D₁.Aligned D₂ φ) (h₂ : D₂.Aligned D₃ ψ) :
    D₁.Aligned D₃ (φ.trans ψ) := by
  constructor
  · intro i
    rw [h₂.1 i, h₁.1 i, facetEquivOfFaceOrder_trans]
  · intro i
    rw [h₂.2 i, h₁.2 i, imageVertex_trans]

theorem Aligned.withForms_right
    {P Q : ConvexPolytope d}
    {D₁ : SimplexFacetPresentation P ι} {D₂ : SimplexFacetPresentation Q ι}
    {φ : FaceType P ≃o FaceType Q} (h : D₁.Aligned D₂ φ)
    (f : Option ι → E d →ᵃ[ℝ] ℝ)
    (hf : ∀ i, SupportsFace Q (D₂.facet i).val.val (f i)) :
    D₁.Aligned (D₂.withForms f hf) φ := h

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart27

section BundlePart28
/- Source: Papers/ProjectiveSimplexPresentation.lean -/



@[expose] public section

/-!
# Transporting a simplex-facet presentation through a positive chart

The transformed supporting forms are the literal inverse homogeneous
transforms of the original forms.  Their zero sets are proved to be the
images of the original faces.  This identifies the admissibility signs
and the coplanarity pattern of a new homogeneous point.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

namespace SimplexFacetPresentation

variable {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q ι)

def projective
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (q : VertexType Q → E d) (h : VertexType Q → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) :
    SimplexFacetPresentation (projectivePolytope Q L q h hh hL) ι :=
  (D.transport (projectivePolytopeFaceOrderIso Q L q h hh hL)).withForms
    (fun i => projectiveTransportAffine L (D.form i))
    (fun i => positiveProjectiveFaceOrderIso_supports Q _ L
      (projectiveVertexEquiv Q L q h hh hL) h hh hL (D.facet i).val
      (D.form i) (D.supports i))

@[simp] theorem projective_form
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (q : VertexType Q → E d) (h : VertexType Q → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • (q v, 1))
    (i : Option ι) :
    (D.projective L q h hh hL).form i = projectiveTransportAffine L (D.form i) := by
  simp only [projective, withForms]

theorem projective_aligned
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (q : VertexType Q → E d) (h : VertexType Q → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • (q v, 1)) :
    D.Aligned (D.projective L q h hh hL) (projectivePolytopeFaceOrderIso Q L q h hh hL) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

theorem projective_admissible_of_homogeneous
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (q : VertexType Q → E d) (h : VertexType Q → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • (q v, 1))
    (z : E d × ℝ) (a : E d) (c : ℝ) (hc : 0 < c)
    (hz : L z = c • (a, 1))
    (hbase : homogeneousEvaluation z (D.form none) < 0)
    (hsides : ∀ i, 0 ≤ homogeneousEvaluation z (D.form (some i))) :
    (D.projective L q h hh hL).AdmissiblePoint a := by
  constructor
  · change projectiveTransportAffine L (D.form none) a < 0
    rw [projectiveTransportAffine_homogeneous_scaled L (D.form none) z a c hz] at hbase
    by_contra hn
    have hg : 0 ≤ projectiveTransportAffine L (D.form none) a := le_of_not_gt hn
    have hm := mul_nonneg hc.le hg
    linarith
  · intro i
    change 0 ≤ projectiveTransportAffine L (D.form (some i)) a
    have hi := hsides i
    rw [projectiveTransportAffine_homogeneous_scaled L (D.form (some i)) z a c hz] at hi
    exact (mul_nonneg_iff_of_pos_left hc).mp hi

theorem projective_form_zero_iff
    (L : (E d × ℝ) ≃ₗ[ℝ] (E d × ℝ))
    (q : VertexType Q → E d) (h : VertexType Q → ℝ)
    (hh : ∀ v, 0 < h v) (hL : ∀ v, L (v.val, 1) = h v • (q v, 1))
    (z : E d × ℝ) (a : E d) (c : ℝ) (hc : c ≠ 0)
    (hz : L z = c • (a, 1)) (i : Option ι) :
    (D.projective L q h hh hL).form i a = 0 ↔
      homogeneousEvaluation z (D.form i) = 0 := by
  change projectiveTransportAffine L (D.form i) a = 0 ↔ _
  rw [projectiveTransportAffine_homogeneous_scaled L (D.form i) z a c hz]
  exact (mul_eq_zero.trans (or_iff_right hc)).symm

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart28

section BundlePart29
/- Source: Papers/FieldExtension.lean -/



@[expose] public section

/-!
# Restoration over every real subfield

For an actual extension of a polytope through a simplex facet, any
realization of the old face lattice over a real subfield can be extended,
after a positive projective change of chart, over that same subfield.
The original actual polytope supplies the vertex-retention condition.
The prescribed coplanarity pattern is copied by the field values zero
and one; it is not an assumed solution of a realization problem.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open Papers.AffineCoordinates
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {ι : Type*} [Fintype ι]

namespace SimplexFacetPresentation

variable {Q : ConvexPolytope d} (D : SimplexFacetPresentation Q ι)

theorem extension_realizable_over
    (R : ConvexPolytope d) (a : E d)
    (hvertices : R.vertices = insert a Q.vertices) (ha : D.AdmissiblePoint a)
    (K : Subfield ℝ) (hQK : RealizableOver Q K) : RealizableOver R K := by
  obtain ⟨Q', ⟨φ⟩, hQ'K⟩ := hQK
  let D₀ := D.transport φ
  obtain ⟨fK, hfK⟩ := D₀.exists_field_forms K hQ'K
  let D₁ := D₀.withForms (fun i => extendFieldAffine K (fK i)) hfK
  have hD₁ : D.Aligned D₁ φ := D.transport_aligned φ
  have hb (i : Option ι) : D₁.basis i = extendFieldAffine K (fK i) := D₁.basis_apply i
  have hbK (i : Option ι) : AffineCoefficientsIn K (D₁.basis i) := by
    rw [hb i]
    exact extendFieldAffine_coefficients K (fK i)
  let t : ι → K := fun i => if D.form (some i) a = 0 then 0 else 1
  have ht (i : ι) : 0 ≤ (t i : ℝ) := by
    by_cases hi : D.form (some i) a = 0 <;> simp [t, hi]
  have hmask (i : ι) : D.form (some i) a = 0 ↔ (t i : ℝ) = 0 := by
    by_cases hi : D.form (some i) a = 0 <;> simp [t, hi]
  have hcase : (∃ i, 0 < (t i : ℝ)) ∨ ∃ G : FacetType Q', ∀ i, G ≠ D₁.facet i := by
    by_cases hzero : ∀ i, D.form (some i) a = 0
    · obtain ⟨G, hG⟩ := D.other_facet_of_all_coplanar R a hvertices ha hzero
      refine Or.inr ⟨facetEquivOfFaceOrder φ G, ?_⟩
      intro i hi
      exact hG i ((facetEquivOfFaceOrder φ).injective (hi.trans (hD₁.1 i)))
    · push_neg at hzero
      obtain ⟨i, hi⟩ := hzero
      exact Or.inl ⟨i, by simp [t, hi]⟩
  obtain ⟨ε, hε, hchart, hchartnew⟩ := D₁.exists_field_positive_chart K t ht hcase
  have hεR : (ε : ℝ) ≠ 0 := by
    intro heq
    apply hε
    exact Subtype.ext (by simpa only [Subfield.coe_zero] using heq)
  let rK : Option ι → K := fun i => i.elim (-1) t
  have hrK : (fun i => (rK i : ℝ)) = restorationValues (fun i => (t i : ℝ)) := by
    funext i
    cases i <;> simp only [rK, restorationValues, Option.elim_none, Option.elim_some,
      Subfield.coe_neg, Subfield.coe_one]
  let z := restorationVector D₁.basis (fun i => (t i : ℝ))
  have hzK : (∀ j, z.1 j ∈ K) ∧ z.2 ∈ K := by
    have hr := real_solution_coordinates_in K D₁.basis fK hb rK
    rw [hrK] at hr
    exact hr
  let e : ι ≃ Fin d := (Fintype.equivFin ι).trans (finCongr D₁.index_card)
  let L := basisChartEquiv D₁.basis e (ε : ℝ) hεR
  let g := positiveRestorationChart D₁.basis (ε : ℝ)
  have hden (w : E d × ℝ) : (L w).2 = homogeneousEvaluation w g :=
    basisChartEquiv_snd_form D₁.basis e (ε : ℝ) hεR w
  let q : VertexType Q' → E d := fun v => normalizedImage L (v.val, 1)
  let h : VertexType Q' → ℝ := fun v => g v.val
  have hh (v : VertexType Q') : 0 < h v := hchart v.val v.property
  have hdenold (v : VertexType Q') : (L (v.val, 1)).2 = h v := by
    rw [hden, homogeneousEvaluation_homogenize]
  have hL (v : VertexType Q') : L (v.val, 1) = h v • (q v, 1) := by
    have hn : (L (v.val, 1)).2 ≠ 0 := by rw [hdenold v]; exact ne_of_gt (hh v)
    simpa only [hdenold v] using normalizedImage_lift L (v.val, 1) hn
  let Q'' := projectivePolytope Q' L q h hh hL
  let ψ := projectivePolytopeFaceOrderIso Q' L q h hh hL
  let D₂ := D₁.projective L q h hh hL
  have hD₂ : D.Aligned D₂ (φ.trans ψ) :=
    hD₁.trans (D₁.projective_aligned L q h hh hL)
  let a' := normalizedImage L z
  let c := (L z).2
  have hc : 0 < c := by
    change 0 < (L z).2
    rw [hden]
    exact hchartnew
  have hzL : L z = c • (a', 1) := normalizedImage_lift L z (ne_of_gt hc)
  have hzbase : homogeneousEvaluation z (D₁.form none) < 0 := by
    rw [← D₁.basis_apply, restorationVector_none]
    norm_num
  have hzside (i : ι) : 0 ≤ homogeneousEvaluation z (D₁.form (some i)) := by
    rw [← D₁.basis_apply, restorationVector_some]
    exact ht i
  have ha' : D₂.AdmissiblePoint a' :=
    D₁.projective_admissible_of_homogeneous L q h hh hL z a' c hc hzL hzbase hzside
  have hsame : D.SameCoplanar a D₂ a' := by
    intro i
    change D.form (some i) a = 0 ↔ (D₁.projective L q h hh hL).form (some i) a' = 0
    rw [D₁.projective_form_zero_iff L q h hh hL z a' c (ne_of_gt hc) hzL (some i)]
    rw [← D₁.basis_apply, restorationVector_some]
    exact hmask i
  have hqK (v : VertexType Q') (j : Fin d) : q v j ∈ K :=
    normalizedBasisChart_coordinates_in K D₁.basis hbK e (ε : ℝ) hεR ε.property
      (v.val, 1) ⟨hQ'K v.val v.property, K.one_mem⟩ j
  have hQ''K : CoordinatesIn K Q'' :=
    projectivePolytope_coordinates K Q' L q h hh hL hqK
  have ha'K : ∀ j, a' j ∈ K :=
    normalizedBasisChart_coordinates_in K D₁.basis hbK e (ε : ℝ) hεR ε.property z hzK
  obtain ⟨R', hR', hRR'⟩ :=
    D.realize_extension_from_admissible_point D₂ (φ.trans ψ) hD₂
      R a a' hvertices ha ha' hsame
  refine ⟨R', hRR', ?_⟩
  intro x hx j
  rw [hR'] at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact ha'K j
  · exact hQ''K x hx j

end SimplexFacetPresentation
end Papers.Polytopes

end
end
end BundlePart29

section BundlePart30
/- Source: Papers/SimpleDeletionFields.lean -/




@[expose] public section

/-!
# Simple vertex deletion preserves every real realization field

Both implications concern ordinary convex polytopes, their actual
extreme vertices, and their full face orders.  The simplex-facet
presentation used in restoration is derived from the given simple
vertex.  No coordinate-field or extra incidence hypothesis is retained
in the final statement.

This is the field clause of Theorem 3.  Its separate rational-density
clause is not included in this theorem's name or conclusion.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem RealizableOver.restore_simple_vertex
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) (K : Subfield ℝ)
    (hQK : RealizableOver (deleteVertex P v.val hne) K) : RealizableOver P K := by
  obtain ⟨D, _, _, ha⟩ := exists_deletion_simplexFacetPresentation P hP v hs hcard hne
  apply D.extension_realizable_over P v.val _ ha K hQK
  exact (Finset.insert_erase v.property).symm

theorem simpleDeletion_realizable_iff
    (P : ConvexPolytope d) (hP : P.IsFullDim) (v : VertexType P)
    (hs : IsSimpleVertex P v) (hcard : d + 1 < P.vertices.card)
    (hne : (P.vertices.erase v.val).Nonempty) (K : Subfield ℝ) :
    RealizableOver P K ↔ RealizableOver (deleteVertex P v.val hne) K :=
  ⟨RealizableOver.delete_of_simple P hP v hs hcard hne K,
    RealizableOver.restore_simple_vertex P hP v hs hcard hne K⟩

theorem simpleDeletionFieldsClaim : SimpleDeletionFieldsClaim := by
  intro d P v hP hcard hs hne K
  exact simpleDeletion_realizable_iff P hP v hs hcard hne K

end Papers.Polytopes

end
end
end BundlePart30


#print axioms Papers.Polytopes.simpleDeletion_realizable_iff
