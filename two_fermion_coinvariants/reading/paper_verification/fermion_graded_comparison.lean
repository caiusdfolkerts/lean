module

public import PaperVerification.FermionFilteredMultiplication
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Canonical comparison of actual associated-graded quotient pieces

The map sends a bounded representative to the class of its highest component.
Its kernel is proved to be the previous filtration step using actual relation
lifts. The two quotient maps have equal kernels, so the resulting equivalence
is a first-isomorphism-theorem comparison, not a transported grading.

-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.Fermion.BasisFiltered

variable {R A Q Q₀ I J : Type*} [CommRing R]
  [Ring A] [Algebra R A] [Ring Q] [Algebra R Q] [Ring Q₀] [Algebra R Q₀]
  (b : Module.Basis I R A) (w : I → ℕ)
  (q : A →ₐ[R] Q) (q₀ : A →ₐ[R] Q₀)
  (hone : Homogeneous b w 0 (1 : A))
  (hmul : ∀ i j,Homogeneous b w (w i+w j) (b i*b j))

/-- The bounded quotient map, with its actual image as codomain. -/
def boundedImageMap (d : ℕ) : boundPiece b w d →ₗ[R]
    (quotientFiltration b w q hone hmul).piece d where
  toFun x := ⟨q x,⟨x,x.property,rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change q.toLinearMap ((x : A) + (y : A)) = q.toLinearMap x + q.toLinearMap y
    exact map_add q.toLinearMap (x : A) (y : A)
  map_smul' c x := by
    apply Subtype.ext
    change q.toLinearMap (c • (x : A)) = c • q.toLinearMap x
    exact map_smul q.toLinearMap c (x : A)

/-- Projection to the actual successive quotient of the quotient filtration. -/
def gradedProjection (d : ℕ) : boundPiece b w d →ₗ[R]
    FilteredAlgebra.GradedPiece (quotientFiltration b w q hone hmul) d :=
  (FilteredAlgebra.previousRestricted (quotientFiltration b w q hone hmul) d).mkQ.comp
    (boundedImageMap b w q hone hmul d)

@[simp] theorem gradedProjection_apply (d : ℕ) (x : boundPiece b w d) :
    gradedProjection b w q hone hmul d x =
      Submodule.Quotient.mk (⟨q x,⟨x,x.property,rfl⟩⟩ :
        (quotientFiltration b w q hone hmul).piece d) := rfl

theorem gradedProjection_surjective (d : ℕ) :
    Function.Surjective (gradedProjection b w q hone hmul d) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
      obtain ⟨x,hx,hqx⟩ := z.property
      refine ⟨⟨x,hx⟩,?_⟩
      rw [gradedProjection_apply]
      apply congrArg Submodule.Quotient.mk
      exact Subtype.ext hqx

/-- The highest component takes values in the actual homogeneous quotient image. -/
def topRepresentative (d : ℕ) : boundPiece b w d →ₗ[R]
    (homogeneousPiece b w d).map q₀.toLinearMap where
  toFun x := ⟨q₀ (component b w d x),
    ⟨component b w d x,homogeneous_component b w d x,rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change q₀.toLinearMap (component b w d ((x : A) + (y : A))) =
      q₀.toLinearMap (component b w d x) + q₀.toLinearMap (component b w d y)
    simp only [map_add]
  map_smul' c x := by
    apply Subtype.ext
    change q₀.toLinearMap (component b w d (c • (x : A))) =
      c • q₀.toLinearMap (component b w d x)
    simp only [map_smul]

@[simp] theorem topRepresentative_coe (d : ℕ) (x : boundPiece b w d) :
    (topRepresentative b w q₀ d x : Q₀)=q₀ (component b w d x) := rfl

theorem topRepresentative_surjective (d : ℕ) :
    Function.Surjective (topRepresentative b w q₀ d) := by
  rintro ⟨y,x,hx,rfl⟩
  refine ⟨⟨x,homogeneous_bound b w hx⟩,?_⟩
  apply Subtype.ext
  rw [topRepresentative_coe,component_of_homogeneous b w hx,if_pos rfl]
  rfl

variable (f g : J → A) (degree : J → ℕ)
  (hf : ∀ j,HasTop b w (degree j) (f j) (g j))
  (hker : q.toLinearMap.ker=Submodule.span R (Set.range f))
  (hker₀ : q₀.toLinearMap.ker=Submodule.span R (Set.range g))
  (hinitial : initialSubmodule b w q.toLinearMap.ker ≤ q₀.toLinearMap.ker)

include hf hker hker₀ hinitial in
/-- The previous actual filtration step is exactly the kernel of the highest
component map. Both implications use actual representatives and relations. -/
theorem gradedProjection_zero_iff (d : ℕ) (x : boundPiece b w d) :
    gradedProjection b w q hone hmul d x=0 ↔ q₀ (component b w d x)=0 := by
  constructor
  · intro hz
    rw [gradedProjection_apply,FilteredAlgebra.gradedPiece_mk_eq_zero_iff] at hz
    cases d with
    | zero =>
        have hqx : q (x : A)=0 := hz
        change q₀.toLinearMap (component b w _ x) = 0
        apply LinearMap.mem_ker.mp
        apply hinitial
        exact Submodule.subset_span ⟨x,LinearMap.mem_ker.mpr hqx,0,x.property,rfl⟩
    | succ d =>
        obtain ⟨y,hy,hyq⟩ := hz
        change q.toLinearMap y = q.toLinearMap (x : A) at hyq
        have hrel : (x : A)-y ∈ q.toLinearMap.ker := by
          rw [LinearMap.mem_ker,map_sub,hyq,sub_self]
        have hb : Bound b w (d+1) ((x : A)-y) :=
          bound_sub b w x.property (bound_mono b w (Nat.le_succ d) hy)
        have ht : component b w (d+1) ((x : A)-y)=component b w (d+1) x := by
          rw [map_sub,component_eq_zero_of_bound_lt b w (Nat.lt_succ_self d) hy,sub_zero]
        change q₀.toLinearMap (component b w _ x) = 0
        apply LinearMap.mem_ker.mp
        apply hinitial
        exact Submodule.subset_span ⟨(x : A)-y,hrel,d+1,hb,ht⟩
  · intro hz
    have hg : component b w d x ∈ Submodule.span R (Set.range g) := by
      rw [← hker₀]
      exact LinearMap.mem_ker.mpr hz
    obtain ⟨a,ha,hab,hat⟩ :=
      relation_component_lifts b w f g degree hf (component b w d x) hg d
    have hqa : q a=0 := by
      change q.toLinearMap a = 0
      apply LinearMap.mem_ker.mp
      rwa [hker]
    have htop : component b w d ((x : A)-a)=0 := by
      rw [map_sub,hat,component_of_homogeneous b w
        (homogeneous_component b w d x),if_pos rfl,sub_self]
    have hb : Bound b w d ((x : A)-a) := bound_sub b w x.property hab
    rw [gradedProjection_apply,FilteredAlgebra.gradedPiece_mk_eq_zero_iff]
    cases d with
    | zero =>
        have he := eq_zero_of_bound_zero_component_zero b w hb htop
        change q (x : A)=0
        have h := congrArg q he
        simpa only [map_sub,hqa,sub_zero,map_zero] using h
    | succ d =>
        change q (x : A) ∈ (boundPiece b w d).map q.toLinearMap
        refine ⟨(x : A)-a,bound_pred_of_component_zero b w hb htop,?_⟩
        change q ((x : A)-a) = q (x : A)
        rw [map_sub,hqa,sub_zero]

include hf hker hker₀ hinitial in
theorem gradedProjection_ker_eq (d : ℕ) :
    (gradedProjection b w q hone hmul d).ker=(topRepresentative b w q₀ d).ker := by
  ext x
  change gradedProjection b w q hone hmul d x=0 ↔ topRepresentative b w q₀ d x=0
  rw [gradedProjection_zero_iff b w q q₀ hone hmul f g degree hf hker hker₀ hinitial]
  constructor
  · exact fun h ↦ Subtype.ext h
  · exact fun h ↦ congrArg Subtype.val h

/-- Canonical identification of the actual degree-`d` associated quotient with
the degree-`d` homogeneous quotient image. -/
def gradedPieceComparison (d : ℕ) :
    FilteredAlgebra.GradedPiece (quotientFiltration b w q hone hmul) d ≃ₗ[R]
      (homogeneousPiece b w d).map q₀.toLinearMap :=
  ((gradedProjection b w q hone hmul d).quotKerEquivOfSurjective
      (gradedProjection_surjective b w q hone hmul d)).symm.trans
    ((Submodule.quotEquivOfEq _ _
      (gradedProjection_ker_eq b w q q₀ hone hmul f g degree hf hker hker₀ hinitial d)).trans
      ((topRepresentative b w q₀ d).quotKerEquivOfSurjective
        (topRepresentative_surjective b w q₀ d)))

@[simp] theorem gradedPieceComparison_projection (d : ℕ) (x : boundPiece b w d) :
    gradedPieceComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial d
      (gradedProjection b w q hone hmul d x)=topRepresentative b w q₀ d x := by
  simp only [gradedPieceComparison,LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply,Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The formula makes clear that the comparison uses the original top
component and the original homogeneous quotient map. -/
@[simp] theorem gradedPieceComparison_projection_coe (d : ℕ) (x : boundPiece b w d) :
    (gradedPieceComparison b w q q₀ hone hmul f g degree hf hker hker₀ hinitial d
      (gradedProjection b w q hone hmul d x) : Q₀)=q₀ (component b w d x) := by
  rw [gradedPieceComparison_projection,topRepresentative_coe]

end PaperVerification.Fermion.BasisFiltered
