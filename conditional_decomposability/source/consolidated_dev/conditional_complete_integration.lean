module
public import consolidated.all_rigid_cover_cases
public import consolidated.homothety_uniform_cover
public import consolidated.universal_shephard
public import consolidated_dev.codim_two_extra_base
public import consolidated.minkowski_codimension_two_deletion
public import consolidated.proper_image_exact_summand
public import consolidated_dev.conditional_upper_canonical
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Sym.Sym2
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Tauto

set_option Elab.async false

section BundlePart0
/- Source: Papers/HomothetyProjectiveTransport.lean -/






@[expose] public section

/-!
# Projective transport of actual parallel maps

A homothety parameter is represented by `(a,b)` and evaluated as `a • x+b`.
Its evaluation kernel is the line through `(1,-x)`. A positive projective
change acts on these parameter lines by the same invertible linear map.
This gives exact transport of parallel maps, including reflection of global
homotheties. No rigidity or genericity assumption is needed.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d e : ℕ}

def evalParameter (p : ℝ × E d) (x : E d) : E d := p.1 • x + p.2

theorem evalParameter_eq_iff (p q : ℝ × E d) (x : E d) :
    evalParameter p x = evalParameter q x ↔
      ∃ c : ℝ, p-q = c • vertexVector x := by
  constructor
  · intro he
    refine ⟨p.1-q.1,?_⟩
    apply Prod.ext
    · change p.1-q.1=(p.1-q.1)*1
      ring
    · change p.2-q.2=(p.1-q.1) • (-x)
      change p.1 • x + p.2 = q.1 • x + q.2 at he
      have hb : p.2-q.2=q.1 • x-p.1 • x := by
        calc
          p.2-q.2 = (p.1 • x+p.2)-(q.1 • x+q.2)+(q.1 • x-p.1 • x) := by module
          _ = q.1 • x-p.1 • x := by rw [he,sub_self,zero_add]
      rw [hb]
      module
  · rintro ⟨c,hc⟩
    have hfst : p.1-q.1=c := by
      simpa only [Prod.fst_sub,Prod.smul_fst,vertexVector,smul_eq_mul,mul_one] using congrArg Prod.fst hc
    have hsnd : p.2-q.2=c • (-x) := congrArg Prod.snd hc
    rw [←hfst] at hsnd
    unfold evalParameter
    calc
      p.1 • x+p.2 = q.1 • x+q.2+((p.1-q.1) • x+(p.2-q.2)) := by module
      _ = q.1 • x+q.2 := by rw [hsnd]; module

theorem evalParameter_transport_iff
    (L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E e))
    (x : E d) (y : E e) (h : ℝ) (hh : h≠0)
    (hL : L (vertexVector x)=h • vertexVector y)
    (p q : ℝ × E d) :
    evalParameter (L p) y = evalParameter (L q) y ↔
      evalParameter p x = evalParameter q x := by
  rw [evalParameter_eq_iff,evalParameter_eq_iff]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c/h,?_⟩
    apply L.injective
    rw [map_sub,map_smul,hL,smul_smul,div_mul_cancel₀ _ hh]
    exact hc
  · rintro ⟨c,hc⟩
    refine ⟨c*h,?_⟩
    rw [←map_sub,hc,map_smul,hL,smul_smul]

/-- The transported map is defined on all ambient points; only actual
vertices are used in the parallel-map predicates. -/
def transportParallelMap (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (β : VertexType P ≃ VertexType Q)
    (L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E e)) (f : E d → E d) (y : E e) : E e :=
  if hy : y∈Q.vertices then
    evalParameter (L (0,f (β.symm ⟨y,hy⟩).val)) y
  else 0

@[simp] theorem transportParallelMap_vertex
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (β : VertexType P ≃ VertexType Q)
    (L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E e)) (f : E d → E d) (v : VertexType P) :
    transportParallelMap P Q β L f (β v).val =
      evalParameter (L (0,f v.val)) (β v).val := by
  simp only [transportParallelMap,dite_eq_left (β v).property]
  rw [Equiv.symm_apply_apply]

theorem transportParallelMap_homothety_value
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (β : VertexType P ≃ VertexType Q)
    (L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E e))
    (h : VertexType P → ℝ) (hh : ∀v,h v≠0)
    (hL : ∀v,L (vertexVector v.val)=h v • vertexVector (β v).val)
    (f : E d → E d) (v : VertexType P) (p : ℝ × E d)
    (hv : f v.val=evalParameter p v.val) :
    transportParallelMap P Q β L f (β v).val=evalParameter (L p) (β v).val := by
  rw [transportParallelMap_vertex]
  apply (evalParameter_transport_iff L v.val (β v).val (h v) (hh v) (hL v) (0,f v.val) p).mpr
  simpa only [evalParameter,zero_smul,zero_add] using hv

theorem transportParallelMap_parallel
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (β : VertexType P ≃ VertexType Q)
    (L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E e))
    (h : VertexType P → ℝ) (hh : ∀v,h v≠0)
    (hL : ∀v,L (vertexVector v.val)=h v • vertexVector (β v).val)
    (hedge : ∀v w:VertexType P,
      GeneralVertexStep Q (β v).val (β w).val → GeneralVertexStep P v.val w.val)
    (f : E d → E d) (hf : IsParallelMap P f) :
    IsParallelMap Q (transportParallelMap P Q β L f) := by
  intro x hx y hy hxy
  obtain ⟨v,hv⟩ := β.surjective ⟨x,hx⟩
  obtain ⟨w,hw⟩ := β.surjective ⟨y,hy⟩
  have hvx : (β v).val=x := congrArg Subtype.val hv
  have hwy : (β w).val=y := congrArg Subtype.val hw
  rw [←hvx,←hwy] at hxy ⊢
  obtain ⟨c,hc⟩ := hf v.val v.property w.val w.property (hedge v w hxy)
  let p : ℝ × E d := (c,f v.val-c • v.val)
  have hpv : f v.val=evalParameter p v.val := by dsimp [evalParameter,p]; module
  have hpw : f w.val=evalParameter p w.val := by
    dsimp [evalParameter,p]
    calc
      f w.val = f v.val+c • (w.val-v.val) := by rw [←hc]; abel
      _ = c • w.val+(f v.val-c • v.val) := by module
  rw [transportParallelMap_homothety_value P Q β L h hh hL f v p hpv,
    transportParallelMap_homothety_value P Q β L h hh hL f w p hpw]
  exact ⟨(L p).1,by unfold evalParameter; module⟩

theorem transportParallelMap_nonhomothetic
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (β : VertexType P ≃ VertexType Q)
    (L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E e))
    (h : VertexType P → ℝ) (hh : ∀v,h v≠0)
    (hL : ∀v,L (vertexVector v.val)=h v • vertexVector (β v).val)
    (f : E d → E d) (hnon : ¬IsHomothetyOnVertices P f) :
    ¬IsHomothetyOnVertices Q (transportParallelMap P Q β L f) := by
  rintro ⟨a,b,hab⟩
  let p : ℝ × E d := L.symm (a,b)
  apply hnon
  refine ⟨p.1,p.2,?_⟩
  intro x hx
  let v : VertexType P := ⟨x,hx⟩
  have hv := hab (β v).val (β v).property
  rw [transportParallelMap_vertex] at hv
  have he : evalParameter (L (0,f v.val)) (β v).val = evalParameter (L p) (β v).val := by
    simpa only [p,L.apply_symm_apply,evalParameter] using hv
  have hold := (evalParameter_transport_iff L v.val (β v).val (h v) (hh v) (hL v)
    (0,f v.val) p).mp he
  simpa only [evalParameter,zero_smul,zero_add] using hold

end Papers.Polytopes.HomothetyParameters

namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d e : ℕ}

/-- A positive signed homogeneous chart induces the actual polytope, its
face order isomorphism, and its exact map on extreme vertices. -/
theorem exists_signed_projective_polytope
    (P : ConvexPolytope d)
    (L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E e))
    (hpos : ∀x∈P.toSet,0<(L (vertexVector x)).1) :
    ∃ Q : ConvexPolytope e, ∃ β : VertexType P ≃ VertexType Q,
      ∃ h : VertexType P → ℝ,
      (∀v,0<h v) ∧
      (∀v,L (vertexVector v.val)=h v • vertexVector (β v).val) ∧
      (Nonempty (FaceType P ≃o FaceType Q)) ∧
      (∀v w:VertexType P,
        GeneralVertexStep Q (β v).val (β w).val → GeneralVertexStep P v.val w.val) := by
  let h : VertexType P → ℝ := fun v => (L (vertexVector v.val)).1
  let q : VertexType P → E e := fun v => (h v)⁻¹ • (-(L (vertexVector v.val)).2)
  have hh : ∀v,0<h v := fun v => hpos v.val (subset_convexHull ℝ _ v.property)
  have hX : ∀v,L (vertexVector v.val)=h v • vertexVector (q v) := by
    intro v
    apply Prod.ext
    · change h v=h v*1
      ring
    · change (L (vertexVector v.val)).2=h v • (-((h v)⁻¹ • (-(L (vertexVector v.val)).2)))
      simp only [smul_neg,neg_neg,smul_smul,mul_inv_cancel₀ (ne_of_gt (hh v)),one_smul]
  let M := (signedHomogeneousEquiv (d:=d)).trans (L.trans (signedHomogeneousEquiv (d:=e)).symm)
  have hM : ∀v,M (v.val,1)=h v • (q v,1) := by
    intro v
    apply Prod.ext
    · change -(L (vertexVector v.val)).2 = h v • q v
      dsimp only [q]
      rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (hh v)),one_smul]
    · change h v=h v*1
      ring
  let Q := projectivePolytope P M q h hh hM
  let β := projectiveVertexEquiv P M q h hh hM
  let φ := projectivePolytopeFaceOrderIso P M q h hh hM
  have hinc (F : FaceType P) (v : VertexType P) :
      (β v).val∈(φ F).val ↔ v.val∈F.val :=
    positiveProjectiveFaceOrderIso_incidence P Q M β h hh hM F v
  refine ⟨Q,β,h,hh,hX,⟨φ⟩,?_⟩
  intro v w hstep
  obtain ⟨hw,hn,G,hG,hGdim,hvG,hwG⟩ := hstep
  let GG : FaceType Q := ⟨G,hG⟩
  let F : FaceType P := φ.symm GG
  have hφ : φ F=GG := φ.apply_symm_apply GG
  refine ⟨w.property,?_,F.val,F.property,?_,?_,?_⟩
  · intro he
    exact hn (congrArg (fun z:VertexType P=>(β z).val) (Subtype.ext he))
  · have hd := Papers.ActualFaceOrder.faceDim_image φ F
    rw [hφ] at hd
    exact hd.symm.trans hGdim
  · apply (hinc F v).mp
    simpa only [hφ] using hvG
  · apply (hinc F w).mp
    simpa only [hφ] using hwG

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/HomothetyProjectiveChart.lean -/





@[expose] public section

/-!
# An actual positive projective chart avoiding the central section

Strong separation gives a linear functional annihilating the parameter
subspace and positive on the entire homogeneous polytope. A transvection
realizes that functional as the new affine coordinate. Both the inverse
and positivity are proved explicitly.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ}

theorem exists_positive_annihilator (P : ConvexPolytope d)
    (D : Submodule ℝ (ℝ × E d))
    (hdis : ∀ x∈P.toSet, vertexVector x∉D) :
    ∃ ell : (ℝ × E d) →ₗ[ℝ] ℝ,
      D ≤ ell.ker ∧ ∀ x∈P.toSet, 0 < ell (vertexVector x) := by
  have hconv : Convex ℝ (vertexVector '' P.toSet) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ a b ha hb hab
    refine ⟨a•x+b•y,(convex_convexHull ℝ (P.vertices : Set (E d))) hx hy ha hb hab,?_⟩
    apply Prod.ext
    · change 1 = a*1+b*1
      nlinarith
    · change -(a•x+b•y)=a•(-x)+b•(-y)
      module
  have hcont : Continuous (vertexVector : E d → ℝ × E d) :=
    continuous_const.prodMk continuous_neg
  have hcompact : IsCompact (vertexVector '' P.toSet) :=
    (P.vertices.finite_toSet.isCompact_convexHull ℝ).image hcont
  have hdisjoint : Disjoint (D : Set (ℝ × E d)) (vertexVector '' P.toSet) := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨x,hx,rfl⟩
    exact hdis x hx hz
  obtain ⟨ell,u,v,hleft,huv,hright⟩ := geometric_hahn_banach_closed_compact
    D.convex D.closed_of_finiteDimensional hconv hcompact hdisjoint
  have hzero : ∀ z∈D,ell z=0 := by
    intro z hz
    by_contra hne
    have hbound := hleft (((u+1)/(ell z))•z) (D.smul_mem _ hz)
    rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hne] at hbound
    linarith
  refine ⟨ell.toLinearMap,fun z hz => hzero z hz,?_⟩
  have hu : 0<u := by simpa only [map_zero] using hleft 0 D.zero_mem
  intro x hx
  exact hu.trans (huv.trans (hright _ ⟨x,hx,rfl⟩))

/-- The shear fixes its anchor because the added functional vanishes there. -/
def chartTransvection (ell : (ℝ × E d) →ₗ[ℝ] ℝ) (x : E d)
    (hx : ell (vertexVector x)=1) : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E d) where
  toFun z := z + (ell z-z.1) • vertexVector x
  invFun z := z - (ell z-z.1) • vertexVector x
  left_inv z := by
    dsimp only
    have hphi : ell (vertexVector x) - (vertexVector x).1 = 0 := by
      change ell (vertexVector x)-1=0
      rw [hx]; ring
    have hphiz : ell (z+(ell z-z.1)•vertexVector x) -
        (z+(ell z-z.1)•vertexVector x).1 = ell z-z.1 := by
      simp only [map_add,map_smul,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
      nlinarith [mul_eq_zero_of_left hphi (ell z-z.1)]
    rw [hphiz]
    abel
  right_inv z := by
    dsimp only
    have hphi : ell (vertexVector x) - (vertexVector x).1 = 0 := by
      change ell (vertexVector x)-1=0
      rw [hx]; ring
    have hphiz : ell (z-(ell z-z.1)•vertexVector x) -
        (z-(ell z-z.1)•vertexVector x).1 = ell z-z.1 := by
      simp only [map_sub,map_smul,Prod.fst_sub,Prod.smul_fst,smul_eq_mul]
      nlinarith [mul_eq_zero_of_left hphi (ell z-z.1)]
    rw [hphiz]
    abel
  map_add' z w := by
    simp only [map_add,Prod.fst_add]
    module
  map_smul' c z := by
    change c • z + (ell (c • z)-(c • z).1) • vertexVector x = c • (z+(ell z-z.1) • vertexVector x)
    simp only [map_smul,Prod.smul_fst,smul_eq_mul]
    module

@[simp] theorem chartTransvection_fst (ell : (ℝ × E d) →ₗ[ℝ] ℝ)
    (x : E d) (hx : ell (vertexVector x)=1) (z : ℝ × E d) :
    (chartTransvection ell x hx z).1 = ell z := by
  change z.1+(ell z-z.1)*1=ell z
  ring

theorem exists_positive_parameter_chart (P : ConvexPolytope d)
    (D : Submodule ℝ (ℝ × E d))
    (hdis : ∀ x∈P.toSet,vertexVector x∉D) :
    ∃ L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E d),
      (∀ z∈D,(L z).1=0) ∧ ∀ x∈P.toSet,0<(L (vertexVector x)).1 := by
  obtain ⟨ell,hker,hpos⟩ := exists_positive_annihilator P D hdis
  obtain ⟨x,hx⟩ := P.vertices_nonempty
  have hxP := subset_convexHull ℝ (P.vertices : Set (E d)) hx
  let ell' := (ell (vertexVector x))⁻¹ • ell
  have hnormal : ell' (vertexVector x)=1 := by
    change (ell (vertexVector x))⁻¹ * ell (vertexVector x)=1
    exact inv_mul_cancel₀ (ne_of_gt (hpos x hxP))
  refine ⟨chartTransvection ell' x hnormal,?_,?_⟩
  · intro z hz
    rw [chartTransvection_fst]
    change (ell (vertexVector x))⁻¹ * ell z=0
    rw [show ell z=0 from hker hz,mul_zero]
  · intro y hy
    rw [chartTransvection_fst]
    exact mul_pos (inv_pos.mpr (hpos x hxP)) (hpos y hy)

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/HomothetyProjectiveReduction.lean -/




@[expose] public section

/-!
# Empty central section gives a genuinely lower-dimensional parallel image

The separating projective chart sends every parameter difference to the
hyperplane with first coordinate zero. The transported homotheties then
have one common scalar. Subtracting it leaves a parallel map with at most
one image value per parameter class. The map is proved nonhomothetic.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ} {I : Type*} [Fintype I]

theorem projective_proper_image_of_empty_central
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (a : I → ℝ) (b : I → E d)
    (hcover : ∀x∈P.vertices,∃i,f x=a i • x+b i)
    (hempty : centralSection P a b=∅) :
    ∃ Q : ConvexPolytope d, Q.IsFullDim ∧ CombinatoriallyEquivalent P Q ∧
      Q.vertices.card=P.vertices.card ∧
      ∃ g : E d → E d, IsParallelMap Q g ∧ ¬IsHomothetyOnVertices Q g ∧
        finrank ℝ (vectorSpan ℝ (g '' (Q.vertices : Set (E d)))) ≤ Fintype.card I-1 := by
  have hdis : ∀x∈P.toSet,vertexVector x∉parameterDirectionSpan a b := by
    intro x hx hD
    have hm : x∈centralSection P a b := ⟨hx,hD⟩
    rw [hempty] at hm
    exact hm.elim
  obtain ⟨L,hLD,hpos⟩ := exists_positive_parameter_chart P (parameterDirectionSpan a b) hdis
  obtain ⟨Q,β,h,hh,hL,⟨φ⟩,hedge⟩ := exists_signed_projective_polytope P L hpos
  let f' := transportParallelMap P Q β L f
  have hparallel : IsParallelMap Q f' :=
    transportParallelMap_parallel P Q β L h (fun v=>(ne_of_gt (hh v))) hL hedge f hf
  have hnon' : ¬IsHomothetyOnVertices Q f' :=
    transportParallelMap_nonhomothetic P Q β L h (fun v=>(ne_of_gt (hh v))) hL f hnon
  obtain ⟨v,hv⟩ := P.vertices_nonempty
  obtain ⟨i₀,hi₀⟩ := hcover v hv
  letI : Nonempty I := ⟨i₀⟩
  let α : ℝ := (L (parameterVector a b i₀)).1
  let bp : I → E d := fun i => (L (parameterVector a b i)).2
  have hscalar (i:I) : (L (parameterVector a b i)).1=α := by
    have hmem : parameterVector a b i-parameterVector a b i₀∈parameterDirectionSpan a b :=
      Submodule.subset_span ⟨(i,i₀),rfl⟩
    have hz := hLD _ hmem
    rw [map_sub,Prod.fst_sub] at hz
    exact sub_eq_zero.mp hz
  let g : E d → E d := fun x => f' x-α • x
  have hg : IsParallelMap Q g := by
    intro x hx y hy hxy
    obtain ⟨c,hc⟩ := hparallel x hx y hy hxy
    refine ⟨c-α,?_⟩
    change (f' y-α • y)-(f' x-α • x)=(c-α) • (y-x)
    calc
      (f' y-α • y)-(f' x-α • x)=(f' y-f' x)-α • (y-x) := by module
      _=(c-α) • (y-x) := by rw [hc]; module
  have hg_non : ¬IsHomothetyOnVertices Q g := by
    rintro ⟨c,u,hu⟩
    apply hnon'
    refine ⟨c+α,u,?_⟩
    intro x hx
    have hxg := hu x hx
    change f' x-α • x=c • x+u at hxg
    calc
      f' x = (f' x-α • x)+α • x := by abel
      _ = (c+α) • x+u := by rw [hxg]; module
  have hvalues : g '' (Q.vertices : Set (E d)) ⊆ Set.range bp := by
    rintro y ⟨x,hx,rfl⟩
    obtain ⟨w,hw⟩ := β.surjective ⟨x,hx⟩
    have hwx : (β w).val=x := congrArg Subtype.val hw
    obtain ⟨i,hi⟩ := hcover w.val w.property
    refine ⟨i,?_⟩
    have he := transportParallelMap_homothety_value P Q β L h
      (fun v=>ne_of_gt (hh v)) hL f w (parameterVector a b i) hi
    rw [hwx] at he
    change bp i=transportParallelMap P Q β L f x-α • x
    rw [he]
    unfold evalParameter
    rw [hscalar]
    dsimp [bp]
    module
  have hrank := Submodule.finrank_mono (vectorSpan_mono ℝ hvalues)
  have hcard := finrank_vectorSpan_range_add_one_le ℝ bp
  have hQ : Q.IsFullDim := (Papers.ActualFaceOrder.dim_eq φ).trans hP
  refine ⟨Q,hQ,⟨φ⟩,(Papers.ActualFaceOrder.vertices_card_eq φ).symm,g,hg,hg_non,?_⟩
  omega

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/HomothetyUniformReduction.lean -/




@[expose] public section

/-! The full alternative of Proposition 12, with its projective image
constructed and its nonempty central section resolved geometrically. -/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ} {I : Type*} [Fintype I]

/-- An actual face-equivalent realization carrying a nonhomothetic
parallel map of bounded affine image dimension. -/
def ParallelImageReduction (P : ConvexPolytope d) (k : ℕ) : Prop :=
  ∃ Q : ConvexPolytope d, Q.IsFullDim ∧ CombinatoriallyEquivalent P Q ∧
    Q.vertices.card=P.vertices.card ∧
    ∃ g : E d → E d, IsParallelMap Q g ∧ ¬IsHomothetyOnVertices Q g ∧
      finrank ℝ (vectorSpan ℝ (g '' (Q.vertices : Set (E d)))) ≤ k

theorem ParallelImageReduction.mono {P : ConvexPolytope d} {k l : ℕ}
    (h : ParallelImageReduction P k) (hkl : k ≤ l) : ParallelImageReduction P l := by
  obtain ⟨Q,hQ,hPQ,hcard,g,hg,hgn,hrank⟩ := h
  exact ⟨Q,hQ,hPQ,hcard,g,hg,hgn,hrank.trans hkl⟩

/-- Proposition 12 with the paper's exact image bound, `m - 1`. -/
theorem uniform_cover_shephard_or_image_card
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (a : I → ℝ) (b : I → E d)
    (hcover : ∀y∈P.vertices,∃j,f y=a j • y+b j)
    (hprivate : ∀i,∃x∈fullClass P f a b i,∀j,f x=a j • x+b j→j=i)
    (hm : 4≤Fintype.card I) (hd : Fintype.card I+1≤d)
    (hN : P.vertices.card≤4*d-5) :
    HasShephardProperty P ∨ ParallelImageReduction P (Fintype.card I-1) := by
  by_cases hne : (centralVertices P a b).Nonempty
  · exact Or.inl (uniform_nonempty_central_shephard P hP f hf hnon a b hcover hprivate hm hd hN hne)
  · apply Or.inr
    obtain ⟨hind,htm,ht,hr,hbudget,i,hi⟩ :=
      uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
    obtain ⟨B,hB,hclique,hpos,hfacets,hfibers,hinter,hF⟩ :=
      minimumClass_fiber_faces P hP f hf a b hcover hprivate i (by omega) hi
    have hempty : centralSection P a b=∅ := by
      rcases hF with he|hF
      · exact he
      · obtain ⟨x,hx⟩ := (facePolytope P hF).vertices_nonempty
        have hx' := Finset.mem_filter.mp hx
        exact False.elim (hne ⟨x,Finset.mem_filter.mpr ⟨hx'.1,hx'.2.2⟩⟩)
    obtain ⟨Q,hQ,hPQ,hcard,g,hg,hgn,hrank⟩ :=
      projective_proper_image_of_empty_central P hP f hf hnon a b hcover hempty
    exact ⟨Q,hQ,hPQ,hcard,g,hg,hgn,hrank⟩

/-- The same construction in the dimension form used by the final
proper-image persistence argument. -/
theorem uniform_cover_shephard_or_proper_image
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (a : I → ℝ) (b : I → E d)
    (hcover : ∀y∈P.vertices,∃j,f y=a j • y+b j)
    (hprivate : ∀i,∃x∈fullClass P f a b i,∀j,f x=a j • x+b j→j=i)
    (hm : 4≤Fintype.card I) (hd : Fintype.card I+1≤d)
    (hN : P.vertices.card≤4*d-5) :
    HasShephardProperty P ∨ ParallelImageReduction P (d-2) := by
  rcases uniform_cover_shephard_or_image_card P hP f hf hnon a b
    hcover hprivate hm hd hN with hS | hR
  · exact Or.inl hS
  · exact Or.inr (hR.mono (by omega))

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/HomothetySubcover.lean -/





@[expose] public section

/-!
# Removing redundant homotheties

Every finite homothety cover has a subcover in which each parameter has a
private actual vertex. The subcover retains the original homotheties and
does not increase their number. Reindexing by the retained finite set
therefore supplies the hypotheses of the class-bound theorem.

-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*}

theorem exists_essential_subcover (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) (S : Finset I)
    (hcover : ∀ x ∈ P.vertices, ∃ i ∈ S, f x = a i • x + b i) :
    ∃ T ⊆ S,
      (∀ x ∈ P.vertices, ∃ i ∈ T, f x = a i • x + b i) ∧
      ∀ i ∈ T, ∃ x ∈ fullClass P f a b i,
        ∀ j ∈ T, f x = a j • x + b j → j = i := by
  classical
  revert hcover
  refine Finset.strongInductionOn S ?_
  intro S ih hcover
  by_cases hessential : ∀ i ∈ S, ∃ x ∈ fullClass P f a b i,
      ∀ j ∈ S, f x = a j • x + b j → j = i
  · exact ⟨S, Finset.Subset.refl S, hcover, hessential⟩
  · push_neg at hessential
    obtain ⟨i, hi, hredundant⟩ := hessential
    have hcover' : ∀ x ∈ P.vertices,
        ∃ j ∈ S.erase i, f x = a j • x + b j := by
      intro x hx
      obtain ⟨j, hj, hxj⟩ := hcover x hx
      by_cases hji : j = i
      · subst j
        obtain ⟨k, hk, hxk, hki⟩ :=
          hredundant x (Finset.mem_filter.mpr ⟨hx, hxj⟩)
        exact ⟨k, Finset.mem_erase.mpr ⟨hki, hk⟩, hxk⟩
      · exact ⟨j, Finset.mem_erase.mpr ⟨hji, hj⟩, hxj⟩
    obtain ⟨T, hTS, hTcover, hTprivate⟩ :=
      ih (S.erase i) (Finset.erase_ssubset hi) hcover'
    exact ⟨T, hTS.trans (Finset.erase_subset i S), hTcover, hTprivate⟩

/-- A one-parameter cover really is a homothety on all actual vertices. -/
theorem homothety_of_cover_card_le_one (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) (S : Finset I)
    (hcover : ∀ x ∈ P.vertices, ∃ i ∈ S, f x = a i • x + b i)
    (hcard : S.card ≤ 1) : IsHomothetyOnVertices P f := by
  obtain ⟨x, hx⟩ := P.vertices_nonempty
  obtain ⟨i, hi, hxi⟩ := hcover x hx
  refine ⟨a i, b i, ?_⟩
  intro y hy
  obtain ⟨j, hj, hyj⟩ := hcover y hy
  have hji : j = i := Finset.card_le_one.mp hcard j hj i hi
  simpa only [hji] using hyj

/-- A nonhomothetic map retains at least two essential parameters. -/
theorem exists_essential_subcover_nontrivial (P : ConvexPolytope d)
    (f : E d → E d) (a : I → ℝ) (b : I → E d) (S : Finset I)
    (hcover : ∀ x ∈ P.vertices, ∃ i ∈ S, f x = a i • x + b i)
    (hnon : ¬IsHomothetyOnVertices P f) :
    ∃ T ⊆ S, 2 ≤ T.card ∧
      (∀ x ∈ P.vertices, ∃ i ∈ T, f x = a i • x + b i) ∧
      ∀ i ∈ T, ∃ x ∈ fullClass P f a b i,
        ∀ j ∈ T, f x = a j • x + b j → j = i := by
  obtain ⟨T, hTS, hTc, hTp⟩ := exists_essential_subcover P f a b S hcover
  have htwo : 2 ≤ T.card := by
    by_contra h
    exact hnon (homothety_of_cover_card_le_one P f a b T hTc (by omega))
  exact ⟨T, hTS, htwo, hTc, hTp⟩

theorem reindexed_cover (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) (S : Finset I)
    (hcover : ∀ x ∈ P.vertices, ∃ i ∈ S, f x = a i • x + b i) :
    ∀ x ∈ P.vertices, ∃ i : S, f x = a i.val • x + b i.val := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := hcover x hx
  exact ⟨⟨i, hi⟩, hxi⟩

theorem reindexed_private (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) (S : Finset I)
    (hprivate : ∀ i ∈ S, ∃ x ∈ fullClass P f a b i,
      ∀ j ∈ S, f x = a j • x + b j → j = i) :
    ∀ i : S, ∃ x ∈ fullClass P f (fun j : S => a j.val) (fun j : S => b j.val) i,
      ∀ j : S, f x = a j.val • x + b j.val → j = i := by
  intro i
  obtain ⟨x, hxi, hpriv⟩ := hprivate i.val i.property
  refine ⟨x, hxi, ?_⟩
  intro j hj
  exact Subtype.ext (hpriv j.val j.property hj)

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/EssentialFiniteCover.lean -/




@[expose] public section

/-! Minimal essential covers with a literal finite index and actual private vertices. -/
noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ} {I : Type*} [Fintype I]

theorem exists_essential_fin_cover
    (P : ConvexPolytope n) (f : E n → E n)
    (a : I → ℝ) (b : I → E n)
    (hcover : ∀ x∈P.vertices,∃i:I,f x=a i•x+b i)
    (hnon : ¬IsHomothetyOnVertices P f) :
    ∃ m : ℕ,2≤m ∧ m≤Fintype.card I ∧
      ∃ p : Fin m → ℝ × E n,∃ color : P.vertices → Fin m,
        (∀v:P.vertices,f v.val=(p (color v)).1•v.val+(p (color v)).2) ∧
        ∀i:Fin m,∃x∈P.vertices,
          f x=(p i).1•x+(p i).2 ∧
          ∀j:Fin m,j≠i→f x≠(p j).1•x+(p j).2 := by
  obtain ⟨T,hTsub,hTcard,hTc,hTp⟩ :=
    exists_essential_subcover_nontrivial P f a b Finset.univ
      (fun x hx => by obtain ⟨i,hi⟩ := hcover x hx; exact ⟨i,Finset.mem_univ i,hi⟩) hnon
  let e : T ≃ Fin T.card := Fintype.equivFinOfCardEq (Fintype.card_coe T)
  let p : Fin T.card → ℝ × E n := fun i =>
    (a (e.symm i).val,b (e.symm i).val)
  have hpc : ∀v:P.vertices,∃i:Fin T.card,f v.val=(p i).1•v.val+(p i).2 := by
    intro v
    obtain ⟨i,hi,hfi⟩ := hTc v.val v.property
    refine ⟨e ⟨i,hi⟩,?_⟩
    simpa only [p,Equiv.symm_apply_apply] using hfi
  let color : P.vertices → Fin T.card := fun v => (hpc v).choose
  refine ⟨T.card,hTcard,?_,p,color,fun v => (hpc v).choose_spec,?_⟩
  · simpa only [Finset.card_univ] using Finset.card_le_card hTsub
  · intro i
    obtain ⟨x,hxi,hpriv⟩ := hTp (e.symm i).val (e.symm i).property
    obtain ⟨hx,hfx⟩ := Finset.mem_filter.mp hxi
    refine ⟨x,hx,hfx,?_⟩
    intro j hji hfj
    have hvals : (e.symm j).val=(e.symm i).val :=
      hpriv (e.symm j).val (e.symm j).property hfj
    exact hji (e.symm.injective (Subtype.ext hvals))

end Papers.Polytopes.HomothetyParameters


end
end
end BundlePart5

section BundlePart6
/- Source: Papers/ActualEssentialCovers.lean -/





@[expose] public section

/-! Actual rigid graph covers supply finite essential homothety covers. -/
noncomputable section
namespace Papers.ActualEssentialCovers

open Set
open Papers.Polytopes Papers.Polytopes.HomothetyParameters
open Papers.PolytopeFourRegularTail Papers.ActualHomothetyClasses
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ} {I : Type*} [Fintype I]

theorem essential_cover_of_rigid_cover
    (P : ConvexPolytope n) (f : E n → E n)
    (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (A : I → Finset (E n))
    (hcover : ∀ x ∈ P.vertices, ∃ i : I, x ∈ A i)
    (hrigid : ∀ i : I, RigidInTail P P.vertices (A i)) :
    ∃ m : ℕ, 2 ≤ m ∧ m ≤ Fintype.card I ∧
      ∃ p : Fin m → ℝ × E n, ∃ color : P.vertices → Fin m,
        (∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val) ∧
        ∀ i : Fin m, ∃ x ∈ P.vertices, f x = evaluate (p i) x ∧
          ∀ j : Fin m, j ≠ i → f x ≠ evaluate (p j) x := by
  choose a b hab using fun i => hrigid i f hf
  apply exists_essential_fin_cover P f a b _ hnon
  intro x hx
  obtain ⟨i, hi⟩ := hcover x hx
  exact ⟨i, hab i x hi⟩

theorem essential_cover_of_homothety_cover
    (P : ConvexPolytope n) (f : E n → E n)
    (p : I → ℝ × E n)
    (hcover : ∀ x ∈ P.vertices, ∃ i : I, f x = evaluate (p i) x)
    (hnon : ¬IsHomothetyOnVertices P f) :
    ∃ m : ℕ, 2 ≤ m ∧ m ≤ Fintype.card I ∧
      ∃ q : Fin m → ℝ × E n, ∃ color : P.vertices → Fin m,
        (∀ v : P.vertices, f v.val = evaluate (q (color v)) v.val) ∧
        ∀ i : Fin m, ∃ x ∈ P.vertices, f x = evaluate (q i) x ∧
          ∀ j : Fin m, j ≠ i → f x ≠ evaluate (q j) x :=
  exists_essential_fin_cover P f (fun i => (p i).1) (fun i => (p i).2) hcover hnon

end Papers.ActualEssentialCovers


end
end
end BundlePart6

section BundlePart7
/- Source: Papers/HomothetyCoverRouting.lean -/





@[expose] public section

/-!
# Actual graph covers route to the geometric alternatives

The finite essential subcover is chosen from actual homothety pieces.
If it drops a boundary parameter, at most d−1 parameters remain. If it
does not, every original boundary piece retains a private vertex and the
proved boundary-cover argument applies. The only separate output is a
literal two- or three-parameter cover, for Proposition 11.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open Papers.PolytopeFourRegularTail Papers.ActualEssentialCovers Papers.PolytopeVertexCone
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {d : ℕ}

def SmallEssentialParallelCover (P : ConvexPolytope d) (f : E d → E d) : Prop :=
  ∃m:ℕ,2≤m ∧ m≤3 ∧
    ∃p:Fin m→ℝ×E d,∃color:P.vertices→Fin m,
      (∀v:P.vertices,f v.val=(p (color v)).1 • v.val+(p (color v)).2) ∧
      ∀i:Fin m,∃x∈P.vertices,f x=(p i).1 • x+(p i).2 ∧
        ∀j:Fin m,j≠i→f x≠(p j).1 • x+(p j).2

theorem essential_fin_cover_routes
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (hN : P.vertices.card≤4*d-5)
    (m : ℕ) (hmlo : 2≤m) (hmhi : m≤3 ∨ m+1≤d)
    (p : Fin m→ℝ×E d) (color:P.vertices→Fin m)
    (hcover : ∀v:P.vertices,f v.val=(p (color v)).1 • v.val+(p (color v)).2)
    (hprivate : ∀i:Fin m,∃x∈P.vertices,f x=(p i).1 • x+(p i).2 ∧
      ∀j:Fin m,j≠i→f x≠(p j).1 • x+(p j).2) :
    SmallEssentialParallelCover P f ∨ HasShephardProperty P ∨ ParallelImageReduction P (d-2) := by
  by_cases hm3 : m≤3
  · exact Or.inl ⟨m,hmlo,hm3,p,color,hcover,hprivate⟩
  · apply Or.inr
    apply uniform_cover_shephard_or_proper_image P hP f hf hnon
      (fun i=>(p i).1) (fun i=>(p i).2) ?_ ?_ (by simpa using (show 4≤m by omega))
      (by simpa using (show m+1≤d by omega)) hN
    · intro x hx
      exact ⟨color ⟨x,hx⟩,hcover ⟨x,hx⟩⟩
    · intro i
      obtain ⟨x,hx,hxi,hpriv⟩ := hprivate i
      refine ⟨x,Finset.mem_filter.mpr ⟨hx,hxi⟩,?_⟩
      intro j hj
      by_contra hji
      exact hpriv j hji hj

theorem rigid_cover_routes
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (hd : 3≤d) (hN : P.vertices.card≤4*d-5)
    (hC : HasRigidCover P P.vertices (PaperRigidCoverBound d)) :
    SmallEssentialParallelCover P f ∨ HasShephardProperty P ∨ ParallelImageReduction P (d-2) := by
  obtain ⟨I,hI,A,hcard,hwithin,hrigid,hcover⟩ := hC.indexed
  letI := hI
  obtain ⟨m,hmlo,hmhi,p,color,hpc,hpp⟩ :=
    essential_cover_of_rigid_cover P f hf hnon A hcover hrigid
  have hbound : m≤3 ∨ m+1≤d := by
    by_cases hd3 : d=3
    · left
      have hcard3 : Fintype.card I ≤ 3 := by
        simpa [PaperRigidCoverBound, hd3] using hcard
      exact hmhi.trans hcard3
    · right
      simp only [PaperRigidCoverBound,if_neg hd3] at hcard
      omega
  exact essential_fin_cover_routes P hP f hf hnon hN m hmlo hbound p color hpc hpp

end Papers.Polytopes.HomothetyParameters

namespace Papers.Polytopes.HomothetyParameters
open Set Module
open Papers.PolytopeFourRegularTail Papers.ActualEssentialCovers Papers.PolytopeVertexCone
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {d : ℕ} {I : Type*} [Fintype I]

theorem global_boundary_cover_routes
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (hN : P.vertices.card≤4*d-5)
    (c e j:I) (z:E d) (R:GlobalRigidBoundaryPieces P I c e j z)
    (hcolors:Fintype.card I=d) (hdlo:4≤d) (hdhi:d≤5) :
    SmallEssentialParallelCover P f ∨ HasShephardProperty P ∨ ParallelImageReduction P (d-2) := by
  choose a b hab using fun i => R.rigid i f hf
  let B : BoundaryPieces P f a b c e j z :=
    { piece := R.piece
      within := R.within
      cover := R.cover
      values := hab
      card_le_four := R.card_le_four
      left_card := R.left_card
      right_card := R.right_card
      edge_card := R.edge_card
      left_mem := R.left_mem
      right_mem := R.right_mem
      distinct := R.distinct }
  by_cases hprivate : ∀i,∃x∈fullClass P f a b i,∀k,f x=a k • x+b k→k=i
  · exact Or.inr (Or.inl (B.essential_cover_shephard hP hf hprivate hcolors hdlo hdhi hN))
  · obtain ⟨T,hTS,hTcard,hcover,hpriv⟩ := exists_essential_subcover_nontrivial P f a b
      Finset.univ (fun x hx=>by obtain ⟨i,hi⟩:=B.parameter_cover x hx; exact ⟨i,Finset.mem_univ i,hi⟩) hnon
    have hTlt : T.card<Fintype.card I := by
      by_contra hn
      have he : T=Finset.univ := Finset.eq_of_subset_of_card_le hTS (by simpa using (show Fintype.card I≤T.card by omega))
      apply hprivate
      intro i
      obtain ⟨x,hxi,hxp⟩ := hpriv i (by rw [he]; exact Finset.mem_univ i)
      exact ⟨x,hxi,fun k hk=>hxp k (by rw [he]; exact Finset.mem_univ k) hk⟩
    let a' : T→ℝ := fun i=>a i.val
    let b' : T→E d := fun i=>b i.val
    have hcover' : ∀x∈P.vertices,∃i:T,f x=a' i • x+b' i := reindexed_cover P f a b T hcover
    obtain ⟨m,hmlo,hmhi,p,color,hpc,hpp⟩ := exists_essential_fin_cover P f a' b' hcover' hnon
    have hbound : m+1≤d := by
      rw [Fintype.card_coe] at hmhi
      omega
    exact essential_fin_cover_routes P hP f hf hnon hN m hmlo (Or.inr hbound) p color hpc hpp

theorem boundary_cover_routes
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (hN : P.vertices.card≤4*d-5)
    (hd : d=4 ∨ d=5) (hC : HasRigidBoundaryCover P (d-3)) :
    SmallEssentialParallelCover P f ∨ HasShephardProperty P ∨ ParallelImageReduction P (d-2) := by
  obtain ⟨z,⟨R⟩⟩ := hC
  exact global_boundary_cover_routes P hP f hf hnon hN _ _ _ z R
    (by simp only [Fintype.card_sum,Fintype.card_fin]; omega) (by omega) (by omega)

/-- All graph-theoretic cover cases in Section 8 have now been routed to
the literal small-cover case or one of the proved geometric alternatives. -/
theorem all_actual_covers_routes
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (hd : 3≤d) (hN : P.vertices.card≤4*d-5) :
    SmallEssentialParallelCover P f ∨ HasShephardProperty P ∨ ParallelImageReduction P (d-2) := by
  rcases all_actual_rigid_cover_cases P hP hd hN with hC | ⟨hd45,hC⟩ | hS
  · exact rigid_cover_routes P hP f hf hnon hd hN hC
  · exact boundary_cover_routes P hP f hf hnon hN hd45 hC
  · obtain ⟨F,hF,hFdim,hout,huniq⟩ :=
      HasRigidSetContainingNonsimple.shephard_facet hP hS f hf hnon
    apply Or.inr
    apply Or.inl
    refine ⟨F,⟨hF,hFdim.trans hP.symm⟩,?_⟩
    intro v hv hvF
    have hcard := huniq v hv hvF
    obtain ⟨u,hu⟩ := Finset.card_eq_one.mp hcard
    have hu' : u∈(Papers.PolytopeVertexCone.actualNeighbors P v).filter (fun y=>y∉F) := by
      rw [hu]
      simp
    have huN := Finset.mem_filter.mp hu'
    refine ⟨u,⟨?_,huN.2⟩,?_⟩
    · exact (Papers.PolytopeVertexCone.mem_actualNeighbors_iff P v u).mp huN.1
    · rintro w ⟨hw,hwF⟩
      have hw' : w∈(Papers.PolytopeVertexCone.actualNeighbors P v).filter (fun y=>y∉F) :=
        Finset.mem_filter.mpr ⟨(Papers.PolytopeVertexCone.mem_actualNeighbors_iff P v w).mpr hw,hwF⟩
      rw [hu,Finset.mem_singleton] at hw'
      exact hw'

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/ThreeLineCompatibility.lean -/






@[expose] public section

/-!
# Compatible differences for three collinear projective centers

A common projective plane here means a vector subspace of dimension at
most two.  Coincident centers are allowed: the resulting compatible
parameters may merge two color classes, but they are not all equal.
-/

namespace Papers.ProjectiveCompatibility
open Submodule Module

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem exists_nonzero_of_finrank_one (J : Submodule K W)
    (hJ : finrank K J = 1) : ∃ q ∈ J, q ≠ (0 : W) := by
  apply J.ne_bot_iff.mp
  intro he
  rw [he, finrank_bot] at hJ
  omega

theorem distinct_lines_span_dimension (A B : Submodule K W)
    (hA : finrank K A = 1) (hB : finrank K B = 1) (hne : A ≠ B) :
    finrank K (A ⊔ B : Submodule K W) = 2 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hge := Submodule.finrank_mono (show A ≤ A ⊔ B from le_sup_left)
  rw [hA, hB] at hdim
  rw [hA] at hge
  have hnot : finrank K (A ⊔ B : Submodule K W) ≠ 1 := by
    intro hs
    have ha : A = A ⊔ B :=
      Submodule.eq_of_le_of_finrank_eq le_sup_left (hA.trans hs.symm)
    have hb : B ≤ A := by rw [ha]; exact le_sup_right
    have he : B = A := Submodule.eq_of_le_of_finrank_eq hb (hB.trans hA.symm)
    exact hne he.symm
  omega

theorem three_line_compatible_differences
    (J01 J02 J12 : Submodule K W)
    (h01 : finrank K J01 = 1) (h02 : finrank K J02 = 1)
    (h12 : finrank K J12 = 1)
    (hcollinear : finrank K (J01 ⊔ J02 ⊔ J12 : Submodule K W) ≤ 2) :
    ∃ u v : W, u ∈ J01 ∧ v ∈ J02 ∧ v - u ∈ J12 ∧
      (u ≠ 0 ∨ v ≠ 0) := by
  by_cases he : J01 = J02
  · obtain ⟨u, hu, hune⟩ := exists_nonzero_of_finrank_one J01 h01
    refine ⟨u, u, hu, ?_, ?_, Or.inl hune⟩
    · simpa only [← he] using hu
    · simpa only [sub_self] using J12.zero_mem
  · have hspan : finrank K (J01 ⊔ J02 : Submodule K W) = 2 :=
      distinct_lines_span_dimension J01 J02 h01 h02 he
    have hmono := Submodule.finrank_mono
      (show J01 ⊔ J02 ≤ J01 ⊔ J02 ⊔ J12 from le_sup_left)
    have heq : J01 ⊔ J02 = J01 ⊔ J02 ⊔ J12 :=
      Submodule.eq_of_le_of_finrank_eq le_sup_left (by omega)
    have hsub : J12 ≤ J01 ⊔ J02 := by
      rw [heq]
      exact le_sup_right
    obtain ⟨w, hw, hwne⟩ := exists_nonzero_of_finrank_one J12 h12
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hsub hw)
    refine ⟨-a, b, J01.neg_mem ha, hb, ?_, ?_⟩
    · have hew : b - -a = w := by
        simpa only [sub_neg_eq_add, add_comm] using hab
      rw [hew]
      exact hw
    · by_contra! hzero
      have ha0 : a = 0 := neg_eq_zero.mp hzero.1
      apply hwne
      simpa only [ha0, hzero.2, zero_add] using hab.symm

end Papers.ProjectiveCompatibility

end
end BundlePart8

section BundlePart9
/- Source: Papers/ThreeColorReconstruction.lean -/






@[expose] public section

/-!
# Reconstruction from three collinear forced centers

The rank hypothesis includes every projective coincidence case.  The
result supplies an actual nontrivial parallel map on the colored
vertices, even when two color parameters have to be merged.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module Papers.ProjectiveCompatibility
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def threeColorCenter (J01 J02 J12 : Submodule ℝ (E d × ℝ)) :
    Fin 3 → Fin 3 → Submodule ℝ (E d × ℝ) :=
  ![![⊥, J01, J02], ![J01, ⊥, J12], ![J02, J12, ⊥]]

theorem decomposable_of_three_collinear_centers
    (P : ConvexPolytope d) (label : E d → Fin 3)
    (J01 J02 J12 : Submodule ℝ (E d × ℝ))
    (h01 : finrank ℝ J01 = 1) (h02 : finrank ℝ J02 = 1)
    (h12 : finrank ℝ J12 = 1)
    (hcollinear : finrank ℝ (J01 ⊔ J02 ⊔ J12 : Submodule ℝ (E d × ℝ)) ≤ 2)
    (hclasses : ∀ i : Fin 3, ∃ x ∈ P.vertices, ∃ y ∈ P.vertices,
      x ≠ y ∧ label x = i ∧ label y = i)
    (hcross : ∀ x ∈ P.vertices, ∀ y, GeneralVertexStep P x y →
      label x ≠ label y →
      threeColorCenter J01 J02 J12 (label x) (label y) ≤ edgeProjectiveLine x y) :
    MinkowskiDecomposable P := by
  obtain ⟨u, v, hu, hv, hvu, hnonzero⟩ :=
    three_line_compatible_differences J01 J02 J12 h01 h02 h12 hcollinear
  let q : Fin 3 → E d × ℝ := ![0, u, v]
  let p : Fin 3 → ℝ × E d := fun i => centerParameters (q i)
  have hnu := J01.neg_mem hu
  have hnv := J02.neg_mem hv
  have huv : u - v ∈ J12 := by
    simpa only [neg_sub] using J12.neg_mem hvu
  have hq (i j : Fin 3) (hij : i ≠ j) :
      q j - q i ∈ threeColorCenter J01 J02 J12 i j := by
    fin_cases i <;> fin_cases j <;> simp_all [q, threeColorCenter]
  have hp : ∃ i j : Fin 3, p i ≠ p j := by
    rcases hnonzero with hune | hvne
    · refine ⟨0, 1, ?_⟩
      intro he
      have hh := centerParameters_injective he
      exact hune (by simpa [p, q] using hh.symm)
    · refine ⟨0, 2, ?_⟩
      intro he
      have hh := centerParameters_injective he
      exact hvne (by simpa [p, q] using hh.symm)
  apply decomposable_of_compatible_homothety_centers P label p hclasses hp
  intro x hx y hxy hlabel
  apply hcross x hx y hxy hlabel
  change differenceCenterVector (centerParameters (q (label x)))
    (centerParameters (q (label y))) ∈ _
  rw [differenceCenterVector_centerParameters]
  exact hq (label x) (label y) hlabel

end Papers.Polytopes

end
end
end BundlePart9

section BundlePart10
/- Source: Papers/TwoFaceCenterWitnesses.lean -/




@[expose] public section

/-!
# Actual two-faces witness the reconstructed centers

Crossing edges supplied by the parity theorem lie in the given genuine face.
A center common to their homogeneous lines therefore lies in that face's
homogeneous span. These witnesses can be transported through a face-order
isomorphism before applying the rank-two intersection argument.
-/

noncomputable section

namespace Papers.Polytopes

open Set Papers.Coordinates
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem centers_le_twoFace_span_of_unique_crossing
    (P : ConvexPolytope d) (F : Set (E d))
    (hF : P.IsFace F) (hdim : faceDim F = 2)
    (color : P.vertices → Fin 3) (u v : P.vertices)
    (huF : u.val ∈ F) (hvF : v.val ∈ F)
    (huv : GeneralVertexStep P u.val v.val)
    (hu : color u = 0) (hv : color v = 1)
    (hunique : ∀ x y : P.vertices, x.val ∈ F → y.val ∈ F →
      GeneralVertexStep P x.val y.val → color x = 0 → color y = 1 →
      x = u ∧ y = v)
    (J02 J12 : Submodule ℝ (E d × ℝ))
    (h02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (h12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 1 → color y = 2 → J12 ≤ edgeProjectiveLine x.val y.val) :
    J02 ≤ homogeneousSpan F ∧ J12 ≤ homogeneousSpan F := by
  obtain ⟨e02,e12⟩ := twoFace_contains_other_families_of_unique_crossing
    P F hF hdim color u v huF hvF huv hu hv hunique
  constructor
  · obtain ⟨x,y,hxF,hyF,hxy,hx,hy⟩ := e02
    exact (h02 x y hxy hx hy).trans (ExposedProjectiveBridge.line_le_span hxF hyF)
  · obtain ⟨x,y,hxF,hyF,hxy,hx,hy⟩ := e12
    exact (h12 x y hxy hx hy).trans (ExposedProjectiveBridge.line_le_span hxF hyF)

theorem centers_le_twoFace_span_at_star
    (P : ConvexPolytope d) (F : Set (E d))
    (hF : P.IsFace F) (hdim : faceDim F = 2)
    (color : P.vertices → Fin 3) (u p q : P.vertices)
    (huF : u.val ∈ F) (hpF : p.val ∈ F) (hqF : q.val ∈ F)
    (hu : color u = 0) (hp : color p = 0) (hq : color q = 1)
    (hup : GeneralVertexStep P u.val p.val)
    (huq : GeneralVertexStep P u.val q.val)
    (hstar : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → x = u ∨ y = u)
    (J02 J12 : Submodule ℝ (E d × ℝ))
    (h02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (h12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 1 → color y = 2 → J12 ≤ edgeProjectiveLine x.val y.val) :
    J02 ≤ homogeneousSpan F ∧ J12 ≤ homogeneousSpan F := by
  obtain ⟨e02,e12⟩ := twoFace_star_contains_other_families
    P F hF hdim color u p q huF hpF hqF hu hp hq hup huq hstar
  constructor
  · obtain ⟨x,y,hxF,hyF,hxy,hx,hy⟩ := e02
    exact (h02 x y hxy hx hy).trans (ExposedProjectiveBridge.line_le_span hxF hyF)
  · obtain ⟨x,y,hxF,hyF,hxy,hx,hy⟩ := e12
    exact (h12 x y hxy hx hy).trans (ExposedProjectiveBridge.line_le_span hxF hyF)

end Papers.Polytopes


end
end
end BundlePart10

section BundlePart11
/- Source: Papers/ThreeColorWitnessReconstruction.lean -/






@[expose] public section

/-!
# Reconstruction from two genuine two-face witnesses

The two face planes are obtained from actual faces of the given polytope.
Their dimension and distinctness are proved from face geometry, and crossing
parity supplies the two exterior-center incidences. The remaining inputs are
the actual witnessing faces and the already reconstructed crossing-family
centers; their existence is established separately in the three-color argument.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open ExposedProjectiveBridge HomogeneousFaceSpans ThreeColorPlanes
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem threeColor_crossing_condition_of_oriented
    (P : ConvexPolytope d) (label : E d → Fin 3)
    (J01 J02 J12 : Submodule ℝ (E d × ℝ))
    (h01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 1 → J01 ≤ edgeProjectiveLine x.val y.val)
    (h02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (h12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 1 → label y.val = 2 → J12 ≤ edgeProjectiveLine x.val y.val) :
    ∀ x ∈ P.vertices, ∀ y, GeneralVertexStep P x y →
      label x ≠ label y →
      threeColorCenter J01 J02 J12 (label x) (label y) ≤ edgeProjectiveLine x y := by
  intro x hx y hxy hne
  have hy := hxy.1
  have hyx := actualStep_symm hx hxy
  have hsym : edgeProjectiveLine y x = edgeProjectiveLine x y := by
    simp only [edgeProjectiveLine,Set.pair_comm]
  have hall (i j : Fin 3) (hi : label x = i) (hj : label y = j)
      (hij : i ≠ j) :
      threeColorCenter J01 J02 J12 i j ≤ edgeProjectiveLine x y := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · simpa [threeColorCenter] using h01 ⟨x,hx⟩ ⟨y,hy⟩ hxy hi hj
    · simpa [threeColorCenter] using h02 ⟨x,hx⟩ ⟨y,hy⟩ hxy hi hj
    · simpa [threeColorCenter,hsym] using h01 ⟨y,hy⟩ ⟨x,hx⟩ hyx hj hi
    · exact (hij rfl).elim
    · simpa [threeColorCenter] using h12 ⟨x,hx⟩ ⟨y,hy⟩ hxy hi hj
    · simpa [threeColorCenter,hsym] using h02 ⟨y,hy⟩ ⟨x,hx⟩ hyx hj hi
    · simpa [threeColorCenter,hsym] using h12 ⟨y,hy⟩ ⟨x,hx⟩ hyx hj hi
    · exact (hij rfl).elim
  exact hall (label x) (label y) rfl rfl hne

theorem decomposable_of_centers_in_two_actual_twoFaces
    (P : ConvexPolytope d) (label : E d → Fin 3)
    (F G : Set (E d)) (hF : P.IsFace F) (hG : P.IsFace G)
    (hFn : F.Nonempty) (hGn : G.Nonempty)
    (hFdim : faceDim F = 2) (hGdim : faceDim G = 2) (hFG : F ≠ G)
    (J01 J02 J12 : Submodule ℝ (E d × ℝ))
    (h01 : finrank ℝ J01 = 1) (h02 : finrank ℝ J02 = 1)
    (h12 : finrank ℝ J12 = 1)
    (hcentersF : J01 ≤ homogeneousSpan F ∧
      J02 ≤ homogeneousSpan F ∧ J12 ≤ homogeneousSpan F)
    (hcentersG : J01 ≤ homogeneousSpan G ∧
      J02 ≤ homogeneousSpan G ∧ J12 ≤ homogeneousSpan G)
    (hclasses : ∀ i : Fin 3, ∃ x ∈ P.vertices, ∃ y ∈ P.vertices,
      x ≠ y ∧ label x = i ∧ label y = i)
    (hcross01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 1 → J01 ≤ edgeProjectiveLine x.val y.val)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (hcross12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 1 → label y.val = 2 → J12 ≤ edgeProjectiveLine x.val y.val) :
    MinkowskiDecomposable P := by
  apply decomposable_of_three_collinear_centers P label J01 J02 J12 h01 h02 h12
  · exact three_centers_rank_le_two (homogeneousSpan F) (homogeneousSpan G)
      J01 J02 J12 (twoFace_homogeneousSpan_rank F hFn hFdim)
      (twoFace_homogeneousSpan_rank G hGn hGdim)
      (actual_distinct_faces_have_distinct_homogeneousSpan P F G hF hG hFn hGn hFG)
      hcentersF.1 hcentersG.1 hcentersF.2.1 hcentersG.2.1
      hcentersF.2.2 hcentersG.2.2
  · exact hclasses
  · exact threeColor_crossing_condition_of_oriented P label J01 J02 J12
      hcross01 hcross02 hcross12

/-- The single crossing edge supplies the third center. Any two distinct
actual two-faces through that edge force the other two centers onto its line. -/
theorem decomposable_of_single_crossing_twoFace_witnesses
    (P : ConvexPolytope d) (label : E d → Fin 3)
    (u v : P.vertices) (hu : label u.val = 0) (hv : label v.val = 1)
    (huv : GeneralVertexStep P u.val v.val)
    (hunique : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 1 → x = u ∧ y = v)
    (F G : Set (E d)) (hF : P.IsFace F) (hG : P.IsFace G)
    (hFdim : faceDim F = 2) (hGdim : faceDim G = 2) (hFG : F ≠ G)
    (huF : u.val ∈ F) (hvF : v.val ∈ F)
    (huG : u.val ∈ G) (hvG : v.val ∈ G)
    (J02 J12 : Submodule ℝ (E d × ℝ))
    (h02 : finrank ℝ J02 = 1) (h12 : finrank ℝ J12 = 1)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (hcross12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 1 → label y.val = 2 → J12 ≤ edgeProjectiveLine x.val y.val)
    (hclasses : ∀ i : Fin 3, ∃ x ∈ P.vertices, ∃ y ∈ P.vertices,
      x ≠ y ∧ label x = i ∧ label y = i) :
    MinkowskiDecomposable P := by
  let J01 : Submodule ℝ (E d × ℝ) := Submodule.span ℝ {homogenize u.val}
  have h01 : finrank ℝ J01 = 1 := by
    apply finrank_span_singleton
    exact ExposedEdgeCenters.point_ne_zero u.val
  have hcF := centers_le_twoFace_span_of_unique_crossing P F hF hFdim
    (fun x => label x.val) u v huF hvF huv hu hv
    (fun x y _ _ hxy hx hy => hunique x y hxy hx hy) J02 J12 hcross02 hcross12
  have hcG := centers_le_twoFace_span_of_unique_crossing P G hG hGdim
    (fun x => label x.val) u v huG hvG huv hu hv
    (fun x y _ _ hxy hx hy => hunique x y hxy hx hy) J02 J12 hcross02 hcross12
  have hcross01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 1 → J01 ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    obtain ⟨hxU,hyV⟩ := hunique x y hxy hx hy
    subst x
    subst y
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact point_mem_span (Set.mem_insert u.val {v.val})
  apply decomposable_of_centers_in_two_actual_twoFaces P label F G hF hG
    ⟨u.val,huF⟩ ⟨u.val,huG⟩ hFdim hGdim hFG J01 J02 J12 h01 h02 h12
  · exact ⟨Submodule.span_le.mpr
      (by intro z hz; rcases Set.mem_singleton_iff.mp hz with rfl
          exact point_mem_span huF),hcF⟩
  · exact ⟨Submodule.span_le.mpr
      (by intro z hz; rcases Set.mem_singleton_iff.mp hz with rfl
          exact point_mem_span huG),hcG⟩
  · exact hclasses
  · exact hcross01
  · exact hcross02
  · exact hcross12

/-- In the star case, the center of the first family is the star vertex itself.
The two other centers are forced into two distinct genuine face planes. -/
theorem decomposable_of_star_twoFace_witnesses
    (P : ConvexPolytope d) (label : E d → Fin 3)
    (u p q r s : P.vertices)
    (hu : label u.val = 0) (hp : label p.val = 0) (hq : label q.val = 1)
    (hr : label r.val = 0) (hs : label s.val = 1)
    (hup : GeneralVertexStep P u.val p.val)
    (huq : GeneralVertexStep P u.val q.val)
    (hur : GeneralVertexStep P u.val r.val)
    (hus : GeneralVertexStep P u.val s.val)
    (hstar : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 1 → x = u ∨ y = u)
    (F G : Set (E d)) (hF : P.IsFace F) (hG : P.IsFace G)
    (hFdim : faceDim F = 2) (hGdim : faceDim G = 2) (hFG : F ≠ G)
    (huF : u.val ∈ F) (hpF : p.val ∈ F) (hqF : q.val ∈ F)
    (huG : u.val ∈ G) (hrG : r.val ∈ G) (hsG : s.val ∈ G)
    (J02 J12 : Submodule ℝ (E d × ℝ))
    (h02 : finrank ℝ J02 = 1) (h12 : finrank ℝ J12 = 1)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (hcross12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 1 → label y.val = 2 → J12 ≤ edgeProjectiveLine x.val y.val)
    (hclasses : ∀ i : Fin 3, ∃ x ∈ P.vertices, ∃ y ∈ P.vertices,
      x ≠ y ∧ label x = i ∧ label y = i) :
    MinkowskiDecomposable P := by
  let J01 : Submodule ℝ (E d × ℝ) := Submodule.span ℝ {homogenize u.val}
  have h01 : finrank ℝ J01 = 1 := by
    apply finrank_span_singleton
    exact ExposedEdgeCenters.point_ne_zero u.val
  have hcF := centers_le_twoFace_span_at_star P F hF hFdim
    (fun x => label x.val) u p q huF hpF hqF hu hp hq hup huq hstar
    J02 J12 hcross02 hcross12
  have hcG := centers_le_twoFace_span_at_star P G hG hGdim
    (fun x => label x.val) u r s huG hrG hsG hu hr hs hur hus hstar
    J02 J12 hcross02 hcross12
  have hcross01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 1 → J01 ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    rcases hstar x y hxy hx hy with hxu | hyu
    · subst x
      exact point_mem_span (Set.mem_insert u.val {y.val})
    · subst y
      exact point_mem_span (Set.mem_insert_of_mem x.val (Set.mem_singleton u.val))
  apply decomposable_of_centers_in_two_actual_twoFaces P label F G hF hG
    ⟨u.val,huF⟩ ⟨u.val,huG⟩ hFdim hGdim hFG J01 J02 J12 h01 h02 h12
  · exact ⟨Submodule.span_le.mpr
      (by intro z hz; rcases Set.mem_singleton_iff.mp hz with rfl
          exact point_mem_span huF),hcF⟩
  · exact ⟨Submodule.span_le.mpr
      (by intro z hz; rcases Set.mem_singleton_iff.mp hz with rfl
          exact point_mem_span huG),hcG⟩
  · exact hclasses
  · exact hcross01
  · exact hcross02
  · exact hcross12

end Papers.Polytopes


end
end
end BundlePart11

section BundlePart12
/- Source: Papers/ActualSingleEdgeReconstruction.lean -/




@[expose] public section

/-!
# Reconstruction when one crossing family is a single edge

The two required witnessing faces are constructed from the unconditional
incident-two-face count. They are not assumptions of the decomposability
theorem.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem exists_two_actual_twoFaces_through_edge
    (P : ConvexPolytope d) (hdim : 3 ≤ P.dim)
    {x y : E d} (hx : x ∈ P.vertices) (hxy : GeneralVertexStep P x y) :
    ∃ F G : Set (E d), P.IsFace F ∧ P.IsFace G ∧
      faceDim F = 2 ∧ faceDim G = 2 ∧ F ≠ G ∧
      x ∈ F ∧ y ∈ F ∧ x ∈ G ∧ y ∈ G := by
  have hc := incidentTwoFaces_card_actual P hx hxy
  obtain ⟨F,hF,G,hG,hne⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (incidentTwoFaces P x y).card)
  obtain ⟨hFdim,hxF,hyF⟩ := (Finset.mem_filter.mp hF).2
  obtain ⟨hGdim,hxG,hyG⟩ := (Finset.mem_filter.mp hG).2
  exact ⟨F.val,G.val,F.property,G.property,hFdim,hGdim,
    (fun h => hne (Subtype.ext h)),hxF,hyF,hxG,hyG⟩

theorem decomposable_of_actual_single_crossing_centers
    (P : ConvexPolytope d) (hdim : 3 ≤ P.dim) (label : E d → Fin 3)
    (u v : P.vertices) (hu : label u.val = 0) (hv : label v.val = 1)
    (huv : GeneralVertexStep P u.val v.val)
    (hunique : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 1 → x = u ∧ y = v)
    (J02 J12 : Submodule ℝ (E d × ℝ))
    (h02 : finrank ℝ J02 = 1) (h12 : finrank ℝ J12 = 1)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (hcross12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 1 → label y.val = 2 → J12 ≤ edgeProjectiveLine x.val y.val)
    (hclasses : ∀ i : Fin 3, ∃ x ∈ P.vertices, ∃ y ∈ P.vertices,
      x ≠ y ∧ label x = i ∧ label y = i) :
    MinkowskiDecomposable P := by
  obtain ⟨F,G,hF,hG,hFdim,hGdim,hFG,huF,hvF,huG,hvG⟩ :=
    exists_two_actual_twoFaces_through_edge P hdim u.property huv
  exact decomposable_of_single_crossing_twoFace_witnesses P label u v hu hv huv hunique
    F G hF hG hFdim hGdim hFG huF hvF huG hvG J02 J12 h02 h12
    hcross02 hcross12 hclasses

end Papers.Polytopes


end
end
end BundlePart12

@[expose] public section BundlePart13
/- Source: Papers/ThreeColorVertexFigureCut.lean -/




/-!
# Two crossing edges in a vertex figure

The hypotheses below are exactly the elementary consequences of two-vertex
connectivity used in the star-center case: degree at least two, connectivity,
and connectivity after deleting one vertex.
-/

namespace Papers.Polytopes.ThreeColorVertexFigure

variable {I : Type*} (G : SimpleGraph I)

theorem crossing_edge_of_reachable (A : Set I) {u v : I}
    (hu : u ∈ A) (hv : v ∉ A) (hreach : G.Reachable u v) :
    ∃ x ∈ A, ∃ y ∉ A, G.Adj x y := by
  have hwalk : ∀ {u v : I}, G.Walk u v → u ∈ A → v ∉ A →
      ∃ x ∈ A, ∃ y ∉ A, G.Adj x y := by
    intro u v p
    induction p with
    | nil =>
        intro hu hv
        exact (hv hu).elim
    | @cons u v w huv p ih =>
        intro hu hw
        by_cases hv : v ∈ A
        · exact ih hv hw
        · exact ⟨u, hu, v, hv, huv⟩
  obtain ⟨p⟩ := hreach
  exact hwalk p hu hv

/-- A nontrivial cut of a graph satisfying the vertex-figure connectivity
conditions has at least two distinct crossing edges. -/
theorem two_crossing_edges
    (hconn : G.Preconnected)
    (hdelete : ∀ x : I, (G.induce {z : I | z ≠ x}).Preconnected)
    (hdegree : ∀ x : I, ∃ y z : I, y ≠ z ∧ G.Adj x y ∧ G.Adj x z)
    (A : Set I) (hA : A.Nonempty) (hAc : Aᶜ.Nonempty) :
    ∃ x y u v : I, x ∈ A ∧ y ∉ A ∧ u ∈ A ∧ v ∉ A ∧
      G.Adj x y ∧ G.Adj u v ∧ (x ≠ u ∨ y ≠ v) := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hAc
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    crossing_edge_of_reachable G A ha hb (hconn a b)
  by_cases hsecond : ∃ u v : I, u ∈ A ∧ v ∉ A ∧ G.Adj u v ∧
      (u ≠ x ∨ v ≠ y)
  · obtain ⟨u, v, hu, hv, huv, hne⟩ := hsecond
    exact ⟨x, y, u, v, hx, hy, hu, hv, hxy, huv,
      hne.imp Ne.symm Ne.symm⟩
  have hunique {u v : I} (hu : u ∈ A) (hv : v ∉ A)
      (huv : G.Adj u v) : u = x ∧ v = y := by
    by_contra h
    have hne : u ≠ x ∨ v ≠ y := by tauto
    exact hsecond ⟨u, v, hu, hv, huv, hne⟩
  obtain ⟨z, hzneq, hxz⟩ : ∃ z : I, z ≠ y ∧ G.Adj x z := by
    obtain ⟨z, w, hzw, hxz, hxw⟩ := hdegree x
    by_cases hzy : z = y
    · exact ⟨w, by simpa [hzy] using hzw.symm, hxw⟩
    · exact ⟨z, hzy, hxz⟩
  have hzA : z ∈ A := by
    by_contra hz
    exact hzneq (hunique hx hz hxz).2
  let S : Set I := {v | v ≠ x}
  let z' : S := ⟨z, hxz.ne.symm⟩
  let y' : S := ⟨y, hxy.ne.symm⟩
  let A' : Set S := {v | v.val ∈ A}
  have hreach : (G.induce S).Reachable z' y' := hdelete x z' y'
  obtain ⟨u, hu, v, hv, huv⟩ :=
    crossing_edge_of_reachable (G.induce S) A' hzA hy hreach
  have hueq : u.val = x := (hunique hu hv huv).1
  exact (u.property hueq).elim

/-- The usual degree formulation supplies two distinct neighbors. -/
theorem two_distinct_neighbors_of_degree_ge_two [Fintype I]
    [DecidableRel G.Adj] (x : I) (hx : 2 ≤ G.degree x) :
    ∃ y z : I, y ≠ z ∧ G.Adj x y ∧ G.Adj x z := by
  classical
  have hcard : 1 < (G.neighborFinset x).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨y, hy, z, hz, hne⟩ := Finset.one_lt_card.mp hcard
  exact ⟨y, z, hne, (G.mem_neighborFinset x y).mp hy,
    (G.mem_neighborFinset x z).mp hz⟩

end Papers.Polytopes.ThreeColorVertexFigure


end BundlePart13

@[expose] public section BundlePart14
/- Source: Papers/VertexCenterCuts.lean -/



/-!
# Excluding two vertex centers

Two distinct vertex centers share a color family. After removing those two
vertices, that color is separated from the other colors, contradicting the
appropriate instance of Balinski connectivity.
-/

namespace Papers.Polytopes.VertexCenterCuts

open Papers.Polytopes.ThreeColorVertexFigure

variable {I : Type*}

theorem not_preconnected_of_crossing_cut
    (G : SimpleGraph I) (A B : Set I)
    (hcross : ∀ x y, G.Adj x y → x ∈ A → y ∉ A → x ∈ B ∨ y ∈ B)
    (hA : (A \ B).Nonempty) (hAc : (Aᶜ \ B).Nonempty) :
    ¬ (G.induce Bᶜ).Preconnected := by
  intro hconn
  obtain ⟨a,ha,hna⟩ := hA
  obtain ⟨b,hb,hnb⟩ := hAc
  let a' : ↥(Bᶜ) := ⟨a,hna⟩
  let b' : ↥(Bᶜ) := ⟨b,hnb⟩
  let A' : Set ↥(Bᶜ) := {v | v.val ∈ A}
  obtain ⟨x,hx,y,hy,hxy⟩ :=
    crossing_edge_of_reachable (G.induce Bᶜ) A' (u:=a') (v:=b')
      (show a' ∈ A' from ha) (show b' ∉ A' from hb) (hconn a' b')
  rcases hcross x.val y.val hxy hx hy with h | h
  · exact x.property h
  · exact y.property h

theorem two_stars_separate_common_color
    (G : SimpleGraph I) (color : I → Fin 3) (u v : I)
    (hzeroOne : ∀ x y, G.Adj x y → color x = 0 → color y = 1 →
      x = u ∨ y = u)
    (hzeroTwo : ∀ x y, G.Adj x y → color x = 0 → color y = 2 →
      x = v ∨ y = v)
    (a b : I) (ha : color a = 0) (hb : color b ≠ 0)
    (hau : a ≠ u) (hav : a ≠ v) (hbu : b ≠ u) (hbv : b ≠ v) :
    ¬ (G.induce ({u,v} : Set I)ᶜ).Preconnected := by
  apply not_preconnected_of_crossing_cut G {x | color x = 0} {u,v}
  · intro x y hxy hx hy
    have hzero : color y ≠ 0 := hy
    have hcolor : color y = 1 ∨ color y = 2 := by omega
    rcases hcolor with hcolor | hcolor
    · rcases hzeroOne x y hxy hx hcolor with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h])
    · rcases hzeroTwo x y hxy hx hcolor with h | h
      · exact Or.inl (by simp [h])
      · exact Or.inr (by simp [h])
  · exact ⟨a,ha,by simp [hau,hav]⟩
  · exact ⟨b,hb,by simp [hbu,hbv]⟩

end Papers.Polytopes.VertexCenterCuts


end BundlePart14

section BundlePart15
/- Source: Papers/ActualCenterClassification.lean -/





@[expose] public section

/-!
# Centers in the actual body: stars, single edges, and vertex cuts

Every assertion here concerns actual vertices and actual exposed edges.
Balinski connectivity is applied to the genuine polytope graph when two
vertex centers would separate one color from the others.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open ExposedEdgeCenters
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {C : Type*}

namespace CrossingFamily

variable {P : ConvexPolytope d} {color : P.vertices → C} {a b : C}

theorem vertex_center_is_star
    (J : Submodule ℝ (E d × ℝ))
    (hcenter : ∀ e : CrossingFamily P color a b, J ≤ e.line)
    (u : P.vertices) (huJ : homogenize u.val ∈ J) :
    ∀ e : CrossingFamily P color a b, u = e.left ∨ u = e.right := by
  intro e
  have hline : J ≤ edgeLine e.left.val e.right.val := by
    simpa only [exposed_edgeLine_eq_edgeProjectiveLine,line] using hcenter e
  have h := endpoint_of_vertex_center P.toSet e.support
    (vertex_mem_body_of_mem_vertices P e.left.property)
    (vertex_mem_body_of_mem_vertices P e.right.property)
    (vertex_mem_body_extremePoints P u.property)
    e.support_left e.support_right e.support_zero_iff_segment J hline huJ
  exact h.imp Subtype.ext Subtype.ext

theorem star_or_subsingleton_of_center_meets
    (hab : a ≠ b) (J : Submodule ℝ (E d × ℝ))
    (hcenter : ∀ e : CrossingFamily P color a b, J ≤ e.line)
    (hmeet : ∃ z ∈ P.toSet, homogenize z ∈ J) :
    (∃ u : P.vertices, homogenize u.val ∈ J ∧
      ∀ e : CrossingFamily P color a b, u = e.left ∨ u = e.right) ∨
      Subsingleton (CrossingFamily P color a b) := by
  have hline (e : CrossingFamily P color a b) :
      J ≤ edgeLine e.left.val e.right.val := by
    simpa only [exposed_edgeLine_eq_edgeProjectiveLine,line] using hcenter e
  have h := star_or_single_edge_of_center_meets P.toSet
    (fun e : CrossingFamily P color a b => e.left.val)
    (fun e : CrossingFamily P color a b => e.right.val)
    (fun e => vertex_mem_body_extremePoints P e.left.property)
    (fun e => vertex_mem_body_extremePoints P e.right.property)
    (fun e => e.isEdge.2.1)
    (fun e => (segment_isFace_of_generalVertexStep P e.left.property e.isEdge).1.isExtreme)
    support support_left support_right support_zero_iff_segment J hline hmeet
  rcases h with ⟨z,hz,hzJ,hstar⟩ | hsingle
  · have hzV : z ∈ P.vertices := by
      change z ∈ (P.vertices : Set (E d))
      rw [P.vertices_eq_extremePoints]
      exact hz
    exact Or.inl ⟨⟨z,hzV⟩,hzJ,fun e => (hstar e).imp Subtype.ext Subtype.ext⟩
  · right
    refine ⟨fun e f => ?_⟩
    rcases hsingle e f with h | h
    · exact endpointPair_injective (Prod.ext h.1 h.2)
    · exact (left_ne_right_of_different_colors hab e f h.1).elim

theorem singleton_family_of_inside_nonvertex_center
    (hab : a ≠ b) (J : Submodule ℝ (E d × ℝ))
    (hcenter : ∀ e : CrossingFamily P color a b, J ≤ e.line)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J)
    (hmeet : ∃ z ∈ P.toSet, homogenize z ∈ J)
    (e : CrossingFamily P color a b) :
    ∀ f : CrossingFamily P color a b, f = e := by
  rcases star_or_subsingleton_of_center_meets hab J hcenter hmeet with
    ⟨u,huJ,hstar⟩ | hs
  · exact (hnotvertex u.val u.property huJ).elim
  · exact fun f => hs.elim f e

theorem center_outside_of_disjoint_actual_edges
    (J : Submodule ℝ (E d × ℝ))
    (hcenter : ∀ e : CrossingFamily P color a b, J ≤ e.line)
    (e f : CrossingFamily P color a b)
    (hdisjoint : Disjoint ({e.left.val,e.right.val} : Set (E d))
      {f.left.val,f.right.val}) :
    ¬ ∃ z ∈ P.toSet, homogenize z ∈ J := by
  apply center_exterior_of_disjoint_edges P.toSet
    (fun e : CrossingFamily P color a b => e.left.val)
    (fun e : CrossingFamily P color a b => e.right.val)
    (fun e => vertex_mem_body_extremePoints P e.left.property)
    (fun e => vertex_mem_body_extremePoints P e.right.property)
    (fun e => e.isEdge.2.1)
    (fun e => (segment_isFace_of_generalVertexStep P e.left.property e.isEdge).1.isExtreme)
    support support_left support_right support_zero_iff_segment J
    (fun e => by
      simpa only [exposed_edgeLine_eq_edgeProjectiveLine,line] using hcenter e) e f hdisjoint

end CrossingFamily

theorem impossible_two_actual_star_centers
    (P : ConvexPolytope d) (hdim : 3 ≤ P.dim)
    (color : P.vertices → Fin 3) (u v a b : P.vertices)
    (h01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → x = u ∨ y = u)
    (h02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → x = v ∨ y = v)
    (ha : color a = 0) (hb : color b ≠ 0)
    (hau : a ≠ u) (hav : a ≠ v) (hbu : b ≠ u) (hbv : b ≠ v) :
    False := by
  let S : Finset (E d) := {u.val,v.val}
  have hcard : S.card < P.dim := by
    have hc : S.card ≤ 2 := by
      dsimp [S]
      exact (Finset.card_insert_le _ _).trans (by simp)
    omega
  have hconn := Papers.PolytopeBalinski.deleted_vertexGraph_connected P S hcard
  have hset : {r : P.vertices | r.val ∉ S} = ({u,v} : Set P.vertices)ᶜ := by
    ext r
    constructor
    · intro hr
      change r ∉ ({u,v} : Set P.vertices)
      intro h
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
      rcases h with rfl | rfl <;> exact hr (by simp [S])
    · intro hr h
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at h
      rcases h with hu | hv
      · apply hr
        exact Set.mem_insert_iff.mpr (Or.inl (Subtype.ext hu))
      · apply hr
        exact Set.mem_insert_iff.mpr
          (Or.inr (Set.mem_singleton_iff.mpr (Subtype.ext hv)))
  have hc : ((Papers.PolytopeBalinski.vertexGraph P).induce
      ({u,v} : Set P.vertices)ᶜ).Preconnected := by
    have hpc := hconn.preconnected
    change ((Papers.PolytopeBalinski.vertexGraph P).induce {r : P.vertices | r.val ∉ S}).Preconnected at hpc
    rw [hset] at hpc
    exact hpc
  exact VertexCenterCuts.two_stars_separate_common_color
    (Papers.PolytopeBalinski.vertexGraph P) color u v h01 h02 a b ha hb
    hau hav hbu hbv hc

end Papers.Polytopes


end
end
end BundlePart15

section BundlePart16
/- Source: Papers/SingleEdgeCentral.lean -/





@[expose] public section

/-! A sole crossing edge spans the central projective line. -/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily ExposedProjectiveBridge HomogeneousFaceSpans
open ThreeColorPlanes CrossingLineGeometry
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem single_crossing_edge_spans_central_line
    (P : ConvexPolytope d) (hdim : 3 ≤ P.dim)
    (color : P.vertices → Fin 3)
    (D J02 J12 : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (h02 : finrank ℝ J02 = 1)
    (h12 : finrank ℝ J12 = 1) (h02D : J02 ≤ D) (h12D : J12 ≤ D)
    (hne : J02 ≠ J12)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (hcross12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 1 → color y = 2 → J12 ≤ edgeProjectiveLine x.val y.val)
    (e : CrossingFamily P color 0 1)
    (hunique : ∀ f : CrossingFamily P color 0 1, f = e) :
    e.line = D := by
  obtain ⟨F,G,hF,hG,hFdim,hGdim,hFG,huF,hvF,huG,hvG⟩ :=
    exists_two_actual_twoFaces_through_edge P hdim e.left.property e.isEdge
  have hsingle : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → x = e.left ∧ y = e.right := by
    intro x y hxy hx hy
    let f : CrossingFamily P color 0 1 := ⟨(x,y),hxy,hx,hy⟩
    have h := hunique f
    exact ⟨congrArg CrossingFamily.left h,congrArg CrossingFamily.right h⟩
  have hcF := centers_le_twoFace_span_of_unique_crossing P F hF hFdim color
    e.left e.right huF hvF e.isEdge e.property.2.1 e.property.2.2
    (fun x y _ _ hxy hx hy => hsingle x y hxy hx hy) J02 J12 hcross02 hcross12
  have hcG := centers_le_twoFace_span_of_unique_crossing P G hG hGdim color
    e.left e.right huG hvG e.isEdge e.property.2.1 e.property.2.2
    (fun x y _ _ hxy hx hy => hsingle x y hxy hx hy) J02 J12 hcross02 hcross12
  have hspan := sup_eq_plane_of_distinct_points D J02 J12 hD h02 h12 h02D h12D hne
  have hDF : D ≤ homogeneousSpan F := by rw [← hspan]; exact sup_le hcF.1 hcF.2
  have hDG : D ≤ homogeneousSpan G := by rw [← hspan]; exact sup_le hcG.1 hcG.2
  have hle : D ≤ e.line :=
    center_le_common_line (homogeneousSpan F) (homogeneousSpan G) e.line D
      (twoFace_homogeneousSpan_rank F hF.2 hFdim)
      (twoFace_homogeneousSpan_rank G hG.2 hGdim)
      (actual_distinct_faces_have_distinct_homogeneousSpan P F G hF hG hF.2 hG.2 hFG)
      e.line_finrank_eq_two (line_le_span huF hvF) (line_le_span huG hvG) hDF hDG
  exact (Submodule.eq_of_le_of_finrank_le hle
    (by rw [hD,e.line_finrank_eq_two])).symm

theorem inside_nonvertex_center_gives_central_family
    (P : ConvexPolytope d) (hdim : 3 ≤ P.dim)
    (color : P.vertices → Fin 3)
    (D J01 J02 J12 : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (h02 : finrank ℝ J02 = 1)
    (h12 : finrank ℝ J12 = 1) (h02D : J02 ≤ D) (h12D : J12 ≤ D)
    (hne : J02 ≠ J12)
    (hcross01 : ∀ e : CrossingFamily P color 0 1, J01 ≤ e.line)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (hcross12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 1 → color y = 2 → J12 ≤ edgeProjectiveLine x.val y.val)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J01)
    (hmeet : ∃ z ∈ P.toSet, homogenize z ∈ J01)
    (e : CrossingFamily P color 0 1) :
    ∀ f : CrossingFamily P color 0 1, f.line ≤ D := by
  have hsingle := singleton_family_of_inside_nonvertex_center
    (by decide : (0 : Fin 3) ≠ 1) J01 hcross01 hnotvertex hmeet e
  have heq := single_crossing_edge_spans_central_line P hdim color D J02 J12
    hD h02 h12 h02D h12D hne hcross02 hcross12 e hsingle
  intro f
  rw [hsingle f,heq]

end Papers.Polytopes


end
end
end BundlePart16

section BundlePart17
/- Source: Papers/CofacialFamilyCenters.lean -/




@[expose] public section

/-!
# The cofacial degree of one actual crossing family

A two-face whose plane omits the central projective line cannot contain
crossings with two distinct centers. Actual cut parity then supplies a
different edge of the chosen family. This establishes the geometric input
to the cofacial degree count.
-/

noncomputable section
namespace Papers.Polytopes.CrossingFamily

open Set Module Papers.Coordinates
open Papers.Polytopes.ExposedProjectiveBridge
open Papers.Polytopes.CrossingLineGeometry
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem second_zero_one_edge_of_omitted_central_line
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (e : CrossingFamily P color 0 1)
    (D J01 J02 : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (h01 : finrank ℝ J01 = 1)
    (h02 : finrank ℝ J02 = 1) (hJ01 : J01 ≤ D) (hJ02 : J02 ≤ D)
    (hne : J01 ≠ J02)
    (hcross01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → J01 ≤ edgeProjectiveLine x.val y.val)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (F : Set (E d)) (hF : P.IsFace F) (hdim : faceDim F = 2)
    (heF : liesIn F e) (hproper : ¬ D ≤ homogeneousSpan F) :
    ∃ f : CrossingFamily P color 0 1, e ≠ f ∧ liesIn F f := by
  have h01F : J01 ≤ homogeneousSpan F :=
    (hcross01 e.left e.right e.isEdge e.property.2.1 e.property.2.2).trans
      (line_le_span heF.1 heF.2)
  apply second_edge_in_twoFace (by decide : (0 : Fin 3) ≠ 1) e F hF hdim heF
  intro x y hxF hyF hxy hx hy
  have hcases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
    fin_cases c <;> simp
  rcases hcases (color y) with h0 | h1 | h2
  · exact (hy h0).elim
  · exact h1
  · exfalso
    have h02F : J02 ≤ homogeneousSpan F :=
      (hcross02 x y hxy hx h2).trans (line_le_span hxF hyF)
    apply hproper
    rw [← sup_eq_plane_of_distinct_points D J01 J02 hD h01 h02 hJ01 hJ02 hne]
    exact sup_le h01F h02F

theorem zero_one_cofacial_degree_from_incident_faces
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (e : CrossingFamily P color 0 1)
    (D J01 J02 : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (h01 : finrank ℝ J01 = 1)
    (h02 : finrank ℝ J02 = 1) (hJ01 : J01 ≤ D) (hJ02 : J02 ≤ D)
    (hne : J01 ≠ J02)
    (hcross01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → J01 ≤ edgeProjectiveLine x.val y.val)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (hoff : ¬ e.line ≤ D)
    (hpair : ∀ f : CrossingFamily P color 0 1, e ≠ f →
      3 ≤ finrank ℝ (e.line ⊔ f.line : Submodule ℝ (E d × ℝ))) :
    (incidentTwoFaces P e.left.val e.right.val).card ≤
      (cofacialGraph (P := P) (color := color) (a := 0) (b := 1)).degree e + 1 := by
  apply cofacial_degree_from_actual_twoFaces e D hD hoff hpair
  intro F hF hdim heF hproper
  exact second_zero_one_edge_of_omitted_central_line P color e D J01 J02
    hD h01 h02 hJ01 hJ02 hne hcross01 hcross02 F hF hdim heF hproper

theorem zero_one_cofacial_degree_lower_bound
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (e : CrossingFamily P color 0 1)
    (D J01 J02 : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (h01 : finrank ℝ J01 = 1)
    (h02 : finrank ℝ J02 = 1) (hJ01 : J01 ≤ D) (hJ02 : J02 ≤ D)
    (hne : J01 ≠ J02)
    (hcross01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → J01 ≤ edgeProjectiveLine x.val y.val)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (hoff : ¬ e.line ≤ D)
    (hpair : ∀ f : CrossingFamily P color 0 1, e ≠ f →
      3 ≤ finrank ℝ (e.line ⊔ f.line : Submodule ℝ (E d × ℝ)))
    (hfaces : d - 1 ≤ (incidentTwoFaces P e.left.val e.right.val).card) :
    d - 2 ≤ (cofacialGraph (P := P) (color := color) (a := 0) (b := 1)).degree e := by
  have h := zero_one_cofacial_degree_from_incident_faces P color e D J01 J02
    hD h01 h02 hJ01 hJ02 hne hcross01 hcross02 hoff hpair
  omega

end Papers.Polytopes.CrossingFamily


end
end
end BundlePart17

section BundlePart18
/- Source: Papers/OffCentralCofacialDegree.lean -/





@[expose] public section

/-!
# Cofacial degree restricted to off-central edges

The forest count uses only noncentral crossing edges. A good two-face cannot
supply a central partner edge, since such an edge would span the whole
central projective line. This proves the required degree bound in the
induced graph on off-central crossing edges.
-/

noncomputable section
namespace Papers.Polytopes.CrossingFamily

open Set Module Papers.Coordinates
open Papers.Polytopes.ExposedProjectiveBridge
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

abbrev OffCentralFamily (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (a b : Fin 3) (D : Submodule ℝ (E d × ℝ)) :=
  {e : CrossingFamily P color a b // ¬ e.line ≤ D}

noncomputable def offCentralCofacialGraph
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (a b : Fin 3) (D : Submodule ℝ (E d × ℝ)) :
    SimpleGraph (OffCentralFamily P color a b D) :=
  (cofacialGraph (P := P) (color := color) (a := a) (b := b)).induce
    {e : CrossingFamily P color a b | ¬ e.line ≤ D}

theorem zero_one_offCentral_degree_lower_bound
    (P : ConvexPolytope d) (hP : P.IsFullDim) (color : P.vertices → Fin 3)
    (D J01 J02 : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (h01 : finrank ℝ J01 = 1)
    (h02 : finrank ℝ J02 = 1) (hJ01 : J01 ≤ D) (hJ02 : J02 ≤ D)
    (hne : J01 ≠ J02)
    (hcross01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → J01 ≤ edgeProjectiveLine x.val y.val)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (e : OffCentralFamily P color 0 1 D) :
    d - 2 ≤ (offCentralCofacialGraph P color 0 1 D).degree e := by
  let G := offCentralCofacialGraph P color 0 1 D
  let faces := incidentTwoFaces P e.val.left.val e.val.right.val
  let bad (F : ActualFaceType P) := D ≤ homogeneousSpan F.val
  let partner (F : ActualFaceType P) (f : OffCentralFamily P color 0 1 D) :=
    e ≠ f ∧ liesIn F.val f.val
  have hmem (F : ActualFaceType P) (hF : F ∈ faces) :
      faceDim F.val = 2 ∧ liesIn F.val e.val := by
    exact (Finset.mem_filter.mp hF).2
  apply CofacialCounting.cofacial_degree_lower_bound G d e faces bad partner
  · exact incidentTwoFaces_card_actual_fullDim P hP e.val.left.property e.val.isEdge
  · intro F hF H hH hbadF hbadH
    apply Subtype.ext
    exact actual_twoFaces_eq_of_central_line_and_offline_edge P F.val H.val
      F.property H.property (hmem F hF).1 (hmem H hH).1
      e.val.left.val e.val.right.val (hmem F hF).2.1 (hmem F hF).2.2
      (hmem H hH).2.1 (hmem H hH).2.2 D hD e.property hbadF hbadH
  · intro F hF hgood
    obtain ⟨f,hef,hfF⟩ := second_zero_one_edge_of_omitted_central_line
      P color e.val D J01 J02 hD h01 h02 hJ01 hJ02 hne hcross01 hcross02
      F.val F.property (hmem F hF).1 (hmem F hF).2 hgood
    have hoff : ¬ f.line ≤ D := by
      intro hfD
      have heq : f.line = D :=
        Submodule.eq_of_le_of_finrank_le hfD
          (by rw [hD,f.line_finrank_eq_two])
      apply hgood
      change D ≤ homogeneousSpan F.val
      rw [← heq]
      exact line_le_span hfF.1 hfF.2
    let f' : OffCentralFamily P color 0 1 D := ⟨f,hoff⟩
    have hef' : e ≠ f' := fun h => hef (congrArg Subtype.val h)
    refine ⟨f',?_,hef',hfF⟩
    change (cofacialGraph (P := P) (color := color) (a := 0) (b := 1)).Adj e.val f
    exact ⟨hef,F.val,F.property,(hmem F hF).1,(hmem F hF).2,hfF⟩
  · intro F hF H hH f hfF hfH
    have hef : e.val ≠ f.val := fun h => hfF.1 (Subtype.ext h)
    apply Subtype.ext
    exact actual_twoFaces_eq_of_two_lines P F.val H.val F.property H.property
      ⟨e.val.left.val,(hmem F hF).2.1⟩ ⟨e.val.left.val,(hmem H hH).2.1⟩
      (hmem F hF).1 (hmem H hH).1 e.val.line f.val.line
      (pair_line_rank_ge_three (by decide : (0 : Fin 3) ≠ 1) e.val f.val hef)
      (line_le_span (hmem F hF).2.1 (hmem F hF).2.2)
      (line_le_span (hmem H hH).2.1 (hmem H hH).2.2)
      (line_le_span hfF.2.1 hfF.2.2) (line_le_span hfH.2.1 hfH.2.2)

theorem zero_one_offCentral_family_card_lower_bound
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 2 ≤ d)
    (color : P.vertices → Fin 3)
    (D J01 J02 : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (h01 : finrank ℝ J01 = 1)
    (h02 : finrank ℝ J02 = 1) (hJ01 : J01 ≤ D) (hJ02 : J02 ≤ D)
    (hne : J01 ≠ J02)
    (hcross01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → J01 ≤ edgeProjectiveLine x.val y.val)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (e : OffCentralFamily P color 0 1 D) :
    d - 1 ≤ Fintype.card (OffCentralFamily P color 0 1 D) := by
  apply CofacialCounting.family_size_lower_bound (offCentralCofacialGraph P color 0 1 D)
    d hd e
  exact zero_one_offCentral_degree_lower_bound P hP color D J01 J02 hD h01 h02
    hJ01 hJ02 hne hcross01 hcross02 e

theorem zero_one_actual_cofacial_degree_lower_bound
    (P : ConvexPolytope d) (hP : P.IsFullDim) (color : P.vertices → Fin 3)
    (D J01 J02 : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (h01 : finrank ℝ J01 = 1)
    (h02 : finrank ℝ J02 = 1) (hJ01 : J01 ≤ D) (hJ02 : J02 ≤ D)
    (hne : J01 ≠ J02)
    (hcross01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → J01 ≤ edgeProjectiveLine x.val y.val)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (e : CrossingFamily P color 0 1) (hoff : ¬ e.line ≤ D) :
    d - 2 ≤ (cofacialGraph (P := P) (color := color) (a := 0) (b := 1)).degree e := by
  apply zero_one_cofacial_degree_lower_bound P color e D J01 J02 hD h01 h02
    hJ01 hJ02 hne hcross01 hcross02 hoff
  · intro f hef
    exact pair_line_rank_ge_three (by decide : (0 : Fin 3) ≠ 1) e f hef
  · exact incidentTwoFaces_card_actual_fullDim P hP e.left.property e.isEdge

end Papers.Polytopes.CrossingFamily


end
end
end BundlePart18

section BundlePart19
/- Source: Papers/GeneralCrossingDegree.lean -/



@[expose] public section

/-! Cofacial bounds with an arbitrary naming of the three colors. -/

noncomputable section
namespace Papers.Polytopes.CrossingFamily

open Set Module Papers.Coordinates
open ExposedProjectiveBridge CrossingLineGeometry
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem three_colors_cover (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (i : Fin 3) :
    i = a ∨ i = b ∨ i = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases i <;> simp_all

theorem second_edge_of_omitted_central_line
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (e : CrossingFamily P color a b)
    (D Jab Jac : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (habdim : finrank ℝ Jab = 1)
    (hacdim : finrank ℝ Jac = 1) (hJab : Jab ≤ D) (hJac : Jac ≤ D)
    (hne : Jab ≠ Jac)
    (hcrossab : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = a → color y = b → Jab ≤ edgeProjectiveLine x.val y.val)
    (hcrossac : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = a → color y = c → Jac ≤ edgeProjectiveLine x.val y.val)
    (F : Set (E d)) (hF : P.IsFace F) (hdim : faceDim F = 2)
    (heF : liesIn F e) (hproper : ¬ D ≤ homogeneousSpan F) :
    ∃ f : CrossingFamily P color a b, e ≠ f ∧ liesIn F f := by
  have habF : Jab ≤ homogeneousSpan F :=
    (hcrossab e.left e.right e.isEdge e.property.2.1 e.property.2.2).trans
      (line_le_span heF.1 heF.2)
  apply second_edge_in_twoFace hab e F hF hdim heF
  intro x y hxF hyF hxy hx hy
  rcases three_colors_cover a b c hab hac hbc (color y) with ha | hb | hc
  · exact (hy ha).elim
  · exact hb
  · exfalso
    have hacF : Jac ≤ homogeneousSpan F :=
      (hcrossac x y hxy hx hc).trans (line_le_span hxF hyF)
    apply hproper
    rw [← sup_eq_plane_of_distinct_points D Jab Jac hD habdim hacdim hJab hJac hne]
    exact sup_le habF hacF

theorem offCentral_degree_lower_bound
    (P : ConvexPolytope d) (hP : P.IsFullDim) (color : P.vertices → Fin 3)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (D Jab Jac : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (habdim : finrank ℝ Jab = 1)
    (hacdim : finrank ℝ Jac = 1) (hJab : Jab ≤ D) (hJac : Jac ≤ D)
    (hne : Jab ≠ Jac)
    (hcrossab : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = a → color y = b → Jab ≤ edgeProjectiveLine x.val y.val)
    (hcrossac : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = a → color y = c → Jac ≤ edgeProjectiveLine x.val y.val)
    (e : OffCentralFamily P color a b D) :
    d - 2 ≤ (offCentralCofacialGraph P color a b D).degree e := by
  let G := offCentralCofacialGraph P color a b D
  let faces := incidentTwoFaces P e.val.left.val e.val.right.val
  let bad (F : ActualFaceType P) := D ≤ homogeneousSpan F.val
  let partner (F : ActualFaceType P) (f : OffCentralFamily P color a b D) :=
    e ≠ f ∧ liesIn F.val f.val
  have hmem (F : ActualFaceType P) (hF : F ∈ faces) :
      faceDim F.val = 2 ∧ liesIn F.val e.val := (Finset.mem_filter.mp hF).2
  apply CofacialCounting.cofacial_degree_lower_bound G d e faces bad partner
  · exact incidentTwoFaces_card_actual_fullDim P hP e.val.left.property e.val.isEdge
  · intro F hF H hH hbadF hbadH
    apply Subtype.ext
    exact actual_twoFaces_eq_of_central_line_and_offline_edge P F.val H.val
      F.property H.property (hmem F hF).1 (hmem H hH).1
      e.val.left.val e.val.right.val (hmem F hF).2.1 (hmem F hF).2.2
      (hmem H hH).2.1 (hmem H hH).2.2 D hD e.property hbadF hbadH
  · intro F hF hgood
    obtain ⟨f,hef,hfF⟩ := second_edge_of_omitted_central_line
      P color a b c hab hac hbc e.val D Jab Jac hD habdim hacdim hJab hJac hne
      hcrossab hcrossac F.val F.property (hmem F hF).1 (hmem F hF).2 hgood
    have hoff : ¬ f.line ≤ D := by
      intro hfD
      have heq : f.line = D :=
        Submodule.eq_of_le_of_finrank_le hfD
          (by rw [hD,f.line_finrank_eq_two])
      apply hgood
      change D ≤ homogeneousSpan F.val
      rw [← heq]
      exact line_le_span hfF.1 hfF.2
    let f' : OffCentralFamily P color a b D := ⟨f,hoff⟩
    have hef' : e ≠ f' := fun h => hef (congrArg Subtype.val h)
    refine ⟨f',?_,hef',hfF⟩
    change (cofacialGraph (P := P) (color := color) (a := a) (b := b)).Adj e.val f
    exact ⟨hef,F.val,F.property,(hmem F hF).1,(hmem F hF).2,hfF⟩
  · intro F hF H hH f hfF hfH
    have hef : e.val ≠ f.val := fun h => hfF.1 (Subtype.ext h)
    apply Subtype.ext
    exact actual_twoFaces_eq_of_two_lines P F.val H.val F.property H.property
      ⟨e.val.left.val,(hmem F hF).2.1⟩ ⟨e.val.left.val,(hmem H hH).2.1⟩
      (hmem F hF).1 (hmem H hH).1 e.val.line f.val.line
      (pair_line_rank_ge_three hab e.val f.val hef)
      (line_le_span (hmem F hF).2.1 (hmem F hF).2.2)
      (line_le_span (hmem H hH).2.1 (hmem H hH).2.2)
      (line_le_span hfF.2.1 hfF.2.2) (line_le_span hfH.2.1 hfH.2.2)

theorem offCentral_family_card_lower_bound
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 2 ≤ d)
    (color : P.vertices → Fin 3)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (D Jab Jac : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (habdim : finrank ℝ Jab = 1)
    (hacdim : finrank ℝ Jac = 1) (hJab : Jab ≤ D) (hJac : Jac ≤ D)
    (hne : Jab ≠ Jac)
    (hcrossab : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = a → color y = b → Jab ≤ edgeProjectiveLine x.val y.val)
    (hcrossac : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = a → color y = c → Jac ≤ edgeProjectiveLine x.val y.val)
    (e : OffCentralFamily P color a b D) :
    d - 1 ≤ Fintype.card (OffCentralFamily P color a b D) := by
  apply CofacialCounting.family_size_lower_bound (offCentralCofacialGraph P color a b D)
    d hd e
  exact offCentral_degree_lower_bound P hP color a b c hab hac hbc
    D Jab Jac hD habdim hacdim hJab hJac hne hcrossab hcrossac e


theorem actual_cofacial_degree_lower_bound
    (P : ConvexPolytope d) (hP : P.IsFullDim) (color : P.vertices → Fin 3)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (D Jab Jac : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (habdim : finrank ℝ Jab = 1)
    (hacdim : finrank ℝ Jac = 1) (hJab : Jab ≤ D) (hJac : Jac ≤ D)
    (hne : Jab ≠ Jac)
    (hcrossab : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = a → color y = b → Jab ≤ edgeProjectiveLine x.val y.val)
    (hcrossac : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = a → color y = c → Jac ≤ edgeProjectiveLine x.val y.val)
    (e : CrossingFamily P color a b) (hoff : ¬ e.line ≤ D) :
    d - 2 ≤ (cofacialGraph (P := P) (color := color) (a := a) (b := b)).degree e := by
  have hcount := cofacial_degree_from_actual_twoFaces e D hD hoff
    (fun f hef => pair_line_rank_ge_three hab e f hef)
    (fun F hF hdim heF hproper =>
      second_edge_of_omitted_central_line P color a b c hab hac hbc e D Jab Jac
        hD habdim hacdim hJab hJac hne hcrossab hcrossac F hF hdim heF hproper)
  have hlow := incidentTwoFaces_card_actual_fullDim P hP e.left.property e.isEdge
  omega

end Papers.Polytopes.CrossingFamily


end
end
end BundlePart19

@[expose] public section BundlePart20
/- Source: Papers/CentralEdgeDichotomy.lean -/




/-!
# Off-central edges and the unique central edge

A nonvertex center gives a dichotomy: a crossing edge lies wholly in the
central line, or both endpoints are noncentral. Actual exposed edges lying
in one projective line coincide, up to their endpoint orientation.
-/

namespace Papers.Polytopes.CentralEdgeDichotomy

open Papers.Polytopes.ExposedEdgeCenters
open Papers.Polytopes.ExposedLineRanks
open Papers.Polytopes.CrossingLineGeometry

variable {V I : Type*} [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V]

theorem edge_central_or_both_endpoints_noncentral
    (D J : Submodule ℝ (V × ℝ)) {x y : V} (hxy : x ≠ y)
    (hJ : Module.finrank ℝ J = 1) (hJD : J ≤ D)
    (hJL : J ≤ edgeLine x y)
    (hxJ : point x ∉ J) (hyJ : point y ∉ J) :
    edgeLine x y ≤ D ∨ (point x ∉ D ∧ point y ∉ D) := by
  by_cases hLD : edgeLine x y ≤ D
  · exact Or.inl hLD
  have heq := central_intersection_eq_center D (edgeLine x y) J
    (edgeLine_finrank_eq_two hxy) hJ hJD hJL hLD
  refine Or.inr ⟨?_,?_⟩
  · intro hxD
    apply hxJ
    rw [← heq]
    exact ⟨hxD,Submodule.subset_span (by simp)⟩
  · intro hyD
    apply hyJ
    rw [← heq]
    exact ⟨hyD,Submodule.subset_span (by simp)⟩

theorem central_of_no_noncentral_crossing
    (D J : Submodule ℝ (V × ℝ)) {x y : V} (hxy : x ≠ y)
    (hJ : Module.finrank ℝ J = 1) (hJD : J ≤ D)
    (hJL : J ≤ edgeLine x y)
    (hxJ : point x ∉ J) (hyJ : point y ∉ J)
    (hnot : ¬ (point x ∉ D ∧ point y ∉ D)) :
    edgeLine x y ≤ D :=
  (edge_central_or_both_endpoints_noncentral D J hxy hJ hJD hJL hxJ hyJ).resolve_right hnot

/-- Canonically oriented actual exposed edges lying in one projective line
form a subsingleton family. -/
theorem central_exposed_family_subsingleton
    (C : Set V) (D : Submodule ℝ (V × ℝ)) (hD : Module.finrank ℝ D = 2)
    (left right : I → V)
    (hl : ∀ i, left i ∈ C.extremePoints ℝ)
    (hr : ∀ i, right i ∈ C.extremePoints ℝ)
    (hne : ∀ i, left i ≠ right i)
    (support : I → V →ᵃ[ℝ] ℝ)
    (hsleft : ∀ i, support i (left i) = 0)
    (hsright : ∀ i, support i (right i) = 0)
    (hszero : ∀ i z, z ∈ C →
      (support i z = 0 ↔ z ∈ segment ℝ (left i) (right i)))
    (hline : ∀ i, edgeLine (left i) (right i) ≤ D)
    (hcross : ∀ i j, left i ≠ right j)
    (hinj : Function.Injective fun i => (left i,right i)) :
    Subsingleton I := by
  refine ⟨fun i j => hinj ?_⟩
  have hdim := edgeLine_finrank_eq_two (hne j)
  have hDj : D = edgeLine (left j) (right j) :=
    (Submodule.eq_of_le_of_finrank_le (hline j) (by omega)).symm
  have hpoint (z : V) (hz : point z ∈ edgeLine (left i) (right i)) :
      point z ∈ edgeLine (left j) (right j) := by
    rw [← hDj]
    exact hline i hz
  have hleftzero : support j (left i) = 0 :=
    affine_eq_zero_on_edgeLine (support j) (hsleft j) (hsright j)
      (hpoint (left i) (Submodule.subset_span (by simp)))
  have hrightzero : support j (right i) = 0 :=
    affine_eq_zero_on_edgeLine (support j) (hsleft j) (hsright j)
      (hpoint (right i) (Submodule.subset_span (by simp)))
  have hleft : left i = left j := by
    rcases (support_zero_iff_endpoint C (support j) (hl j).1 (hr j).1
      (hsleft j) (hsright j) (hszero j) (hl i)).mp hleftzero with h | h
    · exact h
    · exact (hcross i j h).elim
  have hright : right i = right j := by
    rcases (support_zero_iff_endpoint C (support j) (hl j).1 (hr j).1
      (hsleft j) (hsright j) (hszero j) (hr i)).mp hrightzero with h | h
    · exact (hcross j i h.symm).elim
    · exact h
  exact Prod.ext hleft hright

end Papers.Polytopes.CentralEdgeDichotomy


end BundlePart20

section BundlePart21
/- Source: Papers/ActualFamilyCounting.lean -/






@[expose] public section

/-!
# Counting a matching family against a central vertex and the third color

The two endpoint injections, a noncentral third-color class, and one actual
central vertex have disjoint images in the actual vertex set. This is the
geometric content of 2m+r+1 ≤ f₀(P) used by dense concurrence.
-/

noncomputable section
namespace Papers.Polytopes.ActualFamilyCounting

open Set Module Papers.Coordinates
open ExposedEdgeCenters
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

theorem sumElim_injective {A B C : Type*} (f : A → C) (g : B → C)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hdisjoint : ∀ a b, f a ≠ g b) :
    Function.Injective (Sum.elim f g) := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b => exact congrArg Sum.inl (hf h)
    | inr b => exact (hdisjoint a b h).elim
  | inr a =>
    cases y with
    | inl b => exact (hdisjoint b a h.symm).elim
    | inr b => exact congrArg Sum.inr (hg h)

variable {d : ℕ}

abbrev NoncentralColor (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (D : Submodule ℝ (E d × ℝ)) (i : Fin 3) :=
  {v : P.vertices // color v = i ∧ homogenize v.val ∉ D}

theorem matching_family_third_color_count
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (D J01 : Submodule ℝ (E d × ℝ)) (h01 : finrank ℝ J01 = 1) (hJD : J01 ≤ D)
    (hcenter : ∀ e : CrossingFamily P color 0 1, J01 ≤ e.line)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J01)
    (hoff : ∀ e : CrossingFamily P color 0 1, ¬ e.line ≤ D)
    (w : P.vertices) (hwD : homogenize w.val ∈ D) :
    2 * Fintype.card (CrossingFamily P color 0 1) +
      Fintype.card (NoncentralColor P color D 2) + 1 ≤ P.vertices.card := by
  let I := CrossingFamily P color 0 1
  let T := NoncentralColor P color D 2
  obtain ⟨hinjl,hinjr⟩ :=
    CrossingFamily.endpoint_injections_of_nonvertex_center J01 h01 hcenter hnotvertex
  have hnoncentral (e : I) :
      homogenize e.left.val ∉ D ∧ homogenize e.right.val ∉ D := by
    have hline : J01 ≤ edgeLine e.left.val e.right.val := by
      simpa only [exposed_edgeLine_eq_edgeProjectiveLine,CrossingFamily.line] using hcenter e
    have hdich := CentralEdgeDichotomy.edge_central_or_both_endpoints_noncentral
      D J01 e.isEdge.2.1 h01 hJD hline
      (hnotvertex e.left.val e.left.property) (hnotvertex e.right.val e.right.property)
    apply hdich.resolve_left
    intro h
    apply hoff e
    simpa only [exposed_edgeLine_eq_edgeProjectiveLine,CrossingFamily.line] using h
  let left : I → P.vertices := fun e => e.left
  let right : I → P.vertices := fun e => e.right
  have hl : Function.Injective left := fun _ _ h => hinjl (congrArg Subtype.val h)
  have hr : Function.Injective right := fun _ _ h => hinjr (congrArg Subtype.val h)
  have hlr : ∀ e f, left e ≠ right f := by
    intro e f h
    exact CrossingFamily.left_ne_right_of_different_colors
      (by decide : (0 : Fin 3) ≠ 1) e f (congrArg Subtype.val h)
  let ends : I ⊕ I → P.vertices := Sum.elim left right
  have hends : Function.Injective ends := sumElim_injective left right hl hr hlr
  let third : T → P.vertices := fun v => v.val
  let central : Unit → P.vertices := fun _ => w
  have hthird : Function.Injective third := Subtype.val_injective
  have hcentral : Function.Injective central := fun _ _ _ => Subsingleton.elim _ _
  have htc : ∀ v t, third v ≠ central t := by
    intro v t h
    apply v.property.2
    rw [show v.val = w from h]
    exact hwD
  let rest : T ⊕ Unit → P.vertices := Sum.elim third central
  have hrest : Function.Injective rest :=
    sumElim_injective third central hthird hcentral htc
  have hdisjoint : ∀ a b, ends a ≠ rest b := by
    intro a b h
    cases a with
    | inl e =>
      cases b with
      | inl v =>
        have hc := congrArg color h
        change color e.left = color v.val at hc
        have he : color e.left = 0 := e.property.2.1
        have hv : color v.val = 2 := v.property.1
        rw [he,hv] at hc
        exact (by decide : (0 : Fin 3) ≠ 2) hc
      | inr t =>
        apply (hnoncentral e).1
        rw [show e.left = w from h]
        exact hwD
    | inr e =>
      cases b with
      | inl v =>
        have hc := congrArg color h
        change color e.right = color v.val at hc
        have he : color e.right = 1 := e.property.2.2
        have hv : color v.val = 2 := v.property.1
        rw [he,hv] at hc
        exact (by decide : (1 : Fin 3) ≠ 2) hc
      | inr t =>
        apply (hnoncentral e).2
        rw [show e.right = w from h]
        exact hwD
  have hcard := Fintype.card_le_of_injective (Sum.elim ends rest)
    (sumElim_injective ends rest hends hrest hdisjoint)
  simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_coe] at hcard
  change Fintype.card (CrossingFamily P color 0 1) + Fintype.card (CrossingFamily P color 0 1) + (Fintype.card (NoncentralColor P color D 2) + 1) ≤ P.vertices.card at hcard
  omega

theorem exterior_family_dense_count
    (P : ConvexPolytope d) (hd : 4 ≤ d) (color : P.vertices → Fin 3)
    (D J01 : Submodule ℝ (E d × ℝ)) (h01 : finrank ℝ J01 = 1) (hJD : J01 ≤ D)
    (hcenter : ∀ e : CrossingFamily P color 0 1, J01 ≤ e.line)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J01)
    (hoff : ∀ e : CrossingFamily P color 0 1, ¬ e.line ≤ D)
    (w : P.vertices) (hwD : homogenize w.val ∈ D)
    (hthird : d - 1 ≤ Fintype.card (NoncentralColor P color D 2))
    (hN : P.vertices.card ≤ 4 * d - 5) :
    Fintype.card (CrossingFamily P color 0 1) < 2 * (d - 2) := by
  have h := matching_family_third_color_count P color D J01 h01 hJD hcenter
    hnotvertex hoff w hwD
  omega

theorem exterior_family_three_dimensional_count
    (P : ConvexPolytope 3) (color : P.vertices → Fin 3)
    (D J01 : Submodule ℝ (E 3 × ℝ)) (h01 : finrank ℝ J01 = 1) (hJD : J01 ≤ D)
    (hcenter : ∀ e : CrossingFamily P color 0 1, J01 ≤ e.line)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J01)
    (hoff : ∀ e : CrossingFamily P color 0 1, ¬ e.line ≤ D)
    (w : P.vertices) (hwD : homogenize w.val ∈ D)
    (hthird : 2 ≤ Fintype.card (NoncentralColor P color D 2))
    (hN : P.vertices.card ≤ 7) :
    Fintype.card (CrossingFamily P color 0 1) ≤ 2 := by
  have h := matching_family_third_color_count P color D J01 h01 hJD hcenter
    hnotvertex hoff w hwD
  omega

end Papers.Polytopes.ActualFamilyCounting


end
end
end BundlePart21

section BundlePart22
/- Source: Papers/GeneralFamilyCounting.lean -/



@[expose] public section

/-! The actual matching cardinal bound for any naming of the three colors. -/

noncomputable section
namespace Papers.Polytopes.ActualFamilyCounting
open Set Module Papers.Coordinates ExposedEdgeCenters
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ}

theorem matching_family_third_color_count_at
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (D J01 : Submodule ℝ (E d × ℝ)) (h01 : finrank ℝ J01 = 1) (hJD : J01 ≤ D)
    (hcenter : ∀ e : CrossingFamily P color a b, J01 ≤ e.line)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J01)
    (hoff : ∀ e : CrossingFamily P color a b, ¬ e.line ≤ D)
    (w : P.vertices) (hwD : homogenize w.val ∈ D) :
    2 * Fintype.card (CrossingFamily P color a b) +
      Fintype.card (NoncentralColor P color D c) + 1 ≤ P.vertices.card := by
  let I := CrossingFamily P color a b
  let T := NoncentralColor P color D c
  obtain ⟨hinjl,hinjr⟩ :=
    CrossingFamily.endpoint_injections_of_nonvertex_center J01 h01 hcenter hnotvertex
  have hnoncentral (e : I) :
      homogenize e.left.val ∉ D ∧ homogenize e.right.val ∉ D := by
    have hline : J01 ≤ edgeLine e.left.val e.right.val := by
      simpa only [exposed_edgeLine_eq_edgeProjectiveLine,CrossingFamily.line] using hcenter e
    have hdich := CentralEdgeDichotomy.edge_central_or_both_endpoints_noncentral
      D J01 e.isEdge.2.1 h01 hJD hline
      (hnotvertex e.left.val e.left.property) (hnotvertex e.right.val e.right.property)
    apply hdich.resolve_left
    intro h
    apply hoff e
    simpa only [exposed_edgeLine_eq_edgeProjectiveLine,CrossingFamily.line] using h
  let left : I → P.vertices := fun e => e.left
  let right : I → P.vertices := fun e => e.right
  have hl : Function.Injective left := fun _ _ h => hinjl (congrArg Subtype.val h)
  have hr : Function.Injective right := fun _ _ h => hinjr (congrArg Subtype.val h)
  have hlr : ∀ e f, left e ≠ right f := by
    intro e f h
    exact CrossingFamily.left_ne_right_of_different_colors
      hab e f (congrArg Subtype.val h)
  let ends : I ⊕ I → P.vertices := Sum.elim left right
  have hends : Function.Injective ends := sumElim_injective left right hl hr hlr
  let third : T → P.vertices := fun v => v.val
  let central : Unit → P.vertices := fun _ => w
  have hthird : Function.Injective third := Subtype.val_injective
  have hcentral : Function.Injective central := fun _ _ _ => Subsingleton.elim _ _
  have htc : ∀ v t, third v ≠ central t := by
    intro v t h
    apply v.property.2
    rw [show v.val = w from h]
    exact hwD
  let rest : T ⊕ Unit → P.vertices := Sum.elim third central
  have hrest : Function.Injective rest :=
    sumElim_injective third central hthird hcentral htc
  have hdisjoint : ∀ a b, ends a ≠ rest b := by
    intro a b h
    cases a with
    | inl e =>
      cases b with
      | inl v =>
        have hc := congrArg color h
        change color e.left = color v.val at hc
        have he : color e.left = a := e.property.2.1
        have hv : color v.val = c := v.property.1
        rw [he,hv] at hc
        exact hac hc
      | inr t =>
        apply (hnoncentral e).1
        rw [show e.left = w from h]
        exact hwD
    | inr e =>
      cases b with
      | inl v =>
        have hc := congrArg color h
        change color e.right = color v.val at hc
        have he : color e.right = b := e.property.2.2
        have hv : color v.val = c := v.property.1
        rw [he,hv] at hc
        exact hbc hc
      | inr t =>
        apply (hnoncentral e).2
        rw [show e.right = w from h]
        exact hwD
  have hcard := Fintype.card_le_of_injective (Sum.elim ends rest)
    (sumElim_injective ends rest hends hrest hdisjoint)
  simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_coe] at hcard
  change Fintype.card (CrossingFamily P color a b) + Fintype.card (CrossingFamily P color a b) + (Fintype.card (NoncentralColor P color D c) + 1) ≤ P.vertices.card at hcard
  omega


end Papers.Polytopes.ActualFamilyCounting


end
end
end BundlePart22

section BundlePart23
/- Source: Papers/ActualForcedFamily.lean -/







@[expose] public section

/-!
# Forced exterior centers in every combinatorial realization

All numerical and cofacial inputs are derived from the original actual
polytope.  Only the genuine face-order isomorphism is used to transfer
them to a second realization.  The reconstructed center is exterior
because the transported family contains two disjoint actual edges.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily CrossingFamilyTransport ActualFamilyCounting
open Papers.ActualFaceOrder
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d m : ℕ}

theorem actual_offCentral_family_forced_center
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Fin 3)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (D Jab Jac : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2) (habdim : finrank ℝ Jab = 1)
    (hacdim : finrank ℝ Jac = 1) (hJab : Jab ≤ D) (hJac : Jac ≤ D)
    (hne : Jab ≠ Jac)
    (hcrossab : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = a → color y = b → Jab ≤ edgeProjectiveLine x.val y.val)
    (hcrossac : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = a → color y = c → Jac ≤ edgeProjectiveLine x.val y.val)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ Jab)
    (hoff : ∀ e : CrossingFamily P color a b, ¬ e.line ≤ D)
    (w : P.vertices) (hwD : homogenize w.val ∈ D)
    (hthird : d - 1 ≤ Fintype.card (NoncentralColor P color D c))
    (hN : P.vertices.card ≤ 4 * d - 5)
    (e0 : CrossingFamily P color a b)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    ∃ J : Submodule ℝ (E m × ℝ), finrank ℝ J = 1 ∧
      (∀ f : CrossingFamily Q (colorAlong iso color) a b, J ≤ f.line) ∧
      ¬ ∃ z ∈ Q.toSet, homogenize z ∈ J := by
  have hcenter : ∀ e : CrossingFamily P color a b, Jab ≤ e.line :=
    fun e => hcrossab e.left e.right e.isEdge e.property.2.1 e.property.2.2
  have hdegreeP : ∀ e : CrossingFamily P color a b,
      d - 2 ≤ (cofacialGraph (P := P) (color := color) (a := a) (b := b)).degree e :=
    fun e => actual_cofacial_degree_lower_bound P hP color a b c hab hac hbc
      D Jab Jac hD habdim hacdim hJab hJac hne hcrossab hcrossac e (hoff e)
  have hdegreeQ := minimum_degree_transport iso color a b (d - 2) hdegreeP
  have hcount := matching_family_third_color_count_at P color a b c hab hac hbc
    D Jab habdim hJab hcenter hnotvertex hoff w hwD
  have hcardeq := family_card_eq iso color a b
  have hconcurrent :
      ∃ J : Submodule ℝ (E m × ℝ), finrank ℝ J = 1 ∧
        ∀ f : CrossingFamily Q (colorAlong iso color) a b, J ≤ f.line := by
    by_cases hd3 : d = 3
    · apply concurrent_of_at_most_two_actual_edges hab
      · intro e
        have h := hdegreeQ e
        omega
      · omega
      · exact crossingEquiv iso color a b e0
    · apply concurrent_of_dense_actual_cofacial_graph hab (d - 2) (by omega) hdegreeQ
      · omega
      · exact no_three_transport iso color a b
          (no_three_in_actual_twoFace hab Jab habdim hcenter hnotvertex)
      · exact crossingEquiv iso color a b e0
  obtain ⟨J,hJ,hall⟩ := hconcurrent
  refine ⟨J,hJ,hall,?_⟩
  let G := cofacialGraph (P := P) (color := color) (a := a) (b := b)
  have hneighbor : (G.neighborFinset e0).Nonempty := by
    apply Finset.card_pos.mp
    have h : d - 2 ≤ G.degree e0 := hdegreeP e0
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
      (show 0 < G.degree e0 by omega)
  obtain ⟨f0,hf0⟩ := hneighbor
  have hef : e0 ≠ f0 := ((G.mem_neighborFinset e0 f0).mp hf0).1
  let ee := crossingEquiv iso color a b e0
  let ff := crossingEquiv iso color a b f0
  have heef : ee ≠ ff := fun h => hef ((crossingEquiv iso color a b).injective h)
  obtain ⟨hlP,hrP⟩ := endpoint_injections_of_nonvertex_center Jab habdim hcenter hnotvertex
  have hlQ := left_injective_transport iso color a b
    (fun e f h => hlP (congrArg Subtype.val h))
  have hrQ := right_injective_transport iso color a b
    (fun e f h => hrP (congrArg Subtype.val h))
  have hdisjoint : Disjoint ({ee.left.val,ee.right.val} : Set (E m))
      {ff.left.val,ff.right.val} :=
    ExposedEdgeCenters.endpoint_pairs_disjoint
      (fun e : CrossingFamily Q (colorAlong iso color) a b => e.left.val)
      (fun e => e.right.val)
      (fun e f h => hlQ (Subtype.ext h))
      (fun e f h => hrQ (Subtype.ext h))
      (left_ne_right_of_different_colors hab) heef
  exact center_outside_of_disjoint_actual_edges J hall ee ff hdisjoint

end Papers.Polytopes


end
end
end BundlePart23

section BundlePart24
/- Source: Papers/ActualCentralEdge.lean -/




@[expose] public section

/-!
# An actual central edge excludes every other color pair

A projective line containing one genuine polytope edge cannot contain
another genuine edge with a different unordered endpoint color pair.
This is derived from actual extreme vertices and actual edge supports.
-/

noncomputable section
namespace Papers.Polytopes.CrossingFamily

open Set Module Papers.Coordinates
open ExposedEdgeCenters ExposedProjectiveBridge
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {P : ConvexPolytope d} {color : P.vertices → Fin 3}
variable {a b c f : Fin 3}

theorem central_edges_colorPair_eq
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (e : CrossingFamily P color a b) (g : CrossingFamily P color c f)
    (he : e.line ≤ D) (hg : g.line ≤ D) :
    (s(a,b) : Sym2 (Fin 3)) = s(c,f) := by
  have hgeq : g.line = D :=
    Submodule.eq_of_le_of_finrank_le hg (by rw [hD,g.line_finrank_eq_two])
  have hpoints (v : P.vertices) (hv : homogenize v.val ∈ e.line) :
      v = g.left ∨ v = g.right := by
    have hline : point v.val ∈ edgeLine g.left.val g.right.val := by
      rw [exposed_edgeLine_eq_edgeProjectiveLine]
      change homogenize v.val ∈ g.line
      rw [hgeq]
      exact he hv
    have hz := affine_eq_zero_on_edgeLine g.support g.support_left g.support_right hline
    have hend := (support_zero_iff_endpoint P.toSet g.support
      (vertex_mem_body_of_mem_vertices P g.left.property)
      (vertex_mem_body_of_mem_vertices P g.right.property)
      g.support_left g.support_right g.support_zero_iff_segment
      (vertex_mem_body_extremePoints P v.property)).mp hz
    exact hend.imp Subtype.ext Subtype.ext
  have hl : e.left = g.left ∨ e.left = g.right :=
    hpoints e.left (Submodule.subset_span (by simp [line,edgeProjectiveLine]))
  have hr : e.right = g.left ∨ e.right = g.right :=
    hpoints e.right (Submodule.subset_span (by simp [line,edgeProjectiveLine]))
  have hpair : (s(e.left,e.right) : Sym2 P.vertices) = s(g.left,g.right) := by
    apply Sym2.eq_iff.mpr
    rcases hl with hl | hl <;> rcases hr with hr | hr
    · exact (e.isEdge.2.1 (congrArg Subtype.val (hl.trans hr.symm))).elim
    · exact Or.inl ⟨hl,hr⟩
    · exact Or.inr ⟨hl,hr⟩
    · exact (e.isEdge.2.1 (congrArg Subtype.val (hl.trans hr.symm))).elim
  have hcolors := congrArg (Sym2.map color) hpair
  have hel : color e.left = a := e.property.2.1
  have her : color e.right = b := e.property.2.2
  have hgl : color g.left = c := g.property.2.1
  have hgr : color g.right = f := g.property.2.2
  simpa only [Sym2.map_mk,hel,her,hgl,hgr] using hcolors

theorem offCentral_of_different_central_colorPair
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (e : CrossingFamily P color a b) (he : e.line ≤ D)
    (hpairs : (s(a,b) : Sym2 (Fin 3)) ≠ s(c,f))
    (g : CrossingFamily P color c f) :
    ¬ g.line ≤ D := by
  intro hg
  exact hpairs (central_edges_colorPair_eq D hD e g he hg)

theorem central_edge_left_mem
    (D : Submodule ℝ (E d × ℝ))
    (e : CrossingFamily P color a b) (he : e.line ≤ D) :
    homogenize e.left.val ∈ D :=
  he (Submodule.subset_span (by simp [line,edgeProjectiveLine]))

theorem central_edge_right_mem
    (D : Submodule ℝ (E d × ℝ))
    (e : CrossingFamily P color a b) (he : e.line ≤ D) :
    homogenize e.right.val ∈ D :=
  he (Submodule.subset_span (by simp [line,edgeProjectiveLine]))


theorem vertex_on_central_edge_is_endpoint
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (e : CrossingFamily P color a b) (he : e.line ≤ D)
    (u : P.vertices) (hu : homogenize u.val ∈ D) :
    u = e.left ∨ u = e.right := by
  have heq : e.line = D :=
    Submodule.eq_of_le_of_finrank_le he (by rw [hD,e.line_finrank_eq_two])
  have hline : point u.val ∈ edgeLine e.left.val e.right.val := by
    rw [exposed_edgeLine_eq_edgeProjectiveLine]
    change homogenize u.val ∈ e.line
    rw [heq]
    exact hu
  have hz := affine_eq_zero_on_edgeLine e.support e.support_left e.support_right hline
  have hend := (support_zero_iff_endpoint P.toSet e.support
    (vertex_mem_body_of_mem_vertices P e.left.property)
    (vertex_mem_body_of_mem_vertices P e.right.property)
    e.support_left e.support_right e.support_zero_iff_segment
    (vertex_mem_body_extremePoints P u.property)).mp hz
  exact hend.imp Subtype.ext Subtype.ext

end Papers.Polytopes.CrossingFamily


end
end
end BundlePart24

@[expose] public section BundlePart25
/- Source: Papers/CrossingQuotientRays.lean -/





/-!
# Positive quotient rays for exterior-centered edges

The convex set K is the homogeneous affine image of the actual polytope.
The exterior center condition therefore has its literal geometric meaning.
-/

namespace Papers.Polytopes.CrossingQuotient

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
variable [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ V]

theorem proportional_quotient_of_center
    (q : V →ₗ[ℝ] W) (J : Submodule ℝ V)
    (hJ : Module.finrank ℝ J = 1)
    {X Y : V} (hX : q X ≠ 0)
    (hJline : J ≤ Submodule.span ℝ ({X, Y} : Set V))
    (hJzero : J ≤ q.ker) :
    ∃ c : ℝ, q Y = c • q X := by
  obtain ⟨j, hj⟩ : ∃ j : J, j ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hJ]; norm_num)
  have hjzero : (j : V) ≠ 0 := by
    intro h
    apply hj
    exact Subtype.ext h
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hJline j.property)
  have hqj : q (j : V) = 0 := hJzero j.property
  have hsum : a • q X + b • q Y = 0 := by
    simpa only [map_add, map_smul, hqj] using congrArg q hab
  have hb : b ≠ 0 := by
    intro hb
    have ha : a = 0 := by
      have hsmul : a • q X = 0 := by simpa [hb] using hsum
      exact (smul_eq_zero.mp hsmul).resolve_right hX
    apply hjzero
    simpa [ha, hb] using hab.symm
  refine ⟨-a / b, ?_⟩
  have hby : b • q Y = (-a) • q X := by
    calc
      b • q Y = (a • q X + b • q Y) - a • q X := by abel
      _ = (-a) • q X := by rw [hsum]; simp
  apply smul_right_injective W hb
  change b • q Y = b • ((-a / b) • q X)
  rw [smul_smul]
  have hcoeff : b * (-a / b) = -a := by
    field_simp [hb] <;> ring
  rw [hcoeff]
  exact hby

theorem positive_quotient_of_exterior_center
    (K : Set V) (hK : Convex ℝ K)
    (D J : Submodule ℝ V) (q : V →ₗ[ℝ] W)
    (hker : q.ker = D)
    (hJ : Module.finrank ℝ J = 1) (hJD : J ≤ D)
    {X Y : V} (hXK : X ∈ K) (hYK : Y ∈ K)
    (hX : X ∉ D)
    (hline : Module.finrank ℝ (Submodule.span ℝ ({X, Y} : Set V)) = 2)
    (hJline : J ≤ Submodule.span ℝ ({X, Y} : Set V))
    (hexterior : ∀ z ∈ K, z ∉ J) :
    ∃ c : ℝ, 0 < c ∧ q Y = c • q X := by
  let L := Submodule.span ℝ ({X, Y} : Set V)
  have hqX : q X ≠ 0 := by
    intro h
    apply hX
    rw [← hker]
    exact h
  have hJzero : J ≤ q.ker := by simpa only [hker] using hJD
  have hdep := proportional_quotient_of_center q J hJ hqX hJline hJzero
  apply Papers.Polytopes.ThreeColorForest.positive_scalar_of_segment_avoids_kernel
    q X Y hdep
  intro a b ha hb hab hqzero
  have hcombK : a • X + b • Y ∈ K := hK hXK hYK ha hb hab
  apply hexterior (a • X + b • Y) hcombK
  have hoff : ¬ L ≤ D := by
    intro h
    exact hX (h (Submodule.subset_span (by simp)))
  have hinter : D ⊓ L = J :=
    Papers.Polytopes.CrossingLineGeometry.central_intersection_eq_center
      D L J hline hJ hJD hJline hoff
  rw [← hinter]
  constructor
  · rw [← hker]
    exact hqzero
  · exact Submodule.add_mem _ (Submodule.smul_mem _ a
      (Submodule.subset_span (by simp))) (Submodule.smul_mem _ b
        (Submodule.subset_span (by simp)))

end Papers.Polytopes.CrossingQuotient


end BundlePart25

@[expose] public section BundlePart26
/- Source: Papers/ExteriorCenterForest.lean -/





/-!
# The exterior-center forest for an actual convex body

The hypotheses describe ordinary exposed edges and their projective centers.
No hypothesis assumes acyclicity, a planar section, a geometric forest, or a
combinatorial conclusion.
-/

namespace Papers.Polytopes.ExteriorCenterForest

open Papers.Polytopes.ExposedEdgeCenters
open Papers.Polytopes.ThreeColorForest

variable {V I : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

theorem crossing_graph_isAcyclic
    (C : Set V) (hC : Convex ℝ C)
    (G : SimpleGraph I) (x : I → V) (hxC : ∀ i, x i ∈ C)
    (D : Submodule ℝ (V × ℝ)) (hD : Module.finrank ℝ D = 2)
    (hnoncentral : ∀ i, point (x i) ∉ D)
    (w : V) (hwC : w ∈ C) (hwD : point w ∈ D)
    (center : ∀ {i j}, G.Adj i j → Submodule ℝ (V × ℝ))
    (hcenterDim : ∀ {i j} (h : G.Adj i j), Module.finrank ℝ (center h) = 1)
    (hcenterD : ∀ {i j} (h : G.Adj i j), center h ≤ D)
    (hcenterLine : ∀ {i j} (h : G.Adj i j), center h ≤ edgeLine (x i) (x j))
    (hlineDim : ∀ {i j} (_ : G.Adj i j),
      Module.finrank ℝ (edgeLine (x i) (x j)) = 2)
    (hexterior : ∀ {i j} (h : G.Adj i j), ¬ CenterMeets C (center h))
    (support : ∀ {i j}, G.Adj i j → V →ᵃ[ℝ] ℝ)
    (hsnonneg : ∀ {i j} (h : G.Adj i j) z, z ∈ C → 0 ≤ support h z)
    (hszero : ∀ {i j} (h : G.Adj i j) k,
      support h (x k) = 0 ↔ k = i ∨ k = j) :
    G.IsAcyclic := by
  have hspan (i j k : I) (hij : G.Adj i j) (hik : G.Adj i k) (hjk : j ≠ k) :
      center hij ⊔ center hik = D := by
    have hneq : center hij ≠ center hik := by
      intro heq
      have hi : support hij (x i) = 0 := (hszero hij i).mpr (Or.inl rfl)
      have hj : support hij (x j) = 0 := (hszero hij j).mpr (Or.inr rfl)
      have hk : support hij (x k) ≠ 0 := by
        intro h
        rcases (hszero hij k).mp h with h | h
        · exact hik.ne h.symm
        · exact hjk h.symm
      have hmem :=
        Papers.Polytopes.CrossingLineGeometry.vertex_mem_center_of_separating_form
          (point (x i)) (point (x j)) (point (x k)) (point_ne_zero (x i))
          (affineForm (support hij))
          (by simpa using hi) (by simpa using hj) (by simpa using hk)
          (center hij) (hcenterDim hij) (hcenterLine hij)
          (by rw [heq]; exact hcenterLine hik)
      exact hexterior hij ⟨x i, hxC i, hmem⟩
    exact Papers.Polytopes.CrossingLineGeometry.sup_eq_plane_of_distinct_points
      D (center hij) (center hik) hD (hcenterDim hij) (hcenterDim hik)
      (hcenterD hij) (hcenterD hik) hneq
  let q := D.mkQ
  apply isAcyclic_of_positive_ray_quotient G (fun i => point (x i)) (point w)
    (LinearMap.snd ℝ V ℝ) (fun _ => rfl) rfl q
  · simpa only [q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hwD
  · intro i
    intro hzero
    apply hnoncentral i
    exact (Submodule.Quotient.mk_eq_zero D).mp hzero
  · intro i j hij
    apply Papers.Polytopes.CrossingQuotient.positive_quotient_of_exterior_center
      (point '' C) (convex_point_image C hC) D (center hij) q
      (by simp [q]) (hcenterDim hij) (hcenterD hij)
      ⟨x i, hxC i, rfl⟩ ⟨x j, hxC j, rfl⟩ (hnoncentral i)
      (hlineDim hij) (hcenterLine hij)
    rintro z ⟨v, hv, rfl⟩ hz
    exact hexterior hij ⟨v, hv, hz⟩
  · intro i j k hij hik hjk
    have hplane : D ≤
        Submodule.span ℝ ({point (x i), point (x j), point (x k)} : Set (V × ℝ)) := by
      rw [← hspan i j k hij hik hjk]
      apply sup_le
      · exact (hcenterLine hij).trans (Submodule.span_mono (by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
          tauto))
      · exact (hcenterLine hik).trans (Submodule.span_mono (by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
          tauto))
    refine ⟨hplane hwD, ?_⟩
    have hij_i : support hij (x i) = 0 := (hszero hij i).mpr (Or.inl rfl)
    have hij_j : support hij (x j) = 0 := (hszero hij j).mpr (Or.inr rfl)
    have hik_i : support hik (x i) = 0 := (hszero hik i).mpr (Or.inl rfl)
    have hik_k : support hik (x k) = 0 := (hszero hik k).mpr (Or.inr rfl)
    have hij_k : 0 < support hij (x k) := by
      have hnn := hsnonneg hij (x k) (hxC k)
      have hn : support hij (x k) ≠ 0 := by
        intro h
        rcases (hszero hij k).mp h with h | h
        · exact hik.ne h.symm
        · exact hjk h.symm
      exact lt_of_le_of_ne hnn (Ne.symm hn)
    have hik_j : 0 < support hik (x j) := by
      have hnn := hsnonneg hik (x j) (hxC j)
      have hn : support hik (x j) ≠ 0 := by
        intro h
        rcases (hszero hik j).mp h with h | h
        · exact hij.ne h.symm
        · exact hjk h
      exact lt_of_le_of_ne hnn (Ne.symm hn)
    exact ⟨
      { left := affineForm (support hij)
        right := affineForm (support hik)
        left_at_X := by simpa using hij_i
        left_at_Y := by simpa using hij_j
        left_at_Z := by simpa using hij_k
        left_at_T := by simpa using hsnonneg hij w hwC
        right_at_X := by simpa using hik_i
        right_at_Z := by simpa using hik_k
        right_at_Y := by simpa using hik_j
        right_at_T := by simpa using hsnonneg hik w hwC }⟩

end Papers.Polytopes.ExteriorCenterForest


end BundlePart26

@[expose] public section BundlePart27
/- Source: Papers/ThreeColorForestCount.lean -/








/-!
# Counting exterior crossing edges

A forest has one fewer edge than vertex in each connected component.  Quotient
vertex vectors which are proportional along edges span at most one dimension
per component.  Combining these two facts gives the exact count needed in
Proposition 11, without a classification of three-colored graphs.
-/

namespace Papers.Polytopes.ThreeColorForest

open scoped BigOperators Classical

variable {I W : Type*}
variable [AddCommGroup W] [Module ℝ W]

/-- The partition of the vertex type into its actual connected components. -/
def verticesByComponent (G : SimpleGraph I) :
    (Σ C : G.ConnectedComponent, C) ≃ I where
  toFun v := v.2.val
  invFun v := ⟨G.connectedComponentMk v, ⟨v, rfl⟩⟩
  left_inv := by
    rintro ⟨C, v, hv⟩
    change G.connectedComponentMk v = C at hv
    subst C
    rfl
  right_inv _ := rfl

/-- Every neighbor of a vertex belongs to its connected component. -/
def neighborsByComponent (G : SimpleGraph I)
    (C : G.ConnectedComponent) (v : C) :
    C.toSimpleGraph.neighborSet v ≃ G.neighborSet v.val where
  toFun u := ⟨u.val.val, u.property⟩
  invFun u := ⟨⟨u.val, C.mem_supp_of_adj_mem_supp v.property u.property⟩, u.property⟩
  left_inv := by rintro ⟨⟨u, hu⟩, hadj⟩; rfl
  right_inv := by rintro ⟨u, hu⟩; rfl

theorem degree_in_component [Fintype I] (G : SimpleGraph I) [DecidableRel G.Adj]
    (C : G.ConnectedComponent) [Fintype C] (v : C) :
    C.toSimpleGraph.degree v = G.degree v.val := by
  classical
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using
    Fintype.card_congr (neighborsByComponent G C v)

/-- Euler's elementary forest identity, including isolated vertices and the
empty graph. No topological Euler formula is used. -/
theorem forest_card_identity [Finite I] (G : SimpleGraph I) (hG : G.IsAcyclic) :
    Nat.card G.edgeSet + Nat.card G.ConnectedComponent = Nat.card I := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite G.ConnectedComponent
  letI : ∀ C : G.ConnectedComponent, Fintype C :=
    fun C => Fintype.ofFinite C
  have hvertices :
      (∑ C : G.ConnectedComponent, Fintype.card C) = Fintype.card I := by
    calc
      (∑ C : G.ConnectedComponent, Fintype.card C) =
          Fintype.card (Σ C : G.ConnectedComponent, C) := by
        simpa only [Finset.univ_sigma_univ, Finset.card_univ] using
          (Finset.card_sigma (Finset.univ : Finset G.ConnectedComponent)
            (fun C => (Finset.univ : Finset C))).symm
      _ = Fintype.card I := Fintype.card_congr (verticesByComponent G)
  have hdegrees :
      (∑ C : G.ConnectedComponent, ∑ v : C, G.degree v.val) =
        ∑ v : I, G.degree v := by
    calc
      (∑ C : G.ConnectedComponent, ∑ v : C, G.degree v.val) =
          ∑ v : (Σ C : G.ConnectedComponent, C), G.degree v.2.val := by
        simpa only [Finset.univ_sigma_univ] using
          (Finset.sum_sigma (Finset.univ : Finset G.ConnectedComponent)
            (fun C => (Finset.univ : Finset C))
            (fun v : (Σ C : G.ConnectedComponent, C) => G.degree v.2.val)).symm
      _ = ∑ v : I, G.degree v :=
        Fintype.sum_equiv (verticesByComponent G) _ _ (fun _ => rfl)
  have htree (C : G.ConnectedComponent) :
      (∑ v : C, G.degree v.val) + 2 = 2 * Fintype.card C := by
    have hcard := (hG.isTree_connectedComponent C).card_edgeFinset
    calc
      (∑ v : C, G.degree v.val) + 2 =
          (∑ v : C, C.toSimpleGraph.degree v) + 2 := by
        congr 1
        apply Finset.sum_congr rfl
        intro v _
        exact (degree_in_component G C v).symm
      _ = 2 * C.toSimpleGraph.edgeFinset.card + 2 := by
        rw [C.toSimpleGraph.sum_degrees_eq_twice_card_edges]
      _ = 2 * Fintype.card C := by omega
  have hsum :
      (∑ C : G.ConnectedComponent, ((∑ v : C, G.degree v.val) + 2)) =
        ∑ C : G.ConnectedComponent, 2 * Fintype.card C :=
    Finset.sum_congr rfl (fun C _ => htree C)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, hdegrees, hvertices,
    G.sum_degrees_eq_twice_card_edges] at hsum
  norm_num only [Nat.cast_id] at hsum
  have hidentity :
      G.edgeFinset.card + Fintype.card G.ConnectedComponent = Fintype.card I := by
    omega
  simpa only [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using hidentity

/-- A family of vectors proportional along graph edges spans at most one
dimension per connected component. -/
theorem quotient_rank_le_components [Finite I]
    (G : SimpleGraph I) (v : I → W)
    (hedge : ∀ {i j}, G.Adj i j →
      ∃ c : ℝ, 0 < c ∧ v j = c • v i) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤
      Nat.card G.ConnectedComponent := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite G.ConnectedComponent
  let representative : G.ConnectedComponent → I :=
    fun C => C.nonempty_supp.choose
  have hrep (C : G.ConnectedComponent) : representative C ∈ C :=
    C.nonempty_supp.choose_spec
  let r : G.ConnectedComponent → W := fun C => v (representative C)
  have hspan :
      Submodule.span ℝ (Set.range v) = Submodule.span ℝ (Set.range r) := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      let C := G.connectedComponentMk i
      have hi : i ∈ C := rfl
      have hreach : G.Reachable (representative C) i :=
        C.reachable_of_mem_supp (hrep C) hi
      obtain ⟨c, -, hc⟩ := positive_ray_of_reachable G v hedge hreach
      rw [hc]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨C, rfl⟩)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨C, rfl⟩
      exact Submodule.subset_span ⟨representative C, rfl⟩
  rw [hspan, Nat.card_eq_fintype_card]
  exact finrank_range_le_card r

/-- The edge-and-rank count underlying the forest contradiction. -/
theorem forest_edge_count_add_quotient_rank [Finite I]
    (G : SimpleGraph I) (hG : G.IsAcyclic) (v : I → W)
    (hedge : ∀ {i j}, G.Adj i j →
      ∃ c : ℝ, 0 < c ∧ v j = c • v i) :
    Nat.card G.edgeSet +
        Module.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ Nat.card I := by
  have hcard := forest_card_identity G hG
  have hrank := quotient_rank_le_components G v hedge
  omega

/-- If all three crossing families contain at least r edges, their noncentral
forest already needs at least 4r vertices. -/
theorem three_family_forest_vertex_bound [Finite I]
    (G : SimpleGraph I) (hG : G.IsAcyclic) (v : I → W)
    (hedge : ∀ {i j}, G.Adj i j →
      ∃ c : ℝ, 0 < c ∧ v j = c • v i)
    (r : ℕ)
    (hrank : r ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range v)))
    (hedges : 3 * r ≤ Nat.card G.edgeSet) :
    4 * r ≤ Nat.card I := by
  have h := forest_edge_count_add_quotient_rank G hG v hedge
  omega

end Papers.Polytopes.ThreeColorForest


end BundlePart27

@[expose] public section BundlePart28
/- Source: Papers/NoncentralQuotientRank.lean -/





/-!
# The exact quotient rank of noncentral vertices

Deleting the vectors lying in the central subspace does not change the span
of their images in the quotient. Full affine dimension therefore supplies the
rank d-1 used in the forest count.
-/

namespace Papers.Polytopes.NoncentralQuotientRank

variable {V I : Type*} [AddCommGroup V] [Module ℝ V]

theorem noncentral_images_span_quotient
    (X : I → V) (hX : Submodule.span ℝ (Set.range X) = ⊤)
    (D : Submodule ℝ V) :
    Submodule.span ℝ
      (Set.range (fun i : {i : I // X i ∉ D} => D.mkQ (X i.val))) = ⊤ := by
  classical
  let S : Submodule ℝ (V ⧸ D) := Submodule.span ℝ
    (Set.range (fun i : {i : I // X i ∉ D} => D.mkQ (X i.val)))
  have hpre : Submodule.span ℝ (Set.range X) ≤ S.comap D.mkQ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    change D.mkQ (X i) ∈ S
    by_cases hi : X i ∈ D
    · have hz : D.mkQ (X i) = 0 := by
        simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hi
      rw [hz]
      exact S.zero_mem
    · exact Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩
  change S = ⊤
  apply le_antisymm le_top
  intro z _
  obtain ⟨v,rfl⟩ := D.mkQ_surjective z
  exact hpre (by rw [hX]; trivial)

theorem noncentral_quotient_rank_add
    [FiniteDimensional ℝ V]
    (X : I → V) (hX : Submodule.span ℝ (Set.range X) = ⊤)
    (D : Submodule ℝ V) :
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : {i : I // X i ∉ D} => D.mkQ (X i.val)))) +
        Module.finrank ℝ D = Module.finrank ℝ V := by
  rw [noncentral_images_span_quotient X hX D]
  simpa only [finrank_top] using D.finrank_quotient_add_finrank

theorem noncentral_rank_for_projective_line
    [FiniteDimensional ℝ V]
    (d : ℕ) (hV : Module.finrank ℝ V = d + 1)
    (X : I → V) (hX : Submodule.span ℝ (Set.range X) = ⊤)
    (D : Submodule ℝ V) (hD : Module.finrank ℝ D = 2) :
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : {i : I // X i ∉ D} => D.mkQ (X i.val)))) + 1 = d := by
  have h := noncentral_quotient_rank_add X hX D
  omega

end Papers.Polytopes.NoncentralQuotientRank


end BundlePart28

@[expose] public section BundlePart29
/- Source: Papers/ExteriorCrossingCount.lean -/




/-!
# The noncentral crossing forest has fewer than three full families

This combines the actual exposed-edge forest theorem with the exact quotient
rank. All noncentral vertices are retained, including isolated vertices.
-/

namespace Papers.Polytopes.ExteriorCrossingCount

open Papers.Polytopes.ExposedEdgeCenters
open Papers.Polytopes.ThreeColorForest

variable {V I : Type*} [AddCommGroup V] [Module ℝ V]
  [FiniteDimensional ℝ V] [Finite I]

theorem crossing_edge_card_lt_three_classes
    (d : ℕ) (hd : 3 ≤ d)
    (C : Set V) (hC : Convex ℝ C)
    (x : I → V) (hxC : ∀ i, x i ∈ C)
    (hspan : Submodule.span ℝ (Set.range (fun i => point (x i))) = ⊤)
    (hambient : Module.finrank ℝ (V × ℝ) = d + 1)
    (D : Submodule ℝ (V × ℝ)) (hD : Module.finrank ℝ D = 2)
    (w : V) (hwC : w ∈ C) (hwD : point w ∈ D)
    (G : SimpleGraph {i : I // point (x i) ∉ D})
    (center : ∀ {i j}, G.Adj i j → Submodule ℝ (V × ℝ))
    (hcenterDim : ∀ {i j} (h : G.Adj i j), Module.finrank ℝ (center h) = 1)
    (hcenterD : ∀ {i j} (h : G.Adj i j), center h ≤ D)
    (hcenterLine : ∀ {i j} (h : G.Adj i j),
      center h ≤ edgeLine (x i.val) (x j.val))
    (hlineDim : ∀ {i j} (_ : G.Adj i j),
      Module.finrank ℝ (edgeLine (x i.val) (x j.val)) = 2)
    (hexterior : ∀ {i j} (h : G.Adj i j), ¬ CenterMeets C (center h))
    (support : ∀ {i j}, G.Adj i j → V →ᵃ[ℝ] ℝ)
    (hsnonneg : ∀ {i j} (h : G.Adj i j) z, z ∈ C → 0 ≤ support h z)
    (hszero : ∀ {i j} (h : G.Adj i j) k,
      support h (x k.val) = 0 ↔ k = i ∨ k = j)
    (hN : Nat.card I ≤ 4 * d - 5) :
    Nat.card G.edgeSet < 3 * (d - 1) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  let NC := {i : I // point (x i) ∉ D}
  have hforest : G.IsAcyclic :=
    Papers.Polytopes.ExteriorCenterForest.crossing_graph_isAcyclic
      C hC G (fun i => x i.val) (fun i => hxC i.val)
      D hD (fun i => i.property) w hwC hwD center
      hcenterDim hcenterD hcenterLine hlineDim hexterior support hsnonneg hszero
  have hpositive : ∀ {i j : NC}, G.Adj i j →
      ∃ c : ℝ, 0 < c ∧ D.mkQ (point (x j.val)) =
        c • D.mkQ (point (x i.val)) := by
    intro i j hij
    apply Papers.Polytopes.CrossingQuotient.positive_quotient_of_exterior_center
      (point '' C) (convex_point_image C hC) D (center hij) D.mkQ
      (by simp) (hcenterDim hij) (hcenterD hij)
      ⟨x i.val, hxC i.val, rfl⟩ ⟨x j.val, hxC j.val, rfl⟩ i.property
      (hlineDim hij) (hcenterLine hij)
    rintro z ⟨v,hv,rfl⟩ hz
    exact hexterior hij ⟨v,hv,hz⟩
  have hrank :=
    Papers.Polytopes.NoncentralQuotientRank.noncentral_rank_for_projective_line
      d hambient (fun i => point (x i)) hspan D hD
  have hcount := forest_edge_count_add_quotient_rank G hforest
    (fun i => D.mkQ (point (x i.val))) hpositive
  have hvertices : Nat.card NC ≤ Nat.card I := by
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_le_of_injective (fun i : NC => i.val) Subtype.val_injective
  change Nat.card G.edgeSet +
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : NC => D.mkQ (point (x i.val))))) ≤ Nat.card NC at hcount
  change Module.finrank ℝ (Submodule.span ℝ
    (Set.range (fun i : NC => D.mkQ (point (x i.val))))) + 1 = d at hrank
  omega

end Papers.Polytopes.ExteriorCrossingCount


end BundlePart29

section BundlePart30
/- Source: Papers/ActualExteriorForest.lean -/







@[expose] public section

/-!
# The exterior-center forest for actual polytopes

The generic support-form forest theorem is instantiated with actual
polytope vertices, actual edge supports, and full homogeneous span.
Isolated noncentral vertices remain in the graph.
-/

noncomputable section
namespace Papers.Polytopes.ActualExteriorForest

open Set Module Papers.Coordinates
open ExposedEdgeCenters ExposedProjectiveBridge HomogeneousFaceSpans
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem homogeneousSpan_convexHull (S : Set (E d)) :
    homogeneousSpan (K := ℝ) (convexHull ℝ S) = homogeneousSpan (K := ℝ) S := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨x,hx,rfl⟩
    let H := homogeneousSpan (K := ℝ) S
    have hconv : Convex ℝ {x : E d | homogenize x ∈ H} := by
      intro u hu v hv a b ha hb hab
      change point (a • u + b • v) ∈ H
      rw [point_weighted_sum u v a b hab]
      exact H.add_mem (H.smul_mem a hu) (H.smul_mem b hv)
    exact convexHull_min (fun u hu => point_mem_span hu) hconv hx
  · exact Submodule.span_mono (Set.image_mono (subset_convexHull ℝ S))

theorem homogeneous_ambient_finrank :
    finrank ℝ (E d × ℝ) = d + 1 := by
  rw [Module.finrank_prod]
  simp only [E,finrank_euclideanSpace_fin,CommSemiring.finrank_self]

theorem actual_vertex_homogeneous_span_full
    (P : ConvexPolytope d) (hP : P.IsFullDim) :
    Submodule.span ℝ (Set.range (fun x : P.vertices => point x.val)) = ⊤ := by
  have hbody : P.toSet.Nonempty := by
    obtain ⟨x,hx⟩ := P.vertices_nonempty
    exact ⟨x,vertex_mem_body_of_mem_vertices P hx⟩
  have hrank : finrank ℝ (homogeneousSpan (K := ℝ) P.toSet) = d + 1 := by
    rw [homogeneousSpan_rank_of_nonempty P.toSet hbody]
    change P.dim + 1 = d + 1
    exact congrArg (fun n : ℕ => n + 1) hP
  have htop : homogeneousSpan (K := ℝ) P.toSet = ⊤ := by
    apply Submodule.eq_of_le_of_finrank_le le_top
    rw [finrank_top,homogeneous_ambient_finrank,hrank]
  have hspan : homogeneousSpan (K := ℝ) (P.vertices : Set (E d)) = ⊤ := by
    rw [← homogeneousSpan_convexHull]
    exact htop
  have hrange : Set.range (fun x : P.vertices => point x.val) =
      homogenize '' (P.vertices : Set (E d)) := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.val,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  rw [hrange]
  exact hspan

abbrev NoncentralVertex (P : ConvexPolytope d)
    (D : Submodule ℝ (E d × ℝ)) :=
  {v : P.vertices // homogenize v.val ∉ D}

def crossingGraph (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (D : Submodule ℝ (E d × ℝ)) : SimpleGraph (NoncentralVertex P D) where
  Adj x y := GeneralVertexStep P x.val.val y.val.val ∧ color x.val ≠ color y.val
  symm := ⟨by
    intro x y h
    exact ⟨actualStep_symm x.val.property h.1,h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1.2.1 rfl⟩

theorem actual_crossing_edge_card_lt_three_classes
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Fin 3)
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (center : Fin 3 → Fin 3 → Submodule ℝ (E d × ℝ))
    (hcenterDim : ∀ i j, i ≠ j → finrank ℝ (center i j) = 1)
    (hcenterD : ∀ i j, i ≠ j → center i j ≤ D)
    (hcross : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x ≠ color y → center (color x) (color y) ≤ edgeProjectiveLine x.val y.val)
    (hexterior : ∀ i j, i ≠ j → ¬ ∃ z ∈ P.toSet, homogenize z ∈ center i j)
    (w : E d) (hwP : w ∈ P.toSet) (hwD : homogenize w ∈ D)
    (hN : P.vertices.card ≤ 4 * d - 5) :
    Nat.card (crossingGraph P color D).edgeSet < 3 * (d - 1) := by
  let G := crossingGraph P color D
  let J : ∀ {i j : NoncentralVertex P D}, G.Adj i j → Submodule ℝ (E d × ℝ) :=
    fun {i j} _ => center (color i.val) (color j.val)
  let support : ∀ {i j : NoncentralVertex P D}, G.Adj i j → E d →ᵃ[ℝ] ℝ :=
    fun {i j} h =>
      Classical.choose (exists_nonnegative_affine_edge_form P i.val.property h.1)
  have hs (i j : NoncentralVertex P D) (h : G.Adj i j) :
      (∀ z ∈ P.toSet, 0 ≤ support h z) ∧
      (∀ z ∈ P.toSet, support h z = 0 ↔ z ∈ segment ℝ i.val.val j.val.val) :=
    Classical.choose_spec (exists_nonnegative_affine_edge_form P i.val.property h.1)
  refine ExteriorCrossingCount.crossing_edge_card_lt_three_classes d hd
    P.toSet (convex_convexHull ℝ _) (fun x : P.vertices => x.val)
    (fun x => vertex_mem_body_of_mem_vertices P x.property)
    (actual_vertex_homogeneous_span_full P hP) homogeneous_ambient_finrank
    D hD w hwP hwD G J ?_ ?_ ?_ ?_ ?_ support ?_ ?_ ?_
  · intro i j h
    exact hcenterDim _ _ h.2
  · intro i j h
    exact hcenterD _ _ h.2
  · intro i j h
    simpa only [exposed_edgeLine_eq_edgeProjectiveLine] using hcross i.val j.val h.1 h.2
  · intro i j h
    exact ExposedLineRanks.edgeLine_finrank_eq_two h.1.2.1
  · intro i j h
    exact hexterior _ _ h.2
  · intro i j h z hz
    exact (hs i j h).1 z hz
  · intro i j h k
    have hiP := vertex_mem_body_of_mem_vertices P i.val.property
    have hjP := vertex_mem_body_of_mem_vertices P j.val.property
    have hsi : support h i.val.val = 0 :=
      ((hs i j h).2 i.val.val hiP).mpr (left_mem_segment ℝ _ _)
    have hsj : support h j.val.val = 0 :=
      ((hs i j h).2 j.val.val hjP).mpr (right_mem_segment ℝ _ _)
    rw [support_zero_iff_endpoint P.toSet (support h) hiP hjP hsi hsj
      (hs i j h).2 (vertex_mem_body_extremePoints P k.val.property)]
    constructor
    · rintro (hki | hkj)
      · exact Or.inl (Subtype.ext (Subtype.ext hki))
      · exact Or.inr (Subtype.ext (Subtype.ext hkj))
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  · simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hN

end Papers.Polytopes.ActualExteriorForest


end
end
end BundlePart30

section BundlePart31
/- Source: Papers/ActualOffCentralCount.lean -/






@[expose] public section

/-!
# Injecting the three off-central families into the actual forest

Each unordered graph edge receives its actual pair of colors. Thus the
three canonically oriented families inject with disjoint images, retaining
isolated noncentral vertices in the ambient forest.
-/

noncomputable section
namespace Papers.Polytopes.ActualOffCentralCount

open Set Module Papers.Coordinates
open CrossingFamily ActualExteriorForest ExposedEdgeCenters ExposedProjectiveBridge
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {P : ConvexPolytope d} {color : P.vertices → Fin 3}
variable {a b : Fin 3} {D J : Submodule ℝ (E d × ℝ)}

theorem offCentral_endpoints
    (hJ : finrank ℝ J = 1) (hJD : J ≤ D)
    (hcenter : ∀ e : CrossingFamily P color a b, J ≤ e.line)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J)
    (e : OffCentralFamily P color a b D) :
    homogenize e.val.left.val ∉ D ∧ homogenize e.val.right.val ∉ D := by
  have hline : J ≤ edgeLine e.val.left.val e.val.right.val := by
    simpa only [exposed_edgeLine_eq_edgeProjectiveLine,CrossingFamily.line] using hcenter e.val
  have hdich := CentralEdgeDichotomy.edge_central_or_both_endpoints_noncentral
    D J e.val.isEdge.2.1 hJ hJD hline
    (hnotvertex e.val.left.val e.val.left.property)
    (hnotvertex e.val.right.val e.val.right.property)
  apply hdich.resolve_left
  intro h
  apply e.property
  simpa only [exposed_edgeLine_eq_edgeProjectiveLine,CrossingFamily.line] using h

def toForestEdge
    (hab : a ≠ b) (hJ : finrank ℝ J = 1) (hJD : J ≤ D)
    (hcenter : ∀ e : CrossingFamily P color a b, J ≤ e.line)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J)
    (e : OffCentralFamily P color a b D) :
    (crossingGraph P color D).edgeSet :=
  let hl := (offCentral_endpoints hJ hJD hcenter hnotvertex e).1
  let hr := (offCentral_endpoints hJ hJD hcenter hnotvertex e).2
  ⟨s(⟨e.val.left,hl⟩,⟨e.val.right,hr⟩),e.val.isEdge,by
    change color e.val.left ≠ color e.val.right
    have hl : color e.val.left = a := e.val.property.2.1
    have hr : color e.val.right = b := e.val.property.2.2
    rw [hl,hr]
    exact hab⟩

theorem toForestEdge_injective
    (hab : a ≠ b) (hJ : finrank ℝ J = 1) (hJD : J ≤ D)
    (hcenter : ∀ e : CrossingFamily P color a b, J ≤ e.line)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J) :
    Function.Injective (toForestEdge hab hJ hJD hcenter hnotvertex) := by
  intro e f h
  have hp := Sym2.eq_iff.mp (congrArg Subtype.val h)
  rcases hp with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val hl) (congrArg Subtype.val hr)
  · have hcolor := congrArg (fun x : NoncentralVertex P D => color x.val) hl
    change color e.val.left = color f.val.right at hcolor
    have hl : color e.val.left = a := e.val.property.2.1
    have hr : color f.val.right = b := f.val.property.2.2
    rw [hl,hr] at hcolor
    exact (hab hcolor).elim

theorem toForestEdge_colorPair
    (hab : a ≠ b) (hJ : finrank ℝ J = 1) (hJD : J ≤ D)
    (hcenter : ∀ e : CrossingFamily P color a b, J ≤ e.line)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J)
    (e : OffCentralFamily P color a b D) :
    Sym2.map (fun x : NoncentralVertex P D => color x.val)
      (toForestEdge hab hJ hJD hcenter hnotvertex e).val = s(a,b) := by
  change s(color e.val.left,color e.val.right) = s(a,b)
  have hl : color e.val.left = a := e.val.property.2.1
  have hr : color e.val.right = b := e.val.property.2.2
  rw [hl,hr]

theorem toForestEdge_disjoint
    {c f : Fin 3} {K : Submodule ℝ (E d × ℝ)}
    (hab : a ≠ b) (hcf : c ≠ f)
    (hJ : finrank ℝ J = 1) (hK : finrank ℝ K = 1)
    (hJD : J ≤ D) (hKD : K ≤ D)
    (hcenterJ : ∀ e : CrossingFamily P color a b, J ≤ e.line)
    (hcenterK : ∀ e : CrossingFamily P color c f, K ≤ e.line)
    (hnotJ : ∀ x ∈ P.vertices, homogenize x ∉ J)
    (hnotK : ∀ x ∈ P.vertices, homogenize x ∉ K)
    (hpairs : (s(a,b) : Sym2 (Fin 3)) ≠ s(c,f))
    (e : OffCentralFamily P color a b D)
    (g : OffCentralFamily P color c f D) :
    toForestEdge hab hJ hJD hcenterJ hnotJ e ≠
      toForestEdge hcf hK hKD hcenterK hnotK g := by
  intro h
  apply hpairs
  have hcolors := congrArg
    (fun t : (crossingGraph P color D).edgeSet =>
      Sym2.map (fun x : NoncentralVertex P D => color x.val) t.val) h
  simpa only [toForestEdge_colorPair] using hcolors

theorem three_family_card_le_forest_edges
    (D J01 J02 J12 : Submodule ℝ (E d × ℝ))
    (h01 : finrank ℝ J01 = 1) (h02 : finrank ℝ J02 = 1)
    (h12 : finrank ℝ J12 = 1)
    (h01D : J01 ≤ D) (h02D : J02 ≤ D) (h12D : J12 ≤ D)
    (hcenter01 : ∀ e : CrossingFamily P color 0 1, J01 ≤ e.line)
    (hcenter02 : ∀ e : CrossingFamily P color 0 2, J02 ≤ e.line)
    (hcenter12 : ∀ e : CrossingFamily P color 1 2, J12 ≤ e.line)
    (hnot01 : ∀ x ∈ P.vertices, homogenize x ∉ J01)
    (hnot02 : ∀ x ∈ P.vertices, homogenize x ∉ J02)
    (hnot12 : ∀ x ∈ P.vertices, homogenize x ∉ J12) :
    Fintype.card (OffCentralFamily P color 0 1 D) +
      Fintype.card (OffCentralFamily P color 0 2 D) +
      Fintype.card (OffCentralFamily P color 1 2 D) ≤
        Nat.card (crossingGraph P color D).edgeSet := by
  let f01 := toForestEdge (by decide : (0 : Fin 3) ≠ 1)
    h01 h01D hcenter01 hnot01
  let f02 := toForestEdge (by decide : (0 : Fin 3) ≠ 2)
    h02 h02D hcenter02 hnot02
  let f12 := toForestEdge (by decide : (1 : Fin 3) ≠ 2)
    h12 h12D hcenter12 hnot12
  have h01i : Function.Injective f01 := toForestEdge_injective _ _ _ _ _
  have h02i : Function.Injective f02 := toForestEdge_injective _ _ _ _ _
  have h12i : Function.Injective f12 := toForestEdge_injective _ _ _ _ _
  have h0102 : ∀ e f, f01 e ≠ f02 f := by
    intro e f
    exact toForestEdge_disjoint _ _ _ _ _ _ _ _ _ _
      (by decide : (s(0,1) : Sym2 (Fin 3)) ≠ s(0,2)) e f
  have h0112 : ∀ e f, f01 e ≠ f12 f := by
    intro e f
    exact toForestEdge_disjoint _ _ _ _ _ _ _ _ _ _
      (by decide : (s(0,1) : Sym2 (Fin 3)) ≠ s(1,2)) e f
  have h0212 : ∀ e f, f02 e ≠ f12 f := by
    intro e f
    exact toForestEdge_disjoint _ _ _ _ _ _ _ _ _ _
      (by decide : (s(0,2) : Sym2 (Fin 3)) ≠ s(1,2)) e f
  have hrest : Function.Injective (Sum.elim f02 f12) :=
    ActualFamilyCounting.sumElim_injective f02 f12 h02i h12i h0212
  have hdisjoint : ∀ e f, f01 e ≠ Sum.elim f02 f12 f := by
    intro e f
    cases f with
    | inl f => exact h0102 e f
    | inr f => exact h0112 e f
  have hcard := Fintype.card_le_of_injective (Sum.elim f01 (Sum.elim f02 f12))
    (ActualFamilyCounting.sumElim_injective f01 (Sum.elim f02 f12)
      h01i hrest hdisjoint)
  simp only [Fintype.card_sum] at hcard
  rw [Nat.card_eq_fintype_card]
  omega

end Papers.Polytopes.ActualOffCentralCount


end
end
end BundlePart31

section BundlePart32
/- Source: Papers/ActualExteriorAlternative.lean -/



@[expose] public section

/-!
# The exterior-center case forces a single central crossing family

If every family has an off-central edge, the cofacial lower bounds supply
at least 3(d−1) edges of the actual exterior-center forest. Its forest
bound is strictly smaller. Therefore one family is entirely central;
actual exposed edges in that line form a subsingleton family.
-/

noncomputable section
namespace Papers.Polytopes.ActualExteriorAlternative

open Set Module Papers.Coordinates
open CrossingFamily ActualExteriorForest ActualOffCentralCount ExposedProjectiveBridge
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem central_crossing_family_subsingleton
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (a b : Fin 3) (hab : a ≠ b)
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (hall : ∀ e : CrossingFamily P color a b, e.line ≤ D) :
    Subsingleton (CrossingFamily P color a b) := by
  refine CentralEdgeDichotomy.central_exposed_family_subsingleton P.toSet D hD
    (fun e : CrossingFamily P color a b => e.left.val)
    (fun e => e.right.val) ?_ ?_ ?_ CrossingFamily.support ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun e => vertex_mem_body_extremePoints P e.left.property
  · exact fun e => vertex_mem_body_extremePoints P e.right.property
  · exact fun e => e.isEdge.2.1
  · exact CrossingFamily.support_left
  · exact CrossingFamily.support_right
  · exact fun e x hx => e.support_zero_iff_segment x hx
  · intro e
    simpa only [exposed_edgeLine_eq_edgeProjectiveLine,CrossingFamily.line] using hall e
  · exact fun e f => left_ne_right_of_different_colors hab e f
  · exact CrossingFamily.endpointPair_injective

theorem exists_all_central_family
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Fin 3)
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (center : Fin 3 → Fin 3 → Submodule ℝ (E d × ℝ))
    (hcenterDim : ∀ i j, i ≠ j → finrank ℝ (center i j) = 1)
    (hcenterD : ∀ i j, i ≠ j → center i j ≤ D)
    (hdistinct : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → center a b ≠ center a c)
    (hcross : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x ≠ color y → center (color x) (color y) ≤ edgeProjectiveLine x.val y.val)
    (hexterior : ∀ i j, i ≠ j → ¬ ∃ z ∈ P.toSet, homogenize z ∈ center i j)
    (w : E d) (hwP : w ∈ P.toSet) (hwD : homogenize w ∈ D)
    (hN : P.vertices.card ≤ 4 * d - 5) :
    (∀ e : CrossingFamily P color 0 1, e.line ≤ D) ∨
      (∀ e : CrossingFamily P color 0 2, e.line ≤ D) ∨
      (∀ e : CrossingFamily P color 1 2, e.line ≤ D) := by
  by_cases h01all : ∀ e : CrossingFamily P color 0 1, e.line ≤ D
  · exact Or.inl h01all
  by_cases h02all : ∀ e : CrossingFamily P color 0 2, e.line ≤ D
  · exact Or.inr (Or.inl h02all)
  by_cases h12all : ∀ e : CrossingFamily P color 1 2, e.line ≤ D
  · exact Or.inr (Or.inr h12all)
  obtain ⟨e01,he01⟩ := not_forall.mp h01all
  obtain ⟨e02,he02⟩ := not_forall.mp h02all
  obtain ⟨e12,he12⟩ := not_forall.mp h12all
  have hc (a b : Fin 3) (hab : a ≠ b) :
      ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
        color x = a → color y = b →
        center a b ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    have hne : color x ≠ color y := by simpa only [hx,hy] using hab
    simpa only [hx,hy] using hcross x y hxy hne
  have hn (a b : Fin 3) (hab : a ≠ b) :
      ∀ x ∈ P.vertices, homogenize x ∉ center a b := by
    intro x hx hxJ
    exact hexterior a b hab ⟨x,vertex_mem_body_of_mem_vertices P hx,hxJ⟩
  have hfamily (a b : Fin 3) (hab : a ≠ b) :
      ∀ e : CrossingFamily P color a b, center a b ≤ e.line := by
    intro e
    exact hc a b hab e.left e.right e.isEdge e.property.2.1 e.property.2.2
  have hlow01 := offCentral_family_card_lower_bound P hP (by omega) color
    0 1 2 (by decide) (by decide) (by decide) D (center 0 1) (center 0 2)
    hD (hcenterDim 0 1 (by decide)) (hcenterDim 0 2 (by decide))
    (hcenterD 0 1 (by decide)) (hcenterD 0 2 (by decide))
    (hdistinct 0 1 2 (by decide) (by decide) (by decide))
    (hc 0 1 (by decide)) (hc 0 2 (by decide)) ⟨e01,he01⟩
  have hlow02 := offCentral_family_card_lower_bound P hP (by omega) color
    0 2 1 (by decide) (by decide) (by decide) D (center 0 2) (center 0 1)
    hD (hcenterDim 0 2 (by decide)) (hcenterDim 0 1 (by decide))
    (hcenterD 0 2 (by decide)) (hcenterD 0 1 (by decide))
    (hdistinct 0 2 1 (by decide) (by decide) (by decide))
    (hc 0 2 (by decide)) (hc 0 1 (by decide)) ⟨e02,he02⟩
  have hlow12 := offCentral_family_card_lower_bound P hP (by omega) color
    1 2 0 (by decide) (by decide) (by decide) D (center 1 2) (center 1 0)
    hD (hcenterDim 1 2 (by decide)) (hcenterDim 1 0 (by decide))
    (hcenterD 1 2 (by decide)) (hcenterD 1 0 (by decide))
    (hdistinct 1 2 0 (by decide) (by decide) (by decide))
    (hc 1 2 (by decide)) (hc 1 0 (by decide)) ⟨e12,he12⟩
  have hle := three_family_card_le_forest_edges D (center 0 1) (center 0 2) (center 1 2)
    (hcenterDim 0 1 (by decide)) (hcenterDim 0 2 (by decide))
    (hcenterDim 1 2 (by decide)) (hcenterD 0 1 (by decide))
    (hcenterD 0 2 (by decide)) (hcenterD 1 2 (by decide))
    (hfamily 0 1 (by decide)) (hfamily 0 2 (by decide)) (hfamily 1 2 (by decide))
    (hn 0 1 (by decide)) (hn 0 2 (by decide)) (hn 1 2 (by decide))
  have hlt := actual_crossing_edge_card_lt_three_classes P hP hd color D hD
    center hcenterDim hcenterD hcross hexterior w hwP hwD hN
  omega

theorem exists_central_subsingleton_family
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Fin 3)
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (center : Fin 3 → Fin 3 → Submodule ℝ (E d × ℝ))
    (hcenterDim : ∀ i j, i ≠ j → finrank ℝ (center i j) = 1)
    (hcenterD : ∀ i j, i ≠ j → center i j ≤ D)
    (hdistinct : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → center a b ≠ center a c)
    (hcross : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x ≠ color y → center (color x) (color y) ≤ edgeProjectiveLine x.val y.val)
    (hexterior : ∀ i j, i ≠ j → ¬ ∃ z ∈ P.toSet, homogenize z ∈ center i j)
    (w : E d) (hwP : w ∈ P.toSet) (hwD : homogenize w ∈ D)
    (hN : P.vertices.card ≤ 4 * d - 5) :
    ∃ a b : Fin 3, a ≠ b ∧
      (∀ e : CrossingFamily P color a b, e.line ≤ D) ∧
      Subsingleton (CrossingFamily P color a b) := by
  rcases exists_all_central_family P hP hd color D hD center hcenterDim hcenterD
    hdistinct hcross hexterior w hwP hwD hN with h | h | h
  · exact ⟨0,1,by decide,h,central_crossing_family_subsingleton P color 0 1 (by decide) D hD h⟩
  · exact ⟨0,2,by decide,h,central_crossing_family_subsingleton P color 0 2 (by decide) D hD h⟩
  · exact ⟨1,2,by decide,h,central_crossing_family_subsingleton P color 1 2 (by decide) D hD h⟩

end Papers.Polytopes.ActualExteriorAlternative


end
end
end BundlePart32

section BundlePart33
/- Source: Papers/TransportedColorClasses.lean -/




@[expose] public section

/-! Extend vertex colors to the ambient space and transport nontrivial classes. -/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open ActualFamilyCounting CrossingFamilyTransport Papers.ActualFaceOrder
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d m : ℕ}

def vertexColorExtension (P : ConvexPolytope d) (color : P.vertices → Fin 3) :
    E d → Fin 3 :=
  fun x => if hx : x ∈ P.vertices then color ⟨x,hx⟩ else 0

@[simp] theorem vertexColorExtension_at_vertex
    (P : ConvexPolytope d) (color : P.vertices → Fin 3) (v : P.vertices) :
    vertexColorExtension P color v.val = color v := by
  simp only [vertexColorExtension,dif_pos v.property]

theorem two_points_per_color_after_face_iso
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (D : Submodule ℝ (E d × ℝ))
    (hclasses : ∀ i, 2 ≤ Fintype.card (NoncentralColor P color D i))
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    ∀ i : Fin 3, ∃ x ∈ Q.vertices, ∃ y ∈ Q.vertices,
      x ≠ y ∧ vertexColorExtension Q (colorAlong iso color) x = i ∧
        vertexColorExtension Q (colorAlong iso color) y = i := by
  intro i
  have hc : 1 < (Finset.univ : Finset (NoncentralColor P color D i)).card := by
    rw [Finset.card_univ]
    have h := hclasses i
    omega
  obtain ⟨v,hv,w,hw,hvw⟩ := Finset.one_lt_card.mp hc
  let V := vertexEquiv iso v.val
  let W := vertexEquiv iso w.val
  have hne : V.val ≠ W.val := by
    intro h
    apply hvw
    apply Subtype.ext
    exact (vertexEquiv iso).injective (Subtype.ext h)
  refine ⟨V.val,V.property,W.val,W.property,hne,?_,?_⟩
  · rw [vertexColorExtension_at_vertex]
    change color ((vertexEquiv iso).symm (vertexEquiv iso v.val)) = i
    rw [Equiv.symm_apply_apply]
    exact v.property.1
  · rw [vertexColorExtension_at_vertex]
    change color ((vertexEquiv iso).symm (vertexEquiv iso w.val)) = i
    rw [Equiv.symm_apply_apply]
    exact w.property.1

end Papers.Polytopes


end
end
end BundlePart33

section BundlePart34
/- Source: Papers/SingleCentralPersistence.lean -/







@[expose] public section

/-!
# Persistence when one crossing family is central

A genuine central edge supplies a central vertex for the sharp family
counts.  The other two families are automatically off-central and their
centers are forced in every realization.  Actual two-face reconstruction
then proves Minkowski decomposability of every face-isomorphic polytope.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily CrossingFamilyTransport ActualFamilyCounting
open ActualExteriorAlternative Papers.ActualFaceOrder
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d m : ℕ}

theorem decomposable_after_iso_of_single_central_family
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Fin 3)
    (D J01 J02 J12 : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2)
    (h01 : finrank ℝ J01 = 1) (h02 : finrank ℝ J02 = 1)
    (h12 : finrank ℝ J12 = 1)
    (h01D : J01 ≤ D) (h02D : J02 ≤ D) (h12D : J12 ≤ D)
    (h0201 : J02 ≠ J01) (h1201 : J12 ≠ J01)
    (hcross01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → J01 ≤ edgeProjectiveLine x.val y.val)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (hcross12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 1 → color y = 2 → J12 ≤ edgeProjectiveLine x.val y.val)
    (hnot02 : ∀ x ∈ P.vertices, homogenize x ∉ J02)
    (hnot12 : ∀ x ∈ P.vertices, homogenize x ∉ J12)
    (hcentral : ∀ e : CrossingFamily P color 0 1, e.line ≤ D)
    (hclasses : ∀ i, d - 1 ≤ Fintype.card (NoncentralColor P color D i))
    (hN : P.vertices.card ≤ 4 * d - 5)
    (e01 : CrossingFamily P color 0 1)
    (e02 : CrossingFamily P color 0 2)
    (e12 : CrossingFamily P color 1 2)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hoff02 : ∀ e : CrossingFamily P color 0 2, ¬ e.line ≤ D :=
    offCentral_of_different_central_colorPair D hD e01 (hcentral e01)
      (by decide : (s(0,1) : Sym2 (Fin 3)) ≠ s(0,2))
  have hoff12 : ∀ e : CrossingFamily P color 1 2, ¬ e.line ≤ D :=
    offCentral_of_different_central_colorPair D hD e01 (hcentral e01)
      (by decide : (s(0,1) : Sym2 (Fin 3)) ≠ s(1,2))
  have hwD : homogenize e01.left.val ∈ D :=
    central_edge_left_mem D e01 (hcentral e01)
  have hcross10 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 1 → color y = 0 → J01 ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    have h := hcross01 y x (actualStep_symm x.property hxy) hy hx
    simpa only [edgeProjectiveLine,Set.pair_comm] using h
  obtain ⟨K02,hK02,hK02cross,hK02out⟩ :=
    actual_offCentral_family_forced_center P hP hd color
      0 2 1 (by decide) (by decide) (by decide)
      D J02 J01 hD h02 h01 h02D h01D h0201 hcross02 hcross01
      hnot02 hoff02 e01.left hwD (hclasses 1) hN e02 Q iso
  obtain ⟨K12,hK12,hK12cross,hK12out⟩ :=
    actual_offCentral_family_forced_center P hP hd color
      1 2 0 (by decide) (by decide) (by decide)
      D J12 J01 hD h12 h01 h12D h01D h1201 hcross12 hcross10
      hnot12 hoff12 e01.left hwD (hclasses 0) hN e12 Q iso
  let colorQ := colorAlong iso color
  let labelQ := vertexColorExtension Q colorQ
  let u := (crossingEquiv iso color 0 1 e01).left
  let v := (crossingEquiv iso color 0 1 e01).right
  have hu : labelQ u.val = 0 := by
    dsimp only [labelQ]
    rw [vertexColorExtension_at_vertex]
    exact (crossingEquiv iso color 0 1 e01).property.2.1
  have hv : labelQ v.val = 1 := by
    dsimp only [labelQ]
    rw [vertexColorExtension_at_vertex]
    exact (crossingEquiv iso color 0 1 e01).property.2.2
  have huv : GeneralVertexStep Q u.val v.val :=
    (crossingEquiv iso color 0 1 e01).isEdge
  have hs := central_crossing_family_subsingleton P color 0 1 (by decide) D hD hcentral
  have hunique : ∀ x y : Q.vertices, GeneralVertexStep Q x.val y.val →
      labelQ x.val = 0 → labelQ y.val = 1 → x = u ∧ y = v := by
    intro x y hxy hx hy
    have hx' : colorQ x = 0 := by simpa only [labelQ,vertexColorExtension_at_vertex] using hx
    have hy' : colorQ y = 1 := by simpa only [labelQ,vertexColorExtension_at_vertex] using hy
    let f : CrossingFamily Q colorQ 0 1 := ⟨(x,y),hxy,hx',hy'⟩
    have hpre := hs.elim ((crossingEquiv iso color 0 1).symm f) e01
    have heq : f = crossingEquiv iso color 0 1 e01 := by
      have h := congrArg (crossingEquiv iso color 0 1) hpre
      simpa only [Equiv.apply_symm_apply] using h
    exact ⟨congrArg CrossingFamily.left heq,congrArg CrossingFamily.right heq⟩
  have hcrossQ02 : ∀ x y : Q.vertices, GeneralVertexStep Q x.val y.val →
      labelQ x.val = 0 → labelQ y.val = 2 → K02 ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    have hx' : colorQ x = 0 := by simpa only [labelQ,vertexColorExtension_at_vertex] using hx
    have hy' : colorQ y = 2 := by simpa only [labelQ,vertexColorExtension_at_vertex] using hy
    exact hK02cross ⟨(x,y),hxy,hx',hy'⟩
  have hcrossQ12 : ∀ x y : Q.vertices, GeneralVertexStep Q x.val y.val →
      labelQ x.val = 1 → labelQ y.val = 2 → K12 ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    have hx' : colorQ x = 1 := by simpa only [labelQ,vertexColorExtension_at_vertex] using hx
    have hy' : colorQ y = 2 := by simpa only [labelQ,vertexColorExtension_at_vertex] using hy
    exact hK12cross ⟨(x,y),hxy,hx',hy'⟩
  have hclassesQ : ∀ i : Fin 3, ∃ x ∈ Q.vertices, ∃ y ∈ Q.vertices,
      x ≠ y ∧ labelQ x = i ∧ labelQ y = i := by
    exact two_points_per_color_after_face_iso P color D
      (fun i => by have h := hclasses i; omega) Q iso
  have hQdim : 3 ≤ Q.dim := by
    rw [dim_eq iso]
    change 3 ≤ P.dim
    have hPd : P.dim = d := hP
    omega
  exact decomposable_of_actual_single_crossing_centers Q hQdim labelQ u v hu hv huv
    hunique K02 K12 hK02 hK12 hcrossQ02 hcrossQ12 hclassesQ

end Papers.Polytopes


end
end
end BundlePart34

section BundlePart35
/- Source: Papers/CentralFamilyReindex.lean -/



@[expose] public section

/-! Renaming three actual vertex colors preserves all geometric hypotheses. -/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily CrossingFamilyTransport ActualFamilyCounting
open Papers.ActualFaceOrder
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d m : ℕ}

def threeColorEquiv (a b c : Fin 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Fin 3 ≃ Fin 3 :=
  Equiv.ofBijective (![a,b,c] : Fin 3 → Fin 3) (by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      rcases three_colors_cover a b c hab hac hbc i with rfl | rfl | rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩)

theorem exists_third_color (a b : Fin 3) (hab : a ≠ b) :
    ∃ c : Fin 3, a ≠ c ∧ b ≠ c := by
  fin_cases a <;> fin_cases b <;> first | exact (hab rfl).elim | decide

def noncentralColorReindex
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (D : Submodule ℝ (E d × ℝ)) (σ : Fin 3 ≃ Fin 3) (i : Fin 3) :
    NoncentralColor P (fun v => σ.symm (color v)) D i ≃
      NoncentralColor P color D (σ i) where
  toFun v := ⟨v.val,by
    constructor
    · have h := congrArg σ v.property.1
      simpa only [Equiv.apply_symm_apply] using h
    · exact v.property.2⟩
  invFun v := ⟨v.val,by
    constructor
    · change σ.symm (color v.val) = i
      rw [v.property.1,Equiv.symm_apply_apply]
    · exact v.property.2⟩
  left_inv := by intro v; rfl
  right_inv := by intro v; rfl

theorem decomposable_after_iso_of_central_family
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Fin 3)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (center : Fin 3 → Fin 3 → Submodule ℝ (E d × ℝ))
    (hcenterDim : ∀ i j, i ≠ j → finrank ℝ (center i j) = 1)
    (hcenterD : ∀ i j, i ≠ j → center i j ≤ D)
    (hsymm : ∀ i j, center i j = center j i)
    (hdistinct : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → center a b ≠ center a c)
    (hcross : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x ≠ color y → center (color x) (color y) ≤ edgeProjectiveLine x.val y.val)
    (hnotvertex : ∀ i j, i ≠ j → ∀ x ∈ P.vertices, homogenize x ∉ center i j)
    (hcentral : ∀ e : CrossingFamily P color a b, e.line ≤ D)
    (hclasses : ∀ i, d - 1 ≤ Fintype.card (NoncentralColor P color D i))
    (hN : P.vertices.card ≤ 4 * d - 5)
    (eab : CrossingFamily P color a b)
    (eac : CrossingFamily P color a c)
    (ebc : CrossingFamily P color b c)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  let σ := threeColorEquiv a b c hab hac hbc
  let col : P.vertices → Fin 3 := fun v => σ.symm (color v)
  have hσ0 : σ 0 = a := rfl
  have hσ1 : σ 1 = b := rfl
  have hσ2 : σ 2 = c := rfl
  have hcol (v : P.vertices) (i : Fin 3) : col v = i ↔ color v = σ i := by
    constructor
    · intro h
      have hh := congrArg σ h
      simpa only [col,Equiv.apply_symm_apply] using hh
    · intro h
      change σ.symm (color v) = i
      rw [h,Equiv.symm_apply_apply]
  let E01 : CrossingFamily P col 0 1 :=
    ⟨(eab.left,eab.right),eab.isEdge,
      (hcol _ 0).mpr (by rw [hσ0]; exact eab.property.2.1),
      (hcol _ 1).mpr (by rw [hσ1]; exact eab.property.2.2)⟩
  let E02 : CrossingFamily P col 0 2 :=
    ⟨(eac.left,eac.right),eac.isEdge,
      (hcol _ 0).mpr (by rw [hσ0]; exact eac.property.2.1),
      (hcol _ 2).mpr (by rw [hσ2]; exact eac.property.2.2)⟩
  let E12 : CrossingFamily P col 1 2 :=
    ⟨(ebc.left,ebc.right),ebc.isEdge,
      (hcol _ 1).mpr (by rw [hσ1]; exact ebc.property.2.1),
      (hcol _ 2).mpr (by rw [hσ2]; exact ebc.property.2.2)⟩
  have hcrossAt (i j : Fin 3) (hij : i ≠ j) :
      ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
        col x = i → col y = j →
        center (σ i) (σ j) ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    have hx' := (hcol x i).mp hx
    have hy' := (hcol y j).mp hy
    have hneq : color x ≠ color y := by
      rw [hx',hy']
      exact σ.injective.ne hij
    simpa only [hx',hy'] using hcross x y hxy hneq
  have hcentral' : ∀ e : CrossingFamily P col 0 1, e.line ≤ D := by
    intro e
    have hl : color e.left = a := by
      simpa only [hσ0] using (hcol e.left 0).mp e.property.2.1
    have hr : color e.right = b := by
      simpa only [hσ1] using (hcol e.right 1).mp e.property.2.2
    exact hcentral ⟨(e.left,e.right),e.isEdge,hl,hr⟩
  have hclasses' : ∀ i, d - 1 ≤ Fintype.card (NoncentralColor P col D i) := by
    intro i
    rw [Fintype.card_congr (noncentralColorReindex P color D σ i)]
    exact hclasses (σ i)
  have hca : center a c ≠ center a b :=
    hdistinct a c b hac hab hbc.symm
  have hcb : center b c ≠ center a b := by
    rw [hsymm a b]
    exact hdistinct b c a hbc hab.symm hac.symm
  apply decomposable_after_iso_of_single_central_family P hP hd col D
    (center a b) (center a c) (center b c) hD
    (hcenterDim a b hab) (hcenterDim a c hac) (hcenterDim b c hbc)
    (hcenterD a b hab) (hcenterD a c hac) (hcenterD b c hbc) hca hcb
  · simpa only [hσ0,hσ1] using hcrossAt 0 1 (by decide)
  · simpa only [hσ0,hσ2] using hcrossAt 0 2 (by decide)
  · simpa only [hσ1,hσ2] using hcrossAt 1 2 (by decide)
  · exact hnotvertex a c hac
  · exact hnotvertex b c hbc
  · exact hcentral'
  · exact hclasses'
  · exact hN
  · exact E01
  · exact E02
  · exact E12
  · exact iso

end Papers.Polytopes


end
end
end BundlePart35

section BundlePart36
/- Source: Papers/ThreeExteriorPersistence.lean -/




@[expose] public section

/-!
# The complete exterior-center branch of Proposition 11

This theorem starts with actual three-center crossing data on P. Every
graph, face, counting, concurrence, and realization-transport argument is
then constructed. No combinatorial geometry certificate is an input.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily ActualFamilyCounting ActualExteriorAlternative
open Papers.ActualFaceOrder
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d m : ℕ}

theorem decomposable_after_iso_of_three_exterior_centers
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Fin 3)
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (center : Fin 3 → Fin 3 → Submodule ℝ (E d × ℝ))
    (hcenterDim : ∀ i j, i ≠ j → finrank ℝ (center i j) = 1)
    (hcenterD : ∀ i j, i ≠ j → center i j ≤ D)
    (hsymm : ∀ i j, center i j = center j i)
    (hdistinct : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → center a b ≠ center a c)
    (hcross : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x ≠ color y → center (color x) (color y) ≤ edgeProjectiveLine x.val y.val)
    (hexterior : ∀ i j, i ≠ j → ¬ ∃ z ∈ P.toSet, homogenize z ∈ center i j)
    (w : E d) (hwP : w ∈ P.toSet) (hwD : homogenize w ∈ D)
    (hclasses : ∀ i, d - 1 ≤ Fintype.card (NoncentralColor P color D i))
    (hfamilies : ∀ i j, i ≠ j → Nonempty (CrossingFamily P color i j))
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  obtain ⟨a,b,hab,hcentral,hsingle⟩ :=
    exists_central_subsingleton_family P hP hd color D hD center hcenterDim
      hcenterD hdistinct hcross hexterior w hwP hwD hN
  obtain ⟨c,hac,hbc⟩ := exists_third_color a b hab
  have hnotvertex : ∀ i j, i ≠ j → ∀ x ∈ P.vertices, homogenize x ∉ center i j := by
    intro i j hij x hx hxJ
    exact hexterior i j hij ⟨x,vertex_mem_body_of_mem_vertices P hx,hxJ⟩
  exact decomposable_after_iso_of_central_family P hP hd color a b c hab hac hbc
    D hD center hcenterDim hcenterD hsymm hdistinct hcross hnotvertex hcentral
    hclasses hN (Classical.choice (hfamilies a b hab))
    (Classical.choice (hfamilies a c hac)) (Classical.choice (hfamilies b c hbc))
    Q iso

end Papers.Polytopes


end
end
end BundlePart36

section BundlePart37
/- Source: Papers/ThreeNonvertexPersistence.lean -/





@[expose] public section

/-!
# The nonvertex-center branch of Proposition 11

An interior center first gives a sole actual crossing edge, whose incident
two-faces place the central line on that edge.  If every center is exterior,
the actual forest argument supplies the same central-family alternative.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily ActualFamilyCounting Papers.ActualFaceOrder
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d m : ℕ}

theorem subsingleton_crossing_family_is_central
    (P : ConvexPolytope d) (hdim : 3 ≤ P.dim)
    (color : P.vertices → Fin 3)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (center : Fin 3 → Fin 3 → Submodule ℝ (E d × ℝ))
    (hcenterDim : ∀ i j, i ≠ j → finrank ℝ (center i j) = 1)
    (hcenterD : ∀ i j, i ≠ j → center i j ≤ D)
    (hsymm : ∀ i j, center i j = center j i)
    (hdistinct : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → center a b ≠ center a c)
    (hcross : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x ≠ color y → center (color x) (color y) ≤ edgeProjectiveLine x.val y.val)
    (hsingle : Subsingleton (CrossingFamily P color a b))
    (eab : CrossingFamily P color a b) :
    ∀ e : CrossingFamily P color a b, e.line ≤ D := by
  let σ := threeColorEquiv a b c hab hac hbc
  let col : P.vertices → Fin 3 := fun v => σ.symm (color v)
  have hσ0 : σ 0 = a := rfl
  have hσ1 : σ 1 = b := rfl
  have hσ2 : σ 2 = c := rfl
  have hcol (v : P.vertices) (i : Fin 3) : col v = i ↔ color v = σ i := by
    constructor
    · intro h
      have hh := congrArg σ h
      simpa only [col,Equiv.apply_symm_apply] using hh
    · intro h
      change σ.symm (color v) = i
      rw [h,Equiv.symm_apply_apply]
  let E01 : CrossingFamily P col 0 1 :=
    ⟨(eab.left,eab.right),eab.isEdge,
      (hcol _ 0).mpr (by rw [hσ0]; exact eab.property.2.1),
      (hcol _ 1).mpr (by rw [hσ1]; exact eab.property.2.2)⟩
  have hcrossAt (i j : Fin 3) (hij : i ≠ j) :
      ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
        col x = i → col y = j →
        center (σ i) (σ j) ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    have hx' := (hcol x i).mp hx
    have hy' := (hcol y j).mp hy
    have hneq : color x ≠ color y := by
      rw [hx',hy']
      exact σ.injective.ne hij
    simpa only [hx',hy'] using hcross x y hxy hneq
  have hunique : ∀ f : CrossingFamily P col 0 1, f = E01 := by
    intro f
    have hl : color f.left = a := by
      simpa only [hσ0] using (hcol f.left 0).mp f.property.2.1
    have hr : color f.right = b := by
      simpa only [hσ1] using (hcol f.right 1).mp f.property.2.2
    let old : CrossingFamily P color a b := ⟨(f.left,f.right),f.isEdge,hl,hr⟩
    have heq := hsingle.elim old eab
    apply Subtype.ext
    have hv : (f.left,f.right) = (eab.left,eab.right) :=
      congrArg (fun e : CrossingFamily P color a b => (e.left,e.right)) heq
    exact hv
  have hne : center a c ≠ center b c := by
    rw [hsymm a c,hsymm b c]
    exact hdistinct c a b hac.symm hbc.symm hab
  have heq : E01.line = D :=
    single_crossing_edge_spans_central_line P hdim col D
      (center a c) (center b c) hD
      (hcenterDim a c hac) (hcenterDim b c hbc)
      (hcenterD a c hac) (hcenterD b c hbc) hne
      (by simpa only [hσ0,hσ2] using hcrossAt 0 2 (by decide))
      (by simpa only [hσ1,hσ2] using hcrossAt 1 2 (by decide)) E01 hunique
  have heab : eab.line = D := heq
  intro e
  rw [hsingle.elim e eab,heab]

theorem decomposable_after_iso_of_three_nonvertex_centers
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Fin 3)
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (center : Fin 3 → Fin 3 → Submodule ℝ (E d × ℝ))
    (hcenterDim : ∀ i j, i ≠ j → finrank ℝ (center i j) = 1)
    (hcenterD : ∀ i j, i ≠ j → center i j ≤ D)
    (hsymm : ∀ i j, center i j = center j i)
    (hdistinct : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → center a b ≠ center a c)
    (hcross : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x ≠ color y → center (color x) (color y) ≤ edgeProjectiveLine x.val y.val)
    (hnotvertex : ∀ i j, i ≠ j → ∀ x ∈ P.vertices, homogenize x ∉ center i j)
    (w : E d) (hwP : w ∈ P.toSet) (hwD : homogenize w ∈ D)
    (hclasses : ∀ i, d - 1 ≤ Fintype.card (NoncentralColor P color D i))
    (hfamilies : ∀ i j, i ≠ j → Nonempty (CrossingFamily P color i j))
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  by_cases hexterior : ∀ i j, i ≠ j → ¬ ∃ z ∈ P.toSet, homogenize z ∈ center i j
  · exact decomposable_after_iso_of_three_exterior_centers P hP hd color D hD center
      hcenterDim hcenterD hsymm hdistinct hcross hexterior w hwP hwD
      hclasses hfamilies hN Q iso
  push_neg at hexterior
  obtain ⟨a,b,hab,z,hzP,hzJ⟩ := hexterior
  obtain ⟨c,hac,hbc⟩ := exists_third_color a b hab
  let eab := Classical.choice (hfamilies a b hab)
  have hcenter : ∀ e : CrossingFamily P color a b, center a b ≤ e.line := by
    intro e
    have hl : color e.left = a := e.property.2.1
    have hr : color e.right = b := e.property.2.2
    have hne : color e.left ≠ color e.right := by
      rw [hl,hr]
      exact hab
    simpa only [hl,hr,CrossingFamily.line] using
      hcross e.left e.right e.isEdge hne
  have hunique := singleton_family_of_inside_nonvertex_center hab (center a b)
    hcenter (hnotvertex a b hab) ⟨z,hzP,hzJ⟩ eab
  have hsingle : Subsingleton (CrossingFamily P color a b) :=
    ⟨fun e f => (hunique e).trans (hunique f).symm⟩
  have hPdim : 3 ≤ P.dim := by
    have hPd : P.dim = d := hP
    omega
  have hcentral := subsingleton_crossing_family_is_central P hPdim color a b c
    hab hac hbc D hD center hcenterDim hcenterD hsymm hdistinct hcross hsingle eab
  exact decomposable_after_iso_of_central_family P hP hd color a b c hab hac hbc
    D hD center hcenterDim hcenterD hsymm hdistinct hcross hnotvertex hcentral
    hclasses hN eab (Classical.choice (hfamilies a c hac))
    (Classical.choice (hfamilies b c hbc)) Q iso

end Papers.Polytopes


end
end
end BundlePart37

section BundlePart38
/- Source: Papers/StarTwoFaceObstruction.lean -/





@[expose] public section

/-!
# A two-face at a star excludes the third color

If a two-face uses one color-zero and one color-one edge at a zero-colored
star vertex, cut parity supplies a zero-two edge in that face. A nonvertex
center common to all zero-two edges then forces every zero-two edge at the
star into this face, which would create three incident edges in a polygon.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open ExposedProjectiveBridge HomogeneousFaceSpans CrossingLineGeometry
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem twoFace_no_three_incident_edges
    (P : ConvexPolytope d) (F : Set (E d)) (hdim : faceDim F = 2)
    (u p q v : P.vertices)
    (huF : u.val ∈ F) (hpF : p.val ∈ F) (hqF : q.val ∈ F) (hvF : v.val ∈ F)
    (hpq : p ≠ q) (hpv : p ≠ v) (hqv : q ≠ v)
    (hup : GeneralVertexStep P u.val p.val)
    (huq : GeneralVertexStep P u.val q.val)
    (huv : GeneralVertexStep P u.val v.val) : False := by
  have hsub : ({u.val,p.val,q.val,v.val} : Set (E d)) ⊆ F := by
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hplane : finrank ℝ
      (vectorSpan ℝ ({u.val,p.val,q.val,v.val} : Set (E d))) ≤ 2 := by
    have h := Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
    change _ ≤ faceDim F at h
    simpa only [hdim] using h
  exact no_three_actual_edges_in_plane P u.property p.property q.property v.property
    (fun h => hpq (Subtype.ext h)) (fun h => hpv (Subtype.ext h))
    (fun h => hqv (Subtype.ext h)) hup huq huv hplane

theorem no_two_neighbor_from_star_twoFace
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (u p q : P.vertices)
    (hu : color u = 0) (hp : color p = 0) (hq : color q = 1)
    (hup : GeneralVertexStep P u.val p.val)
    (huq : GeneralVertexStep P u.val q.val)
    (hstar : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → x = u ∨ y = u)
    (J02 : Submodule ℝ (E d × ℝ)) (h02 : finrank ℝ J02 = 1)
    (hunot : homogenize u.val ∉ J02)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (F : Set (E d)) (hF : P.IsFace F) (hdim : faceDim F = 2)
    (huF : u.val ∈ F) (hpF : p.val ∈ F) (hqF : q.val ∈ F) :
    ∀ v : P.vertices, GeneralVertexStep P u.val v.val → color v ≠ 2 := by
  intro v huv hv
  obtain ⟨h02edge,_⟩ := twoFace_star_contains_other_families P F hF hdim
    color u p q huF hpF hqF hu hp hq hup huq hstar
  obtain ⟨a,b,haF,hbF,hab,ha,hb⟩ := h02edge
  have hJH : J02 ≤ homogeneousSpan F :=
    (hcross02 a b hab ha hb).trans (line_le_span haF hbF)
  let U : Submodule ℝ (E d × ℝ) := Submodule.span ℝ {homogenize u.val}
  let L : Submodule ℝ (E d × ℝ) := edgeProjectiveLine u.val v.val
  have hU : finrank ℝ U = 1 := finrank_span_singleton
    (ExposedEdgeCenters.point_ne_zero u.val)
  have hL : finrank ℝ L = 2 := by
    change finrank ℝ (edgeProjectiveLine u.val v.val) = 2
    rw [← exposed_edgeLine_eq_edgeProjectiveLine]
    exact ExposedLineRanks.edgeLine_finrank_eq_two huv.2.1
  have hUL : U ≤ L := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact point_mem_span (Set.mem_insert u.val {v.val})
  have hUH : U ≤ homogeneousSpan F := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact point_mem_span huF
  have hJL : J02 ≤ L := hcross02 u v huv hu hv
  have hne : U ≠ J02 := by
    intro heq
    apply hunot
    rw [← heq]
    exact Submodule.mem_span_singleton_self _
  have hsum : U ⊔ J02 = L :=
    sup_eq_plane_of_distinct_points L U J02 hL hU h02 hUL hJL hne
  have hLH : L ≤ homogeneousSpan F := by
    rw [← hsum]
    exact sup_le hUH hJH
  have hvH : homogenize v.val ∈ homogeneousSpan F :=
    hLH (point_mem_span (Set.mem_insert_of_mem u.val (Set.mem_singleton v.val)))
  have hvF := actual_vertex_mem_face_of_homogeneousSpan P F hF v.property hvH
  have hpq : p ≠ q := by
    intro h; have hc := congrArg color h; rw [hp,hq] at hc; exact (by decide : (0 : Fin 3) ≠ 1) hc
  have hpv : p ≠ v := by
    intro h; have hc := congrArg color h; rw [hp,hv] at hc; exact (by decide : (0 : Fin 3) ≠ 2) hc
  have hqv : q ≠ v := by
    intro h; have hc := congrArg color h; rw [hq,hv] at hc; exact (by decide : (1 : Fin 3) ≠ 2) hc
  exact twoFace_no_three_incident_edges P F hdim u p q v
    huF hpF hqF hvF hpq hpv hqv hup huq huv

end Papers.Polytopes


end
end
end BundlePart38

section BundlePart39
/- Source: Papers/StarThirdColorExclusion.lean -/






@[expose] public section

/-!
# A vertex center has no third-color neighbor

The proof uses the actual vertex figure and intrinsic Balinski connectivity
after deleting its possible third-color vertex. Matching at the nonvertex
zero-two center shows that this deleted vertex is the only one of its color.
A crossing edge in the remaining figure then supplies the obstructing
two-face in the original polytope.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open ActualVertexFigure
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem star_has_no_color_two_neighbors
    (P : ConvexPolytope d) (hdim : 3 ≤ P.dim)
    (color : P.vertices → Fin 3) (u p q : P.vertices)
    (hu : color u = 0) (hp : color p = 0) (hq : color q = 1)
    (hup : GeneralVertexStep P u.val p.val)
    (huq : GeneralVertexStep P u.val q.val)
    (hstar : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → x = u ∨ y = u)
    (J02 : Submodule ℝ (E d × ℝ)) (h02 : finrank ℝ J02 = 1)
    (hnotvertex : ∀ x ∈ P.vertices, homogenize x ∉ J02)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val) :
    ∀ v : P.vertices, GeneralVertexStep P u.val v.val → color v ≠ 2 := by
  intro v huv hv
  have hc : ∀ e : CrossingFamily P color 0 2, J02 ≤ e.line :=
    fun e => hcross02 e.left e.right e.isEdge e.property.2.1 e.property.2.2
  have hleftinj :=
    (CrossingFamily.endpoint_injections_of_nonvertex_center J02 h02 hc hnotvertex).1
  have hunique (w : P.vertices) (huw : GeneralVertexStep P u.val w.val)
      (hw : color w = 2) : w = v := by
    let ew : CrossingFamily P color 0 2 := ⟨(u,w),huw,hu,hw⟩
    let ev : CrossingFamily P color 0 2 := ⟨(u,v),huv,hu,hv⟩
    have heq : ew = ev := hleftinj rfl
    exact congrArg (fun e : CrossingFamily P color 0 2 => e.right) heq
  obtain ⟨D⟩ := exists_figure P u.property (by omega)
  let Q := D.figure
  have hQdim : Q.dim + 1 = P.dim :=
    D.figure_dim_add_one (toSet_isFace P)
      (vertex_mem_body_of_mem_vertices P u.property) (by change 1 ≤ P.dim; omega)
  have hQtwo : 2 ≤ Q.dim := by omega
  let equi := neighborEquiv D u.property
  let col : Q.vertices → Fin 3 :=
    fun z => color (neighborVertex P u.val (equi.symm z))
  let pn := asNeighbor P p hup
  let qn := asNeighbor P q huq
  let vn := asNeighbor P v huv
  have hcol (z : Papers.PolytopeVertexCone.actualNeighbors P u.val) :
      col (equi z) = color (neighborVertex P u.val z) := by
    simp only [col,equi.symm_apply_apply]
  have hcp : col (equi pn) = 0 := by
    rw [hcol]
    exact hp
  have hcq : col (equi qn) = 1 := by
    rw [hcol]
    exact hq
  have hcv : col (equi vn) = 2 := by
    rw [hcol]
    exact hv
  let S : Finset (E d) := {(equi vn).val}
  let I := {z : Q.vertices // z.val ∉ S}
  have hpI : (equi pn).val ∉ S := by
    intro h
    have he : equi pn = equi vn := Subtype.ext (Finset.mem_singleton.mp h)
    have hh := congrArg col he
    rw [hcp,hcv] at hh
    exact (by decide : (0 : Fin 3) ≠ 2) hh
  have hqI : (equi qn).val ∉ S := by
    intro h
    have he : equi qn = equi vn := Subtype.ext (Finset.mem_singleton.mp h)
    have hh := congrArg col he
    rw [hcq,hcv] at hh
    exact (by decide : (1 : Fin 3) ≠ 2) hh
  let pI : I := ⟨equi pn,hpI⟩
  let qI : I := ⟨equi qn,hqI⟩
  have hno2 (z : I) : col z.val ≠ 2 := by
    intro hz2
    have hworder : neighborVertex P u.val (equi.symm z.val) = v :=
      hunique _ (neighbor_step P u.val (equi.symm z.val)) hz2
    have hneigh : equi.symm z.val = vn := by
      apply Subtype.ext
      change (equi.symm z.val).val = v.val
      exact congrArg (fun w : P.vertices => w.val) hworder
    have hz : z.val = equi vn := by
      rw [← hneigh]
      exact (equi.apply_symm_apply z.val).symm
    apply z.property
    change z.val.val ∈ ({(equi vn).val} : Finset (E d))
    rw [hz]
    exact Finset.mem_singleton_self _
  let G := (Papers.PolytopeBalinski.vertexGraph Q).induce {z : Q.vertices | z.val ∉ S}
  have hconnected : G.Connected :=
    Papers.PolytopeBalinski.deleted_vertexGraph_connected Q S
      (by simpa only [S,Finset.card_singleton] using (show 1 < Q.dim by omega))
  let A : Set I := {z | col z.val = 0}
  have hpA : pI ∈ A := hcp
  have hqA : qI ∉ A := by
    change col (equi qn) ≠ 0
    rw [hcq]
    decide
  obtain ⟨a,ha,b,hb,hab⟩ :=
    ThreeColorVertexFigure.crossing_edge_of_reachable G A hpA hqA (hconnected pI qI)
  have hca : col a.val = 0 := ha
  have hcb : col b.val = 1 := by
    have hcnot0 : col b.val ≠ 0 := hb
    have hcnot2 := hno2 b
    have hcases (c : Fin 3) : c = 0 ∨ c = 1 ∨ c = 2 := by
      fin_cases c <;> simp
    rcases hcases (col b.val) with h0 | h1 | h2
    · exact (hcnot0 h0).elim
    · exact h1
    · exact (hcnot2 h2).elim
  let an := equi.symm a.val
  let bn := equi.symm b.val
  let av := neighborVertex P u.val an
  let bv := neighborVertex P u.val bn
  have hane : an ≠ bn := by
    intro he
    have hh := congrArg (fun z => color (neighborVertex P u.val z)) he
    change col a.val = col b.val at hh
    rw [hca,hcb] at hh
    exact (by decide : (0 : Fin 3) ≠ 1) hh
  have hfig : GeneralVertexStep Q (neighborImage D u.property an).val
      (neighborImage D u.property bn).val := by
    have haim : neighborImage D u.property an = a.val := equi.apply_symm_apply a.val
    have hbim : neighborImage D u.property bn = b.val := equi.apply_symm_apply b.val
    rw [haim,hbim]
    exact hab
  obtain ⟨F,hF,hFdim,huF,haF,hbF⟩ :=
    (figure_edge_iff_twoFace D u.property an bn hane).mp hfig
  have hforbid := no_two_neighbor_from_star_twoFace P color u av bv
    hu hca hcb (neighbor_step P u.val an) (neighbor_step P u.val bn)
    hstar J02 h02 (hnotvertex u.val u.property) hcross02
    F hF hFdim huF haF hbF
  exact hforbid v huv hv

end Papers.Polytopes


end
end
end BundlePart39

section BundlePart40
/- Source: Papers/ActualStarWitnesses.lean -/





@[expose] public section

/-!
# Two actual star-face witnesses

Intrinsic two-connectivity of the genuine vertex figure supplies two
distinct crossings of the zero/one cut. Their lifted two-faces are distinct:
in one polygon there are only two incident edges at its base vertex.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open ActualVertexFigure
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

structure StarFaceWitness (P : ConvexPolytope d)
    (color : P.vertices → Fin 3) (u : P.vertices) where
  zeroNeighbor : P.vertices
  oneNeighbor : P.vertices
  color_zero : color zeroNeighbor = 0
  color_one : color oneNeighbor = 1
  edge_zero : GeneralVertexStep P u.val zeroNeighbor.val
  edge_one : GeneralVertexStep P u.val oneNeighbor.val
  face : Set (E d)
  isFace : P.IsFace face
  dimension : faceDim face = 2
  center_mem : u.val ∈ face
  zero_mem : zeroNeighbor.val ∈ face
  one_mem : oneNeighbor.val ∈ face

namespace StarFaceWitness

theorem neighbors_eq_of_face_eq
    {P : ConvexPolytope d} {color : P.vertices → Fin 3} {u : P.vertices}
    (W V : StarFaceWitness P color u) (hface : W.face = V.face) :
    W.zeroNeighbor = V.zeroNeighbor ∧ W.oneNeighbor = V.oneNeighbor := by
  have h01 : W.zeroNeighbor ≠ W.oneNeighbor := by
    intro h
    have hc := congrArg color h
    rw [W.color_zero,W.color_one] at hc
    exact (by decide : (0 : Fin 3) ≠ 1) hc
  constructor
  · by_contra hzero
    have h10 : W.oneNeighbor ≠ V.zeroNeighbor := by
      intro h
      have hc := congrArg color h
      rw [W.color_one,V.color_zero] at hc
      exact (by decide : (1 : Fin 3) ≠ 0) hc
    have hvF : V.zeroNeighbor.val ∈ W.face := by rw [hface]; exact V.zero_mem
    exact twoFace_no_three_incident_edges P W.face W.dimension u
      W.zeroNeighbor W.oneNeighbor V.zeroNeighbor W.center_mem W.zero_mem W.one_mem hvF
      h01 hzero h10 W.edge_zero W.edge_one V.edge_zero
  · by_contra hone
    have h01' : W.zeroNeighbor ≠ V.oneNeighbor := by
      intro h
      have hc := congrArg color h
      rw [W.color_zero,V.color_one] at hc
      exact (by decide : (0 : Fin 3) ≠ 1) hc
    have hvF : V.oneNeighbor.val ∈ W.face := by rw [hface]; exact V.one_mem
    exact twoFace_no_three_incident_edges P W.face W.dimension u
      W.zeroNeighbor W.oneNeighbor V.oneNeighbor W.center_mem W.zero_mem W.one_mem hvF
      h01 h01' hone W.edge_zero W.edge_one V.edge_one

end StarFaceWitness

theorem exists_two_starFaceWitnesses
    (P : ConvexPolytope d) (hdim : 3 ≤ P.dim)
    (color : P.vertices → Fin 3) (u p q : P.vertices)
    (hp : color p = 0) (hq : color q = 1)
    (hup : GeneralVertexStep P u.val p.val)
    (huq : GeneralVertexStep P u.val q.val)
    (hno2 : ∀ v : P.vertices, GeneralVertexStep P u.val v.val → color v ≠ 2) :
    ∃ W V : StarFaceWitness P color u, W.face ≠ V.face := by
  obtain ⟨D⟩ := exists_figure P u.property (by omega)
  let Q := D.figure
  have hQdim : Q.dim + 1 = P.dim :=
    D.figure_dim_add_one (toSet_isFace P)
      (vertex_mem_body_of_mem_vertices P u.property) (by change 1 ≤ P.dim; omega)
  have hQtwo : 2 ≤ Q.dim := by omega
  let equi := neighborEquiv D u.property
  let col : Q.vertices → Fin 3 :=
    fun z => color (neighborVertex P u.val (equi.symm z))
  let G := Papers.PolytopeBalinski.vertexGraph Q
  have hdegree (z : Q.vertices) :
      ∃ a b : Q.vertices, a ≠ b ∧ G.Adj z a ∧ G.Adj z b := by
    have hc := actual_neighbor_card_ge_dim Q z.property
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp
      (by omega : 1 < (Papers.PolytopeVertexCone.actualNeighbors Q z.val).card)
    have hza : GeneralVertexStep Q z.val a := (Finset.mem_filter.mp ha).2
    have hzb : GeneralVertexStep Q z.val b := (Finset.mem_filter.mp hb).2
    exact ⟨⟨a,hza.1⟩,⟨b,hzb.1⟩,
      (fun h => hab (congrArg Subtype.val h)),hza,hzb⟩
  let A : Set Q.vertices := {z | col z = 0}
  have hA : A.Nonempty := by
    refine ⟨equi (asNeighbor P p hup),?_⟩
    change color (neighborVertex P u.val
      (equi.symm (equi (asNeighbor P p hup)))) = 0
    rw [equi.symm_apply_apply]
    exact hp
  have hAc : Aᶜ.Nonempty := by
    refine ⟨equi (asNeighbor P q huq),?_⟩
    change color (neighborVertex P u.val
      (equi.symm (equi (asNeighbor P q huq)))) ≠ 0
    rw [equi.symm_apply_apply]
    change color q ≠ 0
    rw [hq]
    decide
  obtain ⟨a,b,c,e,ha,hb,hc,he,hab,hce,hdiff⟩ :=
    ThreeColorVertexFigure.two_crossing_edges G
      (Papers.PolytopeBalinski.vertexGraph_preconnected Q)
      (Papers.PolytopeBalinski.vertexGraph_delete_one_preconnected Q hQtwo)
      hdegree A hA hAc
  have color_one (z : Q.vertices) (hz : z ∉ A) : col z = 1 := by
    have hnot0 : col z ≠ 0 := hz
    have hnot2 : col z ≠ 2 :=
      hno2 (neighborVertex P u.val (equi.symm z))
        (neighbor_step P u.val (equi.symm z))
    have hcases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
      fin_cases i <;> simp
    rcases hcases (col z) with h0 | h1 | h2
    · exact (hnot0 h0).elim
    · exact h1
    · exact (hnot2 h2).elim
  have makeWitness (r s : Q.vertices) (hr : r ∈ A) (hs : s ∉ A) (hrs : G.Adj r s) :
      ∃ W : StarFaceWitness P color u,
        W.zeroNeighbor = neighborVertex P u.val (equi.symm r) ∧
        W.oneNeighbor = neighborVertex P u.val (equi.symm s) := by
    have hne : equi.symm r ≠ equi.symm s := by
      intro h
      have heq : r = s := equi.symm.injective h
      exact hs (heq ▸ hr)
    have himage_r : neighborImage D u.property (equi.symm r) = r :=
      equi.apply_symm_apply r
    have himage_s : neighborImage D u.property (equi.symm s) = s :=
      equi.apply_symm_apply s
    have hstep : GeneralVertexStep Q
        (neighborImage D u.property (equi.symm r)).val
        (neighborImage D u.property (equi.symm s)).val := by
      rw [himage_r,himage_s]
      exact hrs
    obtain ⟨F,hF,hFdim,huF,hrF,hsF⟩ :=
      (figure_edge_iff_twoFace D u.property (equi.symm r) (equi.symm s) hne).mp hstep
    exact ⟨
      { zeroNeighbor := neighborVertex P u.val (equi.symm r)
        oneNeighbor := neighborVertex P u.val (equi.symm s)
        color_zero := hr
        color_one := color_one s hs
        edge_zero := neighbor_step P u.val (equi.symm r)
        edge_one := neighbor_step P u.val (equi.symm s)
        face := F
        isFace := hF
        dimension := hFdim
        center_mem := huF
        zero_mem := hrF
        one_mem := hsF },rfl,rfl⟩
  obtain ⟨W,hWa,hWb⟩ := makeWitness a b ha hb hab
  obtain ⟨V,hVc,hVe⟩ := makeWitness c e hc he hce
  refine ⟨W,V,?_⟩
  intro hface
  obtain ⟨hzero,hone⟩ := W.neighbors_eq_of_face_eq V hface
  have hac : a = c := by
    apply equi.symm.injective
    apply Subtype.ext
    have h := congrArg Subtype.val (hWa.symm.trans (hzero.trans hVc))
    exact h
  have hbe : b = e := by
    apply equi.symm.injective
    apply Subtype.ext
    have h := congrArg Subtype.val (hWb.symm.trans (hone.trans hVe))
    exact h
  rcases hdiff with h | h
  · exact h hac
  · exact h hbe

theorem decomposable_of_actual_star_centers
    (P : ConvexPolytope d) (hdim : 3 ≤ P.dim) (label : E d → Fin 3)
    (u p q : P.vertices)
    (hu : label u.val = 0) (hp : label p.val = 0) (hq : label q.val = 1)
    (hup : GeneralVertexStep P u.val p.val)
    (huq : GeneralVertexStep P u.val q.val)
    (hstar : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 1 → x = u ∨ y = u)
    (J02 J12 : Submodule ℝ (E d × ℝ))
    (h02 : finrank ℝ J02 = 1) (h12 : finrank ℝ J12 = 1)
    (hnotvertex02 : ∀ x ∈ P.vertices, homogenize x ∉ J02)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 0 → label y.val = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (hcross12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      label x.val = 1 → label y.val = 2 → J12 ≤ edgeProjectiveLine x.val y.val)
    (hclasses : ∀ i : Fin 3, ∃ x ∈ P.vertices, ∃ y ∈ P.vertices,
      x ≠ y ∧ label x = i ∧ label y = i) :
    MinkowskiDecomposable P := by
  let color : P.vertices → Fin 3 := fun v => label v.val
  have hno2 := star_has_no_color_two_neighbors P hdim color u p q hu hp hq hup huq
    hstar J02 h02 hnotvertex02 hcross02
  obtain ⟨W,V,hWV⟩ := exists_two_starFaceWitnesses P hdim color u p q
    hp hq hup huq hno2
  exact decomposable_of_star_twoFace_witnesses P label u
    W.zeroNeighbor W.oneNeighbor V.zeroNeighbor V.oneNeighbor
    hu W.color_zero W.color_one V.color_zero V.color_one
    W.edge_zero W.edge_one V.edge_zero V.edge_one hstar
    W.face V.face W.isFace V.isFace W.dimension V.dimension hWV
    W.center_mem W.zero_mem W.one_mem V.center_mem V.zero_mem V.one_mem
    J02 J12 h02 h12 hcross02 hcross12 hclasses

end Papers.Polytopes


end
end
end BundlePart40

section BundlePart41
/- Source: Papers/UniqueVertexCenter.lean -/




@[expose] public section

/-!
# At most one of the three crossing centers is an actual vertex

The two center vertices form an actual vertex cut isolating the shared
color. Noncentral witnesses survive the cut, contradicting intrinsic
Balinski connectivity. Colors are renamed explicitly.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily ActualFamilyCounting
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem impossible_two_vertex_centers_with_common_color
    (P : ConvexPolytope d) (hdim : 3 ≤ P.dim)
    (color : P.vertices → Fin 3)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (D Jab Jac : Submodule ℝ (E d × ℝ))
    (hJabD : Jab ≤ D) (hJacD : Jac ≤ D)
    (hcrossab : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = a → color y = b → Jab ≤ edgeProjectiveLine x.val y.val)
    (hcrossac : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = a → color y = c → Jac ≤ edgeProjectiveLine x.val y.val)
    (u v : P.vertices) (hu : homogenize u.val ∈ Jab) (hv : homogenize v.val ∈ Jac)
    (hclassa : 1 ≤ Fintype.card (NoncentralColor P color D a))
    (hclassb : 1 ≤ Fintype.card (NoncentralColor P color D b)) :
    False := by
  let σ := threeColorEquiv a b c hab hac hbc
  let col : P.vertices → Fin 3 := fun w => σ.symm (color w)
  have hσ0 : σ 0 = a := rfl
  have hσ1 : σ 1 = b := rfl
  have hσ2 : σ 2 = c := rfl
  have hcol (w : P.vertices) (i : Fin 3) : col w = i ↔ color w = σ i := by
    constructor
    · intro h
      have hh := congrArg σ h
      simpa only [col,Equiv.apply_symm_apply] using hh
    · intro h
      change σ.symm (color w) = i
      rw [h,Equiv.symm_apply_apply]
  have hstarab := vertex_center_is_star Jab
    (fun e : CrossingFamily P color a b =>
      hcrossab e.left e.right e.isEdge e.property.2.1 e.property.2.2) u hu
  have hstarac := vertex_center_is_star Jac
    (fun e : CrossingFamily P color a c =>
      hcrossac e.left e.right e.isEdge e.property.2.1 e.property.2.2) v hv
  have h01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      col x = 0 → col y = 1 → x = u ∨ y = u := by
    intro x y hxy hx hy
    have hx' : color x = a := by simpa only [hσ0] using (hcol x 0).mp hx
    have hy' : color y = b := by simpa only [hσ1] using (hcol y 1).mp hy
    exact (hstarab ⟨(x,y),hxy,hx',hy'⟩).imp Eq.symm Eq.symm
  have h02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      col x = 0 → col y = 2 → x = v ∨ y = v := by
    intro x y hxy hx hy
    have hx' : color x = a := by simpa only [hσ0] using (hcol x 0).mp hx
    have hy' : color y = c := by simpa only [hσ2] using (hcol y 2).mp hy
    exact (hstarac ⟨(x,y),hxy,hx',hy'⟩).imp Eq.symm Eq.symm
  obtain ⟨x,hx⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ : Finset (NoncentralColor P color D a)).card by
      rw [Finset.card_univ]; omega)
  obtain ⟨y,hy⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ : Finset (NoncentralColor P color D b)).card by
      rw [Finset.card_univ]; omega)
  have hx0 : col x.val = 0 := (hcol x.val 0).mpr (by rw [hσ0]; exact x.property.1)
  have hy1 : col y.val = 1 := (hcol y.val 1).mpr (by rw [hσ1]; exact y.property.1)
  have hy0 : col y.val ≠ 0 := by rw [hy1]; decide
  have huD : homogenize u.val ∈ D := hJabD hu
  have hvD : homogenize v.val ∈ D := hJacD hv
  have hxu : x.val ≠ u := by
    intro h
    apply x.property.2
    rw [h]
    exact huD
  have hxv : x.val ≠ v := by
    intro h
    apply x.property.2
    rw [h]
    exact hvD
  have hyu : y.val ≠ u := by
    intro h
    apply y.property.2
    rw [h]
    exact huD
  have hyv : y.val ≠ v := by
    intro h
    apply y.property.2
    rw [h]
    exact hvD
  exact impossible_two_actual_star_centers P hdim col u v x.val y.val
    h01 h02 hx0 hy0 hxu hxv hyu hyv

end Papers.Polytopes


end
end
end BundlePart41

section BundlePart42
/- Source: Papers/VertexCenterPersistence.lean -/







@[expose] public section

/-!
# Persistence at an actual vertex center

A real vertex figure excludes third-color neighbors. Consequently both
nonstar families are off-central, so their centers are forced in every
realization. Two real vertex-figure edges then supply the final plane
witnesses used for reconstruction.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily CrossingFamilyTransport ActualFamilyCounting
open Papers.ActualFaceOrder
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d m : ℕ}

theorem decomposable_after_iso_of_vertex_center_with_same_color_neighbor
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Fin 3)
    (D J01 J02 J12 : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2)
    (h01 : finrank ℝ J01 = 1) (h02 : finrank ℝ J02 = 1)
    (h12 : finrank ℝ J12 = 1)
    (h01D : J01 ≤ D) (h02D : J02 ≤ D) (h12D : J12 ≤ D)
    (h0201 : J02 ≠ J01) (h1201 : J12 ≠ J01)
    (hcross01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → J01 ≤ edgeProjectiveLine x.val y.val)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (hcross12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 1 → color y = 2 → J12 ≤ edgeProjectiveLine x.val y.val)
    (hnot02 : ∀ x ∈ P.vertices, homogenize x ∉ J02)
    (hnot12 : ∀ x ∈ P.vertices, homogenize x ∉ J12)
    (u p : P.vertices) (hu : color u = 0) (hp : color p = 0)
    (huJ : homogenize u.val ∈ J01) (hup : GeneralVertexStep P u.val p.val)
    (hclasses : ∀ i, d - 1 ≤ Fintype.card (NoncentralColor P color D i))
    (hN : P.vertices.card ≤ 4 * d - 5)
    (e01 : CrossingFamily P color 0 1)
    (e02 : CrossingFamily P color 0 2)
    (e12 : CrossingFamily P color 1 2)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hPdim : 3 ≤ P.dim := by
    have hPd : P.dim = d := hP
    omega
  have hcenter01 : ∀ e : CrossingFamily P color 0 1, J01 ≤ e.line :=
    fun e => hcross01 e.left e.right e.isEdge e.property.2.1 e.property.2.2
  have hstarFamily := vertex_center_is_star J01 hcenter01 u huJ
  have hstar : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → x = u ∨ y = u := by
    intro x y hxy hx hy
    exact (hstarFamily ⟨(x,y),hxy,hx,hy⟩).imp Eq.symm Eq.symm
  have hue : u = e01.left := by
    rcases hstarFamily e01 with h | h
    · exact h
    · have hc := congrArg color h
      have hr : color e01.right = 1 := e01.property.2.2
      rw [hu,hr] at hc
      exact ((by decide : (0 : Fin 3) ≠ 1) hc).elim
  let q := e01.right
  have hq : color q = 1 := e01.property.2.2
  have huq : GeneralVertexStep P u.val q.val := by rw [hue]; exact e01.isEdge
  have hno2 := star_has_no_color_two_neighbors P hPdim color u p q
    hu hp hq hup huq hstar J02 h02 hnot02 hcross02
  have huD : homogenize u.val ∈ D := h01D huJ
  have hoff02 : ∀ e : CrossingFamily P color 0 2, ¬ e.line ≤ D := by
    intro e he
    rcases vertex_on_central_edge_is_endpoint D hD e he u huD with hl | hr
    · have hstep : GeneralVertexStep P u.val e.right.val := by rw [hl]; exact e.isEdge
      exact hno2 e.right hstep e.property.2.2
    · have hc := congrArg color hr
      have hr : color e.right = 2 := e.property.2.2
      rw [hu,hr] at hc
      exact (by decide : (0 : Fin 3) ≠ 2) hc
  have hoff12 : ∀ e : CrossingFamily P color 1 2, ¬ e.line ≤ D := by
    intro e he
    rcases vertex_on_central_edge_is_endpoint D hD e he u huD with hl | hr
    · have hc := congrArg color hl
      have hl : color e.left = 1 := e.property.2.1
      rw [hu,hl] at hc
      exact (by decide : (0 : Fin 3) ≠ 1) hc
    · have hc := congrArg color hr
      have hr : color e.right = 2 := e.property.2.2
      rw [hu,hr] at hc
      exact (by decide : (0 : Fin 3) ≠ 2) hc
  have hcross10 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 1 → color y = 0 → J01 ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    simpa only [edgeProjectiveLine,Set.pair_comm] using
      hcross01 y x (actualStep_symm x.property hxy) hy hx
  obtain ⟨K02,hK02,hK02cross,hK02out⟩ :=
    actual_offCentral_family_forced_center P hP hd color
      0 2 1 (by decide) (by decide) (by decide)
      D J02 J01 hD h02 h01 h02D h01D h0201 hcross02 hcross01
      hnot02 hoff02 u huD (hclasses 1) hN e02 Q iso
  obtain ⟨K12,hK12,hK12cross,hK12out⟩ :=
    actual_offCentral_family_forced_center P hP hd color
      1 2 0 (by decide) (by decide) (by decide)
      D J12 J01 hD h12 h01 h12D h01D h1201 hcross12 hcross10
      hnot12 hoff12 u huD (hclasses 0) hN e12 Q iso
  let colorQ := colorAlong iso color
  let labelQ := vertexColorExtension Q colorQ
  let U := vertexEquiv iso u
  let V := vertexEquiv iso p
  let W := vertexEquiv iso q
  have hlabels (v : P.vertices) : labelQ (vertexEquiv iso v).val = color v := by
    dsimp only [labelQ]
    rw [vertexColorExtension_at_vertex]
    exact congrArg color ((vertexEquiv iso).symm_apply_apply v)
  have hstarQ : ∀ x y : Q.vertices, GeneralVertexStep Q x.val y.val →
      labelQ x.val = 0 → labelQ y.val = 1 → x = U ∨ y = U := by
    intro x y hxy hx hy
    have hx' : colorQ x = 0 := by simpa only [labelQ,vertexColorExtension_at_vertex] using hx
    have hy' : colorQ y = 1 := by simpa only [labelQ,vertexColorExtension_at_vertex] using hy
    let f : CrossingFamily Q colorQ 0 1 := ⟨(x,y),hxy,hx',hy'⟩
    obtain ⟨g,hg⟩ := (crossingEquiv iso color 0 1).surjective f
    have hxg : vertexEquiv iso g.left = x := congrArg CrossingFamily.left hg
    have hyg : vertexEquiv iso g.right = y := congrArg CrossingFamily.right hg
    rcases hstarFamily g with h | h
    · left
      exact hxg.symm.trans (congrArg (vertexEquiv iso) h.symm)
    · right
      exact hyg.symm.trans (congrArg (vertexEquiv iso) h.symm)
  have hcrossQ02 : ∀ x y : Q.vertices, GeneralVertexStep Q x.val y.val →
      labelQ x.val = 0 → labelQ y.val = 2 → K02 ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    have hx' : colorQ x = 0 := by simpa only [labelQ,vertexColorExtension_at_vertex] using hx
    have hy' : colorQ y = 2 := by simpa only [labelQ,vertexColorExtension_at_vertex] using hy
    exact hK02cross ⟨(x,y),hxy,hx',hy'⟩
  have hcrossQ12 : ∀ x y : Q.vertices, GeneralVertexStep Q x.val y.val →
      labelQ x.val = 1 → labelQ y.val = 2 → K12 ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    have hx' : colorQ x = 1 := by simpa only [labelQ,vertexColorExtension_at_vertex] using hx
    have hy' : colorQ y = 2 := by simpa only [labelQ,vertexColorExtension_at_vertex] using hy
    exact hK12cross ⟨(x,y),hxy,hx',hy'⟩
  have hclassesQ : ∀ i : Fin 3, ∃ x ∈ Q.vertices, ∃ y ∈ Q.vertices,
      x ≠ y ∧ labelQ x = i ∧ labelQ y = i := by
    exact two_points_per_color_after_face_iso P color D
      (fun i => by have h := hclasses i; omega) Q iso
  have hQdim : 3 ≤ Q.dim := by rw [dim_eq iso]; exact hPdim
  refine decomposable_of_actual_star_centers Q hQdim labelQ U V W
    ((hlabels u).trans hu) ((hlabels p).trans hp) ((hlabels q).trans hq)
    (edge_forward iso u p hup) (edge_forward iso u q huq) hstarQ
    K02 K12 hK02 hK12 ?_ hcrossQ02 hcrossQ12 hclassesQ
  intro x hx hxK
  exact hK02out ⟨x,vertex_mem_body_of_mem_vertices Q hx,hxK⟩

theorem decomposable_after_iso_of_vertex_center
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Fin 3)
    (D J01 J02 J12 : Submodule ℝ (E d × ℝ))
    (hD : finrank ℝ D = 2)
    (h01 : finrank ℝ J01 = 1) (h02 : finrank ℝ J02 = 1)
    (h12 : finrank ℝ J12 = 1)
    (h01D : J01 ≤ D) (h02D : J02 ≤ D) (h12D : J12 ≤ D)
    (h0201 : J02 ≠ J01) (h1201 : J12 ≠ J01)
    (hcross01 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 1 → J01 ≤ edgeProjectiveLine x.val y.val)
    (hcross02 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 0 → color y = 2 → J02 ≤ edgeProjectiveLine x.val y.val)
    (hcross12 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 1 → color y = 2 → J12 ≤ edgeProjectiveLine x.val y.val)
    (u p : P.vertices) (hu : color u = 0) (hp : color p = 0)
    (huJ : homogenize u.val ∈ J01) (hup : GeneralVertexStep P u.val p.val)
    (hclasses : ∀ i, d - 1 ≤ Fintype.card (NoncentralColor P color D i))
    (hN : P.vertices.card ≤ 4 * d - 5)
    (e01 : CrossingFamily P color 0 1)
    (e02 : CrossingFamily P color 0 2)
    (e12 : CrossingFamily P color 1 2)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hPdim : 3 ≤ P.dim := by
    have hPd : P.dim = d := hP
    omega
  have hpos (i : Fin 3) : 1 ≤ Fintype.card (NoncentralColor P color D i) := by
    have h := hclasses i
    omega
  have hcross10 : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x = 1 → color y = 0 → J01 ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    simpa only [edgeProjectiveLine,Set.pair_comm] using
      hcross01 y x (actualStep_symm x.property hxy) hy hx
  have hnot02 : ∀ x ∈ P.vertices, homogenize x ∉ J02 := by
    intro x hx hxJ
    exact impossible_two_vertex_centers_with_common_color P hPdim color
      0 1 2 (by decide) (by decide) (by decide) D J01 J02 h01D h02D
      hcross01 hcross02 u ⟨x,hx⟩ huJ hxJ (hpos 0) (hpos 1)
  have hnot12 : ∀ x ∈ P.vertices, homogenize x ∉ J12 := by
    intro x hx hxJ
    exact impossible_two_vertex_centers_with_common_color P hPdim color
      1 0 2 (by decide) (by decide) (by decide) D J01 J12 h01D h12D
      hcross10 hcross12 u ⟨x,hx⟩ huJ hxJ (hpos 1) (hpos 0)
  exact decomposable_after_iso_of_vertex_center_with_same_color_neighbor
    P hP hd color D J01 J02 J12 hD h01 h02 h12 h01D h02D h12D
    h0201 h1201 hcross01 hcross02 hcross12 hnot02 hnot12
    u p hu hp huJ hup hclasses hN e01 e02 e12 Q iso

end Papers.Polytopes


end
end
end BundlePart42

section BundlePart43
/- Source: Papers/VertexCenterReindex.lean -/



@[expose] public section

/-! The actual vertex-center persistence theorem with arbitrary color names. -/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily ActualFamilyCounting Papers.ActualFaceOrder
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d m : ℕ}

theorem decomposable_after_iso_of_vertex_center_at
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Fin 3)
    (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (center : Fin 3 → Fin 3 → Submodule ℝ (E d × ℝ))
    (hcenterDim : ∀ i j, i ≠ j → finrank ℝ (center i j) = 1)
    (hcenterD : ∀ i j, i ≠ j → center i j ≤ D)
    (hsymm : ∀ i j, center i j = center j i)
    (hdistinct : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → center a b ≠ center a c)
    (hcross : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x ≠ color y → center (color x) (color y) ≤ edgeProjectiveLine x.val y.val)
    (u p : P.vertices) (hu : color u = a) (hp : color p = a)
    (huJ : homogenize u.val ∈ center a b) (hup : GeneralVertexStep P u.val p.val)
    (hclasses : ∀ i, d - 1 ≤ Fintype.card (NoncentralColor P color D i))
    (hN : P.vertices.card ≤ 4 * d - 5)
    (eab : CrossingFamily P color a b)
    (eac : CrossingFamily P color a c)
    (ebc : CrossingFamily P color b c)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  let σ := threeColorEquiv a b c hab hac hbc
  let col : P.vertices → Fin 3 := fun v => σ.symm (color v)
  have hσ0 : σ 0 = a := rfl
  have hσ1 : σ 1 = b := rfl
  have hσ2 : σ 2 = c := rfl
  have hcol (v : P.vertices) (i : Fin 3) : col v = i ↔ color v = σ i := by
    constructor
    · intro h
      have hh := congrArg σ h
      simpa only [col,Equiv.apply_symm_apply] using hh
    · intro h
      change σ.symm (color v) = i
      rw [h,Equiv.symm_apply_apply]
  let E01 : CrossingFamily P col 0 1 :=
    ⟨(eab.left,eab.right),eab.isEdge,
      (hcol _ 0).mpr (by rw [hσ0]; exact eab.property.2.1),
      (hcol _ 1).mpr (by rw [hσ1]; exact eab.property.2.2)⟩
  let E02 : CrossingFamily P col 0 2 :=
    ⟨(eac.left,eac.right),eac.isEdge,
      (hcol _ 0).mpr (by rw [hσ0]; exact eac.property.2.1),
      (hcol _ 2).mpr (by rw [hσ2]; exact eac.property.2.2)⟩
  let E12 : CrossingFamily P col 1 2 :=
    ⟨(ebc.left,ebc.right),ebc.isEdge,
      (hcol _ 1).mpr (by rw [hσ1]; exact ebc.property.2.1),
      (hcol _ 2).mpr (by rw [hσ2]; exact ebc.property.2.2)⟩
  have hcrossAt (i j : Fin 3) (hij : i ≠ j) :
      ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
        col x = i → col y = j →
        center (σ i) (σ j) ≤ edgeProjectiveLine x.val y.val := by
    intro x y hxy hx hy
    have hx' := (hcol x i).mp hx
    have hy' := (hcol y j).mp hy
    have hneq : color x ≠ color y := by
      rw [hx',hy']
      exact σ.injective.ne hij
    simpa only [hx',hy'] using hcross x y hxy hneq
  have hclasses' : ∀ i, d - 1 ≤ Fintype.card (NoncentralColor P col D i) := by
    intro i
    rw [Fintype.card_congr (noncentralColorReindex P color D σ i)]
    exact hclasses (σ i)
  have hca : center a c ≠ center a b :=
    hdistinct a c b hac hab hbc.symm
  have hcb : center b c ≠ center a b := by
    rw [hsymm a b]
    exact hdistinct b c a hbc hab.symm hac.symm
  have hu' : col u = 0 := (hcol u 0).mpr (by rw [hσ0]; exact hu)
  have hp' : col p = 0 := (hcol p 0).mpr (by rw [hσ0]; exact hp)
  exact decomposable_after_iso_of_vertex_center P hP hd col D
    (center a b) (center a c) (center b c) hD
    (hcenterDim a b hab) (hcenterDim a c hac) (hcenterDim b c hbc)
    (hcenterD a b hab) (hcenterD a c hac) (hcenterD b c hbc) hca hcb
    (by simpa only [hσ0,hσ1] using hcrossAt 0 1 (by decide))
    (by simpa only [hσ0,hσ2] using hcrossAt 0 2 (by decide))
    (by simpa only [hσ1,hσ2] using hcrossAt 1 2 (by decide))
    u p hu' hp' huJ hup hclasses' hN E01 E02 E12 Q iso

end Papers.Polytopes


end
end
end BundlePart43

section BundlePart44
/- Source: Papers/CentralVertexRecolor.lean -/



@[expose] public section

/-!
# Reassigning a central vertex removes a star family

If a vertex center has no neighbor of its assigned color, assign that
vertex to its other owning color. All noncentral class counts are
unchanged, and the corresponding crossing family becomes empty.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily ActualFamilyCounting
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def recolorVertex (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (u : P.vertices) (b : Fin 3) (v : P.vertices) : Fin 3 :=
  if v = u then b else color v

theorem recolorVertex_cover
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (u : P.vertices) (b : Fin 3)
    (f : E d → E d) (H : Fin 3 → E d → E d)
    (hcover : ∀ v : P.vertices, f v.val = H (color v) v.val)
    (hswitch : f u.val = H b u.val) :
    ∀ v : P.vertices, f v.val = H (recolorVertex P color u b v) v.val := by
  intro v
  by_cases hv : v = u
  · subst v
    simpa [recolorVertex] using hswitch
  · simpa only [recolorVertex,if_neg hv] using hcover v

theorem recolorVertex_has_no_crossing
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (a b : Fin 3) (hab : a ≠ b)
    (u : P.vertices) (hu : color u = a)
    (hstar : ∀ e : CrossingFamily P color a b, u = e.left ∨ u = e.right)
    (hnoSame : ∀ v : P.vertices, GeneralVertexStep P u.val v.val → color v ≠ a) :
    IsEmpty (CrossingFamily P (recolorVertex P color u b) a b) := by
  refine ⟨?_⟩
  intro e
  have hlne : e.left ≠ u := by
    intro h
    have hc : recolorVertex P color u b e.left = a := e.property.2.1
    change (if e.left = u then b else color e.left) = a at hc
    rw [if_pos h] at hc
    exact hab hc.symm
  have hl : color e.left = a := by
    have hc : recolorVertex P color u b e.left = a := e.property.2.1
    simpa only [recolorVertex,if_neg hlne] using hc
  by_cases hr : e.right = u
  · have hstep : GeneralVertexStep P u.val e.left.val := by
      have hs := actualStep_symm e.left.property e.isEdge
      change GeneralVertexStep P e.right.val e.left.val at hs
      simpa only [hr] using hs
    exact hnoSame e.left hstep hl
  · have hc : color e.right = b := by
      have hc : recolorVertex P color u b e.right = b := e.property.2.2
      simpa only [recolorVertex,if_neg hr] using hc
    let old : CrossingFamily P color a b := ⟨(e.left,e.right),e.isEdge,hl,hc⟩
    rcases hstar old with h | h
    · exact hlne h.symm
    · exact hr h.symm

theorem recolorVertex_eq_on_noncentral
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (u : P.vertices) (b : Fin 3)
    (D : Submodule ℝ (E d × ℝ)) (huD : homogenize u.val ∈ D)
    (v : P.vertices) (hvD : homogenize v.val ∉ D) :
    recolorVertex P color u b v = color v := by
  have hne : v ≠ u := by
    intro h
    apply hvD
    rw [h]
    exact huD
  exact if_neg hne

def recolorVertex_noncentralEquiv
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (u : P.vertices) (b : Fin 3)
    (D : Submodule ℝ (E d × ℝ)) (huD : homogenize u.val ∈ D) (i : Fin 3) :
    NoncentralColor P color D i ≃
      NoncentralColor P (recolorVertex P color u b) D i where
  toFun v := ⟨v.val,by
    constructor
    · rw [recolorVertex_eq_on_noncentral P color u b D huD v.val v.property.2]
      exact v.property.1
    · exact v.property.2⟩
  invFun v := ⟨v.val,by
    constructor
    · rw [← recolorVertex_eq_on_noncentral P color u b D huD v.val v.property.2]
      exact v.property.1
    · exact v.property.2⟩
  left_inv := by intro v; rfl
  right_inv := by intro v; rfl

theorem recolorVertex_noncentral_card
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (u : P.vertices) (b : Fin 3)
    (D : Submodule ℝ (E d × ℝ)) (huD : homogenize u.val ∈ D) (i : Fin 3) :
    Fintype.card (NoncentralColor P color D i) =
      Fintype.card (NoncentralColor P (recolorVertex P color u b) D i) :=
  Fintype.card_congr (recolorVertex_noncentralEquiv P color u b D huD i)

end Papers.Polytopes


end
end
end BundlePart44

section BundlePart45
/- Source: Papers/ThreeCenterGeometricReduction.lean -/




@[expose] public section

/-!
# Geometric reduction of the three-center case

When the central line meets P, every genuine three-center configuration
either persists as decomposable in the chosen realization, or admits
one explicit reassignment of a central vertex that removes a crossing
family. Noncentral color counts are preserved by that reassignment.
The homothety-parameter argument subsequently handles the absent family.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily ActualFamilyCounting Papers.ActualFaceOrder
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d m : ℕ}

def CentralRecolorAlternative
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (D : Submodule ℝ (E d × ℝ))
    (center : Fin 3 → Fin 3 → Submodule ℝ (E d × ℝ)) : Prop :=
  ∃ a b : Fin 3, ∃ u : P.vertices,
    a ≠ b ∧ color u = a ∧ homogenize u.val ∈ center a b ∧
    IsEmpty (CrossingFamily P (recolorVertex P color u b) a b) ∧
    ∀ i : Fin 3, Fintype.card (NoncentralColor P color D i) =
      Fintype.card (NoncentralColor P (recolorVertex P color u b) D i)

theorem actual_three_center_geometric_reduction
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Fin 3)
    (D : Submodule ℝ (E d × ℝ)) (hD : finrank ℝ D = 2)
    (center : Fin 3 → Fin 3 → Submodule ℝ (E d × ℝ))
    (hcenterDim : ∀ i j, i ≠ j → finrank ℝ (center i j) = 1)
    (hcenterD : ∀ i j, i ≠ j → center i j ≤ D)
    (hsymm : ∀ i j, center i j = center j i)
    (hdistinct : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → center a b ≠ center a c)
    (hcross : ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
      color x ≠ color y → center (color x) (color y) ≤ edgeProjectiveLine x.val y.val)
    (w : E d) (hwP : w ∈ P.toSet) (hwD : homogenize w ∈ D)
    (hclasses : ∀ i, d - 1 ≤ Fintype.card (NoncentralColor P color D i))
    (hfamilies : ∀ i j, i ≠ j → Nonempty (CrossingFamily P color i j))
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q ∨ CentralRecolorAlternative P color D center := by
  have hfamily (a b : Fin 3) (hab : a ≠ b) :
      ∀ e : CrossingFamily P color a b, center a b ≤ e.line := by
    intro e
    have hl : color e.left = a := e.property.2.1
    have hr : color e.right = b := e.property.2.2
    have hne : color e.left ≠ color e.right := by
      rw [hl,hr]
      exact hab
    simpa only [hl,hr,CrossingFamily.line] using
      hcross e.left e.right e.isEdge hne
  have atVertex (a b : Fin 3) (hab : a ≠ b)
      (u : P.vertices) (hu : color u = a) (huJ : homogenize u.val ∈ center a b) :
      MinkowskiDecomposable Q ∨ CentralRecolorAlternative P color D center := by
    by_cases hsame : ∃ p : P.vertices, GeneralVertexStep P u.val p.val ∧ color p = a
    · obtain ⟨p,hup,hp⟩ := hsame
      obtain ⟨c,hac,hbc⟩ := exists_third_color a b hab
      exact Or.inl (decomposable_after_iso_of_vertex_center_at P hP hd color
        a b c hab hac hbc D hD center hcenterDim hcenterD hsymm hdistinct hcross
        u p hu hp huJ hup hclasses hN
        (Classical.choice (hfamilies a b hab)) (Classical.choice (hfamilies a c hac))
        (Classical.choice (hfamilies b c hbc)) Q iso)
    · have hnoSame : ∀ p : P.vertices, GeneralVertexStep P u.val p.val → color p ≠ a := by
        intro p hup hp
        exact hsame ⟨p,hup,hp⟩
      have huD : homogenize u.val ∈ D := hcenterD a b hab huJ
      have hstar := vertex_center_is_star (center a b) (hfamily a b hab) u huJ
      exact Or.inr ⟨a,b,u,hab,hu,huJ,
        recolorVertex_has_no_crossing P color a b hab u hu hstar hnoSame,
        recolorVertex_noncentral_card P color u b D huD⟩
  by_cases hn : ∀ i j, i ≠ j → ∀ x ∈ P.vertices, homogenize x ∉ center i j
  · exact Or.inl (decomposable_after_iso_of_three_nonvertex_centers P hP hd color
      D hD center hcenterDim hcenterD hsymm hdistinct hcross hn w hwP hwD
      hclasses hfamilies hN Q iso)
  push_neg at hn
  obtain ⟨a,b,hab,x,hx,hxJ⟩ := hn
  let u : P.vertices := ⟨x,hx⟩
  let e := Classical.choice (hfamilies a b hab)
  have hstar := vertex_center_is_star (center a b) (hfamily a b hab) u hxJ
  rcases hstar e with hl | hr
  · have hu : color u = a := (congrArg color hl).trans e.property.2.1
    exact atVertex a b hab u hu hxJ
  · have hu : color u = b := (congrArg color hr).trans e.property.2.2
    have hxu : homogenize u.val ∈ center b a := by rw [← hsymm a b]; exact hxJ
    exact atVertex b a hab.symm u hu hxu

end Papers.Polytopes


end
end
end BundlePart45

section BundlePart46
/- Source: Papers/ActualHomothetyCenters.lean -/





@[expose] public section

/-!
# Actual crossing centers extracted from a homothety cover

The center subspaces are spans of the genuine homothety differences.
Their incidence with every actual crossing edge follows from parallelism.
Affine rank two gives three distinct projective centers on their common
projective line; these properties are derived here, not input certificates.
-/

noncomputable section
namespace Papers.ActualHomothetyCenters

open Set Module
open Papers.Polytopes Papers.Coordinates Papers.ActualHomothetyClasses
open Papers.HomogeneousSpanDimension
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n : ℕ} {I : Type*}

def center (p : I → ℝ × E n) (i j : I) : Submodule ℝ (E n × ℝ) :=
  Submodule.span ℝ {differenceCenterVector (p i) (p j)}

theorem difference_self (a : ℝ × E n) : differenceCenterVector a a = 0 := by
  ext <;> simp [differenceCenterVector]

theorem difference_reverse (a b : ℝ × E n) :
    differenceCenterVector b a = -differenceCenterVector a b := by
  ext <;> simp [differenceCenterVector] <;> abel

theorem difference_sub (a b c : ℝ × E n) :
    differenceCenterVector b c =
      differenceCenterVector a c - differenceCenterVector a b := by
  ext <;> simp [differenceCenterVector] <;> abel

theorem difference_eq_zero_iff (a b : ℝ × E n) :
    differenceCenterVector a b = 0 ↔ a = b := by
  constructor
  · intro h
    have hs := congrArg Prod.snd h
    have hv := congrArg Prod.fst h
    have hs' : b.1 - a.1 = 0 := hs
    have hv' : -(b.2 - a.2) = 0 := hv
    exact Prod.ext (sub_eq_zero.mp hs').symm
      (sub_eq_zero.mp (neg_eq_zero.mp hv')).symm
  · rintro rfl
    exact difference_self a

theorem center_le_direction (p : I → ℝ × E n) (i j : I) :
    center p i j ≤ directionSpan p := by
  apply Submodule.span_le.mpr
  intro z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  exact difference_mem p i j

theorem center_symm (p : I → ℝ × E n) (i j : I) :
    center p i j = center p j i := by
  have hle (a b : I) : center p a b ≤ center p b a := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    have h := (center p b a).neg_mem
      (Submodule.subset_span (Set.mem_singleton (differenceCenterVector (p b) (p a))))
    rw [difference_reverse (p a) (p b),neg_neg] at h
    exact h
  exact le_antisymm (hle i j) (hle j i)

theorem center_rank_one (p : I → ℝ × E n) {i j : I} (h : p i ≠ p j) :
    finrank ℝ (center p i j) = 1 :=
  finrank_span_singleton (mt (difference_eq_zero_iff (p i) (p j)).mp h)

theorem essential_parameters_injective
    (P : ConvexPolytope n) (f : E n → E n) (p : I → ℝ × E n)
    (hprivate : ∀ i : I, ∃ x ∈ P.vertices,
      f x = evaluate (p i) x ∧ ∀ j : I, j ≠ i → f x ≠ evaluate (p j) x) :
    Function.Injective p := by
  intro i j hp
  by_contra hij
  obtain ⟨x,hx,hxi,hxprivate⟩ := hprivate i
  apply hxprivate j (Ne.symm hij)
  rw [← hp]
  exact hxi

theorem center_incidence_of_parallel_cover
    (P : ConvexPolytope n) (f : E n → E n) (p : I → ℝ × E n)
    (hparallel : IsParallelMap P f)
    (color : P.vertices → I)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (x y : P.vertices) (hxy : GeneralVertexStep P x.val y.val) :
    center p (color x) (color y) ≤ edgeProjectiveLine x.val y.val := by
  obtain ⟨μ,hμ⟩ := hparallel x.val x.property y.val y.property hxy
  have heq := edge_identity f (p (color x)) (p (color y)) x.val y.val μ
    (hcover x) (hcover y) hμ
  apply Submodule.span_le.mpr
  intro z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  rw [heq,edgeProjectiveLine,homogeneousSpan,Set.image_pair]
  apply Submodule.sub_mem
  · apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · apply Submodule.smul_mem
    exact Submodule.subset_span (Set.mem_insert _ _)

theorem family_center_incidence
    (P : ConvexPolytope n) (f : E n → E n) (p : I → ℝ × E n)
    (hparallel : IsParallelMap P f)
    (color : P.vertices → I)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (i j : I) (e : CrossingFamily P color i j) :
    center p i j ≤ e.line := by
  have h := center_incidence_of_parallel_cover P f p hparallel color hcover
    e.left e.right e.isEdge
  have hl : color e.left = i := e.property.2.1
  have hr : color e.right = j := e.property.2.2
  rw [hl,hr] at h
  exact h

theorem direction_eq_two_centers
    (p : I → ℝ × E n) (i j k : I)
    (hcover : ∀ a : I, a = i ∨ a = j ∨ a = k) :
    directionSpan p = center p i j ⊔ center p i k := by
  let W := center p i j ⊔ center p i k
  have hbase (a : I) : differenceCenterVector (p i) (p a) ∈ W := by
    rcases hcover a with rfl | rfl | rfl
    · rw [difference_self]
      exact W.zero_mem
    · exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
    · exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨⟨a,b⟩,rfl⟩
    change differenceCenterVector (p a) (p b) ∈ W
    rw [difference_sub (p i) (p a) (p b)]
    exact W.sub_mem (hbase b) (hbase a)
  · exact sup_le (center_le_direction p i j) (center_le_direction p i k)

theorem distinct_centers_of_rank_two
    (p : Fin 3 → ℝ × E n) (hinj : Function.Injective p)
    (hrank : finrank ℝ (directionSpan p) = 2)
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    center p i j ≠ center p i k := by
  have hcover : ∀ a : Fin 3, a = i ∨ a = j ∨ a = k := by
    intro a
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases a <;> simp_all
  have hD := direction_eq_two_centers p i j k hcover
  intro heq
  have hJ := center_rank_one p (fun h => hik (hinj h))
  rw [hD,heq,sup_idem,hJ] at hrank
  omega

theorem direction_rank_le_two (p : Fin 3 → ℝ × E n) :
    finrank ℝ (directionSpan p) ≤ 2 := by
  have hcover : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by
    intro a; fin_cases a <;> simp
  rw [direction_eq_two_centers p 0 1 2 hcover]
  have h0 : finrank ℝ (center p 0 1) ≤ 1 := by
    by_cases hp : p 0 = p 1
    · rw [center, hp, difference_self, Submodule.span_zero_singleton, finrank_bot]
      omega
    · exact (center_rank_one p hp).le
  have h1 : finrank ℝ (center p 0 2) ≤ 1 := by
    by_cases hp : p 0 = p 2
    · rw [center, hp, difference_self, Submodule.span_zero_singleton, finrank_bot]
      omega
    · exact (center_rank_one p hp).le
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (center p 0 1) (center p 0 2)
  omega

end Papers.ActualHomothetyCenters

end
end
end BundlePart46

section BundlePart47
/- Source: Papers/TwoColorActualGeometry.lean -/







@[expose] public section

/-!
# Actual geometry of a two-color homothety cover

Balinski rules out a vertex center. Every two-face through a crossing edge
supplies a different crossing partner, and the family is an actual matching.
-/

noncomputable section
namespace Papers.Polytopes.TwoColorGeometry

open Set Module Papers.Coordinates
open CrossingFamily ExposedProjectiveBridge
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem crossing_family_nonempty
    (P : ConvexPolytope d) (color : P.vertices → Bool)
    (hfalse : ∃ x : P.vertices, color x = false)
    (htrue : ∃ y : P.vertices, color y = true) :
    Nonempty (CrossingFamily P color false true) := by
  obtain ⟨x,hx⟩ := hfalse
  obtain ⟨y,hy⟩ := htrue
  let G := Papers.PolytopeBalinski.vertexGraph P
  have hy' : color y ≠ false := by rw [hy]; decide
  obtain ⟨a,ha,b,hb,hab⟩ :=
    ThreeColorVertexFigure.crossing_edge_of_reachable G {v | color v = false}
      hx hy' (Papers.PolytopeBalinski.vertexGraph_preconnected P x y)
  have hbt : color b = true := by
    cases h : color b <;> simp_all
  exact ⟨⟨(a,b),hab,ha,hbt⟩⟩

theorem center_has_no_actual_vertex
    (P : ConvexPolytope d) (hdim : 2 ≤ P.dim)
    (color : P.vertices → Bool)
    (J : Submodule ℝ (E d × ℝ))
    (hcenter : ∀ e : CrossingFamily P color false true, J ≤ e.line)
    (hclasses : ∀ i : Bool, ∃ x y : P.vertices,
      x ≠ y ∧ color x = i ∧ color y = i) :
    ∀ z ∈ P.vertices, homogenize z ∉ J := by
  intro z hz hzJ
  let u : P.vertices := ⟨z,hz⟩
  have hstar := vertex_center_is_star J hcenter u hzJ
  have hretained (i : Bool) : ∃ x : P.vertices, x ≠ u ∧ color x = i := by
    obtain ⟨x,y,hxy,hxi,hyi⟩ := hclasses i
    by_cases hx : x = u
    · exact ⟨y,fun hy => hxy (hx.trans hy.symm),hyi⟩
    · exact ⟨x,hx,hxi⟩
  obtain ⟨x,hxu,hx⟩ := hretained false
  obtain ⟨y,hyu,hy⟩ := hretained true
  let I := {v : P.vertices // v ≠ u}
  let G := (Papers.PolytopeBalinski.vertexGraph P).induce {v | v ≠ u}
  let x' : I := ⟨x,hxu⟩
  let y' : I := ⟨y,hyu⟩
  have hy' : color y ≠ false := by rw [hy]; decide
  have hconn := Papers.PolytopeBalinski.vertexGraph_delete_one_preconnected P hdim u
  obtain ⟨a,ha,b,hb,hab⟩ :=
    ThreeColorVertexFigure.crossing_edge_of_reachable G {v | color v.val = false}
      hx hy' (hconn x' y')
  have hbt : color b.val = true := by
    cases h : color b.val <;> simp_all
  let e : CrossingFamily P color false true := ⟨(a.val,b.val),hab,ha,hbt⟩
  rcases hstar e with h | h
  · exact a.property h.symm
  · exact b.property h.symm

theorem cofacial_degree_lower_bound
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (color : P.vertices → Bool) (e : CrossingFamily P color false true) :
    d - 1 ≤ (cofacialGraph (P := P) (color := color) (a := false) (b := true)).degree e := by
  let G := cofacialGraph (P := P) (color := color) (a := false) (b := true)
  let faces := incidentTwoFaces P e.left.val e.right.val
  let partner (F : ActualFaceType P) (f : CrossingFamily P color false true) :=
    e ≠ f ∧ liesIn F.val f
  have hmem (F : ActualFaceType P) (hF : F ∈ faces) :
      faceDim F.val = 2 ∧ liesIn F.val e := (Finset.mem_filter.mp hF).2
  have hc : faces.card ≤ G.degree e := by
    apply CofacialCounting.incident_count_le_degree G e faces partner
    · intro F hF
      obtain ⟨f,hef,hfF⟩ := second_edge_in_twoFace (by decide : false ≠ true)
        e F.val F.property (hmem F hF).1 (hmem F hF).2 (by
          intro x y hxF hyF hxy hx hy
          cases h : color y <;> simp_all)
      exact ⟨f,⟨hef,F.val,F.property,(hmem F hF).1,(hmem F hF).2,hfF⟩,hef,hfF⟩
    · intro F hF H hH f hfF hfH
      apply Subtype.ext
      exact actual_twoFaces_eq_of_two_lines P F.val H.val F.property H.property
        F.property.2 H.property.2 (hmem F hF).1 (hmem H hH).1
        e.line f.line (pair_line_rank_ge_three (by decide : false ≠ true) e f hfF.1)
        (line_le_span (hmem F hF).2.1 (hmem F hF).2.2)
        (line_le_span (hmem H hH).2.1 (hmem H hH).2.2)
        (line_le_span hfF.2.1 hfF.2.2) (line_le_span hfH.2.1 hfH.2.2)
  have hl := incidentTwoFaces_card_actual_fullDim P hP e.left.property e.isEdge
  change d - 1 ≤ faces.card at hl
  exact hl.trans hc

theorem twice_family_card_le_vertices
    (P : ConvexPolytope d) (color : P.vertices → Bool)
    (J : Submodule ℝ (E d × ℝ)) (hJ : finrank ℝ J = 1)
    (hcenter : ∀ e : CrossingFamily P color false true, J ≤ e.line)
    (hnotvertex : ∀ z ∈ P.vertices, homogenize z ∉ J) :
    2 * Fintype.card (CrossingFamily P color false true) ≤ P.vertices.card := by
  obtain ⟨hl,hr⟩ := endpoint_injections_of_nonvertex_center J hJ hcenter hnotvertex
  let L : CrossingFamily P color false true → P.vertices := fun e => e.left
  let R : CrossingFamily P color false true → P.vertices := fun e => e.right
  have hL : Function.Injective L := fun e f h => hl (congrArg Subtype.val h)
  have hR : Function.Injective R := fun e f h => hr (congrArg Subtype.val h)
  have hLR : ∀ e f, L e ≠ R f := by
    intro e f h
    exact left_ne_right_of_different_colors (by decide : false ≠ true) e f
      (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective (Sum.elim L R)
    (ActualFamilyCounting.sumElim_injective L R hL hR hLR)
  simp only [Fintype.card_sum,Fintype.card_coe] at hc
  omega

end Papers.Polytopes.TwoColorGeometry


end
end
end BundlePart47

section BundlePart48
/- Source: Papers/TwoColorPersistence.lean -/






@[expose] public section

/-!
# Two-color persistence below 4d−4 vertices

A rank-one crossing center and two vertices in each actual color class
suffice. Actual Balinski, polygon parity, edge supports, and face-order
transport prove a common center in every realization, from which the
nontrivial parallel map is explicitly reconstructed.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily CrossingFamilyTransport Papers.ActualFaceOrder
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d m : ℕ}

theorem decomposable_after_iso_of_two_color_center
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (color : P.vertices → Bool)
    (J : Submodule ℝ (E d × ℝ)) (hJ : finrank ℝ J = 1)
    (hcenter : ∀ e : CrossingFamily P color false true, J ≤ e.line)
    (hclasses : ∀ i : Bool, ∃ x y : P.vertices,
      x ≠ y ∧ color x = i ∧ color y = i)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hPdim : 2 ≤ P.dim := by
    have hPd : P.dim = d := hP
    omega
  have hnotvertex :=
    TwoColorGeometry.center_has_no_actual_vertex P hPdim color J hcenter hclasses
  have hcard := TwoColorGeometry.twice_family_card_le_vertices P color J hJ hcenter hnotvertex
  have hdegreeP : ∀ e : CrossingFamily P color false true,
      d - 1 ≤ (cofacialGraph (P := P) (color := color) (a := false) (b := true)).degree e :=
    TwoColorGeometry.cofacial_degree_lower_bound P hP color
  have hdegreeQ := minimum_degree_transport iso color false true (d - 1) hdegreeP
  have hcardeq := family_card_eq iso color false true
  have hnonempty := TwoColorGeometry.crossing_family_nonempty P color
    (by obtain ⟨x,y,hxy,hx,hy⟩ := hclasses false; exact ⟨x,hx⟩)
    (by obtain ⟨x,y,hxy,hx,hy⟩ := hclasses true; exact ⟨x,hx⟩)
  let e := Classical.choice hnonempty
  obtain ⟨K,hK,hKcross⟩ := concurrent_of_dense_actual_cofacial_graph
    (by decide : false ≠ true) (d - 1) (by omega) hdegreeQ
    (by omega)
    (no_three_transport iso color false true
      (no_three_in_actual_twoFace (by decide : false ≠ true) J hJ hcenter hnotvertex))
    (crossingEquiv iso color false true e)
  obtain ⟨q,hqK,hq⟩ : ∃ q ∈ K, q ≠ (0 : E m × ℝ) := by
    apply K.ne_bot_iff.mp
    intro hbot
    rw [hbot,finrank_bot] at hK
    omega
  let colorQ := colorAlong iso color
  let label : E m → Bool :=
    fun x => if hx : x ∈ Q.vertices then colorQ ⟨x,hx⟩ else false
  have hlabel (v : Q.vertices) : label v.val = colorQ v := by
    simp only [label,dif_pos v.property]
  have hlabels (v : P.vertices) : label (vertexEquiv iso v).val = color v := by
    rw [hlabel]
    exact congrArg color ((vertexEquiv iso).symm_apply_apply v)
  have hclassesQ (i : Bool) : ∃ x ∈ Q.vertices, ∃ y ∈ Q.vertices,
      x ≠ y ∧ label x = i ∧ label y = i := by
    obtain ⟨x,y,hxy,hx,hy⟩ := hclasses i
    let X := vertexEquiv iso x
    let Y := vertexEquiv iso y
    have hne : X.val ≠ Y.val := by
      intro h
      exact hxy ((vertexEquiv iso).injective (Subtype.ext h))
    exact ⟨X.val,X.property,Y.val,Y.property,hne,
      (hlabels x).trans hx,(hlabels y).trans hy⟩
  have hcanonical (x y : Q.vertices) (hxy : GeneralVertexStep Q x.val y.val)
      (hx : colorQ x = false) (hy : colorQ y = true) :
      q ∈ edgeProjectiveLine x.val y.val :=
    hKcross ⟨(x,y),hxy,hx,hy⟩ hqK
  apply decomposable_of_two_color_projective_center Q label q hq
    (hclassesQ false) (hclassesQ true)
  intro x hx y hxy hne
  let X : Q.vertices := ⟨x,hx⟩
  let Y : Q.vertices := ⟨y,hxy.1⟩
  have hne' : colorQ X ≠ colorQ Y := by
    change label X.val ≠ label Y.val at hne
    rw [hlabel X,hlabel Y] at hne
    exact hne
  cases hcx : colorQ X <;> cases hcy : colorQ Y
  · exact (hne' (hcx.trans hcy.symm)).elim
  · exact hcanonical X Y hxy hcx hcy
  · have h := hcanonical Y X (actualStep_symm hx hxy) hcy hcx
    simpa only [edgeProjectiveLine,Set.pair_comm] using h
  · exact (hne' (hcx.trans hcy.symm)).elim

end Papers.Polytopes


end
end
end BundlePart48

section BundlePart49
/- Source: Papers/ActualThreeCoverReductions.lean -/




@[expose] public section

/-!
# Two-color reductions of a genuine three-homothety cover

A missing crossing family allows one color to be separated from the other
two using the remaining actual center.  If the parameter direction space
has rank one, every crossing center is that same line, so the same split
works.  Both conclusions quantify over every actual face-order equivalent
realization.
-/

noncomputable section
namespace Papers.ActualThreeCoverReductions

open Set Module
open Papers.Polytopes Papers.ActualFaceOrder
open Papers.ActualHomothetyClasses Papers.ActualHomothetyCenters
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {d m : ℕ}

def splitZero (P : ConvexPolytope d) (color : P.vertices → Fin 3) :
    P.vertices → Bool := fun v => decide (color v = 0)

theorem actual_step_symm (P : ConvexPolytope d) (x y : P.vertices)
    (h : GeneralVertexStep P x.val y.val) :
    GeneralVertexStep P y.val x.val := by
  obtain ⟨hy,hxy,F,hF,hdim,hxF,hyF⟩ := h
  exact ⟨x.property,hxy.symm,F,hF,hdim,hyF,hxF⟩

theorem splitZero_classes (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (hclasses : ∀ i : Fin 3, ∃ x y : P.vertices,
      x ≠ y ∧ color x = i ∧ color y = i) :
    ∀ i : Bool, ∃ x y : P.vertices,
      x ≠ y ∧ splitZero P color x = i ∧ splitZero P color y = i := by
  intro i
  cases i with
  | false =>
      obtain ⟨x,y,hxy,hx,hy⟩ := hclasses 1
      exact ⟨x,y,hxy,by simp [splitZero,hx],by simp [splitZero,hy]⟩
  | true =>
      obtain ⟨x,y,hxy,hx,hy⟩ := hclasses 0
      exact ⟨x,y,hxy,by simp [splitZero,hx],by simp [splitZero,hy]⟩

theorem decomposable_after_iso_of_missing_01
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (f : E d → E d) (p : Fin 3 → ℝ × E d)
    (hparallel : IsParallelMap P f) (hinj : Function.Injective p)
    (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hclasses : ∀ i : Fin 3, ∃ x y : P.vertices,
      x ≠ y ∧ color x = i ∧ color y = i)
    (hmissing : ∀ e : CrossingFamily P color 0 1, False)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  apply decomposable_after_iso_of_two_color_center P hP hd
    (splitZero P color) (center p 0 2)
    (center_rank_one p (fun h => (by decide : (0 : Fin 3) ≠ 2) (hinj h)))
    ?_ (splitZero_classes P color hclasses) hN Q iso
  intro e
  have hx0 : color e.left ≠ 0 := by
    have h : splitZero P color e.left = false := e.property.2.1
    simpa [splitZero] using h
  have hy0 : color e.right = 0 := by
    have h : splitZero P color e.right = true := e.property.2.2
    simpa [splitZero] using h
  have hx1 : color e.left ≠ 1 := by
    intro hx1
    exact hmissing ⟨(e.right,e.left),actual_step_symm P e.left e.right e.isEdge,hy0,hx1⟩
  have hcolors : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by
    intro i; fin_cases i <;> simp
  have hx2 : color e.left = 2 := by
    rcases hcolors (color e.left) with h | h | h
    · exact False.elim (hx0 h)
    · exact False.elim (hx1 h)
    · exact h
  have h := center_incidence_of_parallel_cover P f p hparallel color hcover
    e.left e.right e.isEdge
  rw [hx2,hy0,center_symm p 2 0] at h
  exact h

theorem center_eq_direction_of_rank_one
    (p : Fin 3 → ℝ × E d) (hinj : Function.Injective p)
    (hrank : finrank ℝ (directionSpan p) = 1)
    {i j : Fin 3} (hij : i ≠ j) :
    center p i j = directionSpan p :=
  Submodule.eq_of_le_of_finrank_eq (center_le_direction p i j)
    ((center_rank_one p (fun h => hij (hinj h))).trans hrank.symm)

theorem decomposable_after_iso_of_rank_one_parameters
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (f : E d → E d) (p : Fin 3 → ℝ × E d)
    (hparallel : IsParallelMap P f) (hinj : Function.Injective p)
    (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hrank : finrank ℝ (directionSpan p) = 1)
    (hclasses : ∀ i : Fin 3, ∃ x y : P.vertices,
      x ≠ y ∧ color x = i ∧ color y = i)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  apply decomposable_after_iso_of_two_color_center P hP hd
    (splitZero P color) (directionSpan p) hrank ?_
    (splitZero_classes P color hclasses) hN Q iso
  intro e
  have hx0 : color e.left ≠ 0 := by
    have h : splitZero P color e.left = false := e.property.2.1
    simpa [splitZero] using h
  have hy0 : color e.right = 0 := by
    have h : splitZero P color e.right = true := e.property.2.2
    simpa [splitZero] using h
  have hne : color e.left ≠ color e.right := by rwa [hy0]
  have h := center_incidence_of_parallel_cover P f p hparallel color hcover
    e.left e.right e.isEdge
  rwa [center_eq_direction_of_rank_one p hinj hrank hne] at h

theorem essential_cover_two_vertices_per_color
    (P : ConvexPolytope d) (hd : 3 ≤ P.dim)
    (f : E d → E d) (p : Fin 3 → ℝ × E d)
    (hparallel : IsParallelMap P f) (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hprivate : ∀ i : Fin 3, ∃ x ∈ P.vertices,
      f x = evaluate (p i) x ∧
        ∀ j : Fin 3, j ≠ i → f x ≠ evaluate (p j) x) :
    ∀ i : Fin 3, ∃ x y : P.vertices, x ≠ y ∧ color x = i ∧ color y = i := by
  intro i
  obtain ⟨v,hv,hvi,hvp⟩ := hprivate i
  have hc := colored_essential_class_bound P f p hparallel color hcover i hv hvi hvp
  have hD := direction_rank_le_two p
  have htwo : 1 < (coloredNoncentral P color p i).card := by omega
  obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp htwo
  simp only [coloredNoncentral, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  exact ⟨x,y,hxy,hx.1,hy.1⟩

theorem decomposable_after_iso_of_essential_missing_01
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (f : E d → E d) (p : Fin 3 → ℝ × E d)
    (hparallel : IsParallelMap P f) (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hprivate : ∀ i : Fin 3, ∃ x ∈ P.vertices,
      f x = evaluate (p i) x ∧
        ∀ j : Fin 3, j ≠ i → f x ≠ evaluate (p j) x)
    (hmissing : ∀ e : CrossingFamily P color 0 1, False)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hdim : 3 ≤ P.dim := by rw [hP]; exact hd
  exact decomposable_after_iso_of_missing_01 P hP hd f p hparallel
    (essential_parameters_injective P f p hprivate) color hcover
    (essential_cover_two_vertices_per_color P hdim f p hparallel color hcover hprivate)
    hmissing hN Q iso

theorem decomposable_after_iso_of_essential_rank_one
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (f : E d → E d) (p : Fin 3 → ℝ × E d)
    (hparallel : IsParallelMap P f) (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hprivate : ∀ i : Fin 3, ∃ x ∈ P.vertices,
      f x = evaluate (p i) x ∧
        ∀ j : Fin 3, j ≠ i → f x ≠ evaluate (p j) x)
    (hrank : finrank ℝ (directionSpan p) = 1)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hdim : 3 ≤ P.dim := by rw [hP]; exact hd
  exact decomposable_after_iso_of_rank_one_parameters P hP hd f p hparallel
    (essential_parameters_injective P f p hprivate) color hcover hrank
    (essential_cover_two_vertices_per_color P hdim f p hparallel color hcover hprivate)
    hN Q iso

end Papers.ActualThreeCoverReductions

end
end
end BundlePart49

section BundlePart50
/- Source: Papers/ActualThreeCoverRecolor.lean -/



@[expose] public section

/-!
# Reassigning a shared star-center vertex

A vertex carrying two homotheties may be assigned to either class.  If
it has no neighbor in its current class, moving it to the other class
removes their crossing family.  The original private-vertex witnesses
remain valid because their definition concerns the homotheties, not the
chosen disjoint coloring.
-/

noncomputable section
namespace Papers.ActualThreeCoverRecolor

open Set Module
open Papers.Polytopes Papers.ActualFaceOrder
open Papers.ActualHomothetyClasses Papers.ActualHomothetyCenters
open Papers.ActualThreeCoverReductions Papers.HomogeneousSpanDimension
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {d m : ℕ}

theorem equal_evaluation_of_difference_on_point
    (p q : ℝ × E d) (x : E d)
    (h : differenceCenterVector p q ∈ Submodule.span ℝ {liftPoint x}) :
    evaluate p x = evaluate q x := by
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp h
  have hs : a = q.1 - p.1 := by
    have hh := congrArg Prod.snd ha
    simpa [liftPoint,differenceCenterVector] using hh
  have hv : (q.1 - p.1) • x = -(q.2 - p.2) := by
    have hh := congrArg Prod.fst ha
    simpa [liftPoint,differenceCenterVector,hs] using hh
  have hd : evaluate q x - evaluate p x = 0 := by
    calc
      evaluate q x - evaluate p x = (q.1 - p.1) • x + (q.2 - p.2) := by
        unfold evaluate
        module
      _ = 0 := by rw [hv,neg_add_cancel]
  exact (sub_eq_zero.mp hd).symm

def recolorStar (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (u : P.vertices) : P.vertices → Fin 3 :=
  fun v => if v = u then 1 else color v

theorem recolorStar_cover
    (P : ConvexPolytope d) (f : E d → E d) (p : Fin 3 → ℝ × E d)
    (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (u : P.vertices) (hu : color u = 0)
    (hequal : evaluate (p 0) u.val = evaluate (p 1) u.val) :
    ∀ v : P.vertices, f v.val = evaluate (p (recolorStar P color u v)) v.val := by
  intro v
  by_cases hv : v = u
  · subst v
    have hc0 : f u.val = evaluate (p 0) u.val := by
      simpa only [hu] using hcover u
    have hc : f u.val = evaluate (p 1) u.val := hc0.trans hequal
    simpa [recolorStar] using hc
  · simpa only [recolorStar,if_neg hv] using hcover v

theorem recolorStar_missing
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (u : P.vertices)
    (hstar : ∀ e : CrossingFamily P color 0 1, e.left = u ∨ e.right = u)
    (hno_same : ∀ v : P.vertices, GeneralVertexStep P u.val v.val → color v ≠ 0) :
    ∀ e : CrossingFamily P (recolorStar P color u) 0 1, False := by
  intro e
  have hxne : e.left ≠ u := by
    intro hxu
    have h : recolorStar P color u e.left = 0 := e.property.2.1
    change (if e.left = u then 1 else color e.left) = 0 at h
    rw [if_pos hxu] at h
    exact (by decide : (1 : Fin 3) ≠ 0) h
  have hx0 : color e.left = 0 := by
    have h : recolorStar P color u e.left = 0 := e.property.2.1
    simpa only [recolorStar,if_neg hxne] using h
  by_cases hyu : e.right = u
  · have hyx := actual_step_symm P e.left e.right e.isEdge
    rw [hyu] at hyx
    exact hno_same e.left hyx hx0
  · have hy1 : color e.right = 1 := by
      have h : recolorStar P color u e.right = 1 := e.property.2.2
      simpa only [recolorStar,if_neg hyu] using h
    let f : CrossingFamily P color 0 1 := ⟨(e.left,e.right),e.isEdge,hx0,hy1⟩
    rcases hstar f with h | h
    · exact hxne h
    · exact hyu h

theorem decomposable_after_iso_of_star_without_same_color_neighbor
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (f : E d → E d) (p : Fin 3 → ℝ × E d)
    (hparallel : IsParallelMap P f) (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hprivate : ∀ i : Fin 3, ∃ x ∈ P.vertices,
      f x = evaluate (p i) x ∧
        ∀ j : Fin 3, j ≠ i → f x ≠ evaluate (p j) x)
    (u : P.vertices) (hu : color u = 0)
    (hequal : evaluate (p 0) u.val = evaluate (p 1) u.val)
    (hstar : ∀ e : CrossingFamily P color 0 1, e.left = u ∨ e.right = u)
    (hno_same : ∀ v : P.vertices, GeneralVertexStep P u.val v.val → color v ≠ 0)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q :=
  decomposable_after_iso_of_essential_missing_01 P hP hd f p hparallel
    (recolorStar P color u) (recolorStar_cover P f p color hcover u hu hequal)
    hprivate (recolorStar_missing P color u hstar hno_same) hN Q iso

end Papers.ActualThreeCoverRecolor

end
end
end BundlePart50

section BundlePart51
/- Source: Papers/EssentialThreeCoverCentral.lean -/




@[expose] public section

/-!
# The central case of an essential three-homothety cover

Every geometric input to the three-center theorem is derived from the
actual parallel map and genuine private-vertex witnesses. Recoloring a
central vertex preserves the original map and essential cover. The
remaining absent family is reduced to the proved two-color persistence
theorem after an explicit permutation of the three parameters.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates
open CrossingFamily ActualFamilyCounting Papers.ActualFaceOrder
open Papers.ActualHomothetyClasses Papers.ActualHomothetyCenters
open Papers.ActualThreeCoverReductions Papers.ActualThreeCoverRecolor
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d m : ℕ}

theorem decomposable_after_iso_of_essential_missing_family
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (f : E d → E d) (p : Fin 3 → ℝ × E d)
    (hparallel : IsParallelMap P f) (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hprivate : ∀ i : Fin 3, ∃ x ∈ P.vertices,
      f x = evaluate (p i) x ∧
        ∀ j : Fin 3, j ≠ i → f x ≠ evaluate (p j) x)
    (a b : Fin 3) (hab : a ≠ b)
    (hmissing : ∀ e : CrossingFamily P color a b, False)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  obtain ⟨c,hac,hbc⟩ := exists_third_color a b hab
  let σ := threeColorEquiv a b c hab hac hbc
  let pp : Fin 3 → ℝ × E d := fun i => p (σ i)
  let col : P.vertices → Fin 3 := fun v => σ.symm (color v)
  have hσ0 : σ 0 = a := rfl
  have hσ1 : σ 1 = b := rfl
  have hcover' : ∀ v : P.vertices, f v.val = evaluate (pp (col v)) v.val := by
    intro v
    simpa only [pp,col,Equiv.apply_symm_apply] using hcover v
  have hprivate' : ∀ i : Fin 3, ∃ x ∈ P.vertices,
      f x = evaluate (pp i) x ∧
        ∀ j : Fin 3, j ≠ i → f x ≠ evaluate (pp j) x := by
    intro i
    obtain ⟨x,hx,hxi,hxp⟩ := hprivate (σ i)
    exact ⟨x,hx,hxi,fun j hji => hxp (σ j) (σ.injective.ne hji)⟩
  have hmissing' : ∀ e : CrossingFamily P col 0 1, False := by
    intro e
    have hl : color e.left = a := by
      have he : col e.left = 0 := e.property.2.1
      have h := congrArg σ he
      simpa only [col,Equiv.apply_symm_apply,hσ0] using h
    have hr : color e.right = b := by
      have he : col e.right = 1 := e.property.2.2
      have h := congrArg σ he
      simpa only [col,Equiv.apply_symm_apply,hσ1] using h
    exact hmissing ⟨(e.left,e.right),e.isEdge,hl,hr⟩
  exact decomposable_after_iso_of_essential_missing_01 P hP hd f pp hparallel col
    hcover' hprivate' hmissing' hN Q iso

def coloredNoncentralEquiv
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (p : Fin 3 → ℝ × E d) (i : Fin 3) :
    coloredNoncentral P color p i ≃ NoncentralColor P color (directionSpan p) i where
  toFun v := ⟨v.val,by
    have hv := v.property
    simp only [coloredNoncentral, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] at hv
    simpa only [Papers.HomogeneousSpanDimension.liftPoint, homogenize] using hv⟩
  invFun v := ⟨v.val,by
    have hv : color v.val = i ∧
        Papers.HomogeneousSpanDimension.liftPoint v.val.val ∉ directionSpan p := by
      simpa only [Papers.HomogeneousSpanDimension.liftPoint, homogenize] using v.property
    simpa only [coloredNoncentral, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and] using hv⟩
  left_inv := by intro v; rfl
  right_inv := by intro v; rfl

theorem coloredNoncentral_card_eq
    (P : ConvexPolytope d) (color : P.vertices → Fin 3)
    (p : Fin 3 → ℝ × E d) (i : Fin 3) :
    (coloredNoncentral P color p i).card =
      Fintype.card (NoncentralColor P color (directionSpan p) i) := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (coloredNoncentralEquiv P color p i)

theorem equal_evaluation_of_actual_center_vertex
    (p : Fin 3 → ℝ × E d) (hinj : Function.Injective p)
    (a b : Fin 3) (hab : a ≠ b) (u : E d)
    (hu : homogenize u ∈ center p a b) :
    evaluate (p a) u = evaluate (p b) u := by
  have hJ := center_rank_one p (fun h => hab (hinj h))
  have hpoint : finrank ℝ (Submodule.span ℝ ({homogenize u} : Set (E d × ℝ))) = 1 :=
    finrank_span_singleton (ExposedEdgeCenters.point_ne_zero u)
  have hle : Submodule.span ℝ ({homogenize u} : Set (E d × ℝ)) ≤ center p a b :=
    Submodule.span_le.mpr (by intro z hz; rcases Set.mem_singleton_iff.mp hz with rfl; exact hu)
  have heq : Submodule.span ℝ ({homogenize u} : Set (E d × ℝ)) = center p a b :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hJ,hpoint])
  apply equal_evaluation_of_difference_on_point
  change differenceCenterVector (p a) (p b) ∈
    Submodule.span ℝ ({homogenize u} : Set (E d × ℝ))
  rw [heq]
  exact Submodule.subset_span (Set.mem_singleton _)

theorem decomposable_after_iso_of_essential_rank_two_meeting
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (f : E d → E d) (p : Fin 3 → ℝ × E d)
    (hparallel : IsParallelMap P f) (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hprivate : ∀ i : Fin 3, ∃ x ∈ P.vertices,
      f x = evaluate (p i) x ∧
        ∀ j : Fin 3, j ≠ i → f x ≠ evaluate (p j) x)
    (hrank : finrank ℝ (directionSpan p) = 2)
    (hmeet : ∃ w ∈ P.toSet, homogenize w ∈ directionSpan p)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hinj := essential_parameters_injective P f p hprivate
  by_cases hfamilies : ∀ i j : Fin 3, i ≠ j → Nonempty (CrossingFamily P color i j)
  · have hclasses : ∀ i, d - 1 ≤
        Fintype.card (NoncentralColor P color (directionSpan p) i) := by
      intro i
      obtain ⟨x,hx,hxi,hxp⟩ := hprivate i
      have h := three_color_class_bound P f p hparallel color hcover hrank i hx hxi hxp
      have hcard := coloredNoncentral_card_eq P color p i
      have hPd : P.dim = d := hP
      omega
    obtain ⟨w,hwP,hwD⟩ := hmeet
    have hresult := actual_three_center_geometric_reduction P hP hd color
      (directionSpan p) hrank (center p)
      (fun i j hij => center_rank_one p (fun h => hij (hinj h)))
      (fun i j _ => center_le_direction p i j) (center_symm p)
      (distinct_centers_of_rank_two p hinj hrank)
      (fun x y hxy _ => center_incidence_of_parallel_cover P f p hparallel color hcover x y hxy)
      w hwP hwD hclasses hfamilies hN Q iso
    rcases hresult with hdone | ⟨a,b,u,hab,hu,huJ,hempty,hcounts⟩
    · exact hdone
    · have hequal := equal_evaluation_of_actual_center_vertex p hinj a b hab u.val huJ
      have hswitch : f u.val = evaluate (p b) u.val := by
        have h := hcover u
        rw [hu] at h
        exact h.trans hequal
      have hnewcover := recolorVertex_cover P color u b f
        (fun i x => evaluate (p i) x) hcover hswitch
      exact decomposable_after_iso_of_essential_missing_family P hP hd f p hparallel
        (recolorVertex P color u b) hnewcover hprivate a b hab
        (fun e => hempty.false e) hN Q iso
  · push_neg at hfamilies
    obtain ⟨a,b,hab,hmissing⟩ := hfamilies
    exact decomposable_after_iso_of_essential_missing_family P hP hd f p hparallel
      color hcover hprivate a b hab (fun e => hmissing.false e) hN Q iso


theorem decomposable_after_iso_of_essential_three_cover_meeting
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (f : E d → E d) (p : Fin 3 → ℝ × E d)
    (hparallel : IsParallelMap P f) (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hprivate : ∀ i : Fin 3, ∃ x ∈ P.vertices,
      f x = evaluate (p i) x ∧
        ∀ j : Fin 3, j ≠ i → f x ≠ evaluate (p j) x)
    (hmeet : ∃ w ∈ P.toSet, homogenize w ∈ directionSpan p)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hinj := essential_parameters_injective P f p hprivate
  have hJ : finrank ℝ (center p 0 1) = 1 :=
    center_rank_one p (fun h => (by decide : (0 : Fin 3) ≠ 1) (hinj h))
  have hlow := Submodule.finrank_mono (center_le_direction p 0 1)
  rw [hJ] at hlow
  have hupp := direction_rank_le_two p
  have hranks : finrank ℝ (directionSpan p) = 1 ∨
      finrank ℝ (directionSpan p) = 2 := by omega
  rcases hranks with h | h
  · exact decomposable_after_iso_of_essential_rank_one P hP hd f p hparallel
      color hcover hprivate h hN Q iso
  · exact decomposable_after_iso_of_essential_rank_two_meeting P hP hd f p hparallel
      color hcover hprivate h hmeet hN Q iso

theorem essential_three_cover_nontrivial
    (P : ConvexPolytope d) (hdim : 3 ≤ P.dim)
    (f : E d → E d) (p : Fin 3 → ℝ × E d)
    (hparallel : IsParallelMap P f) (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hprivate : ∀ i : Fin 3, ∃ x ∈ P.vertices,
      f x = evaluate (p i) x ∧
        ∀ j : Fin 3, j ≠ i → f x ≠ evaluate (p j) x) :
    ¬ IsHomothetyOnVertices P f := by
  have hinj := essential_parameters_injective P f p hprivate
  have hclasses := essential_cover_two_vertices_per_color P hdim f p hparallel
    color hcover hprivate
  rintro ⟨a,b,hab⟩
  have heq (i : Fin 3) : p i = (a,b) := by
    obtain ⟨x,y,hxy,hx,hy⟩ := hclasses i
    have hx' : (p i).1 • x.val + (p i).2 = a • x.val + b := by
      have h := (hcover x).symm.trans (hab x.val x.property)
      simpa only [hx,evaluate] using h
    have hy' : (p i).1 • y.val + (p i).2 = a • y.val + b := by
      have h := (hcover y).symm.trans (hab y.val y.property)
      simpa only [hy,evaluate] using h
    obtain ⟨hs,hb⟩ := homothety_parameters_unique
      (fun h => hxy (Subtype.ext h)) hx' hy'
    exact Prod.ext hs hb
  exact (by decide : (0 : Fin 3) ≠ 1) (hinj ((heq 0).trans (heq 1).symm))

end Papers.Polytopes


end
end
end BundlePart51

section BundlePart52
/- Source: Papers/HomothetyConventionBridge.lean -/




@[expose] public section

/-! The two homogeneous-coordinate conventions in the geometric proof
are linearly equivalent: `(x,1)` corresponds to `(1,-x)`. -/
noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module Papers.HomogeneousSpanDimension
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d:ℕ} {I:Type*}

theorem signed_differenceCenterVector (p q:ℝ×E d) :
    signedHomogeneousEquiv (differenceCenterVector p q)=q-p := by
  apply Prod.ext
  · rfl
  · change -(-(q.2-p.2))=q.2-p.2
    exact neg_neg _

theorem parameterDirectionSpan_eq_signed_directionSpan (p:I→ℝ×E d) :
    parameterDirectionSpan (fun i=>(p i).1) (fun i=>(p i).2)=
      (Papers.ActualHomothetyClasses.directionSpan p).map signedHomogeneousEquiv.toLinearMap := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨⟨i,j⟩,rfl⟩
    refine ⟨differenceCenterVector (p j) (p i),Papers.ActualHomothetyClasses.difference_mem p j i,?_⟩
    exact signed_differenceCenterVector (p j) (p i)
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro z ⟨⟨i,j⟩,rfl⟩
    change signedHomogeneousEquiv (differenceCenterVector (p i) (p j))∈
      parameterDirectionSpan (fun k=>(p k).1) (fun k=>(p k).2)
    rw [signed_differenceCenterVector]
    exact Submodule.subset_span ⟨(j,i),rfl⟩

theorem vertexVector_mem_parameterDirectionSpan_iff (p:I→ℝ×E d) (x:E d) :
    vertexVector x∈parameterDirectionSpan (fun i=>(p i).1) (fun i=>(p i).2) ↔
      liftPoint x∈Papers.ActualHomothetyClasses.directionSpan p := by
  rw [parameterDirectionSpan_eq_signed_directionSpan]
  constructor
  · rintro ⟨v,hv,he⟩
    have hvx : v=liftPoint x := signedHomogeneousEquiv.injective he
    exact hvx ▸ hv
  · intro hx
    exact ⟨liftPoint x,hx,rfl⟩

theorem centralSection_nonempty_iff_actual_center
    (P:ConvexPolytope d) (p:I→ℝ×E d) :
    (centralSection P (fun i=>(p i).1) (fun i=>(p i).2)).Nonempty ↔
      ∃x∈P.toSet,liftPoint x∈Papers.ActualHomothetyClasses.directionSpan p := by
  constructor
  · rintro ⟨x,hx,hD⟩
    exact ⟨x,hx,(vertexVector_mem_parameterDirectionSpan_iff p x).mp hD⟩
  · rintro ⟨x,hx,hD⟩
    exact ⟨x,hx,(vertexVector_mem_parameterDirectionSpan_iff p x).mpr hD⟩

theorem centralSection_eq_empty_iff_no_actual_center
    (P:ConvexPolytope d) (p:I→ℝ×E d) :
    centralSection P (fun i=>(p i).1) (fun i=>(p i).2)=∅ ↔
      ¬∃x∈P.toSet,liftPoint x∈Papers.ActualHomothetyClasses.directionSpan p := by
  rw [←centralSection_nonempty_iff_actual_center]
  exact Set.not_nonempty_iff_eq_empty.symm

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart52

section BundlePart53
/- Source: Papers/ActualTwoCoverReductions.lean -/





@[expose] public section

/-! The actual essential two-homothety cover implies universal decomposability. -/
noncomputable section
namespace Papers.ActualTwoCoverReductions

open Set Module
open Papers.Polytopes Papers.ActualFaceOrder
open Papers.ActualHomothetyClasses Papers.ActualHomothetyCenters
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n m : ℕ}

theorem two_parameter_direction_eq
    (p : Fin 2 → ℝ × E n) :
    directionSpan p=center p 0 1 := by
  have h := direction_eq_two_centers p 0 1 1
    (by intro i; fin_cases i <;> simp)
  simpa only [sup_idem] using h

theorem decomposable_after_iso_of_essential_two_cover
    (P : ConvexPolytope n) (hP : P.IsFullDim) (hn : 3≤n)
    (f : E n → E n) (p : Fin 2 → ℝ × E n)
    (hf : IsParallelMap P f) (color : P.vertices → Fin 2)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hprivate : ∀ i : Fin 2, ∃ x ∈ P.vertices, f x = evaluate (p i) x ∧
      ∀ j : Fin 2, j ≠ i → f x ≠ evaluate (p j) x)
    (hN : P.vertices.card≤4*n-5)
    (Q : ConvexPolytope m) (iso : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hinj := essential_parameters_injective P f p hprivate
  have hJ : finrank ℝ (center p 0 1)=1 :=
    center_rank_one p (hinj.ne (by decide : (0:Fin 2)≠1))
  have hD : finrank ℝ (directionSpan p)=1 := by
    rw [two_parameter_direction_eq,hJ]
  have hclasses : ∀i:Fin 2,∃x y:P.vertices,x≠y ∧ color x=i ∧ color y=i := by
    intro i
    obtain ⟨v,hv,hvi,hpriv⟩ := hprivate i
    have hc := colored_essential_class_bound P f p hf color hcover i hv hvi hpriv
    rw [hD,hP] at hc
    have htwo : 1<(coloredNoncentral P color p i).card := by omega
    obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp htwo
    have hx' : color x = i ∧ HomogeneousSpanDimension.liftPoint x.val ∉ directionSpan p := by
      simpa only [coloredNoncentral,Finset.mem_filter,Finset.mem_univ,true_and] using hx
    have hy' : color y = i ∧ HomogeneousSpanDimension.liftPoint y.val ∉ directionSpan p := by
      simpa only [coloredNoncentral,Finset.mem_filter,Finset.mem_univ,true_and] using hy
    exact ⟨x,y,hxy,hx'.1,hy'.1⟩
  let col : P.vertices → Bool := fun v => finTwoEquiv (color v)
  have hclassesBool : ∀i:Bool,∃x y:P.vertices,x≠y ∧ col x=i ∧ col y=i := by
    intro i
    obtain ⟨x,y,hxy,hx,hy⟩ := hclasses (finTwoEquiv.symm i)
    exact ⟨x,y,hxy,by simp only [col,hx,Equiv.apply_symm_apply],
      by simp only [col,hy,Equiv.apply_symm_apply]⟩
  apply decomposable_after_iso_of_two_color_center P hP hn col
    (center p 0 1) hJ _ hclassesBool hN Q iso
  intro e
  have hl : color e.left=0 := finTwoEquiv.injective
    (show finTwoEquiv (color e.left)=finTwoEquiv 0 from e.property.2.1)
  have hr : color e.right=1 := finTwoEquiv.injective
    (show finTwoEquiv (color e.right)=finTwoEquiv 1 from e.property.2.2)
  have h := center_incidence_of_parallel_cover P f p hf color hcover e.left e.right e.isEdge
  simpa only [hl,hr,CrossingFamily.line] using h

end Papers.ActualTwoCoverReductions


end
end
end BundlePart53

section BundlePart54
/- Source: Papers/SegmentSummandPersistence.lean -/




@[expose] public section

/-! The segment case uses the literal two-valued summand map and the
actual two-homothety reconstruction theorem. -/

noncomputable section
namespace Papers.SegmentSummandPersistence

open Set Module
open Papers.Polytopes Papers.ProperMinkowskiMap
open Papers.ActualFaceOrder Papers.ActualHomothetyClasses
open Papers.ActualTwoCoverReductions
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n m : ℕ}

theorem segment_summand_persists
    (P A B : ConvexPolytope n) (hP : P.IsFullDim) (hn : 3 ≤ n)
    (hsum : P.toSet = A.toSet + B.toSet) (hAdim : A.dim = 1)
    (hN : P.vertices.card ≤ 4*n-5)
    (Q : ConvexPolytope m) (φ : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  obtain ⟨f,a,b,hab,hf,hnon,hvalues,ha,hb⟩ :=
    actual_two_constant_homotheties_of_segment_summand P A B hsum hAdim
      (by rw [hP]; omega)
  let p : Fin 2 → ℝ × E n := fun i => if i=0 then (0,a) else (0,b)
  let color : P.vertices → Fin 2 := fun v => if f v.val=a then 0 else 1
  have hcover : ∀v:P.vertices,f v.val=evaluate (p (color v)) v.val := by
    intro v
    rcases hvalues v.val v.property with h | h
    · simp [color,h,p,evaluate]
    · simp [color,h,hab.symm,p,evaluate]
  have hprivate : ∀i:Fin 2,∃x∈P.vertices,f x=evaluate (p i) x ∧
      ∀j:Fin 2,j≠i→f x≠evaluate (p j) x := by
    intro i
    fin_cases i
    · obtain ⟨x,hx,hfx⟩ := ha
      refine ⟨x,hx,?_,?_⟩
      · simpa [p,evaluate] using hfx
      · intro j hj
        fin_cases j
        · exact (hj rfl).elim
        · simpa [p,evaluate,hfx] using hab
    · obtain ⟨x,hx,hfx⟩ := hb
      refine ⟨x,hx,?_,?_⟩
      · simpa [p,evaluate] using hfx
      · intro j hj
        fin_cases j
        · simpa [p,evaluate,hfx] using hab.symm
        · exact (hj rfl).elim
  exact decomposable_after_iso_of_essential_two_cover P hP hn f p hf color
    hcover hprivate hN Q φ

end Papers.SegmentSummandPersistence

end
end
end BundlePart54

section BundlePart55
/- Source: Papers/MinkowskiCodimensionTwoExtraGeometry.lean -/






@[expose] public section

/-! The saturated extra face in the all-homothetic codimension-two case. -/
noncomputable section
namespace Papers.MinkowskiCodimensionTwoExtraGeometry

open Set Module
open Papers.Polytopes Papers.MinkowskiFaces Papers.MinkowskiVertexMap
open Papers.MinkowskiHomotheticCore Papers.MinkowskiExtraFace
open Papers.MinkowskiQuotientCounting Papers.MinkowskiSummandFibers
open Papers.MinkowskiCodimensionTwoCounts Papers.LinearImageFibers
open Papers.FiniteExposedFaces Papers.FaceVertexCardinality Papers.ProperMinkowskiMap
open Papers.ParallelSupportEvaluation Papers.ParallelFaceDirections
open Papers.PolytopeSimpleTailFace Papers.MinkowskiSmallFibers
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators Pointwise

variable {n : ℕ}

theorem homothetic_extra_saturation
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hsum : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : (quotientPolytope P A).dim=2)
    (hN : P.vertices.card≤4*n-5)
    (hhom : ∀q:(quotientPolytope P A).vertices,SummandHomotheticFiber P A B hsum q)
    (hextra : (extraVertices P A).Nonempty) :
    A.vertices.card=A.dim+1 ∧ (extraVertices P A).card=A.dim ∧
      P.vertices.card=4*A.dim+3 := by
  have hdim := quotient_dimension_add_summand_dimension P A hfull
  have hQcard := quotient_has_three_vertices_of_codimension_two P A B hfull hsum hr hq hN
  have hAI := (vertices_affineIndependent_iff (quotientPolytope P A)).mpr (by omega)
  have hex := extra_card_ge_summand_dimension P A B hsum (by omega) hAI hhom hextra
  have hpart := fiber_extra_partition P A
  have hfiber : (∑q:(quotientPolytope P A).vertices,
      (vertexFiber P (summandProjection A) q).vertices.card)=3*A.vertices.card := by
    simp_rw [homothetic_summand_fiber_card P A B hsum _ (hhom _)]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul,hQcard]
  rw [hfiber] at hpart
  have hA := dimension_add_one_le_vertices A
  omega

theorem outside_core_vertices_eq_extras (P A : ConvexPolytope n) :
    (P.vertices.filter fun x => x∉vertexCore P A)=extraVertices P A := by
  ext x
  simp only [Finset.mem_filter,extraVertices]
  constructor
  · rintro ⟨hx,hout⟩
    refine ⟨hx,?_⟩
    intro hq
    exact hout (subset_convexHull ℝ _ (Finset.mem_filter.mpr ⟨hx,hq⟩))
  · rintro ⟨hx,hq⟩
    exact ⟨hx,extra_vertex_not_in_core P A hx hq⟩

/-- An exposed summand face is exactly the image of the exposed sum-face
vertices under the actual summand map. -/
theorem exposed_face_label_image
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    (w : E n →L[ℝ] ℝ) :
    leftVertexMap P A B hsum ''
      ((facePolytope P (maxFace_isFace P w)).vertices : Set (E n)) =
      ((facePolytope A (maxFace_isFace A w)).vertices : Set (E n)) := by
  let PX := facePolytope P (maxFace_isFace P w)
  let AX := facePolytope A (maxFace_isFace A w)
  let BX := facePolytope B (maxFace_isFace B w)
  have hXsum : PX.toSet=AX.toSet+BX.toSet := by
    simp only [PX,AX,BX,facePolytope_toSet]
    rw [hsum,maxFace_add]
  have hmaps (x:E n) (hx:x∈PX.vertices) :
      leftVertexMap PX AX BX hXsum x=leftVertexMap P A B hsum x := by
    have hxP := ((facePolytope_vertex_iff P (maxFace_isFace P w) x).mp hx).1
    have h1 := leftVertexMap_spec PX AX BX hXsum hx
    have h2 := leftVertexMap_spec P A B hsum hxP
    let a := leftVertexMap PX AX BX hXsum x
    let c := leftVertexMap P A B hsum x
    have ha : a∈A.toSet := by
      have hh := (facePolytope_vertex_iff A (maxFace_isFace A w) a).mp h1.1
      exact subset_convexHull ℝ _ hh.1
    have hb : x-a∈B.toSet := by
      have hh := (facePolytope_vertex_iff B (maxFace_isFace B w) (x-a)).mp h1.2
      exact subset_convexHull ℝ _ hh.1
    have hc : c∈A.toSet := subset_convexHull ℝ _ h2.1
    have hd : x-c∈B.toSet := subset_convexHull ℝ _ h2.2
    have hext : a+(x-a)∈(A.toSet+B.toSet).extremePoints ℝ := by
      rw [← hsum]
      convert vertex_mem_body_extremePoints P hxP using 1 <;> abel
    exact (sum_components_unique ha hb hc hd hext (by abel)).1
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [← hmaps x hx]
    exact (leftVertexMap_spec PX AX BX hXsum hx).1
  · intro ha
    obtain ⟨x,hx,hxa⟩ := leftVertexMap_surjective PX AX BX hXsum ha
    exact ⟨x,hx,(hmaps x hx).symm.trans hxa⟩

/-- Equality in the vertex budget produces a simplex face containing
exactly the extra vertices, with its direction inside the summand. -/
theorem exists_extra_simplex_face
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hsum : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : (quotientPolytope P A).dim=2)
    (hN : P.vertices.card≤4*n-5)
    (hhom : ∀q:(quotientPolytope P A).vertices,SummandHomotheticFiber P A B hsum q)
    (hextra : (extraVertices P A).Nonempty) :
    ∃w:E n →L[ℝ] ℝ,
      (facePolytope P (maxFace_isFace P w)).vertices=extraVertices P A ∧
      AffineIndependent ℝ (fun v:extraVertices P A => v.val) ∧
      vectorSpan ℝ (maxFace P.toSet w.toLinearMap)≤(summandProjection A).ker ∧
      0<(facePolytope A (maxFace_isFace A w)).dim := by
  obtain ⟨hAcard,hXcard,hPcard⟩ :=
    homothetic_extra_saturation P A B hfull hsum hr hq hN hhom hextra
  have hQcard := quotient_has_three_vertices_of_codimension_two P A B hfull hsum hr hq hN
  have hAI := (vertices_affineIndependent_iff (quotientPolytope P A)).mpr (by omega)
  obtain ⟨x,hx⟩ := hextra
  obtain ⟨F,w,b,hface,himage,hdis⟩ :=
    extra_face_contains_translated_summand_facet P A B hsum (by omega) hAI hhom hx
  have hinj : Function.Injective (homothetyMap (1:ℝ) b).linear := by
    intro x y h
    change (1:ℝ)•x=(1:ℝ)•y at h
    simpa only [one_smul] using h
  have hbd : (P.vertices.filter fun x => x∉vertexCore P A).card≤
      finrank ℝ (vectorSpan ℝ F.val.val)+1 := by
    rw [outside_core_vertices_eq_extras,hXcard]
    have hh := F.property.2
    change faceDim F.val.val+1=A.dim at hh
    exact hh.ge
  obtain ⟨hvertices,hbody,hcount,hdir,hind⟩ :=
    Papers.ExposedFaceCountEquality.equality_case P.vertices w.toLinearMap
      (vertexCore P A) F.val.property.2 (homothetyMap 1 b) hinj himage hdis hbd
  change (P.vertices.filter fun x => x∈maxFace P.toSet w.toLinearMap)=
    (P.vertices.filter fun x => x∉vertexCore P A) at hvertices
  change vectorSpan ℝ (maxFace P.toSet w.toLinearMap)=
    (vectorSpan ℝ F.val.val).map (homothetyMap 1 b).linear at hdir
  rw [outside_core_vertices_eq_extras] at hvertices hind
  have hPX : (facePolytope P (maxFace_isFace P w)).vertices=extraVertices P A := by
    rw [← hvertices]
    ext v
    simp only [facePolytope_vertex_iff,Finset.mem_filter]
  refine ⟨w,hPX,hind,?_,?_⟩
  · rw [hdir,summandProjection_kernel]
    have hmap : (homothetyMap (1:ℝ) b).linear=LinearMap.id := by
      ext x
      simp [homothetyMap]
    rw [hmap,Submodule.map_id]
    exact vectorSpan_mono ℝ (face_subset_toSet A F.val.property)
  · have hd := F.property.2
    rw [facePolytope_dim,hface]
    omega

theorem extra_label_injective_and_quotient_constant
    (P A B : ConvexPolytope n) (hfull : P.IsFullDim)
    (hsum : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : (quotientPolytope P A).dim=2)
    (hN : P.vertices.card≤4*n-5)
    (hhom : ∀q:(quotientPolytope P A).vertices,SummandHomotheticFiber P A B hsum q)
    (hextra : (extraVertices P A).Nonempty) :
    Set.InjOn (leftVertexMap P A B hsum) (extraVertices P A : Set (E n)) ∧
      ∀x∈extraVertices P A,∀y∈extraVertices P A,
        summandProjection A x=summandProjection A y := by
  obtain ⟨hAcard,hXcard,hPcard⟩ :=
    homothetic_extra_saturation P A B hfull hsum hr hq hN hhom hextra
  obtain ⟨w,hX,hAI,hdir,hApos⟩ :=
    exists_extra_simplex_face P A B hfull hsum hr hq hN hhom hextra
  let R := facePolytope P (maxFace_isFace P w)
  let C := facePolytope A (maxFace_isFace A w)
  let f := leftVertexMap P A B hsum
  have hR : R.vertices=extraVertices P A := hX
  have hRI : AffineIndependent ℝ (fun x:R.vertices => x.val) := by
    rw [hR]
    exact hAI
  have hXsub : extraVertices P A⊆P.vertices := Finset.filter_subset _ _
  have hclique : ∀x∈extraVertices P A,∀y∈extraVertices P A,x≠y→
      GeneralVertexStep P x y := by
    intro x hx y hy hxy
    have hxR : x∈R.vertices := by rwa [hR]
    have hyR : y∈R.vertices := by rwa [hR]
    have hedge := simplex_graph_adj R hRI ⟨x,hxR⟩ ⟨y,hyR⟩
      (fun h => hxy (congrArg Subtype.val h))
    exact facePolytope_step P (maxFace_isFace P w) ⟨hyR,hxy,hedge.2⟩
  obtain ⟨α,b,hf⟩ := parallel_map_homothetic_on_clique P (extraVertices P A)
    hXsub (by omega) hclique f (leftVertexMap_parallel P A B hsum)
  have hα : α≠0 := by
    intro hzero
    have hCcard : 1<C.vertices.card := by
      have hh := dimension_add_one_le_vertices C
      change 0<C.dim at hApos
      omega
    obtain ⟨a,ha,c,hc,hac⟩ := Finset.one_lt_card.mp hCcard
    have himage := exposed_face_label_image P A B hsum w
    have haimage : a∈f '' (extraVertices P A : Set (E n)) := by
      rw [← hR]
      exact himage.symm ▸ ha
    have hcimage : c∈f '' (extraVertices P A : Set (E n)) := by
      rw [← hR]
      exact himage.symm ▸ hc
    obtain ⟨x,hx,hxa⟩ := haimage
    obtain ⟨y,hy,hyc⟩ := hcimage
    have hfx := hf x hx
    have hfy := hf y hy
    rw [hzero,zero_smul,zero_add] at hfx hfy
    exact hac (hxa.symm.trans (hfx.trans (hfy.symm.trans hyc)))
  constructor
  · intro x hx y hy hxy
    have hh : α•x=α•y := add_right_cancel (by rw [← hf x hx,← hf y hy]; exact hxy)
    exact smul_right_injective _ hα hh
  · intro x hx y hy
    have hxF := ((facePolytope_vertex_iff P (maxFace_isFace P w) x).mp
      (show x∈R.vertices by rwa [hR])).2
    have hyF := ((facePolytope_vertex_iff P (maxFace_isFace P w) y).mp
      (show y∈R.vertices by rwa [hR])).2
    have hxy := hdir (vsub_mem_vectorSpan ℝ hxF hyF)
    change summandProjection A (x-y)=0 at hxy
    rw [map_sub] at hxy
    exact sub_eq_zero.mp hxy

end Papers.MinkowskiCodimensionTwoExtraGeometry

end
end
end BundlePart55

section BundlePart56
/- Source: Papers/MinkowskiCodimensionTwoExtraCenters.lean -/




@[expose] public section

/-! Combinatorially forced edge centers in the saturated extra-face case. -/
noncomputable section
namespace Papers.MinkowskiCodimensionTwoExtraCenters

open Set Module
open Papers.Polytopes Papers.MinkowskiFaces Papers.MinkowskiVertexMap
open Papers.MinkowskiHomotheticCore Papers.MinkowskiExtraFace
open Papers.MinkowskiQuotientCounting Papers.MinkowskiSummandFibers
open Papers.MinkowskiCodimensionTwoCounts Papers.LinearImageFibers
open Papers.MinkowskiCodimensionTwoExtraGeometry Papers.MinkowskiFiberDichotomy
open Papers.ParallelSupportEvaluation Papers.ParallelFaceDirections
open Papers.PolytopeSimpleTailFace Papers.MinkowskiSmallFibers
open Papers.MinkowskiCrossingCenters Papers.MinkowskiCofacialGeometry
open Papers.Polytopes.CrossingFamilyTransport Papers.ActualFaceOrder
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators Pointwise

variable {n m : ℕ}

theorem three_labels_twoFace_quotient_constant
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    (a b c : A.vertices) (hab:a≠b) (hac:a≠c) (hbc:b≠c)
    (F:Set (E n)) (hF:P.IsFace F) (hdF:faceDim F=2)
    (x y z:P.vertices) (hxF:x.val∈F) (hyF:y.val∈F) (hzF:z.val∈F)
    (hfx:summandLabel P A B hsum x=a)
    (hfy:summandLabel P A B hsum y=b)
    (hfz:summandLabel P A B hsum z=c) :
    ∀v∈F,summandProjection A v=summandProjection A x.val := by
  let U := Submodule.span ℝ (Set.range ![b.val-a.val,c.val-a.val])
  have hU : finrank ℝ U=2 := by
    simpa only [U,Fintype.card_fin] using
      finrank_span_eq_card (three_vertex_differences_independent A a b c hab hac hbc)
  have hxR := (facePolytope_vertex_iff P hF x.val).mpr ⟨x.property,hxF⟩
  have hyR := (facePolytope_vertex_iff P hF y.val).mpr ⟨y.property,hyF⟩
  have hzR := (facePolytope_vertex_iff P hF z.val).mpr ⟨z.property,hzF⟩
  have hba := parallel_value_difference_mem_face_direction P (leftVertexMap P A B hsum)
    (leftVertexMap_parallel P A B hsum) hF hxR hyR
  have hca := parallel_value_difference_mem_face_direction P (leftVertexMap P A B hsum)
    (leftVertexMap_parallel P A B hsum) hF hxR hzR
  have hfx' := congrArg Subtype.val hfx
  have hfy' := congrArg Subtype.val hfy
  have hfz' := congrArg Subtype.val hfz
  change leftVertexMap P A B hsum x.val=a.val at hfx'
  change leftVertexMap P A B hsum y.val=b.val at hfy'
  change leftVertexMap P A B hsum z.val=c.val at hfz'
  rw [hfx',hfy'] at hba
  rw [hfx',hfz'] at hca
  have hUF : U=vectorSpan ℝ F := by
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_le.mpr
      rintro v ⟨i,rfl⟩
      fin_cases i
      · exact hba
      · exact hca
    · change faceDim F≤finrank ℝ U
      rw [hdF,hU]
  have hker : U≤(summandProjection A).ker := by
    rw [summandProjection_kernel]
    apply Submodule.span_le.mpr
    rintro v ⟨i,rfl⟩
    fin_cases i
    · exact vsub_mem_vectorSpan ℝ (subset_convexHull ℝ _ b.property)
        (subset_convexHull ℝ _ a.property)
    · exact vsub_mem_vectorSpan ℝ (subset_convexHull ℝ _ c.property)
        (subset_convexHull ℝ _ a.property)
  intro v hv
  have hh := hker (hUF.symm ▸ vsub_mem_vectorSpan ℝ hv hxF)
  change summandProjection A (v-x.val)=0 at hh
  rw [map_sub] at hh
  exact sub_eq_zero.mp hh

theorem crossing_projection_eq
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    (a b:A.vertices) (hab:a≠b)
    (e:CrossingFamily P (summandLabel P A B hsum) a b) :
    summandProjection A e.left.val=summandProjection A e.right.val := by
  by_contra hne
  have heq := Papers.MinkowskiShephardNoExtras.label_eq_of_distinct_quotient_endpoints
    P A B hsum e.left.property e.isEdge hne
  have ha := congrArg Subtype.val e.property.2.1
  have hb := congrArg Subtype.val e.property.2.2
  exact hab (Subtype.ext (ha.symm.trans (heq.trans hb)))

theorem extra_edge_face_avoids_missing_label
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    (a b c:A.vertices) (hab:a≠b)
    (e:CrossingFamily P (summandLabel P A B hsum) a b)
    (he:e.left.val∈extraVertices P A)
    (hc:∀v∈extraVertices P A,leftVertexMap P A B hsum v≠c.val)
    (F:Set (E n)) (hF:P.IsFace F) (hdF:faceDim F=2)
    (heF:CrossingFamily.liesIn F e) :
    ∀z:P.vertices,z.val∈F→summandLabel P A B hsum z≠c := by
  have heq := crossing_projection_eq P A B hsum a b hab e
  have her : e.right.val∈extraVertices P A := by
    apply Finset.mem_filter.mpr
    refine ⟨e.right.property,?_⟩
    rw [← heq]
    exact (Finset.mem_filter.mp he).2
  have hac:a≠c := by
    intro h
    apply hc e.left.val he
    exact congrArg Subtype.val (e.property.2.1.trans h)
  have hbc:b≠c := by
    intro h
    apply hc e.right.val her
    exact congrArg Subtype.val (e.property.2.2.trans h)
  intro z hz hzc
  have hp := three_labels_twoFace_quotient_constant P A B hsum a b c hab hac hbc
    F hF hdF e.left e.right z heF.1 heF.2 hz e.property.2.1 e.property.2.2 hzc z.val hz
  have hzextra : z.val∈extraVertices P A := by
    apply Finset.mem_filter.mpr
    refine ⟨z.property,?_⟩
    rw [hp]
    exact (Finset.mem_filter.mp he).2
  exact hc z.val hzextra (congrArg Subtype.val hzc)

theorem family_card_le_four
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    (hQcard:(quotientPolytope P A).vertices.card=3)
    (hhom:∀q:(quotientPolytope P A).vertices,SummandHomotheticFiber P A B hsum q)
    (hinj:Set.InjOn (leftVertexMap P A B hsum) (extraVertices P A : Set (E n)))
    (a b:A.vertices) (hab:a≠b) :
    Fintype.card (CrossingFamily P (summandLabel P A B hsum) a b)≤4 := by
  let F := CrossingFamily P (summandLabel P A B hsum) a b
  let position : F→Option (quotientPolytope P A).vertices := fun e =>
    if h:summandProjection A e.left.val∈(quotientPolytope P A).vertices
      then some ⟨summandProjection A e.left.val,h⟩ else none
  have hposition : Function.Injective position := by
    intro e f hef
    apply (crossing_endpoint_injective P A B hsum a b hab).1
    have hlabels : leftVertexMap P A B hsum e.left.val=leftVertexMap P A B hsum f.left.val :=
      (congrArg Subtype.val e.property.2.1).trans (congrArg Subtype.val f.property.2.1).symm
    by_cases he:summandProjection A e.left.val∈(quotientPolytope P A).vertices
    · by_cases hf:summandProjection A f.left.val∈(quotientPolytope P A).vertices
      · have hq' : (⟨summandProjection A e.left.val,he⟩:(quotientPolytope P A).vertices)=
            ⟨summandProjection A f.left.val,hf⟩ := by
          simpa only [position,dif_pos he,dif_pos hf,Option.some.injEq] using hef
        have hπ := congrArg Subtype.val hq'
        let q:(quotientPolytope P A).vertices := ⟨summandProjection A e.left.val,he⟩
        apply fiber_map_injective_of_homothetic P (leftVertexMap P A B hsum)
          (summandProjection A) q (hhom q)
        · rw [vertexFiber_vertices]
          exact Finset.mem_filter.mpr ⟨e.left.property,rfl⟩
        · rw [vertexFiber_vertices]
          exact Finset.mem_filter.mpr ⟨f.left.property,hπ.symm⟩
        · exact hlabels
      · simp [position,he,hf] at hef
    · by_cases hf:summandProjection A f.left.val∈(quotientPolytope P A).vertices
      · simp [position,he,hf] at hef
      · exact hinj (Finset.mem_filter.mpr ⟨e.left.property,he⟩)
          (Finset.mem_filter.mpr ⟨f.left.property,hf⟩) hlabels
  have hc := Fintype.card_le_of_injective position hposition
  simpa only [Fintype.card_option,Fintype.card_coe,hQcard] using hc

theorem family_card_le_three_of_no_extra_edge
    (P A B : ConvexPolytope n) (hsum : P.toSet=A.toSet+B.toSet)
    (hQcard:(quotientPolytope P A).vertices.card=3)
    (hhom:∀q:(quotientPolytope P A).vertices,SummandHomotheticFiber P A B hsum q)
    (a b:A.vertices) (hab:a≠b)
    (he:∀e:CrossingFamily P (summandLabel P A B hsum) a b,
      e.left.val∉extraVertices P A) :
    Fintype.card (CrossingFamily P (summandLabel P A B hsum) a b)≤3 := by
  let F := CrossingFamily P (summandLabel P A B hsum) a b
  have hpos (e:F) : summandProjection A e.left.val∈(quotientPolytope P A).vertices := by
    by_contra hn
    exact he e (Finset.mem_filter.mpr ⟨e.left.property,hn⟩)
  let position : F→(quotientPolytope P A).vertices := fun e => ⟨_,hpos e⟩
  have hposition : Function.Injective position := by
    intro e f hef
    apply (crossing_endpoint_injective P A B hsum a b hab).1
    apply fiber_map_injective_of_homothetic P (leftVertexMap P A B hsum)
      (summandProjection A) (position e) (hhom (position e))
    · rw [vertexFiber_vertices]
      exact Finset.mem_filter.mpr ⟨e.left.property,rfl⟩
    · rw [vertexFiber_vertices]
      exact Finset.mem_filter.mpr ⟨f.left.property,(congrArg Subtype.val hef).symm⟩
    · exact (congrArg Subtype.val e.property.2.1).trans (congrArg Subtype.val f.property.2.1).symm
  have hc := Fintype.card_le_of_injective position hposition
  simpa only [Fintype.card_coe,hQcard] using hc

set_option maxHeartbeats 1600000 in
theorem family_degree_with_one_label_excluded
    (P A B : ConvexPolytope n) (hP:P.IsFullDim)
    (hsum:P.toSet=A.toSet+B.toSet)
    (a b c:A.vertices) (hab:a≠b) (hac:a≠c) (hbc:b≠c)
    (e:CrossingFamily P (summandLabel P A B hsum) a b)
    (havoid:∀F:Set (E n),P.IsFace F→faceDim F=2→CrossingFamily.liesIn F e→
      ∀z:P.vertices,z.val∈F→summandLabel P A B hsum z≠c) :
    n+2≤(CrossingFamily.cofacialGraph (P:=P)
      (color:=summandLabel P A B hsum) (a:=a) (b:=b)).degree e+A.vertices.card := by
  let color := summandLabel P A B hsum
  let G := CrossingFamily.cofacialGraph (P:=P) (color:=color) (a:=a) (b:=b)
  let faces := incidentTwoFaces P e.left.val e.right.val
  let bad (F:ActualFaceType P) := ∃z:P.vertices,z.val∈F.val ∧ color z≠a ∧ color z≠b
  let partner (F:ActualFaceType P) (f:CrossingFamily P color a b) :=
    e≠f ∧ CrossingFamily.liesIn F.val f
  have hmem (F:ActualFaceType P) (hF:F∈faces) :
      faceDim F.val=2 ∧ CrossingFamily.liesIn F.val e := (Finset.mem_filter.mp hF).2
  have hbad : (faces.filter bad).card≤A.vertices.card-3 := by
    let others : Finset A.vertices := ((Finset.univ.erase a).erase b).erase c
    have hchoose (F:faces.filter bad) :
        ∃k:A.vertices,k∈others ∧ ∃z∈(facePolytope P F.val.property).vertices,
          leftVertexMap P A B hsum z=k.val := by
      obtain ⟨z,hz,hza,hzb⟩ := (Finset.mem_filter.mp F.property).2
      have hzc := havoid F.val.val F.val.property
        (hmem _ (Finset.mem_filter.mp F.property).1).1
        (hmem _ (Finset.mem_filter.mp F.property).1).2 z hz
      change color z≠c at hzc
      refine ⟨color z,?_,z.val,?_,rfl⟩
      · simp [others,hza,hzb,hzc]
      · exact (facePolytope_vertex_iff P F.val.property z.val).mpr ⟨z.property,hz⟩
    let pick : (faces.filter bad) → others :=
      fun F => ⟨(hchoose F).choose,(hchoose F).choose_spec.1⟩
    have hinj : Function.Injective pick := by
      intro F H heq
      apply Subtype.ext
      apply Subtype.ext
      have hFc := (hchoose F).choose_spec.2
      have hHc := (hchoose H).choose_spec.2
      have hc' : (hchoose F).choose=(hchoose H).choose := congrArg Subtype.val heq
      rw [← hc'] at hHc
      have hother : (hchoose F).choose≠a ∧ (hchoose F).choose≠b := by
        have hmemC := (hchoose F).choose_spec.1
        have hmemB := (Finset.mem_erase.mp hmemC).2
        have hmemA := (Finset.mem_erase.mp hmemB).2
        exact ⟨(Finset.mem_erase.mp hmemA).1,(Finset.mem_erase.mp hmemB).1⟩
      exact twoFaces_eq_of_three_parallel_values P A (leftVertexMap P A B hsum)
        (leftVertexMap_parallel P A B hsum) a b (hchoose F).choose hab
        hother.1.symm hother.2.symm F.val.val H.val.val F.val.property H.val.property
        (hmem _ (Finset.mem_filter.mp F.property).1).1
        (hmem _ (Finset.mem_filter.mp H.property).1).1 e.left e.right
        (hmem _ (Finset.mem_filter.mp F.property).1).2.1
        (hmem _ (Finset.mem_filter.mp F.property).1).2.2
        (hmem _ (Finset.mem_filter.mp H.property).1).2.1
        (hmem _ (Finset.mem_filter.mp H.property).1).2.2
        (congrArg Subtype.val e.property.2.1) (congrArg Subtype.val e.property.2.2) hFc hHc
    have hc' := Fintype.card_le_of_injective pick hinj
    have hc'' : (faces.filter bad).card≤others.card := by
      simpa only [Fintype.card_coe] using hc'
    have ho : others.card=A.vertices.card-3 := by
      simp [others,hab,Ne.symm hab,hac,Ne.symm hac,hbc,Ne.symm hbc]
      omega
    rwa [ho] at hc''
  have hfaces := incidentTwoFaces_card_actual P e.left.property e.isEdge
  have hcount := CofacialCounting.incident_count_le_degree_add_bad G e faces bad partner
    (A.vertices.card-3) hbad ?_ ?_
  · have hAcard : 3≤A.vertices.card := by
      have hc' := Finset.card_le_card (Finset.subset_univ ({a,b,c}:Finset A.vertices))
      simpa [hab,hac,hbc] using hc'
    change P.dim=n at hP
    change P.dim≤faces.card+1 at hfaces
    change n+2≤G.degree e+A.vertices.card
    omega
  · intro F hF hgood
    obtain ⟨f,hef,hfF⟩ := CrossingFamily.second_edge_in_twoFace hab e F.val F.property
      (hmem F hF).1 (hmem F hF).2 (by
        intro x y hxF hyF hxy hxa hya
        by_contra hyb
        exact hgood ⟨y,hyF,hya,hyb⟩)
    exact ⟨f,⟨hef,F.val,F.property,(hmem F hF).1,(hmem F hF).2,hfF⟩,hef,hfF⟩
  · intro F hF H hH f hfF hfH
    apply Subtype.ext
    exact actual_twoFaces_eq_of_two_lines P F.val H.val F.property H.property
      F.property.2 H.property.2 (hmem F hF).1 (hmem H hH).1 e.line f.line
      (CrossingFamily.pair_line_rank_ge_three hab e f hfF.1)
      (Papers.Polytopes.ExposedProjectiveBridge.line_le_span (hmem F hF).2.1 (hmem F hF).2.2)
      (Papers.Polytopes.ExposedProjectiveBridge.line_le_span (hmem H hH).2.1 (hmem H hH).2.2)
      (Papers.Polytopes.ExposedProjectiveBridge.line_le_span hfF.2.1 hfF.2.2)
      (Papers.Polytopes.ExposedProjectiveBridge.line_le_span hfH.2.1 hfH.2.2)

theorem exists_label_missing_from_extras
    (P A B : ConvexPolytope n) (hsum:P.toSet=A.toSet+B.toSet)
    (hcard:(extraVertices P A).card<A.vertices.card) :
    ∃c:A.vertices,∀x∈extraVertices P A,leftVertexMap P A B hsum x≠c.val := by
  have himage : (extraVertices P A).image (leftVertexMap P A B hsum)⊆A.vertices := by
    intro a ha
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact (leftVertexMap_spec P A B hsum (Finset.mem_filter.mp hx).1).1
  have hstrict : (extraVertices P A).image (leftVertexMap P A B hsum)≠A.vertices := by
    intro heq
    have hc := Finset.card_image_le (s:=extraVertices P A) (f:=leftVertexMap P A B hsum)
    rw [heq] at hc
    omega
  obtain ⟨c,hc,hnot⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨himage,hstrict⟩)
  refine ⟨⟨c,hc⟩,?_⟩
  intro x hx heq
  exact hnot (Finset.mem_image.mpr ⟨x,hx,heq⟩)

theorem all_homothetic_extra_centers
    (P A B : ConvexPolytope n) (hfull:P.IsFullDim)
    (hsum:P.toSet=A.toSet+B.toSet)
    (hr:2≤A.dim) (hq:(quotientPolytope P A).dim=2)
    (hN:P.vertices.card≤4*n-5)
    (hhom:∀q:(quotientPolytope P A).vertices,SummandHomotheticFiber P A B hsum q)
    (hextra:(extraVertices P A).Nonempty)
    (Q:ConvexPolytope m) (φ:FaceObject P ≃o FaceObject Q)
    (a b:A.vertices) (hab:a≠b)
    (e:CrossingFamily Q (colorAlong φ (summandLabel P A B hsum)) a b) :
    ∃J:Submodule ℝ (E m×ℝ),finrank ℝ J=1 ∧
      ∀f:CrossingFamily Q (colorAlong φ (summandLabel P A B hsum)) a b,J≤f.line := by
  let color := summandLabel P A B hsum
  have hdim := quotient_dimension_add_summand_dimension P A hfull
  have hQcard := quotient_has_three_vertices_of_codimension_two P A B hfull hsum hr hq hN
  obtain ⟨hAcard,hXcard,hPcard⟩ := homothetic_extra_saturation P A B hfull hsum hr hq hN hhom hextra
  have hinj := (extra_label_injective_and_quotient_constant P A B hfull hsum hr hq hN hhom hextra).1
  have hdP (f:CrossingFamily P color a b) :
      2≤(CrossingFamily.cofacialGraph (P:=P) (color:=color) (a:=a) (b:=b)).degree f := by
    have hh := summand_family_cofacial_degree P A B hfull hsum a b hab f
    omega
  have hdQ := minimum_degree_transport φ color a b 2 hdP
  have hnQ := no_three_transport φ color a b (crossing_no_three P A B hsum a b hab)
  by_cases hex : ∃f:CrossingFamily P color a b,f.left.val∈extraVertices P A
  · obtain ⟨f,hf⟩ := hex
    obtain ⟨c,hc⟩ := exists_label_missing_from_extras P A B hsum (by omega)
    have hac:a≠c := by
      intro h
      exact hc f.left.val hf (congrArg Subtype.val (f.property.2.1.trans h))
    have hbc:b≠c := by
      intro h
      have hπ := crossing_projection_eq P A B hsum a b hab f
      have hright:f.right.val∈extraVertices P A := by
        apply Finset.mem_filter.mpr
        refine ⟨f.right.property,?_⟩
        rw [← hπ]
        exact (Finset.mem_filter.mp hf).2
      exact hc f.right.val hright (congrArg Subtype.val (f.property.2.2.trans h))
    have hhigh := family_degree_with_one_label_excluded P A B hfull hsum a b c hab hac hbc f
      (extra_edge_face_avoids_missing_label P A B hsum a b c hab f hf hc)
    have hhigh' : 3≤(CrossingFamily.cofacialGraph (P:=P) (color:=color) (a:=a) (b:=b)).degree f := by
      omega
    have hc4 := family_card_le_four P A B hsum hQcard hhom hinj a b hab
    rw [family_card_eq φ color a b] at hc4
    apply CrossingFamily.concurrent_of_four_with_high_degree hab hdQ hc4 hnQ
      (crossingEquiv φ color a b f)
    rw [degree_eq]
    exact hhigh'
  · have hn : ∀f:CrossingFamily P color a b,f.left.val∉extraVertices P A := by
      simpa only [not_exists] using hex
    have hc3 := family_card_le_three_of_no_extra_edge P A B hsum hQcard hhom a b hab hn
    rw [family_card_eq φ color a b] at hc3
    change Fintype.card (CrossingFamily Q
      (colorAlong φ (summandLabel P A B hsum)) a b)≤3 at hc3
    exact CrossingFamily.concurrent_of_dense_actual_cofacial_graph hab 2 (by omega) hdQ
      (by omega) hnQ e

theorem all_homothetic_codimension_two_with_extras_universal
    (P A B : ConvexPolytope n) (hfull:P.IsFullDim)
    (hsum:P.toSet=A.toSet+B.toSet)
    (hr:2≤A.dim) (hq:(quotientPolytope P A).dim=2)
    (hN:P.vertices.card≤4*n-5)
    (hhom:∀q:(quotientPolytope P A).vertices,SummandHomotheticFiber P A B hsum q)
    (hextra:(extraVertices P A).Nonempty)
    (Q:ConvexPolytope m) (φ:FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  have hQcard := quotient_has_three_vertices_of_codimension_two P A B hfull hsum hr hq hN
  have hAcard := (homothetic_extra_saturation P A B hfull hsum hr hq hN hhom hextra).1
  obtain ⟨q0,hq0,q1,hq1,hne⟩ := Finset.one_lt_card.mp (show 1<(quotientPolytope P A).vertices.card by omega)
  apply decomposable_after_iso_of_two_simplex_fibers_and_centers P A B hsum (by omega) hAcard
    ⟨q0,hq0⟩ ⟨q1,hq1⟩ (fun h => hne (congrArg Subtype.val h))
    (hhom _) (hhom _) Q φ
  exact all_homothetic_extra_centers P A B hfull hsum hr hq hN hhom hextra Q φ

end Papers.MinkowskiCodimensionTwoExtraCenters

end
end
end BundlePart56

section BundlePart57
/- Source: Papers/ProperSummandPersistence.lean -/







@[expose] public section

/-!
# Persistence of the proper summands required by the lower-bound proof

This collects Proposition 7, the segment case, and the planar endpoint in
dimension three. The codimension-two proof distinguishes the absence of
extra vertices, a nonhomothetic fiber, and three homothetic fibers. Every
branch concludes actual Minkowski decomposability in an arbitrary
full-dimensional realization of the same face lattice.
-/

noncomputable section
namespace Papers.ProperSummandPersistence

open Set Module
open Papers.Polytopes Papers.ActualFaceOrder
open Papers.SegmentSummandPersistence Papers.MinkowskiCodimensionTwoDeletion
open Papers.MinkowskiCodimensionTwoExtraCenters Papers.MinkowskiLargeCodimension
open Papers.ThreeDimensionalProperSummand Papers.MinkowskiQuotientCounting
open Papers.MinkowskiSummandFibers Papers.MinkowskiExtraFace
open Papers.MinkowskiCodimensionTwoCounts
open Papers.ExactShephardCriterion
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

theorem codimension_two_summand_persists
    (P A B : ConvexPolytope n) (hP : P.IsFullDim)
    (hsum : P.toSet=A.toSet+B.toSet)
    (hr : 2≤A.dim) (hq : (quotientPolytope P A).dim=2)
    (hN : P.vertices.card≤4*n-5)
    (Q : ConvexPolytope n) (hQ : Q.IsFullDim)
    (φ : FaceObject P ≃o FaceObject Q) : MinkowskiDecomposable Q := by
  by_cases hall : ∀q:(quotientPolytope P A).vertices,
      SummandHomotheticFiber P A B hsum q
  · by_cases hextra : (extraVertices P A).Nonempty
    · exact all_homothetic_codimension_two_with_extras_universal P A B hP hsum
        hr hq hN hall hextra Q φ
    · have hcover : ∀x∈P.vertices,summandProjection A x∈(quotientPolytope P A).vertices := by
        intro x hx
        by_contra hn
        exact hextra ⟨x,Finset.mem_filter.mpr ⟨hx,hn⟩⟩
      exact decomposable_after_iso_of_exact_shephard_facet P
        (codimension_two_no_extras_shephard P A B hP hsum hr hq hN hcover) Q hQ φ
  · push_neg at hall
    obtain ⟨q,hqbad⟩ := hall
    exact nonhomothetic_codimension_two_persists P A B hP hsum hr hq hN q hqbad Q hQ φ

/-- Proposition 7 in every dimension and codimension used in the paper,
including the one-dimensional summand and the three-dimensional endpoint. -/
theorem proper_summand_persists
    (P A B : ConvexPolytope n) (hP : P.IsFullDim) (hn : 3≤n)
    (hsum : P.toSet=A.toSet+B.toSet) (hr : 0<A.dim)
    (hallowed : A.dim≤n-2 ∨ (n=3 ∧ A.dim≤2))
    (hN : P.vertices.card≤4*n-5)
    (Q : ConvexPolytope n) (hQ : Q.IsFullDim)
    (φ : FaceObject P ≃o FaceObject Q) : MinkowskiDecomposable Q := by
  by_cases hr1 : A.dim=1
  · exact segment_summand_persists P A B hP hn hsum hr1 hN Q φ
  have hr2 : 2≤A.dim := by omega
  rcases hallowed with hsmall | ⟨hn3,hsmall⟩
  · have hdim := quotient_dimension_add_summand_dimension P A hP
    by_cases hq : (quotientPolytope P A).dim=2
    · exact codimension_two_summand_persists P A B hP hsum hr2 hq hN Q hQ φ
    · exact proper_summand_codimension_at_least_three_persists P A B hP hsum hr2
        (by omega) hN Q hQ φ
  · subst n
    exact decomposable_after_iso_of_planar_summand_seven P A B hP hsum
      (by omega) (by simpa using hN) Q hQ φ

end Papers.ProperSummandPersistence

end
end
end BundlePart57

section BundlePart58
/- Source: Papers/ProperImagePersistence.lean -/




@[expose] public section

/-!
# The proper-image alternative implies combinatorial decomposability

Lemma 4 constructs an actual Minkowski summand with exactly the affine
dimension of the parallel image. Proposition 7 then applies, including
its dimension-three endpoint. No summand or rigidity certificate is an
input: the hypotheses concern the original polytope and parallel map.
-/

noncomputable section
namespace Papers.ProperImagePersistence

open Set Module
open Papers.Polytopes Papers.ActualFaceOrder Papers.PolytopeFourRegularTail
open Papers.ProperImageExactSummand Papers.ProperSummandPersistence
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {n : ℕ}

theorem proper_image_persists
    (P : ConvexPolytope n) (hP : P.IsFullDim) (hn : 3≤n)
    (f : E n → E n) (hf : IsParallelMap P f)
    (hnon : ¬IsHomothetyOnVertices P f)
    (hallowed : finrank ℝ (vectorSpan ℝ (f '' (P.vertices : Set (E n))))≤n-2 ∨
      (n=3 ∧ finrank ℝ (vectorSpan ℝ (f '' (P.vertices : Set (E n))))≤2))
    (hN : P.vertices.card≤4*n-5)
    (Q : ConvexPolytope n) (hQ : Q.IsFullDim)
    (φ : FaceObject P ≃o FaceObject Q) : MinkowskiDecomposable Q := by
  have hproper : finrank ℝ (vectorSpan ℝ (f '' (P.vertices : Set (E n))))<n := by
    rcases hallowed with h | ⟨he,h⟩ <;> omega
  obtain ⟨A,B,hdim,hpos,hlt,hsum⟩ := proper_image_actual_summand_exact_dimension P hP f hf
    (nonconstant_of_nonhomothetic P f hnon) hproper (by omega)
  exact proper_summand_persists P A B hP hn hsum hpos (by rwa [hdim]) hN Q hQ φ

end Papers.ProperImagePersistence

end
end
end BundlePart58

section BundlePart59
/- Source: Papers/EssentialThreeCoverPersistence.lean -/






@[expose] public section

/-!
# Proposition 11 for an essential three-homothety cover

The actual central section either meets the polytope or is empty.  In
the first case the three-center reconstruction theorem applies.  In the
second case a separating projective chart produces a nonhomothetic
parallel map with an affine image of dimension at most two.  The proved
proper-image persistence theorem then applies, including its separate
dimension-three endpoint.  The projective realization has the same face
order and the same number of vertices as the original polytope.

All hypotheses concern the original parallel map and its genuine private
vertices.  No concurrency, graph reconstruction, or summand certificate
is assumed in the conclusion below.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module Papers.Coordinates Papers.ActualFaceOrder
open Papers.ActualHomothetyClasses HomothetyParameters
open Papers.ProperImagePersistence
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {d : ℕ}

theorem decomposable_after_iso_of_essential_three_cover
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (f : E d → E d) (p : Fin 3 → ℝ × E d)
    (hf : IsParallelMap P f) (color : P.vertices → Fin 3)
    (hcover : ∀ v : P.vertices, f v.val = evaluate (p (color v)) v.val)
    (hprivate : ∀ i : Fin 3, ∃ x ∈ P.vertices,
      f x = evaluate (p i) x ∧
        ∀ j : Fin 3, j ≠ i → f x ≠ evaluate (p j) x)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (Q : ConvexPolytope d) (hQ : Q.IsFullDim)
    (φ : FaceObject P ≃o FaceObject Q) :
    MinkowskiDecomposable Q := by
  by_cases hmeet : ∃ w ∈ P.toSet, homogenize w ∈ directionSpan p
  · exact decomposable_after_iso_of_essential_three_cover_meeting P hP hd f p hf
      color hcover hprivate hmeet hN Q φ
  have hdim : 3 ≤ P.dim := by rw [hP]; exact hd
  have hnon : ¬ IsHomothetyOnVertices P f :=
    essential_three_cover_nontrivial P hdim f p hf color hcover hprivate
  have hempty : centralSection P (fun i => (p i).1) (fun i => (p i).2) = ∅ :=
    (centralSection_eq_empty_iff_no_actual_center P p).mpr hmeet
  have hcover' : ∀ x ∈ P.vertices, ∃ i : Fin 3,
      f x = (p i).1 • x + (p i).2 := by
    intro x hx
    exact ⟨color ⟨x,hx⟩,hcover ⟨x,hx⟩⟩
  obtain ⟨R,hR,⟨ρ⟩,hcard,g,hg,hgnon,hrank⟩ :=
    projective_proper_image_of_empty_central P hP f hf hnon
      (fun i => (p i).1) (fun i => (p i).2) hcover' hempty
  have hrank2 : finrank ℝ (vectorSpan ℝ (g '' (R.vertices : Set (E d)))) ≤ 2 := by
    simpa using hrank
  have hallowed :
      finrank ℝ (vectorSpan ℝ (g '' (R.vertices : Set (E d)))) ≤ d - 2 ∨
        (d = 3 ∧ finrank ℝ (vectorSpan ℝ (g '' (R.vertices : Set (E d)))) ≤ 2) := by
    by_cases hd3 : d = 3
    · exact Or.inr ⟨hd3,hrank2⟩
    · exact Or.inl (by omega)
  exact proper_image_persists R hR hd g hg hgnon hallowed
    (by rw [hcard]; exact hN) Q hQ (ρ.symm.trans φ)

end Papers.Polytopes

end
end
end BundlePart59

section BundlePart60
/- Source: Papers/ConditionalSharpTheorem.lean -/







@[expose] public section

/-!
# The sharp vertex bound for conditional decomposability

The stronger lower-bound assertion is proved first: below the threshold,
a decomposable full-dimensional realization forces every realization of
its face lattice to be decomposable. The unrestricted wedge construction
then attains the threshold in every dimension at least three.

The final `IsLeast` statement gives the literal minimum of the set of
vertex counts of conditionally decomposable polytopes.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open HomothetyParameters Papers.ActualFaceOrder
open Papers.ActualTwoCoverReductions Papers.ProperImagePersistence
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {d : ℕ}

theorem decomposable_after_iso_of_small_essential_cover
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (f : E d → E d) (hf : IsParallelMap P f)
    (hcover : SmallEssentialParallelCover P f)
    (hN : P.vertices.card ≤ 4*d-5)
    (Q : ConvexPolytope d) (hQ : Q.IsFullDim)
    (φ : FaceObject P ≃o FaceObject Q) : MinkowskiDecomposable Q := by
  obtain ⟨m,hmlo,hmhi,p,color,hvalues,hprivate⟩ := hcover
  have hm : m=2 ∨ m=3 := by omega
  rcases hm with rfl | rfl
  · exact decomposable_after_iso_of_essential_two_cover P hP hd f p hf color
      hvalues hprivate hN Q φ
  · exact decomposable_after_iso_of_essential_three_cover P hP hd f p hf color
      hvalues hprivate hN Q hQ φ

/-- Proposition 11 for an arbitrary cover by at most three homotheties.
Essentiality and private vertices are derived, rather than assumed. -/
theorem decomposable_after_iso_of_at_most_three_homotheties
    {I : Type*} [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (f : E d → E d) (hf : IsParallelMap P f)
    (hnon : ¬IsHomothetyOnVertices P f)
    (p : I → ℝ × E d) (hcard : Fintype.card I ≤ 3)
    (hcover : ∀ x ∈ P.vertices, ∃ i : I,
      f x=(p i).1 • x+(p i).2)
    (hN : P.vertices.card ≤ 4*d-5)
    (Q : ConvexPolytope d) (hPQ : CombinatoriallyEquivalent P Q) :
    MinkowskiDecomposable Q := by
  obtain ⟨φ⟩ := hPQ
  have hQ : Q.IsFullDim := (Papers.ActualFaceOrder.dim_eq φ).trans hP
  obtain ⟨m,hmlo,hmhi,q,color,hvalues,hprivate⟩ :=
    Papers.ActualEssentialCovers.essential_cover_of_homothety_cover P f p hcover hnon
  exact decomposable_after_iso_of_small_essential_cover P hP hd f hf
    ⟨m,hmlo,hmhi.trans hcard,q,color,hvalues,hprivate⟩ hN Q hQ φ

/-- The stronger lower-bound assertion stated immediately after Theorem 1:
every realization of the face lattice is decomposable below `4d−4`. -/
theorem decomposability_determined_by_face_lattice_below_threshold
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (hN : P.vertices.card ≤ 4*d-5) (hdecomp : MinkowskiDecomposable P)
    (Q : ConvexPolytope d) (hPQ : CombinatoriallyEquivalent P Q) :
    MinkowskiDecomposable Q := by
  obtain ⟨φ⟩ := hPQ
  have hQ : Q.IsFullDim := (Papers.ActualFaceOrder.dim_eq φ).trans hP
  obtain ⟨f,hf,hnon⟩ := (minkowski_decomposable_iff_parallel_map P).mp hdecomp
  rcases all_actual_covers_routes P hP f hf hnon hd hN with hsmall | hS | himage
  · exact decomposable_after_iso_of_small_essential_cover P hP hd f hf hsmall hN Q hQ φ
  · exact decomposable_after_iso_of_shephard_property P hP f hf hnon hS Q hQ φ
  · obtain ⟨R,hR,⟨ρ⟩,hcard,g,hg,hgnon,hrank⟩ := himage
    exact proper_image_persists R hR hd g hg hgnon (Or.inl hrank)
      (by rw [hcard]; exact hN) Q hQ (ρ.symm.trans φ)

/-- Below the threshold, decomposability itself is an invariant of the
face lattice. Both directions are consequences of the universal assertion. -/
theorem decomposable_iff_of_face_iso_below_threshold
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3≤d)
    (hN : P.vertices.card≤4*d-5)
    (Q : ConvexPolytope d) (hPQ : CombinatoriallyEquivalent P Q) :
    MinkowskiDecomposable P ↔ MinkowskiDecomposable Q := by
  constructor
  · exact fun h => decomposability_determined_by_face_lattice_below_threshold P hP hd hN h Q hPQ
  · intro h
    obtain ⟨φ⟩ := hPQ
    have hQ : Q.IsFullDim := (Papers.ActualFaceOrder.dim_eq φ).trans hP
    have hNQ : Q.vertices.card≤4*d-5 := by
      rw [←Papers.ActualFaceOrder.vertices_card_eq φ]
      exact hN
    exact decomposability_determined_by_face_lattice_below_threshold Q hQ hd hNQ h P ⟨φ.symm⟩

/-- The lower-bound half of Theorem 1, with no restrictions on the
combinatorial type or the dimensions of its Minkowski summands. -/
theorem conditional_decomposability_lower_bound
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3 ≤ d)
    (hconditional : ConditionallyDecomposable P) :
    4*d-4 ≤ P.vertices.card := by
  by_contra hsmall
  have hN : P.vertices.card ≤ 4*d-5 := by omega
  obtain ⟨⟨A,⟨α⟩,hA⟩,⟨B,⟨β⟩,hB⟩⟩ := hconditional
  have hAfull : A.IsFullDim := (Papers.ActualFaceOrder.dim_eq α).trans hP
  have hAcard : A.vertices.card ≤ 4*d-5 := by
    rw [← Papers.ActualFaceOrder.vertices_card_eq α]
    exact hN
  exact hB (decomposability_determined_by_face_lattice_below_threshold A hAfull hd
    hAcard hA B ⟨α.symm.trans β⟩)

/-- Theorem 1, including both the full lower bound and sharpness in every
dimension in its stated range. -/
theorem conditional_decomposability_sharp (d : ℕ) (hd : 3 ≤ d) :
    (∀ P : ConvexPolytope d, P.IsFullDim → ConditionallyDecomposable P →
      4*d-4 ≤ P.vertices.card) ∧
    (∃ P : ConvexPolytope d, P.IsFullDim ∧ ConditionallyDecomposable P ∧
      P.vertices.card=4*d-4) := by
  exact ⟨fun P hP hc => conditional_decomposability_lower_bound P hP hd hc,
    conditional_decomposability_attainment d hd⟩

/-- The exact target proposition from the initial statement specification. -/
theorem conditional_decomposability_claim : ConditionalDecomposabilityClaim :=
  conditional_decomposability_sharp

/-- An equivalent formulation of the paper's least-number assertion. -/
theorem conditional_vertex_count_isLeast (d : ℕ) (hd : 3 ≤ d) :
    IsLeast {N : ℕ | ∃ P : ConvexPolytope d,
      P.IsFullDim ∧ ConditionallyDecomposable P ∧ P.vertices.card=N} (4*d-4) := by
  obtain ⟨hlower,hattain⟩ := conditional_decomposability_sharp d hd
  refine ⟨hattain,?_⟩
  rintro N ⟨P,hP,hc,hcard⟩
  rw [← hcard]
  exact hlower P hP hc

end Papers.Polytopes

end
end
end BundlePart60

section BundlePart61
/- Source: Papers/WeakSummandPersistence.lean -/




@[expose] public section

/-!
# Proposition 7 with the paper's weak-summand hypothesis

A weak summand is literally a positive rescaling that occurs in an actual
Minkowski sum. The scale is absorbed into the summand polytope, and the
proved invariance of affine dimension supplies the exact hypotheses of the
proper-summand persistence theorem. No replacement of weak summands by an
unproved geometric certificate is used.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open Papers.ProperSummandPersistence Papers.SegmentSummandPersistence
open Papers.WeakSummandScaling Papers.ActualFaceOrder
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical Pointwise

variable {d : ℕ}

def IsWeakSummand (P A : ConvexPolytope d) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ B : ConvexPolytope d,
    P.toSet = ε • A.toSet + B.toSet

/-- Proposition 7, including its separate planar endpoint in dimension
three, stated for an actual weak summand of the original polytope. -/
theorem decomposable_after_iso_of_weak_summand
    (P A : ConvexPolytope d) (hP : P.IsFullDim)
    (hweak : IsWeakSummand P A) (hr : 2 ≤ A.dim)
    (hallowed : A.dim ≤ d-2 ∨ (d=3 ∧ A.dim≤2))
    (hN : P.vertices.card ≤ 4*d-5)
    (Q : ConvexPolytope d) (hPQ : CombinatoriallyEquivalent P Q) :
    MinkowskiDecomposable Q := by
  obtain ⟨ε,hε,B,hsum⟩ := hweak
  obtain ⟨φ⟩ := hPQ
  have hQ : Q.IsFullDim := (Papers.ActualFaceOrder.dim_eq φ).trans hP
  have hd : 3≤d := by rcases hallowed with h | ⟨h,_⟩ <;> omega
  have hdim := scalePolytope_dim A ε hε.ne'
  exact proper_summand_persists P (scalePolytope A ε) B hP hd
    (by rwa [scalePolytope_body]) (by rw [hdim]; omega)
    (by rwa [hdim]) hN Q hQ φ

/-- The segment weak-summand consequence of Lemma 5. -/
theorem decomposable_after_iso_of_segment_weak_summand
    (P A : ConvexPolytope d) (hP : P.IsFullDim) (hd : 3≤d)
    (hweak : IsWeakSummand P A) (hr : A.dim=1)
    (hN : P.vertices.card ≤ 4*d-5)
    (Q : ConvexPolytope d) (hPQ : CombinatoriallyEquivalent P Q) :
    MinkowskiDecomposable Q := by
  obtain ⟨ε,hε,B,hsum⟩ := hweak
  obtain ⟨φ⟩ := hPQ
  exact segment_summand_persists P (scalePolytope A ε) B hP hd
    (by rwa [scalePolytope_body]) (by rw [scalePolytope_dim A ε hε.ne',hr]) hN Q φ

end Papers.Polytopes

end
end
end BundlePart61

section BundlePart62
/- Source: Papers/HomothetyPositiveProjectiveConclusion.lean -/



@[expose] public section

/-!
# The positive projectivity in Proposition 12

This optional strengthening retains the geometric witnesses forgotten by
the main assembly interface. Positive homogeneous relations on vertices
extend to the entire convex hull by normalized convex weights; applying
the same argument to the inverse map proves equality of the bodies.

The final alternative retains the original parallel map: the new map is
its explicitly defined projective transport minus one global homothety.
Its affine image dimension is at most the number of parameters minus one.

This file is deliberately independent of the final theorem's import path.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d e : ℕ}

/-- Literal equality with the positive projective image of the whole
convex body, expressed in the signed homogeneous chart `(1,-x)`. -/
def IsPositiveProjectiveImage
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E e)) : Prop :=
  (∀ x ∈ P.toSet, 0 < (L (vertexVector x)).1) ∧
    Q.toSet = {y | ∃ x ∈ P.toSet, ∃ c : ℝ,
      0 < c ∧ L (vertexVector x) = c • vertexVector y}

theorem vertexVector_convex_combination
    (x y : E d) (a b : ℝ) (hab : a+b=1) :
    vertexVector (a • x+b • y) = a • vertexVector x+b • vertexVector y := by
  apply Prod.ext
  · change 1 = a*1+b*1
    simpa only [mul_one] using hab.symm
  · change -(a • x+b • y) = a • (-x)+b • (-y)
    module

/-- Positive projective preimages of convex sets are convex on a fixed
positive affine chart. The new weights are `a*c₁/t` and `b*c₂/t`, where
`t=a*c₁+b*c₂>0`. -/
theorem positive_homogeneous_preimage_convex
    (L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E e))
    (S : Set (E e)) (hS : Convex ℝ S) :
    Convex ℝ {x | ∃ y ∈ S, ∃ c : ℝ,
      0 < c ∧ L (vertexVector x) = c • vertexVector y} := by
  intro x hx y hy a b ha hb hab
  obtain ⟨u,hu,cx,hcx,hx⟩ := hx
  obtain ⟨v,hv,cy,hcy,hy⟩ := hy
  let t : ℝ := a*cx+b*cy
  have ht : 0<t := by
    rcases lt_or_eq_of_le ha with ha' | ha'
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hcx) (mul_nonneg hb hcy.le)
    · have hb1 : b=1 := by linarith
      simpa only [t, ←ha', zero_mul, zero_add, hb1, one_mul] using hcy
  have hwa : 0≤a*cx/t := div_nonneg (mul_nonneg ha hcx.le) ht.le
  have hwb : 0≤b*cy/t := div_nonneg (mul_nonneg hb hcy.le) ht.le
  have hw : a*cx/t+b*cy/t=1 := by
    rw [←add_div]
    change t/t=1
    exact div_self (ne_of_gt ht)
  have hta : t*(a*cx/t)=a*cx := by
    field_simp [ne_of_gt ht] <;> ring
  have htb : t*(b*cy/t)=b*cy := by
    field_simp [ne_of_gt ht] <;> ring
  refine ⟨(a*cx/t) • u+(b*cy/t) • v,hS hu hv hwa hwb hw,t,ht,?_⟩
  rw [vertexVector_convex_combination x y a b hab, map_add, map_smul,
    map_smul, hx, hy]
  apply Prod.ext
  · change a*(cx*1)+b*(cy*1)=t*1
    dsimp only [t]
    ring
  · change a • (cx • (-u))+b • (cy • (-v)) =
      t • (-((a*cx/t) • u+(b*cy/t) • v))
    simp only [smul_smul, smul_neg, smul_add, hta, htb]
    module

theorem positive_homogeneous_relation_on_hull
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E e))
    (hvertex : ∀ x ∈ P.vertices, ∃ y ∈ Q.toSet, ∃ c : ℝ,
      0<c ∧ L (vertexVector x)=c • vertexVector y) :
    ∀ x ∈ P.toSet, ∃ y ∈ Q.toSet, ∃ c : ℝ,
      0<c ∧ L (vertexVector x)=c • vertexVector y := by
  exact convexHull_min hvertex
    (positive_homogeneous_preimage_convex L Q.toSet
      (convex_convexHull ℝ (Q.vertices : Set (E e))))

/-- Positive projective vertex correspondence gives the ordinary image
of the entire convex hull, in both directions. -/
theorem isPositiveProjectiveImage_of_vertices
    (P : ConvexPolytope d) (Q : ConvexPolytope e)
    (β : VertexType P ≃ VertexType Q)
    (L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E e))
    (h : VertexType P → ℝ) (hh : ∀ v,0<h v)
    (hL : ∀ v,L (vertexVector v.val)=h v • vertexVector (β v).val) :
    IsPositiveProjectiveImage P Q L := by
  have hforward : ∀ x ∈ P.toSet, ∃ y ∈ Q.toSet, ∃ c : ℝ,
      0<c ∧ L (vertexVector x)=c • vertexVector y := by
    apply positive_homogeneous_relation_on_hull P Q L
    intro x hx
    exact ⟨(β ⟨x,hx⟩).val,
      subset_convexHull ℝ _ (β ⟨x,hx⟩).property,
      h ⟨x,hx⟩,hh ⟨x,hx⟩,hL ⟨x,hx⟩⟩
  have hback : ∀ y ∈ Q.toSet, ∃ x ∈ P.toSet, ∃ c : ℝ,
      0<c ∧ L.symm (vertexVector y)=c • vertexVector x := by
    apply positive_homogeneous_relation_on_hull Q P L.symm
    intro y hy
    let v : VertexType P := β.symm ⟨y,hy⟩
    have hβ : (β v).val=y := congrArg Subtype.val (β.apply_symm_apply ⟨y,hy⟩)
    have hv : L (vertexVector v.val)=h v • vertexVector y := by
      simpa only [hβ] using hL v
    refine ⟨v.val,subset_convexHull ℝ _ v.property,(h v)⁻¹,inv_pos.mpr (hh v),?_⟩
    apply L.injective
    rw [LinearEquiv.apply_symm_apply, map_smul, hv, smul_smul,
      inv_mul_cancel₀ (ne_of_gt (hh v)), one_smul]
  constructor
  · intro x hx
    obtain ⟨y,hy,c,hc,he⟩ := hforward x hx
    rw [he]
    change 0<c*1
    simpa only [mul_one] using hc
  · ext y
    constructor
    · intro hy
      obtain ⟨x,hx,c,hc,he⟩ := hback y hy
      refine ⟨x,hx,c⁻¹,inv_pos.mpr hc,?_⟩
      have he' : vertexVector y=c • L (vertexVector x) := by
        simpa only [LinearEquiv.apply_symm_apply, map_smul] using congrArg L he
      calc
        L (vertexVector x)=c⁻¹ • (c • L (vertexVector x)) := by
          rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
        _=c⁻¹ • vertexVector y := by rw [←he']
    · rintro ⟨x,hx,c,hc,he⟩
      obtain ⟨z,hz,k,hk,hz'⟩ := hforward x hx
      have hck : c=k := by
        have hfst := congrArg Prod.fst (he.symm.trans hz')
        simpa only [Prod.smul_fst, vertexVector, smul_eq_mul, mul_one] using hfst
      have heq : c • vertexVector y=c • vertexVector z := by
        calc
          c • vertexVector y=L (vertexVector x) := he.symm
          _=k • vertexVector z := hz'
          _=c • vertexVector z := by rw [←hck]
      have hX : vertexVector y=vertexVector z := by
        have hscaled := congrArg (fun w : ℝ × E e => c⁻¹ • w) heq
        simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul] using hscaled
      have hyz : y=z := by
        have hs := congrArg Prod.snd hX
        change -y = -z at hs
        exact neg_injective hs
      rw [hyz]
      exact hz

/-- A positive projective image of `P`, together with the transported
original parallel map after subtracting one global scalar homothety.
The definition includes equality of the whole convex bodies. -/
def PositiveProjectiveParallelImageReduction
    (P : ConvexPolytope d) (f : E d → E d) (k : ℕ) : Prop :=
  ∃ Q : ConvexPolytope d, Q.IsFullDim ∧ CombinatoriallyEquivalent P Q ∧
    Q.vertices.card=P.vertices.card ∧
    ∃ β : VertexType P ≃ VertexType Q,
    ∃ L : (ℝ × E d) ≃ₗ[ℝ] (ℝ × E d),
      IsPositiveProjectiveImage P Q L ∧
      (∀ v : VertexType P,∃ c : ℝ,
        0<c ∧ L (vertexVector v.val)=c • vertexVector (β v).val) ∧
      ∃ α : ℝ,
        IsParallelMap Q (fun y=>transportParallelMap P Q β L f y-α • y) ∧
        ¬IsHomothetyOnVertices Q (fun y=>transportParallelMap P Q β L f y-α • y) ∧
        finrank ℝ (vectorSpan ℝ
          ((fun y=>transportParallelMap P Q β L f y-α • y) ''
            (Q.vertices : Set (E d))))≤k

theorem PositiveProjectiveParallelImageReduction.forget
    {P : ConvexPolytope d} {f : E d → E d} {k : ℕ}
    (h : PositiveProjectiveParallelImageReduction P f k) : ParallelImageReduction P k := by
  obtain ⟨Q,hQ,hPQ,hcard,β,L,hbody,hvertices,α,hg,hgn,hrank⟩ := h
  exact ⟨Q,hQ,hPQ,hcard,(fun y=>transportParallelMap P Q β L f y-α • y),hg,hgn,hrank⟩

variable {I : Type*} [Fintype I]

theorem positive_projective_parallel_image_of_empty_central
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (a : I → ℝ) (b : I → E d)
    (hcover : ∀x∈P.vertices,∃i,f x=a i • x+b i)
    (hempty : centralSection P a b=∅) :
    PositiveProjectiveParallelImageReduction P f (Fintype.card I-1) := by
  have hdis : ∀x∈P.toSet,vertexVector x∉parameterDirectionSpan a b := by
    intro x hx hD
    have hm : x∈centralSection P a b := ⟨hx,hD⟩
    rw [hempty] at hm
    exact hm.elim
  obtain ⟨L,hLD,hpos⟩ := exists_positive_parameter_chart P (parameterDirectionSpan a b) hdis
  obtain ⟨Q,β,h,hh,hL,⟨φ⟩,hedge⟩ := exists_signed_projective_polytope P L hpos
  let f' := transportParallelMap P Q β L f
  have hparallel : IsParallelMap Q f' :=
    transportParallelMap_parallel P Q β L h (fun v=>(ne_of_gt (hh v))) hL hedge f hf
  have hnon' : ¬IsHomothetyOnVertices Q f' :=
    transportParallelMap_nonhomothetic P Q β L h (fun v=>(ne_of_gt (hh v))) hL f hnon
  obtain ⟨v,hv⟩ := P.vertices_nonempty
  obtain ⟨i₀,hi₀⟩ := hcover v hv
  letI : Nonempty I := ⟨i₀⟩
  let α : ℝ := (L (parameterVector a b i₀)).1
  let bp : I → E d := fun i => (L (parameterVector a b i)).2
  have hscalar (i:I) : (L (parameterVector a b i)).1=α := by
    have hmem : parameterVector a b i-parameterVector a b i₀∈parameterDirectionSpan a b :=
      Submodule.subset_span ⟨(i,i₀),rfl⟩
    have hz := hLD _ hmem
    rw [map_sub,Prod.fst_sub] at hz
    exact sub_eq_zero.mp hz
  let g : E d → E d := fun x => f' x-α • x
  have hg : IsParallelMap Q g := by
    intro x hx y hy hxy
    obtain ⟨c,hc⟩ := hparallel x hx y hy hxy
    refine ⟨c-α,?_⟩
    change (f' y-α • y)-(f' x-α • x)=(c-α) • (y-x)
    calc
      (f' y-α • y)-(f' x-α • x)=(f' y-f' x)-α • (y-x) := by module
      _=(c-α) • (y-x) := by rw [hc]; module
  have hg_non : ¬IsHomothetyOnVertices Q g := by
    rintro ⟨c,u,hu⟩
    apply hnon'
    refine ⟨c+α,u,?_⟩
    intro x hx
    have hxg := hu x hx
    change f' x-α • x=c • x+u at hxg
    calc
      f' x = (f' x-α • x)+α • x := by abel
      _ = (c+α) • x+u := by rw [hxg]; module
  have hvalues : g '' (Q.vertices : Set (E d)) ⊆ Set.range bp := by
    rintro y ⟨x,hx,rfl⟩
    obtain ⟨w,hw⟩ := β.surjective ⟨x,hx⟩
    have hwx : (β w).val=x := congrArg Subtype.val hw
    obtain ⟨i,hi⟩ := hcover w.val w.property
    refine ⟨i,?_⟩
    have he := transportParallelMap_homothety_value P Q β L h
      (fun v=>ne_of_gt (hh v)) hL f w (parameterVector a b i) hi
    rw [hwx] at he
    change bp i=transportParallelMap P Q β L f x-α • x
    rw [he]
    unfold evalParameter
    rw [hscalar]
    dsimp [bp]
    module
  have hrank := Submodule.finrank_mono (vectorSpan_mono ℝ hvalues)
  have hcard := finrank_vectorSpan_range_add_one_le ℝ bp
  have hQ : Q.IsFullDim := (Papers.ActualFaceOrder.dim_eq φ).trans hP
  refine ⟨Q,hQ,⟨φ⟩,(Papers.ActualFaceOrder.vertices_card_eq φ).symm,
    β,L,isPositiveProjectiveImage_of_vertices P Q β L h hh hL,
    (fun v=>⟨h v,hh v,hL v⟩),α,hg,hg_non,?_⟩
  change finrank ℝ (vectorSpan ℝ (g '' (Q.vertices : Set (E d))))≤Fintype.card I-1
  omega

/-- Proposition 12, retaining the positive projectivity of the whole
body, the transport of the given map, and the exact image bound `m-1`. -/
theorem uniform_cover_positive_projectivity_or_shephard
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (a : I → ℝ) (b : I → E d)
    (hcover : ∀y∈P.vertices,∃j,f y=a j • y+b j)
    (hprivate : ∀i,∃x∈fullClass P f a b i,∀j,f x=a j • x+b j→j=i)
    (hmlo : 4≤Fintype.card I) (hmhi : Fintype.card I≤d-1)
    (hN : P.vertices.card≤4*d-5) :
    PositiveProjectiveParallelImageReduction P f (Fintype.card I-1) ∨
      HasShephardProperty P := by
  have hd : Fintype.card I+1≤d := by omega
  by_cases hne : (centralVertices P a b).Nonempty
  · exact Or.inr (uniform_nonempty_central_shephard P hP f hf hnon a b
      hcover hprivate hmlo hd hN hne)
  · apply Or.inl
    obtain ⟨hind,htm,ht,hr,hbudget,i,hi⟩ :=
      uniform_parameter_budget P hP f hf a b hcover hprivate hmlo hd hN
    obtain ⟨B,hB,hclique,hpos,hfacets,hfibers,hinter,hF⟩ :=
      minimumClass_fiber_faces P hP f hf a b hcover hprivate i (by omega) hi
    have hempty : centralSection P a b=∅ := by
      rcases hF with he|hF
      · exact he
      · obtain ⟨x,hx⟩ := (facePolytope P hF).vertices_nonempty
        have hx' := Finset.mem_filter.mp hx
        exact False.elim (hne ⟨x,Finset.mem_filter.mpr ⟨hx'.1,hx'.2.2⟩⟩)
    exact positive_projective_parallel_image_of_empty_central P hP f hf hnon
      a b hcover hempty

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart62

section BundlePart63
/- Source: Papers/ParallelMapVertexDomain.lean -/



@[expose] public section

/-!
# The vertex-domain formulation of the parallel-map criterion

The main development represents a vertex map by a function on the ambient
Euclidean space and constrains it only at actual vertices. This file proves
the equivalence with a function whose domain is literally the vertex type.
Extending such a function arbitrarily away from the vertices introduces no
restriction on its values at vertices.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {d : ℕ}

def IsVertexParallelMap (P : ConvexPolytope d) (f : P.vertices → E d) : Prop :=
  ∀ x y : P.vertices, GeneralVertexStep P x.val y.val →
    ∃ c : ℝ, f y-f x=c • (y.val-x.val)

def IsVertexHomothety (P : ConvexPolytope d) (f : P.vertices → E d) : Prop :=
  ∃ a : ℝ, ∃ b : E d, ∀ v : P.vertices, f v=a • v.val+b

theorem parallel_map_iff_restriction_to_vertices
    (P : ConvexPolytope d) (f : E d → E d) :
    IsParallelMap P f ↔ IsVertexParallelMap P (fun v => f v.val) := by
  constructor
  · intro hf x y hxy
    exact hf x.val x.property y.val y.property hxy
  · intro hf x hx y hy hxy
    exact hf ⟨x,hx⟩ ⟨y,hy⟩ hxy

theorem homothety_iff_restriction_to_vertices
    (P : ConvexPolytope d) (f : E d → E d) :
    IsHomothetyOnVertices P f ↔ IsVertexHomothety P (fun v => f v.val) := by
  constructor
  · rintro ⟨a,b,hab⟩
    exact ⟨a,b,fun v => hab v.val v.property⟩
  · rintro ⟨a,b,hab⟩
    exact ⟨a,b,fun x hx => hab ⟨x,hx⟩⟩

theorem nontrivial_parallel_map_iff_vertex_domain (P : ConvexPolytope d) :
    (∃ f : E d → E d, IsParallelMap P f ∧ ¬IsHomothetyOnVertices P f) ↔
      ∃ f : P.vertices → E d, IsVertexParallelMap P f ∧ ¬IsVertexHomothety P f := by
  constructor
  · rintro ⟨f,hf,hnon⟩
    exact ⟨fun v => f v.val,(parallel_map_iff_restriction_to_vertices P f).mp hf,
      fun h => hnon ((homothety_iff_restriction_to_vertices P f).mpr h)⟩
  · rintro ⟨g,hg,hgnon⟩
    let f : E d → E d := fun x => if hx : x∈P.vertices then g ⟨x,hx⟩ else 0
    have hvalues (v : P.vertices) : f v.val=g v := by simp [f,v.property]
    refine ⟨f,?_,?_⟩
    · intro x hx y hy hxy
      obtain ⟨c,hc⟩ := hg ⟨x,hx⟩ ⟨y,hy⟩ hxy
      refine ⟨c,?_⟩
      rw [hvalues ⟨y,hy⟩,hvalues ⟨x,hx⟩]
      exact hc
    · rintro ⟨a,b,hab⟩
      apply hgnon
      refine ⟨a,b,?_⟩
      intro v
      rw [← hvalues v]
      exact hab v.val v.property

/-- Kallay's criterion with exactly the map domain used in Section 2. -/
theorem minkowski_decomposable_iff_vertex_parallel_map (P : ConvexPolytope d) :
    MinkowskiDecomposable P ↔
      ∃ f : P.vertices → E d, IsVertexParallelMap P f ∧ ¬IsVertexHomothety P f :=
  (minkowski_decomposable_iff_parallel_map P).trans
    (nontrivial_parallel_map_iff_vertex_domain P)

end Papers.Polytopes

end
end
end BundlePart63

section BundlePart64
/- Source: Papers/SimplexReconstructionZeroCounterexample.lean -/





@[expose] public section

/-!
# The positive-dimensional hypothesis in simplex reconstruction

The simplex-reconstruction statement needs `1 ≤ r`.  When `r = 0`
there is just one color, so being homothetic on that color already means
being a global homothety.  Here the other hypotheses are realized by an
actual full-dimensional tetrahedron, with two distinct singleton faces.
The condition on centers for distinct pairs of colors holds in every
combinatorial realization, since `Fin 1` has no distinct pair.

This file is deliberately separate from the proof of the sharp bound.
Its tetrahedron has vertices `(0,0,0)`, `(10,0,10)`, `(10,10,0)`,
and `(0,10,10)`.  Its extreme-point and dimension certificates reuse
the already proved supporting forms for the eight-vertex construction.
-/

noncomputable section
namespace Papers.Polytopes.SimplexReconstructionZeroCounterexample

open Set Module
open Papers.ActualFaceOrder
open Papers.Polytopes.CrossingFamilyTransport
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical BigOperators

def index (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩

theorem index_injective : Function.Injective index := by
  intro i j h
  apply Fin.ext
  simpa only [index] using congrArg (fun k : Fin 8 => k.val) h

def point (i : Fin 4) : E 3 := ConditionalEight.point 0 (index i)

theorem point_injective : Function.Injective point :=
  (ConditionalEight.point_injective 0).comp index_injective

theorem support_separation (v w : Fin 4) (hvw : v ≠ w) :
    ∃ f, ConditionalEight.support 0 f (point v) = ConditionalEight.offset 0 f ∧
      ConditionalEight.offset 0 f < ConditionalEight.support 0 f (point w) :=
  ConditionalEight.support_separation 0 (index v) (index w)
    (fun h => hvw (index_injective h))

def tetrahedron : ConvexPolytope 3 :=
  polytopeOfSeparatingSupports point (by decide)
    (ConditionalEight.support 0) (ConditionalEight.offset 0)
    (fun f v => ConditionalEight.support_bound 0 f (index v)) support_separation

theorem point_vertex (i : Fin 4) : point i ∈ tetrahedron.vertices :=
  Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem tetrahedron_card : tetrahedron.vertices.card = 4 :=
  polytopeOfSeparatingSupports_card point (by decide)
    (ConditionalEight.support 0) (ConditionalEight.offset 0)
    (fun f v => ConditionalEight.support_bound 0 f (index v)) support_separation

theorem point_zero : point 0 = 0 := ConditionalEight.point_zero 0

theorem tetrahedron_fullDim : tetrahedron.IsFullDim := by
  let U := vectorSpan ℝ tetrahedron.toSet
  have hp (v : Fin 4) : point v ∈ U := by
    change point v ∈ vectorSpan ℝ tetrahedron.toSet
    have h := vsub_mem_vectorSpan ℝ
      (subset_convexHull ℝ _ (point_vertex v))
      (subset_convexHull ℝ _ (point_vertex 0))
    simpa only [ConvexPolytope.toSet, point_zero, vsub_eq_sub, sub_zero] using h
  have ha (i : Fin 3) : ConditionalEight.axis i ∈ U := by
    rw [ConditionalEight.axis_combination 0 i]
    apply U.sum_mem
    intro j _
    exact U.smul_mem _ (hp j.succ)
  have htop : U = ⊤ := by
    apply top_unique
    intro x _
    rw [ConditionalEight.coordinate_expansion x]
    exact U.sum_mem (fun i _ => U.smul_mem _ (ha i))
  change finrank ℝ U = 3
  rw [htop, finrank_top, finrank_euclideanSpace_fin]

theorem tetrahedron_affineIndependent :
    AffineIndependent ℝ (fun v : VertexType tetrahedron => v.val) := by
  apply (vertices_affineIndependent_iff tetrahedron).mpr
  have hd : tetrahedron.dim = 3 := tetrahedron_fullDim
  rw [tetrahedron_card, hd]

def color : tetrahedron.vertices → Fin 1 := fun _ => 0

def firstVertex : tetrahedron.vertices := ⟨point 0, point_vertex 0⟩
def secondVertex : tetrahedron.vertices := ⟨point 1, point_vertex 1⟩

theorem vertices_distinct : firstVertex ≠ secondVertex := by
  intro h
  have hi := point_injective (congrArg Subtype.val h)
  exact (by decide : (0 : Fin 4) ≠ 1) hi

theorem each_color_occurs_twice (i : Fin 1) :
    ∃ x y : tetrahedron.vertices, x ≠ y ∧ color x = i ∧ color y = i :=
  ⟨firstVertex, secondVertex, vertices_distinct,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

theorem singleton_face_one_vertex_per_color (v : tetrahedron.vertices) (i : Fin 1) :
    ∃! w : tetrahedron.vertices, w.val ∈ ({v.val} : Set (E 3)) ∧ color w = i := by
  refine ⟨v, ⟨Set.mem_singleton _, Subsingleton.elim _ _⟩, ?_⟩
  intro w hw
  exact Subtype.ext (Set.mem_singleton_iff.mp hw.1)

theorem singleton_is_zero_simplex (v : tetrahedron.vertices) :
    AffineIndependent ℝ (fun _ : Fin 1 => v.val) ∧
      convexHull ℝ (Set.range (fun _ : Fin 1 => v.val)) = {v.val} := by
  exact ⟨affineIndependent_of_subsingleton ℝ _, by simp⟩

theorem singleton_faces_disjoint :
    Disjoint ({firstVertex.val} : Set (E 3)) {secondVertex.val} := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply vertices_distinct
  exact Subtype.ext ((Set.mem_singleton_iff.mp hx).symm.trans
    (Set.mem_singleton_iff.mp hy))

/-- The forced-center premise holds even when quantified over every actual
face-order-equivalent realization, without any geometric assumptions on it. -/
theorem pair_centers_in_every_realization (m : ℕ) (Q : ConvexPolytope m)
    (iso : FaceObject tetrahedron ≃o FaceObject Q) (i j : Fin 1) (hij : i ≠ j) :
    ∃ J : Submodule ℝ (E m × ℝ), finrank ℝ J = 1 ∧
      ∀ e : CrossingFamily Q (colorAlong iso color) i j, J ≤ e.line := by
  exact (hij (Subsingleton.elim i j)).elim

/-- With one color, classwise homothety is global homothety.  The assertion
fails independently of the additional requirement that the map be parallel. -/
theorem no_nontrivial_classwise_homothety :
    ¬ ∃ f : E 3 → E 3,
      IsParallelMap tetrahedron f ∧ ¬ IsHomothetyOnVertices tetrahedron f ∧
      ∀ i : Fin 1, ∃ a : ℝ, ∃ b : E 3,
        ∀ v : tetrahedron.vertices, color v = i → f v.val = a • v.val + b := by
  rintro ⟨f, _, hnontrivial, hclasses⟩
  obtain ⟨a, b, hab⟩ := hclasses 0
  apply hnontrivial
  refine ⟨a, b, ?_⟩
  intro x hx
  exact hab ⟨x, hx⟩ (Subsingleton.elim _ _)

/-- Concrete counterexample to extending Lemma 6 to dimension zero.
The face, dimension, color-count, universal-center, and failed
conclusion clauses are all statements about the actual tetrahedron. -/
theorem lemma6_zero_counterexample :
    tetrahedron.IsFullDim ∧ tetrahedron.vertices.card = 4 ∧
    (∀ i : Fin 1, ∃ x y : tetrahedron.vertices,
      x ≠ y ∧ color x = i ∧ color y = i) ∧
    tetrahedron.IsFace {firstVertex.val} ∧
    tetrahedron.IsFace {secondVertex.val} ∧
    faceDim ({firstVertex.val} : Set (E 3)) = 0 ∧
    faceDim ({secondVertex.val} : Set (E 3)) = 0 ∧
    Disjoint ({firstVertex.val} : Set (E 3)) {secondVertex.val} ∧
    (∀ i : Fin 1, ∃! v : tetrahedron.vertices,
      v.val ∈ ({firstVertex.val} : Set (E 3)) ∧ color v = i) ∧
    (∀ i : Fin 1, ∃! v : tetrahedron.vertices,
      v.val ∈ ({secondVertex.val} : Set (E 3)) ∧ color v = i) ∧
    (∀ (m : ℕ) (Q : ConvexPolytope m)
      (iso : FaceObject tetrahedron ≃o FaceObject Q) (i j : Fin 1), i ≠ j →
      ∃ J : Submodule ℝ (E m × ℝ), finrank ℝ J = 1 ∧
        ∀ e : CrossingFamily Q (colorAlong iso color) i j, J ≤ e.line) ∧
    ¬ (∃ f : E 3 → E 3,
      IsParallelMap tetrahedron f ∧ ¬ IsHomothetyOnVertices tetrahedron f ∧
      ∀ i : Fin 1, ∃ a : ℝ, ∃ b : E 3,
        ∀ v : tetrahedron.vertices, color v = i → f v.val = a • v.val + b) := by
  exact ⟨tetrahedron_fullDim, tetrahedron_card, each_color_occurs_twice,
    vertex_isFace tetrahedron firstVertex.property,
    vertex_isFace tetrahedron secondVertex.property,
    faceDim_singleton _, faceDim_singleton _, singleton_faces_disjoint,
    singleton_face_one_vertex_per_color firstVertex,
    singleton_face_one_vertex_per_color secondVertex,
    pair_centers_in_every_realization, no_nontrivial_classwise_homothety⟩

end Papers.Polytopes.SimplexReconstructionZeroCounterexample

end
end
end BundlePart64

section BundlePart65
/- Source: Papers/CorrectedSimplexReconstruction.lean -/








@[expose] public section

/-!
# The literal positive-dimensional simplex reconstruction lemma

The colors, faces, and crossing families in this file belong to actual
polytopes.  The only projective hypothesis is concurrence of each crossing
family in every realization.  Compatibility between different families is
constructed from a supporting form; it is not a hypothesis.

The final theorem returns a map on the vertex subtype, with the precise
classwise homothety and nontriviality conclusions of corrected Lemma 6.
The condition `1 ≤ r` excludes the separately exhibited one-color
counterexample.
-/

noncomputable section
namespace Papers.CorrectedSimplexReconstruction

open Set Module
open Papers.Polytopes Papers.Coordinates Papers.ProjectiveNormalization
open Papers.ActualFaceOrder Papers.PolytopeSimpleTailFace
open Papers.Polytopes.CrossingFamilyTransport
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical

variable {n m r : ℕ} {I : Type*}

/-- The supporting-form construction, retaining the actual parallel map
and its classwise homothety parameters rather than only decomposability. -/
theorem classwise_parallel_map_of_supporting_center_data
    (P : ConvexPolytope n) (label : E n → I)
    (g : E n →ᵃ[ℝ] ℝ) (A B : I → E n)
    (J : I → I → Submodule ℝ (E n × ℝ))
    (hA : ∀ i, g (A i) = 0)
    (hB : ∀ i, 0 < g (B i))
    (hlabelB : ∀ i, label (B i) = i)
    (hclasses : ∀ i : I, ∃ x ∈ P.vertices, ∃ y ∈ P.vertices,
      x ≠ y ∧ label x = i ∧ label y = i)
    (hI : ∃ i j : I, i ≠ j)
    (hdim : ∀ i j, i ≠ j → finrank ℝ (J i j) = 1)
    (hfirst : ∀ i j, i ≠ j → J i j ≤ edgeProjectiveLine (A i) (A j))
    (hsecond : ∀ i j, i ≠ j → J i j ≤ edgeProjectiveLine (B i) (B j))
    (hcross : ∀ x ∈ P.vertices, ∀ y, GeneralVertexStep P x y →
      label x ≠ label y → J (label x) (label y) ≤ edgeProjectiveLine x y) :
    ∃ f : E n → E n, IsParallelMap P f ∧ ¬ IsHomothetyOnVertices P f ∧
      ∀ i : I, ∃ a : ℝ, ∃ b : E n,
        ∀ x ∈ P.vertices, label x = i → f x = a • x + b := by
  let ell := supportHomogeneousForm g
  let q : I → E n × ℝ := fun i =>
    ProjectiveNormalization.normalize ell (homogenize (B i))
  let p : I → ℝ × E n := fun i => centerParameters (q i)
  have hn (i : I) : ell (homogenize (B i)) ≠ 0 := by
    rw [show ell = supportHomogeneousForm g from rfl,
      supportHomogeneousForm_homogenize]
    exact ne_of_gt (hB i)
  have hdiff (i j : I) (hij : i ≠ j) : q i - q j ∈ J i j := by
    apply normalized_difference_mem_center ell (hn i) (hn j) (J i j) (hdim i j hij)
    · simpa only [edgeProjectiveLine, homogeneousSpan, Set.image_pair] using hsecond i j hij
    · exact (hfirst i j hij).trans (line_le_support_kernel g (hA i) (hA j))
  have hcenter (i j : I) :
      differenceCenterVector (p i) (p j) = q j - q i :=
    differenceCenterVector_centerParameters (q i) (q j)
  have hdistinct : ∃ i j : I, p i ≠ p j := by
    obtain ⟨i,j,hij⟩ := hI
    refine ⟨i,j,?_⟩
    intro he
    have hq : q i = q j := centerParameters_injective he
    have hBij : B i = B j := normalize_homogenize_injective ell (hn i) (hn j) hq
    apply hij
    calc
      i = label (B i) := (hlabelB i).symm
      _ = label (B j) := congrArg label hBij
      _ = j := hlabelB j
  have hcompatible : ∀ x ∈ P.vertices, ∀ y, GeneralVertexStep P x y →
      label x ≠ label y →
      differenceCenterVector (p (label x)) (p (label y)) ∈ edgeProjectiveLine x y := by
    intro x hx y hxy hlabel
    apply hcross x hx y hxy hlabel
    rw [hcenter]
    have hh := (J (label x) (label y)).neg_mem (hdiff (label x) (label y) hlabel)
    simpa only [neg_sub] using hh
  refine ⟨homothetyLabelMap label p,
    homothetyLabelMap_parallel P label p hcompatible,
    homothetyLabelMap_nontrivial P label p hclasses hdistinct,?_⟩
  intro i
  refine ⟨(p i).1,(p i).2,?_⟩
  intro x hx hi
  simp only [homothetyLabelMap,hi]

/-- Every pair of selected, differently colored vertices of an actual
simplex face is an actual edge of the ambient polytope. -/
theorem colored_simplex_representatives_edge
    (P : ConvexPolytope n) (color : P.vertices → I) (F : FaceObject P)
    (hF : AffineIndependent ℝ
      (fun v : (facePolytope P F.property).vertices => v.val))
    (v : I → P.vertices) (hv : ∀ i, (v i).val ∈ F.val)
    (hcolor : ∀ i, color (v i) = i)
    (a b : I) (hab : a ≠ b) :
    GeneralVertexStep P (v a).val (v b).val := by
  let R := facePolytope P F.property
  let x : VertexType R := ⟨(v a).val,
    (facePolytope_vertex_iff P F.property _).mpr ⟨(v a).property,hv a⟩⟩
  let y : VertexType R := ⟨(v b).val,
    (facePolytope_vertex_iff P F.property _).mpr ⟨(v b).property,hv b⟩⟩
  have hxy : (v a).val ≠ (v b).val := by
    intro h
    have hh := congrArg color (show v a = v b from Subtype.ext h)
    rw [hcolor a,hcolor b] at hh
    exact hab hh
  have hedge := simplex_graph_adj R hF x y
    (fun h => hxy (congrArg (fun z : VertexType R => z.val) h))
  have hstep : GeneralVertexStep R x.val y.val := ⟨y.property,hxy,hedge.2⟩
  exact facePolytope_step P F.property hstep

/-- The actual-face hypotheses used below express precisely an `r`-simplex:
one vertex of every one of the `r+1` colors gives its cardinality, and
affine independence then gives its affine dimension. -/
theorem colored_simplex_face_card_and_dimension
    (P : ConvexPolytope n) (color : P.vertices → Fin (r+1)) (F : FaceObject P)
    (hF : AffineIndependent ℝ
      (fun v : (facePolytope P F.property).vertices => v.val))
    (hcolor : ∀ i : Fin (r+1), ∃! v : P.vertices, v.val ∈ F.val ∧ color v = i) :
    (facePolytope P F.property).vertices.card = r+1 ∧ faceDim F.val = r := by
  let R := facePolytope P F.property
  let inclusion : R.vertices → P.vertices := fun v =>
    ⟨v.val,((facePolytope_vertex_iff P F.property v.val).mp v.property).1⟩
  let c : R.vertices → Fin (r+1) := fun v => color (inclusion v)
  have hmem (v : R.vertices) : (inclusion v).val ∈ F.val :=
    ((facePolytope_vertex_iff P F.property v.val).mp v.property).2
  have hc : Function.Bijective c := by
    constructor
    · intro v w hvw
      obtain ⟨u,hu,hunique⟩ := hcolor (c v)
      have hvu : inclusion v = u := hunique (inclusion v) ⟨hmem v,rfl⟩
      have hwu : inclusion w = u := hunique (inclusion w) ⟨hmem w,hvw.symm⟩
      have hvalues : (inclusion v).val = (inclusion w).val :=
        congrArg (fun z : P.vertices => z.val) (hvu.trans hwu.symm)
      exact Subtype.ext hvalues
    · intro i
      obtain ⟨v,hv,hunique⟩ := hcolor i
      let w : R.vertices := ⟨v.val,
        (facePolytope_vertex_iff P F.property v.val).mpr ⟨v.property,hv.1⟩⟩
      refine ⟨w,?_⟩
      exact hv.2
  have hcard : R.vertices.card = r+1 := by
    have hh := Fintype.card_congr (Equiv.ofBijective c hc)
    simpa only [Fintype.card_coe,Fintype.card_fin] using hh
  have hdimension := (vertices_affineIndependent_iff R).mp hF
  have hfaceDimension : R.dim = faceDim F.val := facePolytope_dim P F.property
  exact ⟨hcard,by omega⟩

/-- Reconstruction in one arbitrary target realization.  Only its actual
crossing-family centers are assumed; the two simplex faces are transported
from the source face lattice. -/
theorem classwise_parallel_map_after_iso
    (P : ConvexPolytope n) (color : P.vertices → Fin (r+1)) (hr : 1 ≤ r)
    (hclasses : ∀ i : Fin (r+1), ∃ x y : P.vertices,
      x ≠ y ∧ color x = i ∧ color y = i)
    (F₀ F₁ : FaceObject P) (hdis : Disjoint F₀.val F₁.val)
    (hF₀ : AffineIndependent ℝ
      (fun v : (facePolytope P F₀.property).vertices => v.val))
    (hF₁ : AffineIndependent ℝ
      (fun v : (facePolytope P F₁.property).vertices => v.val))
    (hcolor₀ : ∀ i : Fin (r+1), ∃! v : P.vertices, v.val ∈ F₀.val ∧ color v = i)
    (hcolor₁ : ∀ i : Fin (r+1), ∃! v : P.vertices, v.val ∈ F₁.val ∧ color v = i)
    (Q : ConvexPolytope m) (φ : FaceObject P ≃o FaceObject Q)
    (hcenters : ∀ i j : Fin (r+1), i ≠ j →
      ∃ J : Submodule ℝ (E m × ℝ), finrank ℝ J = 1 ∧
        ∀ e : CrossingFamily Q (colorAlong φ color) i j, J ≤ e.line) :
    ∃ f : E m → E m, IsParallelMap Q f ∧ ¬ IsHomothetyOnVertices Q f ∧
      ∀ i : Fin (r+1), ∃ a : ℝ, ∃ b : E m,
        ∀ v : Q.vertices, colorAlong φ color v = i → f v.val = a • v.val + b := by
  let x₀ : Fin (r+1) → P.vertices := fun i => (hcolor₀ i).choose
  let x₁ : Fin (r+1) → P.vertices := fun i => (hcolor₁ i).choose
  have hx₀ (i : Fin (r+1)) : (x₀ i).val ∈ F₀.val ∧ color (x₀ i) = i :=
    (hcolor₀ i).choose_spec.1
  have hx₁ (i : Fin (r+1)) : (x₁ i).val ∈ F₁.val ∧ color (x₁ i) = i :=
    (hcolor₁ i).choose_spec.1
  let y₀ : Fin (r+1) → Q.vertices := fun i => vertexEquiv φ (x₀ i)
  let y₁ : Fin (r+1) → Q.vertices := fun i => vertexEquiv φ (x₁ i)
  let colorQ := colorAlong φ color
  let label : E m → Fin (r+1) := fun x =>
    if h : x ∈ Q.vertices then colorQ ⟨x,h⟩ else 0
  have label_vertex (v : Q.vertices) : label v.val = colorQ v := by
    simp only [label,dif_pos v.property]
  have label_y₀ (i : Fin (r+1)) : label (y₀ i).val = i := by
    rw [label_vertex]
    change color ((vertexEquiv φ).symm (vertexEquiv φ (x₀ i))) = i
    rw [Equiv.symm_apply_apply]
    exact (hx₀ i).2
  have label_y₁ (i : Fin (r+1)) : label (y₁ i).val = i := by
    rw [label_vertex]
    change color ((vertexEquiv φ).symm (vertexEquiv φ (x₁ i))) = i
    rw [Equiv.symm_apply_apply]
    exact (hx₁ i).2
  have edge₀ (a b : Fin (r+1)) (hab : a ≠ b) :
      GeneralVertexStep Q (y₀ a).val (y₀ b).val :=
    edge_forward φ (x₀ a) (x₀ b)
      (colored_simplex_representatives_edge P color F₀ hF₀ x₀
        (fun i => (hx₀ i).1) (fun i => (hx₀ i).2) a b hab)
  have edge₁ (a b : Fin (r+1)) (hab : a ≠ b) :
      GeneralVertexStep Q (y₁ a).val (y₁ b).val :=
    edge_forward φ (x₁ a) (x₁ b)
      (colored_simplex_representatives_edge P color F₁ hF₁ x₁
        (fun i => (hx₁ i).1) (fun i => (hx₁ i).2) a b hab)
  let family₀ (a b : Fin (r+1)) (hab : a ≠ b) : CrossingFamily Q colorQ a b :=
    ⟨(y₀ a,y₀ b),edge₀ a b hab,
      (label_vertex (y₀ a)).symm.trans (label_y₀ a),
      (label_vertex (y₀ b)).symm.trans (label_y₀ b)⟩
  let J : Fin (r+1) → Fin (r+1) → Submodule ℝ (E m × ℝ) :=
    fun a b => if h : a ≠ b then (hcenters a b h).choose else ⊥
  have hJ (a b : Fin (r+1)) (hab : a ≠ b) :
      finrank ℝ (J a b) = 1 ∧
        ∀ e : CrossingFamily Q colorQ a b, J a b ≤ e.line := by
    have hJeq : J a b = (hcenters a b hab).choose := dif_pos hab
    rw [hJeq]
    exact (hcenters a b hab).choose_spec
  let G₀ := φ F₀
  obtain ⟨g,hg⟩ := exists_supportsFace Q G₀.property
  have hy₀G (i : Fin (r+1)) : (y₀ i).val ∈ G₀.val :=
    (vertex_mem_face_iff φ (x₀ i) F₀).mpr (hx₀ i).1
  have hy₁notG (i : Fin (r+1)) : (y₁ i).val ∉ G₀.val := by
    intro hi
    have hx₁F₀ := (vertex_mem_face_iff φ (x₁ i) F₀).mp hi
    exact Set.disjoint_left.mp hdis hx₁F₀ (hx₁ i).1
  have hclassesQ : ∀ i : Fin (r+1), ∃ x ∈ Q.vertices, ∃ y ∈ Q.vertices,
      x ≠ y ∧ label x = i ∧ label y = i := by
    intro i
    obtain ⟨x,y,hxy,hxi,hyi⟩ := hclasses i
    refine ⟨(vertexEquiv φ x).val,(vertexEquiv φ x).property,
      (vertexEquiv φ y).val,(vertexEquiv φ y).property,?_,?_,?_⟩
    · intro he
      exact hxy ((vertexEquiv φ).injective (Subtype.ext he))
    · rw [label_vertex]
      change color ((vertexEquiv φ).symm (vertexEquiv φ x)) = i
      simpa only [Equiv.symm_apply_apply] using hxi
    · rw [label_vertex]
      change color ((vertexEquiv φ).symm (vertexEquiv φ y)) = i
      simpa only [Equiv.symm_apply_apply] using hyi
  have hI : ∃ i j : Fin (r+1), i ≠ j := by
    apply Fintype.one_lt_card_iff.mp
    simp only [Fintype.card_fin]
    omega
  obtain ⟨f,hf,hnon,hclasswise⟩ := classwise_parallel_map_of_supporting_center_data
    Q label g (fun i => (y₀ i).val) (fun i => (y₁ i).val) J
    (fun i => hg.eq_zero (hy₀G i))
    (fun i => show 0 < g (y₁ i).val from by
      have hnonneg := hg.1 (y₁ i).val (subset_convexHull ℝ _ (y₁ i).property)
      have hneq : g (y₁ i).val ≠ 0 := by
        intro hz
        exact hy₁notG i ((hg.mem_iff _).mpr
          ⟨subset_convexHull ℝ _ (y₁ i).property,hz⟩)
      exact lt_of_le_of_ne hnonneg hneq.symm)
    label_y₁ hclassesQ hI
    (fun a b hab => (hJ a b hab).1)
    (fun a b hab => (hJ a b hab).2 (family₀ a b hab))
    (fun a b hab => (hJ a b hab).2
      ⟨(y₁ a,y₁ b),edge₁ a b hab,
        (label_vertex (y₁ a)).symm.trans (label_y₁ a),
        (label_vertex (y₁ b)).symm.trans (label_y₁ b)⟩)
    (fun x hx y hxy hlabel => (hJ (label x) (label y) hlabel).2
      ⟨(⟨x,hx⟩,⟨y,hxy.1⟩),hxy,
        (label_vertex ⟨x,hx⟩).symm,(label_vertex ⟨y,hxy.1⟩).symm⟩)
  refine ⟨f,hf,hnon,?_⟩
  intro i
  obtain ⟨a,b,hi⟩ := hclasswise i
  refine ⟨a,b,?_⟩
  intro v hv
  exact hi v.val v.property ((label_vertex v).trans hv)

/-- Corrected Lemma 6, literally in the vertex-domain language of the
paper.  Projective concurrence is assumed separately for each actual
crossing family in every realization; no compatibility is assumed.
The conclusion retains both nontriviality and homothety on every color. -/
theorem corrected_simplex_reconstruction
    (P : ConvexPolytope n) (hP : P.IsFullDim)
    (color : P.vertices → Fin (r+1)) (hr : 1 ≤ r)
    (hclasses : ∀ i : Fin (r+1), ∃ x y : P.vertices,
      x ≠ y ∧ color x = i ∧ color y = i)
    (F₀ F₁ : FaceObject P) (hdis : Disjoint F₀.val F₁.val)
    (hF₀ : AffineIndependent ℝ
      (fun v : (facePolytope P F₀.property).vertices => v.val))
    (hF₁ : AffineIndependent ℝ
      (fun v : (facePolytope P F₁.property).vertices => v.val))
    (hcolor₀ : ∀ i : Fin (r+1), ∃! v : P.vertices, v.val ∈ F₀.val ∧ color v = i)
    (hcolor₁ : ∀ i : Fin (r+1), ∃! v : P.vertices, v.val ∈ F₁.val ∧ color v = i)
    (hforced : ∀ (Q : ConvexPolytope n) (φ : FaceObject P ≃o FaceObject Q),
      ∀ i j : Fin (r+1), i ≠ j →
        ∃ J : Submodule ℝ (E n × ℝ), finrank ℝ J = 1 ∧
          ∀ e : CrossingFamily Q (colorAlong φ color) i j, J ≤ e.line) :
    ∀ (Q : ConvexPolytope n) (φ : FaceObject P ≃o FaceObject Q),
      Q.IsFullDim ∧ ∃ f : Q.vertices → E n,
        (∀ x y : Q.vertices, GeneralVertexStep Q x.val y.val →
          ∃ a : ℝ, f y - f x = a • (y.val - x.val)) ∧
        (¬ ∃ a : ℝ, ∃ b : E n, ∀ v : Q.vertices, f v = a • v.val + b) ∧
        (∀ i : Fin (r+1), ∃ a : ℝ, ∃ b : E n,
          ∀ v : Q.vertices, colorAlong φ color v = i → f v = a • v.val + b) := by
  intro Q φ
  have hQ : Q.IsFullDim := (Papers.ActualFaceOrder.dim_eq φ).trans hP
  obtain ⟨f,hf,hnon,hclasswise⟩ := classwise_parallel_map_after_iso
    P color hr hclasses F₀ F₁ hdis hF₀ hF₁ hcolor₀ hcolor₁ Q φ (hforced Q φ)
  refine ⟨hQ,(fun v => f v.val),?_,?_,hclasswise⟩
  · intro x y hxy
    exact hf x.val x.property y.val y.property hxy
  · rintro ⟨a,b,hab⟩
    apply hnon
    refine ⟨a,b,?_⟩
    intro x hx
    exact hab ⟨x,hx⟩

end Papers.CorrectedSimplexReconstruction

end
end
end BundlePart65

section BundlePart66
/- Source: Papers/ConditionalFormalisation.lean -/








/-!
# The sharp vertex bound for conditional decomposability

This public entry point collects Theorem 1, its universal below-threshold
assertion, Propositions 7, 11 and 12 in their mathematical formulations,
the vertex-domain equivalence for parallel maps, and the precise
positive-dimensional simplex reconstruction lemma.

The principal declarations are in `Papers.Polytopes`. The accompanying
formalisation note gives their correspondence with the paper and explains
the supporting proofs and exact definitions.
-/

#check @Papers.Polytopes.conditional_decomposability_sharp
#print axioms Papers.Polytopes.conditional_decomposability_sharp
#check @Papers.Polytopes.conditional_decomposability_claim
#print axioms Papers.Polytopes.conditional_decomposability_claim
#check @Papers.Polytopes.conditional_vertex_count_isLeast
#print axioms Papers.Polytopes.conditional_vertex_count_isLeast
#check @Papers.Polytopes.decomposability_determined_by_face_lattice_below_threshold
#print axioms Papers.Polytopes.decomposability_determined_by_face_lattice_below_threshold
#check @Papers.Polytopes.conditional_decomposability_attainment
#print axioms Papers.Polytopes.conditional_decomposability_attainment
#check @Papers.Polytopes.decomposable_iff_of_face_iso_below_threshold
#print axioms Papers.Polytopes.decomposable_iff_of_face_iso_below_threshold
#check @Papers.Polytopes.decomposable_after_iso_of_at_most_three_homotheties
#print axioms Papers.Polytopes.decomposable_after_iso_of_at_most_three_homotheties
#check @Papers.Polytopes.decomposable_after_iso_of_weak_summand
#print axioms Papers.Polytopes.decomposable_after_iso_of_weak_summand
#check @Papers.Polytopes.HomothetyParameters.uniform_cover_positive_projectivity_or_shephard
#print axioms Papers.Polytopes.HomothetyParameters.uniform_cover_positive_projectivity_or_shephard
#check @Papers.Polytopes.nontrivial_parallel_map_iff_vertex_domain
#print axioms Papers.Polytopes.nontrivial_parallel_map_iff_vertex_domain
#check @Papers.CorrectedSimplexReconstruction.corrected_simplex_reconstruction
#print axioms Papers.CorrectedSimplexReconstruction.corrected_simplex_reconstruction
#check @Papers.Polytopes.SimplexReconstructionZeroCounterexample.lemma6_zero_counterexample
#print axioms Papers.Polytopes.SimplexReconstructionZeroCounterexample.lemma6_zero_counterexample

end BundlePart66

