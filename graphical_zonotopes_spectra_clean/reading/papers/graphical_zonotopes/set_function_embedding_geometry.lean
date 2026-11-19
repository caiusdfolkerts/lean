module

public import Papers.GraphicalZonotopes.SetFunctionEmbedding
public import Papers.GraphicalZonotopes.SupportGeometry
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace GraphicalZonotopes.SetFunctionEmbedding
open Finset
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

@[simp] theorem pullSet_univ (e : W ↪ V) : pullSet e univ=univ := by
  ext w; simp

theorem reconstruct_of_insert_absent (e : W ↪ V) (f : SetFunction V)
    (hf : ∀ v,v∉Set.range e → ∀ S,f (insert v S)=f S) :
    extend e (restrict e f)=f := by
  have hall : ∀ S : Finset V,∀ f : SetFunction V,
      (∀ v,v∉Set.range e → ∀ T,f (insert v T)=f T) →
      f S=f ((pullSet e S).map e) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro f hf; simp
    | @insert v S hv ih =>
      intro f hf
      by_cases hvR : v∈Set.range e
      · obtain ⟨w,rfl⟩ := hvR
        let g : SetFunction V := fun T => f (insert (e w) T)
        have hg : ∀ v,v∉Set.range e → ∀ T,g (insert v T)=g T := by
          intro v hv T
          dsimp only [g]
          rw [insert_comm,hf v hv]
        simpa only [g,pullSet_insert_image,map_insert] using ih g hg
      · rw [hf v hvR,pullSet_insert_not_range e v hvR]
        exact ih f hf
  funext S
  exact (hall S f hf).symm

theorem insert_absent_of_zero_deltas {f : SetFunction V}
    (hn : TranslationNormalized f) (u : V)
    (hz : ∀ v,u≠v → ∀ S,u∉S → v∉S → delta f u v S=0) :
    ∀ S,f (insert u S)=f S := by
  intro S
  induction S using Finset.induction_on with
  | empty => change f {u}=f ∅; rw [hn.2 u,hn.1]
  | @insert v S hv ih =>
    by_cases huv : u=v
    · subst v; simp
    · by_cases huS : u∈S
      · simp [insert_eq_of_mem huS,insert_eq_of_mem (mem_insert_of_mem huS)]
      · have hh := hz v huv S huS hv
        dsimp only [delta] at hh
        rw [ih] at hh
        linarith

/-- Adding unused coordinates preserves actual extremality in the full
supermodular cone. Summands are proved to ignore every new coordinate. -/
theorem extend_extreme (e : W ↪ V) {f : SetFunction W}
    (hf : ExtremeSupermodular f) : ExtremeSupermodular (extend e f) := by
  refine ⟨extend_translationNormalized e hf.1,extend_supermodular e hf.2.1,?_,?_⟩
  · intro he
    apply hf.2.2.1
    funext S
    have hh := congrFun he (S.map e)
    simpa only [extend,pullSet_map,Pi.zero_apply] using hh
  · intro g h hgn hhn hgs hhs hsum
    have hgzero : ∀ u,u∉Set.range e → ∀ v,u≠v → ∀ S,u∉S → v∉S →
        delta g u v S=0 := by
      intro u hu v huv S huS hvS
      have h1 := hgs.elemental u v huv S huS hvS
      have h2 := hhs.elemental u v huv S huS hvS
      have he : delta g u v S+delta h u v S=0 := by
        rw [← delta_add,hsum,delta_extend_not_range e f u v hu]
      linarith
    have hgrec : extend e (restrict e g)=g :=
      reconstruct_of_insert_absent e g (fun u hu =>
        insert_absent_of_zero_deltas hgn u (hgzero u hu))
    have hsum' : restrict e g+restrict e h=f := by
      funext S
      have he := congrFun hsum (S.map e)
      simpa only [restrict,extend,pullSet_map,Pi.add_apply] using he
    obtain ⟨a,ha,hscale⟩ := hf.2.2.2 (restrict e g) (restrict e h)
      (restrict_translationNormalized e hgn) (restrict_translationNormalized e hhn)
      (restrict_supermodular e hgs) (restrict_supermodular e hhs) hsum'
    refine ⟨a,ha,?_⟩
    rw [← hgrec,hscale,extend_smul]

theorem extend_integer (e : W ↪ V) {f : SetFunction W}
    (hf : IntegerValued f) : IntegerValued (extend e f) := fun S => hf (pullSet e S)

theorem extend_dependsOn (e : W ↪ V) (f : SetFunction W) :
    DependsOn (extend e f) (univ.map e) := by
  intro S
  change f (pullSet e S)=f (pullSet e (S∩univ.map e))
  congr 1
  ext w
  simp

/-- The literal linear embedding extends vectors by zero outside the image. -/
def pushVector (e : W ↪ V) : (W → ℝ) →ₗ[ℝ] (V → ℝ) :=
  Fintype.linearCombination ℝ (fun w => basisVector (e w))

@[simp] theorem pushVector_image (e : W ↪ V) (x : W → ℝ) (w : W) :
    pushVector e x (e w)=x w := by
  simp [pushVector,Fintype.linearCombination_apply,basisVector,Pi.single_apply,
    e.injective.eq_iff]

theorem pushVector_outside (e : W ↪ V) (x : W → ℝ) (v : V)
    (hv : v∉Set.range e) : pushVector e x v=0 := by
  have hne : ∀ w,e w≠v := fun w he => hv ⟨w,he⟩
  simp [pushVector,Fintype.linearCombination_apply,basisVector,Pi.single_apply,
    hne,fun w => Ne.symm (hne w)]

theorem pushVector_injective (e : W ↪ V) : Function.Injective (pushVector e) := by
  intro x y he
  funext w
  have hh := congrFun he (e w)
  simpa only [pushVector_image] using hh

theorem subsetSum_pushVector (e : W ↪ V) (x : W → ℝ) (S : Finset V) :
    subsetSum (pushVector e x) S=subsetSum x (pullSet e S) := by
  change subsetSum (∑ w,x w • basisVector (e w)) S=_
  unfold subsetSum
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [sum_comm]
  simp_rw [← mul_sum]
  change (∑ w,x w*subsetSum (basisVector (e w)) S)=_
  simp only [subsetSum_basisVector]
  simp [subsetSum,pullSet,sum_filter]

/-- The extended base polytope is exactly the zero-coordinate linear image
of the original body, including every point and every defining inequality. -/
theorem basePolytope_extend (e : W ↪ V) {f : SetFunction W}
    (hn : TranslationNormalized f) :
    basePolytope (extend e f)=pushVector e '' basePolytope f := by
  ext x
  constructor
  · intro hx
    let p : W → ℝ := fun w => x (e w)
    have hzero : ∀ v,v∉Set.range e → x v=0 := by
      intro v hv
      apply basePolytope_coordinate_zero_of_dependsOn
        (extend_translationNormalized e hn) (extend_dependsOn e f) (x := x) _ hx
      intro hm
      obtain ⟨w,_,he⟩ := mem_map.mp hm
      exact hv ⟨w,he⟩
    have hpush : pushVector e p=x := by
      funext v
      by_cases hv : v∈Set.range e
      · obtain ⟨w,rfl⟩ := hv
        exact pushVector_image e p w
      · rw [pushVector_outside e p v hv,hzero v hv]
    refine ⟨p,?_,hpush⟩
    constructor
    · have ht := hx.1
      rw [← hpush,subsetSum_pushVector,pullSet_univ] at ht
      simpa only [extend,pullSet_univ] using ht
    · intro T
      have ht := hx.2 (T.map e)
      rw [← hpush,subsetSum_pushVector,pullSet_map] at ht
      simpa only [extend,pullSet_map] using ht
  · rintro ⟨p,hp,rfl⟩
    constructor
    · rw [subsetSum_pushVector,pullSet_univ]
      simpa only [extend,pullSet_univ] using hp.1
    · intro S
      rw [subsetSum_pushVector]
      exact hp.2 (pullSet e S)

/-- Affine dimension is unchanged by an injective extension of the vertex
index set. This is a statement about the genuine base polytopes. -/
theorem finrank_vectorSpan_extend (e : W ↪ V) {f : SetFunction W}
    (hn : TranslationNormalized f) :
    Module.finrank ℝ (vectorSpan ℝ (basePolytope (extend e f)))=
      Module.finrank ℝ (vectorSpan ℝ (basePolytope f)) := by
  rw [basePolytope_extend e hn]
  have he := (pushVector e).toAffineMap.map_vectorSpan (s := basePolytope f)
  change Submodule.map (pushVector e) (vectorSpan ℝ (basePolytope f))=
    vectorSpan ℝ (pushVector e '' basePolytope f) at he
  rw [← he]
  exact (Submodule.equivMapOfInjective (pushVector e) (pushVector_injective e)
    (vectorSpan ℝ (basePolytope f))).finrank_eq.symm

end GraphicalZonotopes.SetFunctionEmbedding
