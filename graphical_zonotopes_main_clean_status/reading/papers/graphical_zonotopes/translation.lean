module

public import Papers.GraphicalZonotopes.GraphDefinitions
public import Papers.GraphicalZonotopes.ConeCorrespondence
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem singleton_add_eq_vadd (t : V → ℝ) (Q : Set (V → ℝ)) :
    ({t} : Set (V → ℝ))+Q=t+ᵥQ := by
  rw [Set.singleton_add, ← Set.image_vadd]
  simp only [vadd_eq_add]

theorem basePolytope_eq_vadd_normalize (z : SetFunction V) :
    basePolytope z=(fun v => z {v})+ᵥbasePolytope (normalize z) := by
  conv_lhs => rw [recover_normalize z]
  rw [basePolytope_translate,singleton_add_eq_vadd]

theorem vectorSpan_basePolytope_normalize (z : SetFunction V) :
    vectorSpan ℝ (basePolytope (normalize z))=vectorSpan ℝ (basePolytope z) := by
  rw [basePolytope_eq_vadd_normalize z,vectorSpan_vadd]

theorem IsExposedSegment.vadd {Q : Set (V → ℝ)} {p q : V → ℝ}
    (h : IsExposedSegment Q p q) (t : V → ℝ) :
    IsExposedSegment (t+ᵥQ) (t+p) (t+q) := by
  obtain ⟨hpq,ℓ,a,hbound,hface⟩ := h
  refine ⟨fun he => hpq (add_left_cancel he),ℓ,ℓ t+a,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    change ℓ t+a ≤ ℓ (t+y)
    rw [map_add]
    exact add_le_add (le_refl (ℓ t)) (hbound y hy)
  · have he : {x ∈ t+ᵥQ | ℓ x=ℓ t+a}=t+ᵥ{x ∈ Q | ℓ x=a} := by
      ext x
      constructor
      · rintro ⟨⟨y,hy,rfl⟩,he⟩
        refine ⟨y,⟨hy,?_⟩,rfl⟩
        change ℓ (t+y)=ℓ t+a at he
        rw [map_add] at he
        exact add_left_cancel he
      · rintro ⟨y,⟨hy,he⟩,rfl⟩
        refine ⟨⟨y,hy,rfl⟩,?_⟩
        change ℓ (t+y)=ℓ t+a
        rw [map_add,he]
    rw [he,hface,vadd_segment]
    simp only [vadd_eq_add]

theorem ActualRootEdge.vadd {Q : Set (V → ℝ)} {u v : V}
    (h : ActualRootEdge Q u v) (t : V → ℝ) : ActualRootEdge (t+ᵥQ) u v := by
  obtain ⟨huv,p,q,hface,a,ha,he⟩ := h
  refine ⟨huv,t+p,t+q,hface.vadd t,a,ha,?_⟩
  calc
    (t+q)-(t+p)=q-p := by abel
    _=a • (basisVector u-basisVector v) := he

theorem actualRootEdge_vadd_iff (Q : Set (V → ℝ)) (t : V → ℝ) (u v : V) :
    ActualRootEdge (t+ᵥQ) u v ↔ ActualRootEdge Q u v := by
  constructor
  · intro h
    have he := h.vadd (-t)
    simpa only [vadd_vadd,neg_add_cancel,zero_vadd] using he
  · exact fun h => h.vadd t

theorem actualDirectionGraph_vadd (Q : Set (V → ℝ)) (t : V → ℝ) :
    actualDirectionGraph (t+ᵥQ)=actualDirectionGraph Q := by
  ext u v
  exact actualRootEdge_vadd_iff Q t u v

theorem actualDirectionGraph_normalize (z : SetFunction V) :
    actualDirectionGraph (basePolytope (normalize z))=actualDirectionGraph (basePolytope z) := by
  rw [basePolytope_eq_vadd_normalize z,actualDirectionGraph_vadd]

theorem normalize_smul (z : SetFunction V) (a : ℝ) :
    normalize (a • z)=a • normalize z := by
  funext S
  simp only [normalize,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,modular,subsetSum]
  rw [mul_sub,Finset.mul_sum]

@[simp] theorem normalize_modular (t : V → ℝ) : normalize (modular t)=0 := by
  funext S
  simp [normalize,modular,subsetSum]

/-- Geometric indecomposability passes to the normalized cone directly.
The proof permits the original polytope to have an arbitrary translation. -/
theorem MinkowskiIndecomposable.extremeSupermodular_normalize {z : SetFunction V}
    (hn : Normalized z) (hs : Supermodular z) (hne : normalize z ≠ 0)
    (hi : MinkowskiIndecomposable (basePolytope z)) : ExtremeSupermodular (normalize z) := by
  have h0n := normalize_translationNormalized hn
  have h0s := hs.normalize
  refine ⟨h0n,h0s,hne,?_⟩
  intro f g hfn hgn hfs hgs hfg
  let t : V → ℝ := fun v => z {v}
  have hftn : Normalized (f+modular t) := by
    change f ∅+subsetSum t ∅=0
    simpa only [subsetSum,Finset.sum_empty,add_zero] using (show f ∅=0 from hfn.1)
  have hfts := hfs.add (modular_supermodular t)
  have hsum : basePolytope (f+modular t)+basePolytope g=basePolytope z := by
    rw [← basePolytope_add hftn hgn.1 hfts hgs]
    congr 1
    calc
      f+modular t+g=(f+g)+modular t := by abel
      _=normalize z+modular t := by rw [hfg]
      _=z := (recover_normalize z).symm
  obtain ⟨a,s,ha,he⟩ := hi.2 (basePolytope (f+modular t)) (basePolytope g)
    (basePolytope_compact hftn hfts) (basePolytope_compact hgn.1 hgs)
    (basePolytope_convex _) (basePolytope_convex _) hsum
  rw [← basePolytope_smul hn hs ha,← basePolytope_translate] at he
  have han : Normalized (a • z+modular s) := by
    change a*z ∅+subsetSum s ∅=0
    simp only [show z ∅=0 from hn,mul_zero,subsetSum,Finset.sum_empty,add_zero]
  have has := (hs.smul ha).add (modular_supermodular s)
  have hefun := congrArg lowerSupport he
  rw [lowerSupport_basePolytope hftn hfts,lowerSupport_basePolytope han has] at hefun
  have hnorm := congrArg normalize hefun
  rw [normalize_add,normalize_modular,add_zero,normalize_eq_self hfn,
    normalize_add,normalize_smul,normalize_modular,add_zero] at hnorm
  exact ⟨a,ha,hnorm⟩

end GraphicalZonotopes
