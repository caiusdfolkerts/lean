module
public import graph_foundation.part011
public import shared_results.part004
public import paper_results.part006

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.IncidenceAlexanderComplex -/
section

/-! # The literal incidence ideal and its Alexander-dual cover

Variables are the disjoint sum of the left vertices and the incidences.
Each first generator chooses z_a or the complete incidence block X_a for
each a. The other generators are the right incidence blocks W_r.
The Alexander-dual complex is proved to be the union of the join of an
isolated z_a with its leaf simplex and the complements of the W_r.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u v w
variable {L : Type u} {R : Type v} {T : Type w} [Fintype L] [Fintype R] [Fintype T]
  [DecidableEq L] [DecidableEq R] [LinearOrder (L ⊕ T)]

def incidenceChoiceSupport (left : T → L) (D : Finset L) : Finset (L ⊕ T) :=
  D.image Sum.inl ∪ ((Finset.univ.filter fun t => left t ∉ D).image Sum.inr)

def incidenceRightSupport (right : T → R) (r : R) : Finset (L ⊕ T) :=
  (Finset.univ.filter fun t => right t = r).image Sum.inr

@[simp] theorem incidenceChoiceSupport_inl (left : T → L) (D : Finset L) (a : L) :
    Sum.inl a ∈ incidenceChoiceSupport left D ↔ a ∈ D := by
  simp [incidenceChoiceSupport]

@[simp] theorem incidenceChoiceSupport_inr (left : T → L) (D : Finset L) (t : T) :
    Sum.inr t ∈ incidenceChoiceSupport left D ↔ left t ∉ D := by
  simp [incidenceChoiceSupport]

@[simp] theorem incidenceRightSupport_inl (right : T → R) (r : R) (a : L) :
    Sum.inl a ∉ incidenceRightSupport (L := L) right r := by
  simp [incidenceRightSupport]

@[simp] theorem incidenceRightSupport_inr (right : T → R) (r : R) (t : T) :
    Sum.inr t ∈ incidenceRightSupport (L := L) right r ↔ right t = r := by
  simp [incidenceRightSupport]

/-- The actual squarefree generator family of
`prod_a (z_a,X_a) + (W_r | r)`. -/
def incidenceColonFamily (left : T → L) (right : T → R) : Family (L ⊕ T) :=
  (Finset.univ.image fun D : Finset L => faceExponent (incidenceChoiceSupport left D)) ∪
    (Finset.univ.image fun r : R => faceExponent (incidenceRightSupport (L := L) right r))

theorem incidenceColonFamily_contains_squarefree (left : T → L) (right : T → R)
    (F : Finset (L ⊕ T)) : Contains (incidenceColonFamily left right) (faceExponent F) ↔
      (∃ D : Finset L, incidenceChoiceSupport left D ⊆ F) ∨
        ∃ r : R, incidenceRightSupport (L := L) right r ⊆ F := by
  constructor
  · rintro ⟨a,ha,hle⟩
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp ha
      exact Or.inl ⟨D,(faceExponent_le_faceExponent_iff _ _).mp hle⟩
    · obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp ha
      exact Or.inr ⟨r,(faceExponent_le_faceExponent_iff _ _).mp hle⟩
  · rintro (⟨D,hD⟩ | ⟨r,hr⟩)
    · exact ⟨_,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨D,Finset.mem_univ _,rfl⟩),
        (faceExponent_le_faceExponent_iff _ _).mpr hD⟩
    · exact ⟨_,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩),
        (faceExponent_le_faceExponent_iff _ _).mpr hr⟩

/-- The join of the complexes consisting of z_a and a disjoint full
simplex on the leaves at a. -/
def incidenceJoinFaces (left : T → L) (F : Finset (L ⊕ T)) : Prop :=
  ∀ a : L, Sum.inl a ∈ F → ∀ t : T, left t = a → Sum.inr t ∉ F

def incidenceCoverFaces (right : T → R) (F : Finset (L ⊕ T)) : Prop :=
  ∃ r : R, ∀ t : T, right t = r → Sum.inr t ∉ F

def incidenceIntersectionFaces (left : T → L) (right : T → R) (Q : Finset R)
    (F : Finset (L ⊕ T)) : Prop :=
  incidenceJoinFaces left F ∧ ∀ t : T, right t ∈ Q → Sum.inr t ∉ F

def incidenceNerveFaces (left : T → L) (right : T → R) (Q : Finset R) : Prop :=
  ∀ a : L, ∃ t : T, left t = a ∧ right t ∉ Q

theorem incidenceJoinFaces_iff_choice_complement (left : T → L) (F : Finset (L ⊕ T)) :
    incidenceJoinFaces left F ↔ ∃ D : Finset L,
      incidenceChoiceSupport left D ⊆ Finset.univ \ F := by
  constructor
  · intro h
    let D := Finset.univ.filter fun a : L => Sum.inl a ∉ F
    refine ⟨D,?_⟩
    intro v hv
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    cases v with
    | inl a => simpa only [incidenceChoiceSupport_inl,D,Finset.mem_filter,
        Finset.mem_univ,true_and] using hv
    | inr t =>
        have ha : Sum.inl (left t) ∈ F := by
          have hh := (incidenceChoiceSupport_inr left D t).mp hv
          simpa only [D,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using hh
        exact h (left t) ha t rfl
  · rintro ⟨D,hD⟩ a ha t hta ht
    by_cases hd : a ∈ D
    · exact (Finset.mem_sdiff.mp (hD ((incidenceChoiceSupport_inl left D a).mpr hd))).2 ha
    · have htd : left t ∉ D := by simpa only [hta] using hd
      exact (Finset.mem_sdiff.mp (hD ((incidenceChoiceSupport_inr left D t).mpr htd))).2 ht

theorem incidenceCoverFaces_iff_complement (right : T → R) (F : Finset (L ⊕ T)) :
    incidenceCoverFaces right F ↔ ∃ r : R,
      incidenceRightSupport (L := L) right r ⊆ Finset.univ \ F := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r,?_⟩
    intro v hv
    cases v with
    | inl a => exact False.elim (incidenceRightSupport_inl right r a hv)
    | inr t => exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        hr t ((incidenceRightSupport_inr right r t).mp hv)⟩
  · rintro ⟨r,hr⟩
    exact ⟨r,fun t ht => (Finset.mem_sdiff.mp
      (hr ((incidenceRightSupport_inr right r t).mpr ht))).2⟩

/-- The exact union in the first display of the proof of Lemma 10.1. -/
theorem incidenceAlexanderDual_faces (left : T → L) (right : T → R) (F : Finset (L ⊕ T)) :
    alexanderDualFaces (incidenceColonFamily left right) F ↔
      incidenceJoinFaces left F ∨ incidenceCoverFaces right F := by
  simp only [alexanderDualFaces, stanleyReisnerFaces, not_not,
    incidenceColonFamily_contains_squarefree]
  simpa only [Finset.subset_iff, Finset.mem_sdiff] using
    or_congr (incidenceJoinFaces_iff_choice_complement left F).symm
      (incidenceCoverFaces_iff_complement right F).symm

theorem incidenceJoinFaces_downward (left : T → L) : Simplicial.Downward (incidenceJoinFaces left) := by
  intro F H hHF hF a ha t ht
  exact fun h => hF a (hHF ha) t ht (hHF h)

theorem incidenceCoverFaces_downward (right : T → R) :
    Simplicial.Downward (incidenceCoverFaces (L := L) right) := by
  rintro F H hHF ⟨r,hr⟩
  exact ⟨r,fun t ht h => hr t ht (hHF h)⟩

theorem incidenceIntersectionFaces_downward (left : T → L) (right : T → R) (Q : Finset R) :
    Simplicial.Downward (incidenceIntersectionFaces left right Q) := by
  intro F H hHF hF
  exact ⟨incidenceJoinFaces_downward left hHF hF.1,
    fun t ht h => hF.2 t ht (hHF h)⟩

theorem incidenceNerveFaces_downward (left : T → L) (right : T → R) :
    Simplicial.Downward (incidenceNerveFaces left right) := by
  intro Q P hPQ hQ a
  obtain ⟨t,ht,htr⟩ := hQ a
  exact ⟨t,ht,fun hp => htr (hPQ hp)⟩

/-- The cover is a cone on each actual left variable. -/
theorem incidenceCoverFaces_insert_left (right : T → R) (a : L)
    {F : Finset (L ⊕ T)} (hF : incidenceCoverFaces right F) :
    incidenceCoverFaces right (insert (Sum.inl a) F) := by
  obtain ⟨r,hr⟩ := hF
  exact ⟨r,fun t ht => by simpa only [Finset.mem_insert,Sum.inr_ne_inl,false_or] using hr t ht⟩

/-- Every intersection contains the complete simplex on the z variables,
including the empty face. -/
theorem incidenceIntersectionFaces_left_simplex (left : T → L) (right : T → R)
    (Q : Finset R) (D : Finset L) :
    incidenceIntersectionFaces left right Q (D.image Sum.inl) := by
  constructor
  · intro a ha t ht
    simp
  · intro t ht
    simp

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.JoinedTwoSimplexContraction -/
section

/-! # The actual integral contraction of a join of two-simplex factors

The disjoint row supports are fixed independently of the cover index.
The face tensor equivalence is the signed exterior multiplication map,
so this construction contracts the literal augmented face differential.
Every good row contributes its difference of chosen vertices. If one
one-block is empty, its fixed zero vertex contracts the entire join.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice.JoinedTwoSimplex
open Classical CommAlg CommAlg.Simplicial HomologicalPerturbation
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]
variable {m : ℕ}

def Faces (S : Fin m → V → Prop) (Z E : Fin m → Finset V) : Finset V → Prop :=
  separatedFamilyFaces S (fun p => TwoSimplex.Faces (Z p) (E p))

theorem downward (S : Fin m → V → Prop) (Z E : Fin m → Finset V) :
    Downward (Faces S Z E) := by
  intro F H hHF hF
  refine ⟨fun x hx => hF.1 x (hHF hx),fun p => ?_⟩
  exact TwoSimplex.downward (Z p) (E p)
    (Finset.filter_subset_filter (S p) hHF) (hF.2 p)

theorem projected_eq_ideal {P : Finset V → Prop} (hP : Downward P) :
    projectedTotalDifferential (k := k) P=idealTotalDifferential hP := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact faceProjection_eq_self P (boundary_mem_basisSpan hP x.property)

theorem involute_on_piece (P : Finset V → Prop) (j : ℕ)
    (x : TotalFaceModule (k := k) P) (hx : x ∈ totalFacePiece P j) :
    totalFaceInvolute P x=(-1:k)^j • x := by
  apply Subtype.ext
  change CliffordAlgebra.involute x.val=(-1:k)^j • x.val
  change x.val∈Chains P j at hx
  generalize x.val = y at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,⟨hF,hcard⟩,rfl⟩ := hx
      simpa only [Simplicial.basis,hcard] using!
        TauCeti.ExteriorAlgebra.involute_basis (Pi.basisFun k V) F
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy,smul_add]
  | smul r x hx ih => rw [map_smul,ih,smul_comm]

theorem row_homotopy_odd (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (hz : z∈Z) (he : e∈E) :
    totalFaceInvolute (TwoSimplex.Faces Z E)*(TwoSimplex.contraction (k := k) Z E hZE z e hz he).h+
      (TwoSimplex.contraction Z E hZE z e hz he).h*totalFaceInvolute (TwoSimplex.Faces Z E)=0 := by
  apply (totalFaceBasis (TwoSimplex.Faces Z E)).ext
  intro F
  let x := totalFaceBasis (k := k) (TwoSimplex.Faces Z E) F
  have hx : x ∈ totalFacePiece (TwoSimplex.Faces Z E) F.val.card := by
    change (totalFaceBasis (k := k) (TwoSimplex.Faces Z E) F).val ∈
      Chains (TwoSimplex.Faces Z E) F.val.card
    rw [totalFaceBasis_val]
    exact basis_mem F.property rfl
  have hh : (TwoSimplex.contraction Z E hZE z e hz he).h x∈
      totalFacePiece (TwoSimplex.Faces Z E) (F.val.card+1) :=
    TwoSimplex.homotopy_raises Z E hZE z e hz he F.val.card x.val hx
  change totalFaceInvolute _ ((TwoSimplex.contraction Z E hZE z e hz he).h x)+
    (TwoSimplex.contraction Z E hZE z e hz he).h (totalFaceInvolute _ x)=0
  rw [involute_on_piece _ _ _ hh,involute_on_piece _ _ _ hx,map_smul]
  rw [pow_succ,mul_neg_one]
  simpa only [neg_add_cancel,zero_smul] using!
    (add_smul (-((-1 : k)^F.val.card)) ((-1 : k)^F.val.card)
      ((TwoSimplex.contraction Z E hZE z e hz he).h x)).symm

section Good
variable (S : Fin m → V → Prop) (Z E : Fin m → Finset V)
  (hS : ∀p q,p≠q → ∀v,S p v → ¬S q v)
  (hZ : ∀p v,v∈Z p → S p v) (hE : ∀p v,v∈E p → S p v)
  (hZE : ∀p,Disjoint (Z p) (E p))
  (z e : Fin m → V) (hz : ∀p,z p∈Z p) (he : ∀p,e p∈E p)

include hZ hE in
theorem row_supported (p : Fin m) (F : Finset V)
    (hF : TwoSimplex.Faces (Z p) (E p) F) : ∀v∈F,S p v := by
  intro v hv
  rcases hF with hF | hF
  · exact hZ p v (hF hv)
  · exact hE p v (hF hv)

def tensorEquiv : (⨂[k] p,TotalFaceModule (k := k) (TwoSimplex.Faces (Z p) (E p))) ≃ₗ[k]
    TotalFaceModule (k := k) (Faces S Z E) :=
  finiteFaceTensorEquiv S (fun p => TwoSimplex.Faces (Z p) (E p)) hS
    (row_supported S Z E hZ hE)

def tensorContraction : LinearContraction (R := k)
    (M := ⨂[k] p,TotalFaceModule (k := k) (TwoSimplex.Faces (Z p) (E p)))
    (H := k) :=
  (LinearContraction.finiteTensor
    (fun p => TwoSimplex.contraction (Z p) (E p) (hZE p) (z p) (e p) (hz p) (he p))
    (fun p => totalFaceInvolute (TwoSimplex.Faces (Z p) (E p)))
    (fun p => totalFaceInvolute_square _)
    (fun p => by
      rw [TwoSimplex.contraction_d,← projected_eq_ideal]
      exact projectedTotalDifferential_anticommute _)
    (fun p => row_homotopy_odd (Z p) (E p) (hZE p) (z p) (e p) (hz p) (he p))).changeTarget
      (PiTensorProduct.constantBaseRingEquiv (Fin m) k).toLinearEquiv

/-- Strong contraction of the literal joined augmented face complex. -/
def contraction : LinearContraction (R := k)
    (M := TotalFaceModule (k := k) (Faces S Z E)) (H := k) :=
  (tensorContraction Z E hZE z e hz he).changeSource (tensorEquiv S Z E hS hZ hE)

theorem tensorContraction_d :
    (tensorContraction (k := k) Z E hZE z e hz he).d=
      finiteFaceTensorDifferential (fun p => TwoSimplex.Faces (Z p) (E p)) := by
  change TensorCycleSpanning.differential _ _=signedTensorDifferential _ _
  unfold TensorCycleSpanning.differential signedTensorDifferential
  congr 1
  funext p
  congr 1
  funext q
  simp only [TensorCycleSpanning.factor,signedTensorFactor,TwoSimplex.contraction_d,
    projected_eq_ideal (TwoSimplex.downward (Z q) (E q))]
  rfl

theorem contraction_d :
    (contraction (k := k) S Z E hS hZ hE hZE z e hz he).d=
      idealTotalDifferential (downward S Z E) := by
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := (tensorEquiv (k := k) S Z E hS hZ hE).surjective x
  change tensorEquiv S Z E hS hZ hE
    ((tensorContraction Z E hZE z e hz he).d
      ((tensorEquiv S Z E hS hZ hE).symm (tensorEquiv S Z E hS hZ hE y)))=_
  rw [LinearEquiv.symm_apply_apply,tensorContraction_d]
  have hc := LinearMap.congr_fun
    (finiteFaceTensorEquiv_is_chain (k := k) S (fun p => TwoSimplex.Faces (Z p) (E p)) hS
      (row_supported S Z E hZ hE)) y
  change projectedTotalDifferential (k := k) (Faces S Z E)
      (tensorEquiv S Z E hS hZ hE y)=
    tensorEquiv S Z E hS hZ hE
      ((finiteFaceTensorDifferential (fun p => TwoSimplex.Faces (Z p) (E p))) y) at hc
  rw [projected_eq_ideal (downward S Z E)] at hc
  exact hc.symm

/-- This common ambient row projection does not depend on the selected
vertices used for the contraction. -/
theorem projection_tensor (x : ∀p,TotalFaceModule (k := k) (TwoSimplex.Faces (Z p) (E p))) :
    (contraction S Z E hS hZ hE hZE z e hz he).projection
      (tensorEquiv S Z E hS hZ hE (⨂ₜ[k] p,x p))=
        ∏p,TwoSimplex.projectionAmbient (E p) (x p).val := by
  change PiTensorProduct.constantBaseRingEquiv (Fin m) k
    (PiTensorProduct.map (fun p => (TwoSimplex.contraction (Z p) (E p) (hZE p)
      (z p) (e p) (hz p) (he p)).projection)
        ((tensorEquiv S Z E hS hZ hE).symm (tensorEquiv S Z E hS hZ hE (⨂ₜ[k] p,x p))))=_
  rw [LinearEquiv.symm_apply_apply,PiTensorProduct.map_tprod]
  simp only [TwoSimplex.contraction_projection,PiTensorProduct.constantBaseRingEquiv_tprod]

end Good

section NaturalProjection
variable (S : Fin m → V → Prop) (Z E E' : Fin m → Finset V)
  (hS : ∀p q,p≠q → ∀v,S p v → ¬S q v)
  (hZ : ∀p v,v∈Z p → S p v) (hE : ∀p v,v∈E p → S p v)
  (hE' : ∀p v,v∈E' p → S p v)

def projection : TotalFaceModule (k := k) (Faces S Z E) →ₗ[k] k :=
  (PiTensorProduct.constantBaseRingEquiv (Fin m) k).toLinearMap.comp
    ((PiTensorProduct.map (fun p => (TwoSimplex.projectionAmbient (E p)).comp
      (TotalFaceModule (k := k) (TwoSimplex.Faces (Z p) (E p))).subtype)).comp
        (tensorEquiv S Z E hS hZ hE).symm.toLinearMap)

theorem projection_tprod
    (x : ∀p,TotalFaceModule (k := k) (TwoSimplex.Faces (Z p) (E p))) :
    projection S Z E hS hZ hE (tensorEquiv S Z E hS hZ hE (⨂ₜ[k] p,x p))=
      ∏p,TwoSimplex.projectionAmbient (E p) (x p).val := by
  simp only [projection,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply,PiTensorProduct.map_tprod,
    Submodule.subtype_apply]
  exact PiTensorProduct.constantBaseRingEquiv_tprod _

theorem good_projection (hZE : ∀p,Disjoint (Z p) (E p))
    (z e : Fin m → V) (hz : ∀p,z p∈Z p) (he : ∀p,e p∈E p) :
    (contraction (k := k) S Z E hS hZ hE hZE z e hz he).projection=
      projection S Z E hS hZ hE := by
  apply LinearMap.ext
  intro x
  rfl

def faceInclusion {P Q : Finset V → Prop} (h : ∀F,P F → Q F) :
    TotalFaceModule (k := k) P →ₗ[k] TotalFaceModule (k := k) Q :=
  Submodule.inclusion (Submodule.span_le.mpr (by
    rintro x ⟨F,hF,rfl⟩
    exact Submodule.subset_span ⟨F,h F hF,rfl⟩))

variable (hEE' : ∀p,E p⊆E' p)

def rowInclusion (p : Fin m) :
    TotalFaceModule (k := k) (TwoSimplex.Faces (Z p) (E p)) →ₗ[k]
      TotalFaceModule (k := k) (TwoSimplex.Faces (Z p) (E' p)) :=
  faceInclusion fun F hF => hF.imp id (fun h => h.trans (hEE' p))

def inclusion : TotalFaceModule (k := k) (Faces S Z E) →ₗ[k]
    TotalFaceModule (k := k) (Faces S Z E') :=
  faceInclusion fun F hF => ⟨hF.1,fun p => (hF.2 p).imp id (fun h => h.trans (hEE' p))⟩

theorem tensorEquiv_inclusion
    (x : ⨂[k] p,TotalFaceModule (k := k) (TwoSimplex.Faces (Z p) (E p))) :
    tensorEquiv S Z E' hS hZ hE' (PiTensorProduct.map (rowInclusion Z E E' hEE') x)=
      inclusion S Z E E' hEE' (tensorEquiv S Z E hS hZ hE x) := by
  have hm : (tensorEquiv (k := k) S Z E' hS hZ hE').toLinearMap.comp
      (PiTensorProduct.map (rowInclusion Z E E' hEE'))=
      (inclusion S Z E E' hEE').comp (tensorEquiv S Z E hS hZ hE).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro y
    apply Subtype.ext
    have h₁ := LinearMap.congr_fun (finiteFaceTensorEquiv_actual_product (k := k)
      S (fun p => TwoSimplex.Faces (Z p) (E' p)) hS (row_supported S Z E' hZ hE'))
        (⨂ₜ[k] p,rowInclusion Z E E' hEE' p (y p))
    have h₂ := LinearMap.congr_fun (finiteFaceTensorEquiv_actual_product (k := k)
      S (fun p => TwoSimplex.Faces (Z p) (E p)) hS (row_supported S Z E hZ hE))
        (⨂ₜ[k] p,y p)
    simpa only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,
      LinearEquiv.coe_coe,PiTensorProduct.map_tprod,tensorEquiv,
      Submodule.subtype_apply,finiteFaceProduct,PiTensorProduct.lift.tprod,
      MultilinearMap.compLinearMap_apply,MultilinearMap.mkPiAlgebraFin_apply,
      rowInclusion,inclusion,faceInclusion,Submodule.inclusion_apply] using! h₁.trans h₂.symm
  exact LinearMap.congr_fun hm x

/-- The same projection works for good-to-good and bad-to-good cover
inclusions; the latter case is why the one-block augmentation is used. -/
theorem projection_natural (hZE' : ∀p,Disjoint (Z p) (E' p)) :
    (projection (k := k) S Z E' hS hZ hE').comp (inclusion S Z E E' hEE')=
      projection S Z E hS hZ hE := by
  have hm : ((projection (k := k) S Z E' hS hZ hE').comp (inclusion S Z E E' hEE')).comp
      (tensorEquiv S Z E hS hZ hE).toLinearMap=
      (projection S Z E hS hZ hE).comp (tensorEquiv S Z E hS hZ hE).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,LinearEquiv.coe_coe]
    rw [← tensorEquiv_inclusion S Z E E' hS hZ hE hE' hEE',PiTensorProduct.map_tprod,
      projection_tprod,projection_tprod]
    apply Finset.prod_congr rfl
    intro p _
    exact TwoSimplex.projection_natural (Z p) (E p) (E' p) (hZE' p) (hEE' p)
      (x p).val (x p).property
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := (tensorEquiv (k := k) S Z E hS hZ hE).surjective x
  exact LinearMap.congr_fun hm y

theorem projection_zero_of_empty (a : Fin m) (ha : E a=∅) :
    projection (k := k) S Z E hS hZ hE=0 := by
  have hrow : TwoSimplex.projectionAmbient (k := k) (E a)=0 := by
    rw [ha]
    apply (basis (V := V) (k := k)).ext
    intro F
    simp [TwoSimplex.projectionAmbient,TwoSimplex.positiveSimplexPart_basis,
      Finset.subset_empty]
  have hm : (projection (k := k) S Z E hS hZ hE).comp
      (tensorEquiv S Z E hS hZ hE).toLinearMap=0 := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change projection S Z E hS hZ hE (tensorEquiv S Z E hS hZ hE (⨂ₜ[k] p,x p))=0
    rw [projection_tprod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by rw [hrow]; rfl)
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := (tensorEquiv (k := k) S Z E hS hZ hE).surjective x
  exact LinearMap.congr_fun hm y

end NaturalProjection

section Cone
variable (S : Fin m → V → Prop) (Z E : Fin m → Finset V)
  (hS : ∀p q,p≠q → ∀v,S p v → ¬S q v)
  (hZ : ∀p v,v∈Z p → S p v)
  (a : Fin m) (ha : E a=∅) (z : V) (hz : z∈Z a)

include hS hZ a ha hz in
theorem insert_vertex {F : Finset V} (hF : Faces S Z E F) : Faces S Z E (insert z F) := by
  refine ⟨?_,?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ⟨a,hZ a _ hz⟩
    · exact hF.1 v hv
  · intro p
    by_cases hpa : p=a
    · subst p
      have hFa : F.filter (S a)⊆Z a := by
        rcases hF.2 a with h | h
        · exact h
        · exact (Finset.subset_empty.mp (ha ▸ h)) ▸ Finset.empty_subset _
      left
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hv,hva⟩
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hz
      · exact hFa (Finset.mem_filter.mpr ⟨hv,hva⟩)
    · have hzp : ¬S p z := hS a p (Ne.symm hpa) z (hZ a z hz)
      simpa only [Finset.filter_insert,if_neg hzp] using hF.2 p

include hS hZ a ha hz in
theorem creation_mem (x : Ambient V k) (hx : x∈TotalFaceModule (Faces S Z E)) :
    creation z x∈TotalFaceModule (Faces S Z E) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hF,rfl⟩ := hx
      rw [creation_basis]
      split_ifs
      · exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (Submodule.subset_span
          ⟨insert z F,insert_vertex S Z E hS hZ a ha z hz hF,rfl⟩)
  | zero => simpa using Submodule.zero_mem (TotalFaceModule (k := k) (Faces S Z E))
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

/-- An empty one-block makes the literal join a cone, including its
augmentation in face-cardinality zero. -/
def zeroContraction : LinearContraction (R := k)
    (M := TotalFaceModule (k := k) (Faces S Z E)) (H := (⊥ : Submodule k k)) where
  d := idealTotalDifferential (downward S Z E)
  h := ((creation z).domRestrict (TotalFaceModule (Faces S Z E))).codRestrict _
    (fun x => creation_mem S Z E hS hZ a ha z hz x.val x.property)
  inclusion := 0
  projection := 0
  differential := LinearMap.ext fun x => Subtype.ext (boundary_boundary x.val)
  retract := Subsingleton.elim _ _
  inclusion_cycle := by simp
  projection_boundary := by simp
  homotopy := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change boundary (creation z x.val)+creation z (boundary x.val)=x.val-0
    rw [boundary_creation,sub_add_cancel,sub_zero]
  squareHomotopy := LinearMap.ext fun x => Subtype.ext (TwoSimplex.creation_square z x.val)
  homotopyInclusion := by simp
  projectionHomotopy := by simp

@[simp] theorem zeroContraction_d :
    (zeroContraction (k := k) S Z E hS hZ a ha z hz).d=
      idealTotalDifferential (downward S Z E) := rfl

end Cone
end FourPapers.Sublattice.JoinedTwoSimplex
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.JoinedTwoSimplexDegrees -/
section

/-! # Actual face-cardinality degrees of the incidence contraction -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Simplicial HomologicalPerturbation
open scoped TensorProduct
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

namespace TwoSimplex

theorem projection_basis_ne_one (E F : Finset V) (hF : F.card≠1) :
    projectionAmbient (k := k) E (basis F)=0 := by
  change -emptyCoefficient (boundary (positiveSimplexPart E (basis F)))=0
  rw [positiveSimplexPart_basis]
  split_ifs
  · rw [face_boundary_basis_sum,map_sum]
    have hz : ∀v : {v // v∈F},emptyCoefficient
        (TauCeti.ExteriorAlgebra.basisEraseSign v.val F • basis (F.erase v.val))=(0:k) := by
      intro v
      have hne : F.erase v.val≠∅ := by
        intro he
        have hc := Finset.card_erase_add_one v.property
        rw [he,Finset.card_empty,zero_add] at hc
        exact hF hc.symm
      simp only [Units.smul_def,map_zsmul,emptyCoefficient_basis,if_neg hne,zsmul_zero]
    rw [Finset.sum_eq_zero (fun v _ => hz v),neg_zero]
  · simp

theorem generator_degree (Z E : Finset V) (z e : V) (hz : z∈Z) (he : e∈E) :
    generator (k := k) z e∈Chains (Faces Z E) 1 := by
  exact Submodule.sub_mem _ (basis_mem (Or.inl (by simpa using hz)) (by simp))
    (basis_mem (Or.inr (by simpa using he)) (by simp))

theorem summandProjection_preserves (Z E : Finset V) (hZE : Disjoint Z E)
    (z e : V) (hz : z∈Z) (he : e∈E) (j : ℕ)
    (x : TotalFaceModule (k := k) (Faces Z E)) (hx : x∈totalFacePiece (Faces Z E) j) :
    (contraction Z E hZE z e hz he).summandProjection x∈totalFacePiece (Faces Z E) j := by
  rw [totalFacePiece_eq_basis_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hcard,rfl⟩ := hx
      change F.val.card = j at hcard
      change ((contraction (k := k) Z E hZE z e hz he).summandProjection
        (totalFaceBasis (k := k) (Faces Z E) F)).val∈Chains (k := k) (Faces Z E) j
      rw [LinearContraction.summandProjection_apply,contraction_inclusion_val,
        contraction_projection,totalFaceBasis_val]
      by_cases hj : j=1
      · rw [hj]
        exact Submodule.smul_mem _ _ (generator_degree (k := k) Z E z e hz he)
      · have hF : F.val.card≠1 := by simpa only [hcard] using hj
        rw [projection_basis_ne_one E F.val hF,zero_smul]
        exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

end TwoSimplex

namespace JoinedTwoSimplex
variable {m : ℕ}
  (S : Fin m → V → Prop) (Z E : Fin m → Finset V)
  (hS : ∀p q,p≠q → ∀v,S p v → ¬S q v)
  (hZ : ∀p v,v∈Z p → S p v) (hE : ∀p v,v∈E p → S p v)

abbrev Tensor := ⨂[k] p,TotalFaceModule (k := k) (TwoSimplex.Faces (Z p) (E p))

def tensorBasis : Module.Basis (∀p,{F : Finset V // TwoSimplex.Faces (Z p) (E p) F}) k
    (Tensor (k := k) Z E) := Basis.piTensorProduct fun p => totalFaceBasis _

def tensorPiece (j : ℕ) : Submodule k (Tensor (k := k) Z E) :=
  Submodule.span k (tensorBasis Z E '' {f | ∑p,(f p).val.card=j})

include hZ hE in
private theorem row_support (p : Fin m) (F : Finset V)
    (hF : TwoSimplex.Faces (Z p) (E p) F) : ∀v∈F,S p v := by
  intro v hv
  rcases hF with hF | hF
  · exact hZ p v (hF hv)
  · exact hE p v (hF hv)

include hS hZ hE in
theorem union_card (f : ∀p,{F : Finset V // TwoSimplex.Faces (Z p) (E p) F}) :
    (finiteFaceUnion fun p => (f p).val).card=∑p,(f p).val.card := by
  apply Finset.card_biUnion
  intro p hp q hq hpq
  apply Finset.disjoint_left.mpr
  intro v hvp hvq
  exact hS p q hpq v (row_support S Z E hZ hE p _ (f p).property v hvp)
    (row_support S Z E hZ hE q _ (f q).property v hvq)

theorem tprod_mem_piece (j : Fin m → ℕ)
    (x : ∀p,TotalFaceModule (k := k) (TwoSimplex.Faces (Z p) (E p)))
    (hx : ∀p,x p∈totalFacePiece (TwoSimplex.Faces (Z p) (E p)) (j p)) :
    (⨂ₜ[k] p,x p)∈tensorPiece Z E (∑p,j p) := by
  have hh := TensorCycleSpanning.multilinear_mem_span (PiTensorProduct.tprod k)
    (fun p => totalFaceBasis (k := k) (TwoSimplex.Faces (Z p) (E p)) ''
      {F | F.val.card=j p}) x (fun p => by
        simpa only [totalFacePiece_eq_basis_span] using hx p)
  apply Submodule.span_le.mpr ?_ hh
  rintro y ⟨a,ha,rfl⟩
  choose f hf heq using ha
  have hae : a=fun p => totalFaceBasis (TwoSimplex.Faces (Z p) (E p)) (f p) :=
    funext fun p => (heq p).symm
  rw [hae,← Basis.piTensorProduct_apply]
  exact Submodule.subset_span ⟨f,Finset.sum_congr rfl (fun p _ => hf p),rfl⟩

theorem equiv_preserves_piece (j : ℕ) (x : Tensor (k := k) Z E)
    (hx : x∈tensorPiece Z E j) :
    tensorEquiv S Z E hS hZ hE x∈totalFacePiece (Faces S Z E) j := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨f,hf,rfl⟩ := hx
      unfold tensorEquiv finiteFaceTensorEquiv tensorBasis
      erw [signedBasisEquiv_basis]
      apply Submodule.smul_mem
      change (totalFaceBasis (k := k)
        (separatedFamilyFaces S (fun p => TwoSimplex.Faces (Z p) (E p)))
          (finiteFaceIndexEquiv S _ hS (row_support S Z E hZ hE) f)).val∈
        Chains (k := k) (Faces S Z E) j
      rw [totalFaceBasis_val]
      exact basis_mem (finiteFaceIndexEquiv S _ hS (row_support S Z E hZ hE) f).property
        ((union_card S Z E hS hZ hE f).trans hf)
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

theorem equiv_symm_preserves_piece (j : ℕ)
    (x : TotalFaceModule (k := k) (Faces S Z E)) (hx : x∈totalFacePiece (Faces S Z E) j) :
    (tensorEquiv S Z E hS hZ hE).symm x∈tensorPiece Z E j := by
  rw [totalFacePiece_eq_basis_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hF,rfl⟩ := hx
      let f := (finiteFaceIndexEquiv S (fun p => TwoSimplex.Faces (Z p) (E p)) hS
        (row_support S Z E hZ hE)).symm F
      let ε := faceListSign _ (finiteFamily_faces_pairwise S _ hS
        (row_support S Z E hZ hE) f)
      have he : tensorEquiv (k := k) S Z E hS hZ hE (tensorBasis Z E f)=
          ε • totalFaceBasis (k := k) (Faces S Z E) F := by
        unfold tensorEquiv finiteFaceTensorEquiv tensorBasis
        erw [signedBasisEquiv_basis]
        simp only [f,Equiv.apply_symm_apply]
        rfl
      have hs : (tensorEquiv (k := k) S Z E hS hZ hE).symm (totalFaceBasis (k := k) (Faces S Z E) F)=
          ε⁻¹ • tensorBasis Z E f := by
        apply (tensorEquiv S Z E hS hZ hE).injective
        rw [LinearEquiv.apply_symm_apply,map_zsmul_unit,he,smul_smul,inv_mul_cancel,one_smul]
      rw [hs]
      apply Submodule.smul_mem
      refine Submodule.subset_span ⟨f,?_,rfl⟩
      change (∑ p,(f p).val.card)=j
      rw [← union_card S Z E hS hZ hE]
      have hff := congrArg Subtype.val
        ((finiteFaceIndexEquiv S _ hS (row_support S Z E hZ hE)).apply_symm_apply F)
      exact (congrArg Finset.card hff).trans hF
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

theorem projection_zero_off_degree (j : ℕ) (hj : j≠m)
    (x : TotalFaceModule (k := k) (Faces S Z E)) (hx : x∈totalFacePiece (Faces S Z E) j) :
    projection S Z E hS hZ hE x=0 := by
  have hy := equiv_symm_preserves_piece S Z E hS hZ hE j x hx
  have hh : ∀ y : Tensor (k := k) Z E,y∈tensorPiece Z E j → projection S Z E hS hZ hE
      (tensorEquiv S Z E hS hZ hE y)=0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨f,hf,rfl⟩ := hy
        have hn : ¬∀p,(f p).val.card=1 := by
          intro h
          apply hj
          simpa only [h,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
            using hf.symm
        obtain ⟨a,ha⟩ := not_forall.mp hn
        have hp := projection_tprod (k := k) S Z E hS hZ hE
          (fun p => totalFaceBasis (k := k) (TwoSimplex.Faces (Z p) (E p)) (f p))
        have hz : (∏ p,TwoSimplex.projectionAmbient (k := k) (E p)
            (totalFaceBasis (k := k) (TwoSimplex.Faces (Z p) (E p)) (f p)).val)=0 := by
          apply Finset.prod_eq_zero (Finset.mem_univ a)
          rw [totalFaceBasis_val]
          exact TwoSimplex.projection_basis_ne_one (k := k) (E a) (f a).val ha
        simpa only [tensorBasis,Basis.piTensorProduct_apply] using hp.trans hz
    | zero => simp
    | add y z hy hz ihy ihz => rw [map_add,map_add,ihy,ihz,add_zero]
    | smul r y hy ih => rw [map_smul,map_smul,ih,smul_zero]
  simpa only [LinearEquiv.apply_symm_apply] using hh _ hy

variable (hZE : ∀p,Disjoint (Z p) (E p))
  (z e : Fin m → V) (hz : ∀p,z p∈Z p) (he : ∀p,e p∈E p)

theorem tensor_homotopy_raises (j : ℕ) (x : Tensor (k := k) Z E) (hx : x∈tensorPiece Z E j) :
    (tensorContraction Z E hZE z e hz he).h x∈tensorPiece Z E (j+1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨f,hf,rfl⟩ := hx
      change (LinearContraction.finiteTensor
        (fun p => TwoSimplex.contraction (k := k) (Z p) (E p) (hZE p)
          (z p) (e p) (hz p) (he p))
        (fun p => totalFaceInvolute (k := k) (TwoSimplex.Faces (Z p) (E p)))
        (fun p => totalFaceInvolute_square _)
        (fun p => by
          rw [TwoSimplex.contraction_d,← projected_eq_ideal]
          exact projectedTotalDifferential_anticommute _)
        (fun p => row_homotopy_odd (Z p) (E p) (hZE p)
          (z p) (e p) (hz p) (he p))).h (tensorBasis Z E f)∈_
      rw [LinearContraction.finiteTensor_h,LinearMap.sum_apply]
      apply Submodule.sum_mem
      intro p _
      rw [tensorBasis,Basis.piTensorProduct_apply,PiTensorProduct.map_tprod]
      let a : Fin m → ℕ := fun q => (f q).val.card+if q=p then 1 else 0
      have ha : ∑q,a q=j+1 := by
        change (∑ q,(f q).val.card)=j at hf
        simp only [a,Finset.sum_add_distrib,hf,Finset.sum_ite_eq',Finset.mem_univ,if_true]
      rw [← ha]
      apply tprod_mem_piece
      intro q
      have hq : totalFaceBasis (k := k) (TwoSimplex.Faces (Z q) (E q)) (f q) ∈
          totalFacePiece (TwoSimplex.Faces (Z q) (E q)) (f q).val.card := by
        change (totalFaceBasis (k := k) (TwoSimplex.Faces (Z q) (E q)) (f q)).val ∈
          Chains (TwoSimplex.Faces (Z q) (E q)) (f q).val.card
        rw [totalFaceBasis_val]
        exact basis_mem (f q).property rfl
      by_cases hqp : q<p
      · simp only [if_pos hqp,Module.End.mul_apply,a,if_neg (ne_of_lt hqp),add_zero]
        have hproj := TwoSimplex.summandProjection_preserves (Z q) (E q) (hZE q)
          (z q) (e q) (hz q) (he q) (f q).val.card _ hq
        rw [involute_on_piece _ _ _ hproj]
        exact Submodule.smul_mem _ _ hproj
      · by_cases heq : q=p
        · subst q
          simp only [lt_self_iff_false,if_false,if_pos rfl,a,add_zero]
          exact TwoSimplex.homotopy_raises (Z p) (E p) (hZE p) (z p) (e p)
            (hz p) (he p) (f p).val.card _ hq
        · simpa only [if_neg hqp,if_neg heq,Module.End.one_apply,a,add_zero] using hq
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

theorem homotopy_raises (j : ℕ) (x : TotalFaceModule (k := k) (Faces S Z E))
    (hx : x∈totalFacePiece (Faces S Z E) j) :
    (contraction S Z E hS hZ hE hZE z e hz he).h x∈totalFacePiece (Faces S Z E) (j+1) :=
  equiv_preserves_piece S Z E hS hZ hE (j+1) _
    (tensor_homotopy_raises Z E hZE z e hz he j _
      (equiv_symm_preserves_piece S Z E hS hZ hE j x hx))

theorem inclusion_degree (r : k) :
    (contraction S Z E hS hZ hE hZE z e hz he).inclusion r∈totalFacePiece (Faces S Z E) m := by
  have h1 : (contraction (k := k) S Z E hS hZ hE hZE z e hz he).inclusion 1∈
      totalFacePiece (Faces S Z E) m := by
    change tensorEquiv S Z E hS hZ hE
      (PiTensorProduct.map (fun p => (TwoSimplex.contraction (Z p) (E p) (hZE p)
        (z p) (e p) (hz p) (he p)).inclusion)
          ((PiTensorProduct.constantBaseRingEquiv (Fin m) k).symm 1))∈_
    have he1 : (PiTensorProduct.constantBaseRingEquiv (Fin m) k).symm 1=
        ⨂ₜ[k] _ : Fin m,(1:k) := by
      apply (PiTensorProduct.constantBaseRingEquiv (Fin m) k).injective
      simp
    rw [he1,PiTensorProduct.map_tprod]
    apply equiv_preserves_piece S Z E hS hZ hE
    convert tprod_mem_piece Z E (fun _ => 1) _ (fun p => ?_) using 1 <;> try simp
    change (1:k) • TwoSimplex.generator (z p) (e p)∈Chains (TwoSimplex.Faces (Z p) (E p)) 1
    simpa only [one_smul] using
      TwoSimplex.generator_degree (k := k) (Z p) (E p) (z p) (e p) (hz p) (he p)
  have hr : (contraction (k := k) S Z E hS hZ hE hZE z e hz he).inclusion r =
      r • (contraction (k := k) S Z E hS hZ hE hZE z e hz he).inclusion 1 := by
    simpa only [smul_eq_mul,mul_one] using
      (contraction (k := k) S Z E hS hZ hE hZE z e hz he).inclusion.map_smul r (1 : k)
  rw [hr]
  exact Submodule.smul_mem (totalFacePiece (Faces S Z E) m) r h1

end JoinedTwoSimplex
end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FaceParity -/
section

set_option autoImplicit false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma faceInvolute_basis (F : Finset V) :
    CliffordAlgebra.involute (Simplicial.basis (k := k) F) =
      (-1 : k)^F.card • Simplicial.basis F := by
  simpa only [Simplicial.basis] using
    TauCeti.ExteriorAlgebra.involute_basis (Pi.basisFun k V) F

/-- The actual projected exterior differential anticommutes with the actual
parity involution. No restriction on characteristic or on the face predicate. -/
lemma projectedTotalDifferential_parity (P : Finset V → Prop) :
    projectedTotalDifferential (k := k) P * totalFaceInvolute P =
      -(totalFaceInvolute P * projectedTotalDifferential P) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change faceProjection P (Simplicial.boundary (CliffordAlgebra.involute x.val)) =
    -CliffordAlgebra.involute (faceProjection P (Simplicial.boundary x.val))
  have h := CliffordAlgebra.involute_contractLeft
    (Fintype.linearCombination k (fun _ : V => (1 : k))) x.val
  have hb : Simplicial.boundary (CliffordAlgebra.involute x.val) =
      -CliffordAlgebra.involute (Simplicial.boundary x.val) := by
    simpa only [neg_neg] using (congrArg (fun z => -z) h).symm
  rw [hb,map_neg,faceProjection_involute]


end FourPapers.Sublattice

end
end

/- BEGIN EXACT BODY: FourPapers.Common.CechFaceComplex -/
section

/-!
# The augmented Čech cone on an actual finite face cover

The indices are pairs (Q,F), including the empty cover index Q. The face F
belongs to every selected cover member. Both differentials are restrictions
of the genuine tensor-exterior differentials. The first removes a cover
index; the second removes a vertex, with the usual sign (-1)^|Q|. Thus the
total differential is checked before any homological reduction is made.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.CechFace
open Classical CommAlg FourPapers.Sublattice
open scoped TensorProduct DirectSum
universe u
variable {k V R : Type u} [CommRing k] [Fintype V] [LinearOrder V]
  [Fintype R] [LinearOrder R]

abbrev Ambient := Simplicial.Ambient R k ⊗[k] Simplicial.Ambient V k

def ambientBasis : Module.Basis (Finset R × Finset V) k (Ambient (k:=k) (V:=V) (R:=R)) :=
  (Simplicial.basis (V:=R) (k:=k)).tensorProduct (Simplicial.basis (V:=V) (k:=k))

def ambientHorizontal : Module.End k (Ambient (k:=k) (V:=V) (R:=R)) :=
  Simplicial.boundary.rTensor (Simplicial.Ambient V k)

def ambientVertical : Module.End k (Ambient (k:=k) (V:=V) (R:=R)) :=
  TensorProduct.map CliffordAlgebra.involute.toLinearMap Simplicial.boundary

theorem ambientHorizontal_square :
    ambientHorizontal (k:=k) (V:=V) (R:=R)*ambientHorizontal=0 := by
  apply TensorProduct.ext'
  intro x y
  change Simplicial.boundary (Simplicial.boundary x) ⊗ₜ[k] y=0
  rw [Simplicial.boundary_boundary,TensorProduct.zero_tmul]

theorem ambientVertical_square :
    ambientVertical (k:=k) (V:=V) (R:=R)*ambientVertical=0 := by
  apply TensorProduct.ext'
  intro x y
  change CliffordAlgebra.involute (CliffordAlgebra.involute x) ⊗ₜ[k]
    Simplicial.boundary (Simplicial.boundary y)=0
  rw [Simplicial.boundary_boundary,TensorProduct.tmul_zero]

theorem ambient_anticommute :
    ambientHorizontal (k:=k) (V:=V) (R:=R)*ambientVertical+
      ambientVertical*ambientHorizontal=0 := by
  apply TensorProduct.ext'
  intro x y
  change Simplicial.boundary (CliffordAlgebra.involute x) ⊗ₜ[k] Simplicial.boundary y+
    CliffordAlgebra.involute (Simplicial.boundary x) ⊗ₜ[k] Simplicial.boundary y=0
  have he : Simplicial.boundary (CliffordAlgebra.involute x)=
      -CliffordAlgebra.involute (Simplicial.boundary x) := by
    have h := CliffordAlgebra.involute_contractLeft
      (Fintype.linearCombination k (fun _ : R => (1:k))) x
    simpa only [neg_neg] using (congrArg (fun z => -z) h).symm
  rw [he,TensorProduct.neg_tmul,neg_add_cancel]

theorem ambientDifferential_square :
    (ambientHorizontal (k:=k) (V:=V) (R:=R)+ambientVertical)*
      (ambientHorizontal+ambientVertical)=0 := by
  calc
    _=ambientHorizontal*ambientHorizontal+
      (ambientHorizontal*ambientVertical+ambientVertical*ambientHorizontal)+
        ambientVertical*ambientVertical := by noncomm_ring
    _=0 := by rw [ambientHorizontal_square,ambientVertical_square,ambient_anticommute]; simp

theorem ambientHorizontal_basis (Q : Finset R) (F : Finset V) :
    ambientHorizontal (ambientBasis (k:=k) (Q,F))=
      ∑ r : {r // r∈Q},TauCeti.ExteriorAlgebra.basisEraseSign r.val Q •
        ambientBasis (Q.erase r.val,F) := by
  simp only [ambientHorizontal,ambientBasis,Module.Basis.tensorProduct_apply,
    LinearMap.rTensor_tmul,face_boundary_basis_sum,TensorProduct.sum_tmul,
    TensorProduct.smul_tmul']

theorem ambientVertical_basis (Q : Finset R) (F : Finset V) :
    ambientVertical (ambientBasis (k:=k) (Q,F))=
      (-1:k)^Q.card •
        ∑ v : {v // v∈F},TauCeti.ExteriorAlgebra.basisEraseSign v.val F •
          ambientBasis (Q,F.erase v.val) := by
  simp only [ambientVertical,ambientBasis,Module.Basis.tensorProduct_apply,
    TensorProduct.map_tmul,AlgHom.toLinearMap_apply,faceInvolute_basis,
    face_boundary_basis_sum,TensorProduct.smul_tmul',TensorProduct.tmul_sum,
    TensorProduct.tmul_smul]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [TensorProduct.smul_tmul']
  congr 1
  exact smul_comm _ _ _

variable (B : Finset V → Prop) (U : R → Finset V)

/-- U r is the set of vertices omitted by cover member r. -/
def intersectionFaces (Q : Finset R) (F : Finset V) : Prop :=
  B F ∧ ∀ r∈Q,Disjoint F (U r)

def pairFaces (a : Finset R × Finset V) : Prop := intersectionFaces B U a.1 a.2

def totalModule : Submodule k (Ambient (k:=k) (V:=V) (R:=R)) :=
  Submodule.span k (ambientBasis '' {a | pairFaces B U a})

def totalBasis : Module.Basis {a : Finset R × Finset V // pairFaces B U a} k
    (totalModule (k:=k) B U) := Grading.restrictedBasis ambientBasis (pairFaces B U)

@[simp] theorem totalBasis_val (a : {a : Finset R × Finset V // pairFaces B U a}) :
    (totalBasis (k:=k) B U a).val=ambientBasis a.val := Grading.restrictedBasis_val _ _ _

theorem intersectionFaces_antitone {P Q : Finset R} (hPQ : P⊆Q)
    {F : Finset V} (hF : intersectionFaces B U Q F) : intersectionFaces B U P F :=
  ⟨hF.1,fun r hr => hF.2 r (hPQ hr)⟩

theorem intersectionFaces_downward (hB : Simplicial.Downward B) (Q : Finset R) :
    Simplicial.Downward (intersectionFaces B U Q) := by
  intro F G hGF hF
  exact ⟨hB hGF hF.1,fun r hr => (hF.2 r hr).mono_left hGF⟩

theorem horizontal_mem {z : Ambient (k:=k) (V:=V) (R:=R)} (hz : z∈totalModule B U) :
    ambientHorizontal z∈totalModule B U := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨Q,F⟩,hF,rfl⟩ := hz
      rw [ambientHorizontal_basis]
      apply Submodule.sum_mem
      intro r _
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨(Q.erase r.val,F),
        intersectionFaces_antitone B U (Finset.erase_subset _ _) hF,rfl⟩
  | zero => simpa only [map_zero] using (totalModule (k:=k) B U).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

theorem vertical_mem (hB : Simplicial.Downward B)
    {z : Ambient (k:=k) (V:=V) (R:=R)} (hz : z∈totalModule B U) :
    ambientVertical z∈totalModule B U := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨⟨Q,F⟩,hF,rfl⟩ := hz
      rw [ambientVertical_basis]
      apply Submodule.smul_mem
      apply Submodule.sum_mem
      intro v _
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨(Q,F.erase v.val),
        intersectionFaces_downward B U hB Q (Finset.erase_subset _ _) hF,rfl⟩
  | zero => simpa only [map_zero] using (totalModule (k:=k) B U).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

def horizontal : Module.End k (totalModule (k:=k) B U) :=
  (ambientHorizontal.domRestrict (totalModule B U)).codRestrict _
    (fun z => horizontal_mem B U z.property)

def vertical (hB : Simplicial.Downward B) : Module.End k (totalModule (k:=k) B U) :=
  (ambientVertical.domRestrict (totalModule B U)).codRestrict _
    (fun z => vertical_mem B U hB z.property)

theorem differential_square (hB : Simplicial.Downward B) :
    (horizontal (k:=k) B U+vertical B U hB)*(horizontal B U+vertical B U hB)=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun (ambientDifferential_square (k:=k) (V:=V) (R:=R)) z.val

def blockIndexEquiv : {a : Finset R × Finset V // pairFaces B U a} ≃
    Σ Q : Finset R,{F : Finset V // intersectionFaces B U Q F} where
  toFun a := ⟨a.val.1,a.val.2,a.property⟩
  invFun a := ⟨(a.1,a.2.val),a.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The genuine Čech tensor module is the finite direct sum of the
actual intersection chain modules, with no homology substitution. -/
def blockEquiv : totalModule (k:=k) B U ≃ₗ[k]
    (⨁ Q : Finset R,TotalFaceModule (k:=k) (intersectionFaces B U Q)) :=
  (totalBasis B U).equiv
    (DFinsupp.basis (fun Q : Finset R => totalFaceBasis (intersectionFaces B U Q)))
    (blockIndexEquiv B U)

@[simp] theorem blockEquiv_basis (Q : Finset R)
    (F : {F : Finset V // intersectionFaces B U Q F}) :
    blockEquiv (k:=k) B U (totalBasis B U ⟨(Q,F.val),F.property⟩)=
      DirectSum.lof k (Finset R) (fun Q => TotalFaceModule (intersectionFaces B U Q)) Q
        (totalFaceBasis (intersectionFaces B U Q) F) := by
  calc
    _ = (DFinsupp.basis (fun Q : Finset R =>
        totalFaceBasis (k := k) (intersectionFaces B U Q))) ⟨Q,F⟩ :=
      Module.Basis.equiv_apply
        (b := totalBasis (k := k) B U)
        (b' := DFinsupp.basis (fun Q : Finset R =>
          totalFaceBasis (k := k) (intersectionFaces B U Q)))
        (e := blockIndexEquiv B U) (i := ⟨(Q,F.val),F.property⟩)
    _ = _ := FourPapers.directSum_basis_apply
      (fun Q : Finset R => totalFaceBasis (k := k) (intersectionFaces B U Q)) Q F

theorem blockEquiv_symm_lof_val (Q : Finset R)
    (z : TotalFaceModule (k:=k) (intersectionFaces B U Q)) :
    ((blockEquiv B U).symm
      (DirectSum.lof k (Finset R) (fun Q => TotalFaceModule (intersectionFaces B U Q)) Q z)).val=
        Simplicial.basis Q ⊗ₜ[k] z.val := by
  have he : (totalModule (k:=k) B U).subtype.comp
      ((blockEquiv B U).symm.toLinearMap.comp
        (DirectSum.lof k (Finset R) (fun Q => TotalFaceModule (intersectionFaces B U Q)) Q))=
      (TensorProduct.mk k (Simplicial.Ambient R k) (Simplicial.Ambient V k)
        (Simplicial.basis Q)).comp (TotalFaceModule (k:=k) (intersectionFaces B U Q)).subtype := by
    apply (totalFaceBasis (k:=k) (intersectionFaces B U Q)).ext
    intro F
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,Submodule.subtype_apply]
    rw [← blockEquiv_basis (k := k) B U Q F,
      LinearEquiv.symm_apply_apply,totalBasis_val,totalFaceBasis_val]
    simp only [ambientBasis,Module.Basis.tensorProduct_apply,TensorProduct.mk_apply]
  exact LinearMap.congr_fun he z

end FourPapers.CechFace

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.CechBlockTransfer -/
section

/-!
# Finite Čech transfer on the genuine intersection chain modules

The perturbation decreases the cardinality of the cover index. Every
intersection homotopy preserves that index. This constructs the inverse
operators in the perturbation lemma by a finite triangular argument.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.CechFace
open Classical CommAlg FourPapers.Sublattice HomologicalPerturbation
open scoped TensorProduct DirectSum
universe u
variable {k V R : Type u} [CommRing k] [Fintype V] [LinearOrder V]
  [Fintype R] [LinearOrder R]
  (B : Finset V → Prop) (U : R → Finset V)

abbrev BlockModule := ⨁ Q : Finset R,TotalFaceModule (k:=k) (intersectionFaces B U Q)

def blockBasis : Module.Basis (Σ Q : Finset R,{F : Finset V // intersectionFaces B U Q F})
    k (BlockModule (k:=k) B U) :=
  DFinsupp.basis (fun Q : Finset R => totalFaceBasis (intersectionFaces B U Q))

def blockHorizontal : Module.End k (BlockModule (k:=k) B U) :=
  (blockEquiv B U).toLinearMap.comp
    ((horizontal B U).comp (blockEquiv B U).symm.toLinearMap)

def eraseCoverIndex
    (a : Σ Q : Finset R,{F : Finset V // intersectionFaces B U Q F})
    (r : {r // r∈a.1}) :
    Σ Q : Finset R,{F : Finset V // intersectionFaces B U Q F} :=
  ⟨a.1.erase r.val,a.2.val,
    intersectionFaces_antitone B U (Finset.erase_subset _ _) a.2.property⟩

theorem blockHorizontal_basis
    (a : Σ Q : Finset R,{F : Finset V // intersectionFaces B U Q F}) :
    blockHorizontal (k:=k) B U (blockBasis B U a)=
      ∑ r : {r // r∈a.1},TauCeti.ExteriorAlgebra.basisEraseSign r.val a.1 •
        blockBasis B U (eraseCoverIndex B U a r) := by
  have he : (blockEquiv (k:=k) B U).symm (blockBasis B U a)=
      totalBasis B U ⟨(a.1,a.2.val),a.2.property⟩ := by
    apply (blockEquiv B U).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (Module.Basis.equiv_apply
      (b := totalBasis (k := k) B U) (b' := blockBasis (k := k) B U)
      (e := blockIndexEquiv B U) (i := ⟨(a.1,a.2.val),a.2.property⟩)).symm
  change blockEquiv B U (horizontal B U ((blockEquiv B U).symm (blockBasis B U a)))=_
  rw [he]
  have hd : horizontal (k:=k) B U (totalBasis B U ⟨(a.1,a.2.val),a.2.property⟩)=
      ∑ r : {r // r∈a.1},TauCeti.ExteriorAlgebra.basisEraseSign r.val a.1 •
        totalBasis B U ⟨((eraseCoverIndex B U a r).1,(eraseCoverIndex B U a r).2.val),
          (eraseCoverIndex B U a r).2.property⟩ := by
    apply Subtype.ext
    simp only [horizontal,LinearMap.codRestrict_apply,LinearMap.domRestrict_apply,
      totalBasis_val,Submodule.coe_sum,Submodule.coe_smul_of_tower]
    exact ambientHorizontal_basis a.1 a.2.val
  rw [hd,map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_zsmul_unit]
  congr 1
  exact Module.Basis.equiv_apply
    (b := totalBasis (k := k) B U) (b' := blockBasis (k := k) B U)
    (e := blockIndexEquiv B U)
    (i := ⟨((eraseCoverIndex B U a r).1,(eraseCoverIndex B U a r).2.val),
      (eraseCoverIndex B U a r).2.property⟩)

theorem blockHorizontal_decreases :
    DegreeDecreasing (blockBasis (k:=k) B U) (fun a => a.1.card) (blockHorizontal B U) := by
  apply degreeDecreasing_of_mem_span
  intro a
  rw [blockHorizontal_basis]
  apply Submodule.sum_mem
  intro r _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨eraseCoverIndex B U a r,
    Finset.card_erase_lt_of_mem r.property,rfl⟩

section Contractions
variable {H : Finset R → Type u}
  [∀Q,AddCommGroup (H Q)] [∀Q,Module k (H Q)]
  (C : ∀Q,LinearContraction (R:=k)
    (M:=TotalFaceModule (k:=k) (intersectionFaces B U Q)) (H:=H Q))

/-- Multiply both the differential and homotopy by the same square root
of one. This gives the exact Čech tensor sign without changing projection. -/
def signedBlockContraction (Q : Finset R) : LinearContraction (R:=k)
    (M:=TotalFaceModule (k:=k) (intersectionFaces B U Q)) (H:=H Q) :=
  if Even Q.card then C Q else (C Q).negDifferential

theorem signedBlockContraction_d (Q : Finset R) :
    (signedBlockContraction B U C Q).d=(-1:k)^Q.card • (C Q).d := by
  unfold signedBlockContraction
  split_ifs with he
  · rw [Even.neg_one_pow he,one_smul]
  · rw [Odd.neg_one_pow (Nat.not_even_iff_odd.mp he)]
    change -(C Q).d=(-1:k) • (C Q).d
    exact (neg_one_smul k (C Q).d).symm

def intersectionContraction : LinearContraction (R:=k)
    (M:=BlockModule (k:=k) B U) (H:=⨁Q,H Q) :=
  LinearContraction.directSum (signedBlockContraction B U C)

theorem intersectionHomotopy_nonincreasing :
    DegreeNonincreasing (blockBasis (k:=k) B U) (fun a => a.1.card)
      (intersectionContraction B U C).h := by
  intro a b hab
  change a.1.card < b.1.card at hab
  have hne : a.1≠b.1 := by
    intro h
    rw [h] at hab
    exact Nat.lt_irrefl _ hab
  rw [show blockBasis (k:=k) B U a=
      DirectSum.lof k (Finset R) (fun Q => TotalFaceModule (intersectionFaces B U Q))
        a.1 (totalFaceBasis (intersectionFaces B U a.1) a.2) from
      FourPapers.directSum_basis_apply _ _ _,
    intersectionContraction,LinearContraction.directSum_h_lof]
  change (totalFaceBasis (intersectionFaces B U b.1)).repr
    ((DirectSum.lof k (Finset R)
      (fun Q => TotalFaceModule (intersectionFaces B U Q)) a.1
        ((signedBlockContraction B U C a.1).h
          (totalFaceBasis (intersectionFaces B U a.1) a.2))) b.1) b.2=0
  simp only [DirectSum.lof_eq_of,DirectSum.of_eq_of_ne _ _ _ (Ne.symm hne),
    map_zero,Finsupp.zero_apply]

variable (hB : Simplicial.Downward B)
  (hd : ∀Q,(C Q).d=idealTotalDifferential (intersectionFaces_downward B U hB Q))

include hd in
theorem intersectionDifferential_actual (z : totalModule (k:=k) B U) :
    (intersectionContraction B U C).d (blockEquiv B U z)=
      blockEquiv B U (vertical B U hB z) := by
  have he : (intersectionContraction B U C).d.comp (blockEquiv B U).toLinearMap=
      (blockEquiv B U).toLinearMap.comp (vertical B U hB) := by
    apply (totalBasis (k:=k) B U).ext
    intro a
    rcases a with ⟨⟨Q,F⟩,hF⟩
    change (intersectionContraction (k := k) B U C).d
        (blockEquiv (k := k) B U (totalBasis (k := k) B U ⟨(Q,F),hF⟩))=
      blockEquiv (k := k) B U
        (vertical (k := k) B U hB (totalBasis (k := k) B U ⟨(Q,F),hF⟩))
    rw [blockEquiv_basis (k := k) B U Q ⟨F,hF⟩]
    simp only [intersectionContraction,LinearContraction.directSum_d_lof,
      signedBlockContraction_d,hd,LinearMap.smul_apply,map_smul]
    apply (blockEquiv B U).symm.injective
    rw [LinearEquiv.symm_apply_apply,map_smul]
    apply Subtype.ext
    rw [Submodule.coe_smul,blockEquiv_symm_lof_val,idealTotalDifferential_val,
      totalFaceBasis_val]
    simp only [vertical,LinearMap.codRestrict_apply,LinearMap.domRestrict_apply,totalBasis_val]
    change (-1:k)^Q.card • (Simplicial.basis Q ⊗ₜ[k]
      Simplicial.boundary (Simplicial.basis F))=
        ambientVertical (ambientBasis (k:=k) (Q,F))
    simp only [ambientVertical,ambientBasis,Module.Basis.tensorProduct_apply,
      TensorProduct.map_tmul,AlgHom.toLinearMap_apply,faceInvolute_basis,
      TensorProduct.smul_tmul']
  exact LinearMap.congr_fun he z

include hB hd in
theorem perturbed_square :
    ((intersectionContraction B U C).d+blockHorizontal B U)*
      ((intersectionContraction B U C).d+blockHorizontal B U)=0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨x,rfl⟩ := (blockEquiv (k:=k) B U).surjective z
  have hc (x : totalModule (k:=k) B U) :
      (((intersectionContraction (k := k) B U C).d+blockHorizontal (k := k) B U :
        Module.End k (BlockModule (k := k) B U))) (blockEquiv (k := k) B U x)=
        blockEquiv (k := k) B U
          ((vertical (k := k) B U hB+horizontal (k := k) B U :
            Module.End k (totalModule (k := k) B U)) x) := by
    simp only [LinearMap.add_apply,intersectionDifferential_actual B U C hB hd,
      blockHorizontal,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply,map_add]
  have hsquare : (horizontal (k := k) B U+vertical (k := k) B U hB :
      Module.End k (totalModule (k := k) B U))
      ((horizontal (k := k) B U+vertical (k := k) B U hB :
        Module.End k (totalModule (k := k) B U)) x)=0 :=
    LinearMap.congr_fun (differential_square (k := k) B U hB) x
  change ((intersectionContraction (k := k) B U C).d+blockHorizontal (k := k) B U :
      Module.End k (BlockModule (k := k) B U))
    (((intersectionContraction (k := k) B U C).d+blockHorizontal (k := k) B U :
      Module.End k (BlockModule (k := k) B U)) (blockEquiv (k := k) B U x))=0
  rw [hc,hc,add_comm (vertical (k := k) B U hB) (horizontal (k := k) B U),hsquare,map_zero]

/-- The actual finite inverse construction, rather than an assumed
degeneration of a spectral sequence, produces the Čech deformation retract. -/
def transferred : LinearDeformationRetract (R:=k)
    (M:=BlockModule (k:=k) B U) (H:=⨁Q,H Q) :=
  (intersectionContraction B U C).perturbByDegree (blockBasis B U) (fun a => a.1.card)
    (blockHorizontal B U) (blockHorizontal_decreases B U)
    (intersectionHomotopy_nonincreasing B U C) (perturbed_square B U C hB hd)

end Contractions
end FourPapers.CechFace

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.CechNerveReduction -/
section

/-! # Natural intersection contractions give the actual nerve differential

The projection on every intersection is an actual coefficient in a
zero-or-one submodule of the base ring. Its compatibility with cover
inclusions identifies the transferred differential exactly with the
augmented nerve boundary. No collapse or comparison is assumed.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.CechFace.NerveReduction
open Classical CommAlg FourPapers.Sublattice HomologicalPerturbation
open scoped DirectSum
universe u
variable {k V R : Type u} [CommRing k] [Fintype V] [LinearOrder V]
  [Fintype R] [LinearOrder R]
  (B : Finset V → Prop) (U : R → Finset V) (K : Finset R → Prop)

def intersectionInclusion (P Q : Finset R) (hPQ : P⊆Q) :
    TotalFaceModule (k := k) (intersectionFaces B U Q) →ₗ[k]
      TotalFaceModule (k := k) (intersectionFaces B U P) :=
  Submodule.inclusion (Submodule.span_le.mpr (by
    rintro x ⟨F,hF,rfl⟩
    exact Submodule.subset_span ⟨F,intersectionFaces_antitone B U hPQ hF,rfl⟩))

abbrev Lines := ⨁Q : Finset R,CoefficientLineSum.line (k := k) K Q

def targetEquiv : Lines (k := k) K ≃ₗ[k] TotalFaceModule (k := k) K :=
  (CoefficientLineSum.equivalence K).trans (totalFaceBasis K).repr.symm

/-- This ambient formula also covers a bad nerve face: its coefficient
line is zero, so both sides are zero. -/
theorem targetEquiv_lof_val (Q : Finset R) (r : CoefficientLineSum.line (k := k) K Q) :
    (targetEquiv K (DirectSum.lof k (Finset R) (fun Q => ↥(CoefficientLineSum.line (k := k) K Q)) Q r)).val=
      r.val • Simplicial.basis Q := by
  -- Evaluate coordinates with the concrete decision instance on finite sets.
  have hcoord : CoefficientLineSum.equivalence (k := k) K
      (DirectSum.lof k (Finset R) (fun Q => ↥(CoefficientLineSum.line (k := k) K Q)) Q r) =
      if hQ : K Q then Finsupp.single ⟨Q, hQ⟩ r.val else 0 := by
    ext P
    rw [CoefficientLineSum.equivalence_apply]
    by_cases hQ : K Q
    · rw [dif_pos hQ]
      by_cases hQP : Q = P.val
      · subst Q
        simp only [DirectSum.lof_eq_of, DirectSum.of_eq_same, Finsupp.single_apply,
          Subtype.ext_iff, if_true]
      · simp only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hQP),
          ZeroMemClass.coe_zero, Finsupp.single_apply, Subtype.ext_iff, if_neg hQP]
    · rw [dif_neg hQ]
      have hQP : Q ≠ P.val := fun h => hQ (h.symm ▸ P.property)
      simp only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hQP),
        ZeroMemClass.coe_zero, Finsupp.zero_apply]
  unfold targetEquiv
  rw [LinearEquiv.trans_apply, hcoord]
  split_ifs with hQ
  · simp only [Module.Basis.repr_symm_apply,Finsupp.linearCombination_single,
      Submodule.coe_smul_of_tower,totalFaceBasis_val]
  · rw [map_zero,ZeroMemClass.coe_zero,CoefficientLineSum.val_zero K Q hQ,zero_smul]

variable (C : ∀Q : Finset R,LinearContraction (R := k)
  (M := TotalFaceModule (k := k) (intersectionFaces B U Q))
  (H := CoefficientLineSum.line (k := k) K Q))

def projection : BlockModule (k := k) B U →ₗ[k] TotalFaceModule (k := k) K :=
  (targetEquiv K).toLinearMap.comp (intersectionContraction B U C).projection

theorem signed_projection (Q : Finset R) :
    (signedBlockContraction B U C Q).projection=(C Q).projection := by
  unfold signedBlockContraction
  split_ifs <;> rfl

theorem projection_basis_val (a : ΣQ : Finset R,{F : Finset V // intersectionFaces B U Q F}) :
    (projection B U K C (blockBasis B U a)).val=
      ((C a.1).projection (totalFaceBasis (intersectionFaces B U a.1) a.2)).val •
        Simplicial.basis a.1 := by
  rw [show blockBasis (k := k) B U a=DirectSum.lof k (Finset R)
      (fun Q => TotalFaceModule (intersectionFaces B U Q)) a.1
        (totalFaceBasis (intersectionFaces B U a.1) a.2) from FourPapers.directSum_basis_apply _ _ _]
  change (targetEquiv K ((intersectionContraction B U C).projection _)).val=_
  rw [intersectionContraction,LinearContraction.directSum_projection_lof,
    signed_projection,targetEquiv_lof_val]

variable (hB : Simplicial.Downward B) (hK : Simplicial.Downward K)
  (hd : ∀Q,(C Q).d=idealTotalDifferential (intersectionFaces_downward B U hB Q))
  (hnat : ∀ (P Q : Finset R) (hPQ : P⊆Q)
    (x : TotalFaceModule (k := k) (intersectionFaces B U Q)),
    ((C P).projection (intersectionInclusion B U P Q hPQ x)).val=((C Q).projection x).val)

section
attribute [local irreducible] projection blockHorizontal blockBasis idealTotalDifferential

include hnat in
set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
theorem projection_horizontal :
    (projection (k := k) B U K C).comp (blockHorizontal (k := k) B U)=
      (idealTotalDifferential (k := k) hK).comp (projection (k := k) B U K C) := by
  apply (blockBasis (k := k) B U).ext
  intro a
  change projection (k := k) B U K C
      (blockHorizontal (k := k) B U (blockBasis (k := k) B U a))=
    idealTotalDifferential (k := k) hK
      (projection (k := k) B U K C (blockBasis (k := k) B U a))
  apply Subtype.ext
  rw [blockHorizontal_basis (k := k) B U a,map_sum,Submodule.coe_sum,
    idealTotalDifferential_val,projection_basis_val (k := k) B U K C a,
    map_smul,face_boundary_basis_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_zsmul_unit,Submodule.coe_smul_of_tower,
    projection_basis_val (k := k) B U K C (eraseCoverIndex B U a r)]
  have hh := hnat (a.1.erase r.val) a.1 (Finset.erase_subset _ _)
    (totalFaceBasis (k := k) (intersectionFaces B U a.1) a.2)
  have he : intersectionInclusion (k := k) B U (a.1.erase r.val) a.1 (Finset.erase_subset _ _)
      (totalFaceBasis (k := k) (intersectionFaces B U a.1) a.2)=
      totalFaceBasis (k := k) (intersectionFaces B U (a.1.erase r.val))
        (eraseCoverIndex B U a r).2 := by
    apply Subtype.ext
    change (totalFaceBasis (k := k) (intersectionFaces B U a.1) a.2).val=
      (totalFaceBasis (k := k) (intersectionFaces B U (a.1.erase r.val))
        (eraseCoverIndex B U a r).2).val
    dsimp only [eraseCoverIndex]
    rw [totalFaceBasis_val,totalFaceBasis_val]
  rw [he] at hh
  dsimp only [eraseCoverIndex] at hh ⊢
  calc
    _ = TauCeti.ExteriorAlgebra.basisEraseSign r.val a.1 •
        (((C a.1).projection (totalFaceBasis (k := k) (intersectionFaces B U a.1) a.2)).val •
          Simplicial.basis (k := k) (a.1.erase r.val)) :=
      congrArg (fun c : k => TauCeti.ExteriorAlgebra.basisEraseSign r.val a.1 •
        (c • Simplicial.basis (k := k) (a.1.erase r.val))) hh
    _ = _ := smul_comm _ _ _

end

def lineDifferential : Module.End k (Lines (k := k) K) :=
  (targetEquiv K).symm.toLinearMap.comp
    ((idealTotalDifferential hK).comp (targetEquiv K).toLinearMap)

include hnat in
theorem lineProjection_horizontal :
    (intersectionContraction B U C).projection.comp (blockHorizontal B U)=
      (lineDifferential K hK).comp (intersectionContraction B U C).projection := by
  apply LinearMap.ext
  intro x
  apply (targetEquiv K).injective
  change projection B U K C (blockHorizontal B U x)=
    targetEquiv K ((targetEquiv K).symm
      (idealTotalDifferential hK (projection B U K C x)))
  rw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (projection_horizontal B U K C hK hnat) x

def deformation : LinearDeformationRetract (R := k)
    (M := BlockModule (k := k) B U) (H := TotalFaceModule (k := k) K) :=
  (transferred B U C hB hd).changeTarget (targetEquiv K)

include hnat in
/-- The final target differential is literally the augmented boundary
of K, with all orientation signs inherited from the cover order. -/
theorem deformation_target :
    (deformation B U K C hB hd).targetD=idealTotalDifferential hK := by
  have hh := (intersectionContraction B U C).transferredDifferential_eq_of_natural_projection
    (blockHorizontal B U) (lineDifferential K hK)
    (lineProjection_horizontal B U K C hK hnat)
    ((intersectionContraction B U C).leftPerturbationUnit (blockBasis B U) (fun a => a.1.card)
      (blockHorizontal B U) (blockHorizontal_decreases B U)
      (intersectionHomotopy_nonincreasing B U C))
    ((intersectionContraction B U C).leftPerturbationUnit_val (blockBasis B U) (fun a => a.1.card)
      (blockHorizontal B U) (blockHorizontal_decreases B U)
      (intersectionHomotopy_nonincreasing B U C))
  apply LinearMap.ext
  intro x
  change targetEquiv K ((intersectionContraction B U C).transferredDifferential _ _
    ((targetEquiv K).symm x))=idealTotalDifferential hK x
  rw [hh]
  simp only [lineDifferential,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

include hK hnat in
theorem deformation_projection :
    (deformation B U K C hB hd).projection=projection B U K C := by
  have hh := (intersectionContraction B U C).transferredProjection_eq_of_natural_projection
    (blockHorizontal B U) (lineDifferential K hK)
    (lineProjection_horizontal B U K C hK hnat)
    ((intersectionContraction B U C).leftPerturbationUnit (blockBasis B U) (fun a => a.1.card)
      (blockHorizontal B U) (blockHorizontal_decreases B U)
      (intersectionHomotopy_nonincreasing B U C))
    ((intersectionContraction B U C).leftPerturbationUnit_val (blockBasis B U) (fun a => a.1.card)
      (blockHorizontal B U) (blockHorizontal_decreases B U)
      (intersectionHomotopy_nonincreasing B U C))
  change (targetEquiv K).toLinearMap.comp
    ((intersectionContraction B U C).transferredProjection _ _)=_
  rw [hh]
  rfl

def totalDeformation : LinearDeformationRetract (R := k)
    (M := totalModule (k := k) B U) (H := TotalFaceModule (k := k) K) :=
  (deformation B U K C hB hd).changeSource (blockEquiv B U).symm

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
theorem totalDeformation_source :
    (totalDeformation (k := k) B U K C hB hd).sourceD=
      horizontal (k := k) B U+vertical (k := k) B U hB := by
  apply LinearMap.ext
  intro x
  apply (blockEquiv (k := k) B U).injective
  change blockEquiv (k := k) B U ((blockEquiv (k := k) B U).symm
    (((intersectionContraction (k := k) B U C).d+blockHorizontal (k := k) B U :
      Module.End k (BlockModule (k := k) B U)) (blockEquiv (k := k) B U x)))=
    blockEquiv (k := k) B U
      ((horizontal (k := k) B U+vertical (k := k) B U hB :
        Module.End k (totalModule (k := k) B U)) x)
  rw [LinearEquiv.apply_symm_apply,LinearMap.add_apply,
    intersectionDifferential_actual (k := k) B U C hB hd]
  simp only [LinearMap.add_apply,map_add,blockHorizontal,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact add_comm _ _

include hnat in
theorem totalDeformation_target :
    (totalDeformation B U K C hB hd).targetD=idealTotalDifferential hK :=
  deformation_target B U K C hB hK hd hnat

end FourPapers.CechFace.NerveReduction
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IncidenceSingletonJoin -/
section

/-!
# The unexpanded incidence ideal in Lemma 10.1

Each zero block is the single actual variable z_a. The other block is
the actual set of incidence variables at a not omitted by Q. This is
the literal L ⊕ T construction, separate from the expanded zero blocks
used for the sublattice top colon.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice.IncidenceSingletonJoin
open Classical CommAlg CommAlg.Simplicial HomologicalPerturbation

universe u
variable {L R T k : Type u} [Fintype L] [Fintype R] [Fintype T]
  [DecidableEq L] [DecidableEq R] [LinearOrder (L ⊕ T)] [CommRing k]
  (left : T → L) (right : T → R)

def rowSupport (p : Fin (Fintype.card L)) : L ⊕ T → Prop :=
  Sum.elim (fun a => Fintype.equivFin L a=p) (fun t => Fintype.equivFin L (left t)=p)

def zeroBlock (p : Fin (Fintype.card L)) : Finset (L ⊕ T) :=
  {Sum.inl ((Fintype.equivFin L).symm p)}

def oneBlock (Q : Finset R) (p : Fin (Fintype.card L)) : Finset (L ⊕ T) :=
  (Finset.univ.filter fun t => Fintype.equivFin L (left t)=p ∧ right t∉Q).image Sum.inr

@[simp] theorem zeroBlock_inl (p : Fin (Fintype.card L)) (a : L) :
    Sum.inl a∈zeroBlock (T:=T) p ↔ Fintype.equivFin L a=p := by
  simp [zeroBlock,Equiv.eq_symm_apply]

@[simp] theorem zeroBlock_inr (p : Fin (Fintype.card L)) (t : T) :
    Sum.inr t∉zeroBlock (L:=L) p := by simp [zeroBlock]

@[simp] theorem oneBlock_inl (Q : Finset R) (p : Fin (Fintype.card L)) (a : L) :
    Sum.inl a∉oneBlock left right Q p := by simp [oneBlock]

@[simp] theorem oneBlock_inr (Q : Finset R) (p : Fin (Fintype.card L)) (t : T) :
    Sum.inr t∈oneBlock left right Q p ↔
      Fintype.equivFin L (left t)=p ∧ right t∉Q := by simp [oneBlock]

theorem support_disjoint (p q : Fin (Fintype.card L)) (hpq : p≠q)
    (v : L ⊕ T) (hp : rowSupport left p v) : ¬rowSupport left q v := by
  cases v <;> exact fun hq => hpq (hp.symm.trans hq)

theorem zero_supported (p : Fin (Fintype.card L)) (v : L ⊕ T)
    (hv : v∈zeroBlock (T:=T) p) : rowSupport left p v := by
  cases v with
  | inl a => exact (zeroBlock_inl p a).mp hv
  | inr t => exact False.elim (zeroBlock_inr p t hv)

theorem one_supported (Q : Finset R) (p : Fin (Fintype.card L)) (v : L ⊕ T)
    (hv : v∈oneBlock left right Q p) : rowSupport left p v := by
  cases v with
  | inl a => exact False.elim (oneBlock_inl left right Q p a hv)
  | inr t => exact ((oneBlock_inr left right Q p t).mp hv).1

theorem zero_one_disjoint (Q : Finset R) (p : Fin (Fintype.card L)) :
    Disjoint (zeroBlock (T:=T) p) (oneBlock left right Q p) := by
  apply Finset.disjoint_left.mpr
  intro v hvz hve
  cases v with
  | inl a => exact oneBlock_inl left right Q p a hve
  | inr t => exact zeroBlock_inr p t hvz

theorem faces_iff (Q : Finset R) (F : Finset (L ⊕ T)) :
    JoinedTwoSimplex.Faces (rowSupport left) (zeroBlock (T:=T)) (oneBlock left right Q) F ↔
      incidenceIntersectionFaces left right Q F := by
  constructor
  · rintro ⟨hcover,hrows⟩
    constructor
    · intro a ha t hta ht
      let p := Fintype.equivFin L a
      have hza : Sum.inl a∈F.filter (rowSupport left p) :=
        Finset.mem_filter.mpr ⟨ha,rfl⟩
      have hxt : Sum.inr t∈F.filter (rowSupport left p) :=
        Finset.mem_filter.mpr ⟨ht,by change Fintype.equivFin L (left t)=p; rw [hta]⟩
      rcases hrows p with hz | hx
      · exact zeroBlock_inr p t (hz hxt)
      · exact oneBlock_inl left right Q p a (hx hza)
    · intro t htQ htF
      let p := Fintype.equivFin L (left t)
      have hxt : Sum.inr t∈F.filter (rowSupport left p) :=
        Finset.mem_filter.mpr ⟨htF,rfl⟩
      rcases hrows p with hz | hx
      · exact zeroBlock_inr p t (hz hxt)
      · exact ((oneBlock_inr left right Q p t).mp (hx hxt)).2 htQ
  · rintro ⟨hjoin,hQ⟩
    constructor
    · intro v hv
      cases v with
      | inl a => exact ⟨Fintype.equivFin L a,rfl⟩
      | inr t => exact ⟨Fintype.equivFin L (left t),rfl⟩
    · intro p
      by_cases hz : Sum.inl ((Fintype.equivFin L).symm p)∈F
      · left
        intro v hv
        obtain ⟨hvF,hvp⟩ := Finset.mem_filter.mp hv
        cases v with
        | inl a => exact (zeroBlock_inl p a).mpr hvp
        | inr t =>
            have hleft : left t=(Fintype.equivFin L).symm p := by
              apply (Fintype.equivFin L).injective
              simpa only [rowSupport,Sum.elim_inr,Equiv.apply_symm_apply] using hvp
            exact (hjoin _ hz t hleft hvF).elim
      · right
        intro v hv
        obtain ⟨hvF,hvp⟩ := Finset.mem_filter.mp hv
        cases v with
        | inl a =>
            have ha : a=(Fintype.equivFin L).symm p := by
              apply (Fintype.equivFin L).injective
              simpa only [rowSupport,Sum.elim_inl,Equiv.apply_symm_apply] using hvp
            exact (hz (ha ▸ hvF)).elim
        | inr t =>
            exact (oneBlock_inr left right Q p t).mpr ⟨hvp,fun htQ => hQ t htQ hvF⟩

def sourceEquiv (Q : Finset R) :
    TotalFaceModule (k:=k) (JoinedTwoSimplex.Faces (rowSupport left)
      (zeroBlock (T:=T)) (oneBlock left right Q)) ≃ₗ[k]
    TotalFaceModule (k:=k) (incidenceIntersectionFaces left right Q) :=
  LinearEquiv.ofEq _ _ (congrArg (TotalFaceModule (k:=k))
    (funext fun F => propext (faces_iff left right Q F)))

theorem sourceEquiv_piece (Q : Finset R) (j : ℕ)
    (x : TotalFaceModule (k:=k) (JoinedTwoSimplex.Faces (rowSupport left)
      (zeroBlock (T:=T)) (oneBlock left right Q))) :
    x∈totalFacePiece (JoinedTwoSimplex.Faces (rowSupport left)
      (zeroBlock (T:=T)) (oneBlock left right Q)) j ↔
      sourceEquiv left right Q x∈totalFacePiece (incidenceIntersectionFaces left right Q) j := by
  change x.val∈Chains _ j ↔ (sourceEquiv left right Q x).val∈Chains _ j
  simp only [sourceEquiv,LinearEquiv.coe_ofEq_apply]
  generalize x.val = z
  rw [show JoinedTwoSimplex.Faces (rowSupport left) (zeroBlock (T:=T))
    (oneBlock left right Q)=incidenceIntersectionFaces left right Q from
      funext fun F => propext (faces_iff left right Q F)]

theorem sourceEquiv_symm_piece (Q : Finset R) (j : ℕ)
    (x : TotalFaceModule (k:=k) (incidenceIntersectionFaces left right Q))
    (hx : x∈totalFacePiece (incidenceIntersectionFaces left right Q) j) :
    (sourceEquiv left right Q).symm x∈totalFacePiece
      (JoinedTwoSimplex.Faces (rowSupport left) (zeroBlock (T:=T)) (oneBlock left right Q)) j :=
  (sourceEquiv_piece (k := k) left right Q j _).mpr (by simpa only [LinearEquiv.apply_symm_apply] using hx)

theorem cech_intersection_iff (Q : Finset R) (F : Finset (L ⊕ T)) :
    CechFace.intersectionFaces (incidenceJoinFaces left)
      (incidenceRightSupport (L:=L) right) Q F ↔
      incidenceIntersectionFaces left right Q F := by
  constructor
  · rintro ⟨hB,hQ⟩
    exact ⟨hB,fun t ht htF => Finset.disjoint_left.mp (hQ (right t) ht) htF
      ((incidenceRightSupport_inr right (right t) t).mpr rfl)⟩
  · rintro ⟨hB,hQ⟩
    refine ⟨hB,fun r hr => Finset.disjoint_left.mpr ?_⟩
    intro v hvF hvU
    cases v with
    | inl a => exact incidenceRightSupport_inl right r a hvU
    | inr t =>
        have ht : right t=r := (incidenceRightSupport_inr right r t).mp hvU
        exact hQ t (by simpa only [ht] using hr) hvF

theorem nerve_iff_nonempty (Q : Finset R) :
    incidenceNerveFaces left right Q ↔ ∀p,(oneBlock left right Q p).Nonempty := by
  constructor
  · intro h p
    obtain ⟨t,ht,htr⟩ := h ((Fintype.equivFin L).symm p)
    exact ⟨Sum.inr t,(oneBlock_inr left right Q p t).mpr
      ⟨by simp only [ht,Equiv.apply_symm_apply],htr⟩⟩
  · intro h a
    obtain ⟨v,hv⟩ := h (Fintype.equivFin L a)
    cases v with
    | inl b => exact (oneBlock_inl left right Q _ b hv).elim
    | inr t =>
        obtain ⟨ht,htr⟩ := (oneBlock_inr left right Q _ t).mp hv
        exact ⟨t,(Fintype.equivFin L).injective ht,htr⟩

def nerveLine (Q : Finset R) : Submodule k k :=
  if incidenceNerveFaces left right Q then ⊤ else ⊥

def lineEquiv (Q : Finset R) (hQ : incidenceNerveFaces left right Q) :
    nerveLine (k:=k) left right Q ≃ₗ[k] k :=
  (LinearEquiv.ofEq _ _ (if_pos hQ)).trans Submodule.topEquiv

def verticalProjection (Q : Finset R) :
    TotalFaceModule (k:=k) (incidenceIntersectionFaces left right Q) →ₗ[k] k :=
  (JoinedTwoSimplex.projection (rowSupport left) (zeroBlock (T:=T)) (oneBlock left right Q)
    (support_disjoint left) (zero_supported left) (one_supported left right Q)).comp
      (sourceEquiv left right Q).symm.toLinearMap

def zeroVertex (p : Fin (Fintype.card L)) : L ⊕ T :=
  Sum.inl ((Fintype.equivFin L).symm p)

theorem zeroVertex_mem (p : Fin (Fintype.card L)) :
    zeroVertex (T:=T) p∈zeroBlock (T:=T) p := by simp [zeroVertex,zeroBlock]

/-- Actual strong contraction for every intersection in the displayed
unexpanded incidence ideal of Lemma 10.1, over any commutative ring. -/
def contraction (Q : Finset R) : LinearContraction (R:=k)
    (M:=TotalFaceModule (k:=k) (incidenceIntersectionFaces left right Q))
    (H:=nerveLine (k:=k) left right Q) := by
  by_cases hQ : incidenceNerveFaces left right Q
  · let hn := (nerve_iff_nonempty left right Q).mp hQ
    let e := fun p => (hn p).choose
    let C := JoinedTwoSimplex.contraction (k:=k) (rowSupport left) (zeroBlock (T:=T))
      (oneBlock left right Q) (support_disjoint left) (zero_supported left)
      (one_supported left right Q) (zero_one_disjoint left right Q)
      (zeroVertex (T:=T)) e zeroVertex_mem (fun p => (hn p).choose_spec)
    exact (C.changeTarget (lineEquiv left right Q hQ).symm).changeSource (sourceEquiv left right Q)
  · have hn : ¬∀p,(oneBlock left right Q p).Nonempty :=
      fun h => hQ ((nerve_iff_nonempty left right Q).mpr h)
    let a := Classical.choose (not_forall.mp hn)
    have ha : oneBlock left right Q a=∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (Classical.choose_spec (not_forall.mp hn))
    let C := JoinedTwoSimplex.zeroContraction (k:=k) (rowSupport left) (zeroBlock (T:=T))
      (oneBlock left right Q) (support_disjoint left) (zero_supported left)
      a ha (zeroVertex (T:=T) a) (zeroVertex_mem a)
    let e : (⊥ : Submodule k k) ≃ₗ[k] nerveLine left right Q :=
      LinearEquiv.ofEq _ _ (by simp only [nerveLine,if_neg hQ])
    exact (C.changeTarget e).changeSource (sourceEquiv left right Q)

theorem contraction_d (Q : Finset R) :
    (contraction (k:=k) left right Q).d=
      idealTotalDifferential (incidenceIntersectionFaces_downward left right Q) := by
  unfold contraction
  split_ifs with hQ
  all_goals
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [LinearContraction.changeSource,LinearContraction.changeTarget,
      LinearMap.comp_apply,LinearEquiv.coe_coe,JoinedTwoSimplex.contraction_d,
      JoinedTwoSimplex.zeroContraction_d,idealTotalDifferential_val,
      sourceEquiv,LinearEquiv.coe_ofEq_apply,LinearEquiv.ofEq_symm]

theorem contraction_projection_val (Q : Finset R)
    (x : TotalFaceModule (k:=k) (incidenceIntersectionFaces left right Q)) :
    ((contraction left right Q).projection x).val=verticalProjection left right Q x := by
  unfold contraction
  split_ifs with hQ
  · rfl
  · dsimp [LinearContraction.changeSource,LinearContraction.changeTarget]
    change 0=JoinedTwoSimplex.projection (rowSupport left) (zeroBlock (T:=T))
      (oneBlock left right Q) (support_disjoint left) (zero_supported left)
      (one_supported left right Q) ((sourceEquiv left right Q).symm x)
    have hn : ¬∀p,(oneBlock left right Q p).Nonempty :=
      fun h => hQ ((nerve_iff_nonempty left right Q).mpr h)
    obtain ⟨a,ha⟩ := not_forall.mp hn
    rw [JoinedTwoSimplex.projection_zero_of_empty _ _ _ _ _ _ a
      (Finset.not_nonempty_iff_eq_empty.mp ha)]
    rfl

theorem projection_zero_off_degree (Q : Finset R) (j : ℕ) (hj : j≠Fintype.card L)
    (x : TotalFaceModule (k:=k) (incidenceIntersectionFaces left right Q))
    (hx : x∈totalFacePiece (incidenceIntersectionFaces left right Q) j) :
    (contraction left right Q).projection x=0 := by
  apply Subtype.ext
  rw [contraction_projection_val]
  exact JoinedTwoSimplex.projection_zero_off_degree (rowSupport left) (zeroBlock (T:=T))
    (oneBlock left right Q) (support_disjoint left) (zero_supported left)
    (one_supported left right Q) j hj _ (sourceEquiv_symm_piece (k := k) left right Q j x hx)

theorem inclusion_degree (Q : Finset R) (r : nerveLine (k:=k) left right Q) :
    (contraction left right Q).inclusion r∈
      totalFacePiece (incidenceIntersectionFaces left right Q) (Fintype.card L) := by
  unfold contraction
  split_ifs with hQ
  · exact (sourceEquiv_piece (k := k) left right Q _ _).mp
      (JoinedTwoSimplex.inclusion_degree (rowSupport left) (zeroBlock (T:=T))
        (oneBlock left right Q) (support_disjoint left) (zero_supported left)
        (one_supported left right Q) (zero_one_disjoint left right Q)
        (zeroVertex (T:=T)) _ zeroVertex_mem _ _)
  · change sourceEquiv (k := k) left right Q 0 ∈ _
    rw [map_zero]
    exact Submodule.zero_mem _

theorem homotopy_raises (Q : Finset R) (j : ℕ)
    (x : TotalFaceModule (k:=k) (incidenceIntersectionFaces left right Q))
    (hx : x∈totalFacePiece (incidenceIntersectionFaces left right Q) j) :
    (contraction left right Q).h x∈
      totalFacePiece (incidenceIntersectionFaces left right Q) (j+1) := by
  unfold contraction
  split_ifs with hQ
  · exact (sourceEquiv_piece (k := k) left right Q _ _).mp
      (JoinedTwoSimplex.homotopy_raises (rowSupport left) (zeroBlock (T:=T))
        (oneBlock left right Q) (support_disjoint left) (zero_supported left)
        (one_supported left right Q) (zero_one_disjoint left right Q)
        (zeroVertex (T:=T)) _ zeroVertex_mem _ j _
          (sourceEquiv_symm_piece (k := k) left right Q j x hx))
  · have hn : ¬∀p,(oneBlock left right Q p).Nonempty :=
      fun h => hQ ((nerve_iff_nonempty left right Q).mpr h)
    let a := Classical.choose (not_forall.mp hn)
    have ha : oneBlock left right Q a=∅ :=
      Finset.not_nonempty_iff_eq_empty.mp (Classical.choose_spec (not_forall.mp hn))
    apply (sourceEquiv_piece (k := k) left right Q _ _).mp
    apply creation_mem_of_cone
    · intro s hs
      exact JoinedTwoSimplex.insert_vertex (rowSupport left) (zeroBlock (T:=T))
        (oneBlock left right Q) (support_disjoint left) (zero_supported left)
        a ha (zeroVertex (T:=T) a) (zeroVertex_mem a) hs
    · exact sourceEquiv_symm_piece (k := k) left right Q j x hx

def intersectionInclusion {P Q : Finset R} (hPQ : P⊆Q) :
    TotalFaceModule (k:=k) (incidenceIntersectionFaces left right Q) →ₗ[k]
      TotalFaceModule (k:=k) (incidenceIntersectionFaces left right P) :=
  Submodule.inclusion (Submodule.span_le.mpr (by
    rintro x ⟨F,hF,rfl⟩
    exact Submodule.subset_span ⟨F,⟨hF.1,fun t ht => hF.2 t (hPQ ht)⟩,rfl⟩))

theorem oneBlock_antitone {P Q : Finset R} (hPQ : P⊆Q)
    (p : Fin (Fintype.card L)) : oneBlock left right Q p⊆oneBlock left right P p := by
  intro v hv
  cases v with
  | inl a => exact (oneBlock_inl left right Q p a hv).elim
  | inr t =>
      obtain ⟨ht,hQ⟩ := (oneBlock_inr left right Q p t).mp hv
      exact (oneBlock_inr left right P p t).mpr ⟨ht,fun h => hQ (hPQ h)⟩

/-- Actual row projections commute with every cover inclusion, including
an empty leaf block becoming nonempty. -/
theorem projection_natural {P Q : Finset R} (hPQ : P⊆Q)
    (x : TotalFaceModule (k:=k) (incidenceIntersectionFaces left right Q)) :
    verticalProjection left right P (intersectionInclusion left right hPQ x)=
      verticalProjection left right Q x := by
  have he := LinearMap.congr_fun
    (JoinedTwoSimplex.projection_natural (k:=k) (rowSupport left) (zeroBlock (T:=T))
      (oneBlock left right Q) (oneBlock left right P) (support_disjoint left)
      (zero_supported left) (one_supported left right Q) (one_supported left right P)
      (oneBlock_antitone left right hPQ) (zero_one_disjoint left right P))
        ((sourceEquiv left right Q).symm x)
  have hxy : (sourceEquiv left right P).symm (intersectionInclusion left right hPQ x)=
      JoinedTwoSimplex.inclusion (rowSupport left) (zeroBlock (T:=T))
        (oneBlock left right Q) (oneBlock left right P) (oneBlock_antitone left right hPQ)
          ((sourceEquiv left right Q).symm x) := by
    apply Subtype.ext
    rfl
  change JoinedTwoSimplex.projection (k := k) (rowSupport left) (zeroBlock (T:=T))
    (oneBlock left right P) (support_disjoint left) (zero_supported left)
    (one_supported left right P)
    ((sourceEquiv left right P).symm (intersectionInclusion left right hPQ x)) = _
  rw [hxy]
  exact he

def cechSourceEquiv (Q : Finset R) :
    TotalFaceModule (k:=k) (CechFace.intersectionFaces (incidenceJoinFaces left)
      (incidenceRightSupport (L:=L) right) Q) ≃ₗ[k]
      TotalFaceModule (k:=k) (incidenceIntersectionFaces left right Q) :=
  LinearEquiv.ofEq _ _ (congrArg (TotalFaceModule (k:=k))
    (funext fun F => propext (cech_intersection_iff left right Q F)))

def cechContraction (Q : Finset R) : LinearContraction (R:=k)
    (M:=TotalFaceModule (k:=k) (CechFace.intersectionFaces (incidenceJoinFaces left)
      (incidenceRightSupport (L:=L) right) Q))
    (H:=CoefficientLineSum.line (k:=k) (incidenceNerveFaces left right) Q) :=
  (contraction left right Q).changeSource (cechSourceEquiv left right Q).symm

theorem cechSourceEquiv_piece (Q : Finset R) (j : ℕ)
    (x : TotalFaceModule (k:=k) (CechFace.intersectionFaces (incidenceJoinFaces left)
      (incidenceRightSupport (L:=L) right) Q)) :
    x∈totalFacePiece (CechFace.intersectionFaces (incidenceJoinFaces left)
      (incidenceRightSupport (L:=L) right) Q) j ↔
      cechSourceEquiv left right Q x∈totalFacePiece (incidenceIntersectionFaces left right Q) j := by
  change x.val∈Chains _ j ↔ (cechSourceEquiv left right Q x).val∈Chains _ j
  simp only [cechSourceEquiv,LinearEquiv.coe_ofEq_apply]
  generalize x.val = z
  rw [show CechFace.intersectionFaces (incidenceJoinFaces left)
    (incidenceRightSupport (L:=L) right) Q=incidenceIntersectionFaces left right Q from
      funext fun F => propext (cech_intersection_iff left right Q F)]

theorem cechHomotopy_raises (Q : Finset R) (j : ℕ)
    (x : TotalFaceModule (k:=k) (CechFace.intersectionFaces (incidenceJoinFaces left)
      (incidenceRightSupport (L:=L) right) Q))
    (hx : x∈totalFacePiece (CechFace.intersectionFaces (incidenceJoinFaces left)
      (incidenceRightSupport (L:=L) right) Q) j) :
    (cechContraction left right Q).h x∈totalFacePiece
      (CechFace.intersectionFaces (incidenceJoinFaces left)
        (incidenceRightSupport (L:=L) right) Q) (j+1) := by
  apply (cechSourceEquiv_piece left right Q (j+1) _).mpr
  change (contraction (k := k) left right Q).h (cechSourceEquiv left right Q x)∈
    totalFacePiece (incidenceIntersectionFaces left right Q) (j+1)
  exact homotopy_raises left right Q j _ ((cechSourceEquiv_piece left right Q j x).mp hx)

theorem cechInclusion_degree (Q : Finset R)
    (r : CoefficientLineSum.line (k:=k) (incidenceNerveFaces left right) Q) :
    (cechContraction left right Q).inclusion r∈totalFacePiece
      (CechFace.intersectionFaces (incidenceJoinFaces left)
        (incidenceRightSupport (L:=L) right) Q) (Fintype.card L) := by
  apply (cechSourceEquiv_piece left right Q _ _).mpr
  change cechSourceEquiv (k := k) left right Q
    ((cechSourceEquiv (k := k) left right Q).symm ((contraction left right Q).inclusion r)) ∈ _
  rw [LinearEquiv.apply_symm_apply]
  exact inclusion_degree left right Q r

theorem cechProjection_zero_off_degree (Q : Finset R) (j : ℕ) (hj : j≠Fintype.card L)
    (x : TotalFaceModule (k:=k) (CechFace.intersectionFaces (incidenceJoinFaces left)
      (incidenceRightSupport (L:=L) right) Q))
    (hx : x∈totalFacePiece (CechFace.intersectionFaces (incidenceJoinFaces left)
      (incidenceRightSupport (L:=L) right) Q) j) :
    (cechContraction left right Q).projection x=0 :=
  projection_zero_off_degree left right Q j hj _ ((cechSourceEquiv_piece left right Q j x).mp hx)

theorem cechContraction_d [LinearOrder R] (Q : Finset R) :
    (cechContraction (k:=k) left right Q).d=idealTotalDifferential
      (CechFace.intersectionFaces_downward (incidenceJoinFaces left)
        (incidenceRightSupport (L:=L) right) (incidenceJoinFaces_downward left) Q) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((contraction left right Q).d (cechSourceEquiv left right Q x)).val=
    Simplicial.boundary x.val
  rw [contraction_d]
  rfl

section OrderedNerve
variable [LinearOrder R]

theorem cechProjection_natural (P Q : Finset R) (hPQ : P⊆Q)
    (x : TotalFaceModule (k:=k) (CechFace.intersectionFaces (incidenceJoinFaces left)
      (incidenceRightSupport (L:=L) right) Q)) :
    ((cechContraction left right P).projection
      (CechFace.NerveReduction.intersectionInclusion (incidenceJoinFaces left)
        (incidenceRightSupport (L:=L) right) P Q hPQ x)).val=
      ((cechContraction left right Q).projection x).val := by
  change ((contraction left right P).projection (intersectionInclusion left right hPQ
    (cechSourceEquiv left right Q x))).val=
      ((contraction left right Q).projection (cechSourceEquiv left right Q x)).val
  rw [contraction_projection_val,contraction_projection_val]
  exact projection_natural left right hPQ _

/-- The literal augmented Čech complex for the singleton-zero-block
incidence ideal retracts to the actual augmented nerve complex. -/
def nerveDeformation : LinearDeformationRetract (R:=k)
    (M:=CechFace.totalModule (k:=k) (incidenceJoinFaces left)
      (incidenceRightSupport (L:=L) right))
    (H:=TotalFaceModule (k:=k) (incidenceNerveFaces left right)) :=
  CechFace.NerveReduction.totalDeformation (incidenceJoinFaces left)
    (incidenceRightSupport (L:=L) right) (incidenceNerveFaces left right)
    (cechContraction left right) (incidenceJoinFaces_downward left) (cechContraction_d left right)

theorem nerveDeformation_source :
    (nerveDeformation (k:=k) left right).sourceD=
      CechFace.horizontal (incidenceJoinFaces left) (incidenceRightSupport (L:=L) right)+
      CechFace.vertical (incidenceJoinFaces left) (incidenceRightSupport (L:=L) right)
        (incidenceJoinFaces_downward left) :=
  CechFace.NerveReduction.totalDeformation_source _ _ _ _ _ _

theorem nerveDeformation_target :
    (nerveDeformation (k:=k) left right).targetD=
      idealTotalDifferential (incidenceNerveFaces_downward left right) :=
  CechFace.NerveReduction.totalDeformation_target _ _ _ _ _ _ _ (cechProjection_natural left right)

end OrderedNerve

end FourPapers.Sublattice.IncidenceSingletonJoin

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IncidenceIdealPresentation -/
section

/-! # The literal product-and-sum ideal in Lemma 10.1

This identifies the exponent-family quotient with the actual displayed
polynomial ideal. The row and column block polynomials are products of
the original incidence variables.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid MvPolynomial
open scoped Pointwise

universe u
variable {L R T k : Type u} [Fintype L] [Fintype R] [Fintype T]
  [DecidableEq L] [DecidableEq R] [LinearOrder (L ⊕ T)] [CommRing k]

def incidenceLeafSupport (left : T→L) (a : L) : Finset (L ⊕ T) :=
  (Finset.univ.filter fun t=>left t=a).image Sum.inr

def incidenceLeafMonomial (left : T→L) (a : L) : MvPolynomial (L ⊕ T) k :=
  monomial (faceExponent (incidenceLeafSupport left a)) 1

def incidenceRightMonomial (right : T→R) (r : R) : MvPolynomial (L ⊕ T) k :=
  monomial (faceExponent (incidenceRightSupport (L:=L) right r)) 1

theorem monomial_faceExponent_eq_prod {V : Type u} [Fintype V] [LinearOrder V]
    (F : Finset V) : monomial (faceExponent F) (1:k)=∏v∈F,X v := by
  simp only [faceExponent,monomial_sum_one,X]

theorem incidenceLeafMonomial_eq_prod (left : T→L) (a : L) :
    incidenceLeafMonomial (k:=k) left a=
      ∏t∈Finset.univ.filter (fun t=>left t=a),X (Sum.inr t) := by
  rw [incidenceLeafMonomial,monomial_faceExponent_eq_prod]
  exact Finset.prod_image (by intro a ha b hb h; exact Sum.inr.inj h)

theorem incidenceRightMonomial_eq_prod (right : T→R) (r : R) :
    incidenceRightMonomial (k:=k) (L:=L) right r=
      ∏t∈Finset.univ.filter (fun t=>right t=r),X (Sum.inr t) := by
  rw [incidenceRightMonomial,monomial_faceExponent_eq_prod]
  exact Finset.prod_image (by intro a ha b hb h; exact Sum.inr.inj h)

theorem incidenceChoiceExponent_sum (left : T→L) (D : Finset L) :
    faceExponent (incidenceChoiceSupport left D)=
      ∑a:L,if a∈D then Finsupp.single (Sum.inl a) 1 else
        faceExponent (incidenceLeafSupport left a) := by
  ext v
  cases v with
  | inl b =>
      rw [Finsupp.finset_sum_apply,Finset.sum_eq_single b]
      · by_cases hb : b∈D <;>
          simp [faceExponent_apply,incidenceChoiceSupport_inl,incidenceLeafSupport,hb]
      · intro a ha hab
        by_cases haD : a∈D <;>
          simp [haD,Finsupp.single_apply,hab,Ne.symm hab,faceExponent_apply,incidenceLeafSupport]
      · simp
  | inr t =>
      rw [Finsupp.finset_sum_apply,Finset.sum_eq_single (left t)]
      · by_cases ht : left t∈D <;>
          simp [faceExponent_apply,incidenceChoiceSupport_inr,incidenceLeafSupport,ht]
      · intro a ha hat
        by_cases haD : a∈D <;>
          simp [haD,Finsupp.single_apply,hat,Ne.symm hat,faceExponent_apply,incidenceLeafSupport]
      · simp

theorem incidenceChoiceMonomial_product (left : T→L) (D : Finset L) :
    monomial (faceExponent (incidenceChoiceSupport left D)) (1:k)=
      ∏a:L,if a∈D then X (Sum.inl a) else incidenceLeafMonomial left a := by
  rw [incidenceChoiceExponent_sum,monomial_sum_one]
  apply Finset.prod_congr rfl
  intro a _
  by_cases ha : a∈D <;> simp [ha,X,incidenceLeafMonomial]

def incidenceDisplayedIdeal (left : T→L) (right : T→R) : Ideal (MvPolynomial (L ⊕ T) k) :=
  (∏a:L,Ideal.span {X (Sum.inl a),incidenceLeafMonomial left a})+
    Ideal.span (Set.range (incidenceRightMonomial (k:=k) (L:=L) right))

/-- Every choice generator is precisely a product choosing z_a or X_a
in each row; no monomial-presentation hypothesis is assumed. -/
theorem incidenceChoiceGenerators_eq_product (left : T→L) :
    (fun v : Exponent (L ⊕ T)=>monomial v (1:k)) ''
      ((Finset.univ.image fun D:Finset L=>faceExponent (incidenceChoiceSupport left D)) :
        Set (Exponent (L ⊕ T)))=
      ∏a:L,({X (Sum.inl a),incidenceLeafMonomial (k:=k) left a} : Set (MvPolynomial (L ⊕ T) k)) := by
  ext f
  constructor
  · rintro ⟨v,hv,rfl⟩
    obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp hv
    apply (Set.mem_fintype_prod _ _).mpr
    refine ⟨fun a=>if a∈D then X (Sum.inl a) else incidenceLeafMonomial left a,?_,?_⟩
    · intro a
      by_cases ha : a ∈ D <;> simp [ha]
    · exact (incidenceChoiceMonomial_product left D).symm
  · intro hprod
    obtain ⟨f,hchoices,rfl⟩ := (Set.mem_fintype_prod _ _).mp hprod
    let D : Finset L := Finset.univ.filter fun a=>f a=X (Sum.inl a)
    refine ⟨faceExponent (incidenceChoiceSupport left D),
      Finset.mem_image.mpr ⟨D,Finset.mem_univ _,rfl⟩,?_⟩
    change monomial (faceExponent (incidenceChoiceSupport left D)) (1 : k) = ∏ i, f i
    rw [incidenceChoiceMonomial_product (k := k) left D]
    apply Finset.prod_congr rfl
    intro a _
    by_cases ha : f a=X (Sum.inl a)
    · have hDa : a ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩
      rw [if_pos hDa]
      exact ha.symm
    · have hx : f a = incidenceLeafMonomial left a := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, ha, false_or] using hchoices a
      have hDa : a ∉ D := by
        simpa only [D, Finset.mem_filter, Finset.mem_univ, true_and] using ha
      rw [if_neg hDa]
      exact hx.symm

/-- Exact equality with the polynomial ideal printed in Lemma 10.1. -/
theorem incidenceColonFamily_ideal (left : T→L) (right : T→R) :
    monomialIdeal k (incidenceColonFamily left right)=incidenceDisplayedIdeal left right := by
  unfold monomialIdeal incidenceColonFamily incidenceDisplayedIdeal
  rw [Finset.coe_union,Set.image_union,Ideal.span_union]
  rw [incidenceChoiceGenerators_eq_product,← Ideal.prod_span]
  congr 1
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨v,hv,rfl⟩
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hv
    exact ⟨r,rfl⟩
  · rintro ⟨r,rfl⟩
    exact ⟨_,Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩,rfl⟩

end FourPapers.Sublattice

end
end
end


end
