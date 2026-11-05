module
public import graph_foundation.part011
public import shared_results.part004
public import paper_results.part007

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.CechHorizontalReduction -/
section

/-!
# The horizontal augmented Čech contraction

For a fixed face F, its cover indices form the full simplex on the cover
members containing F. If that set is nonempty, exterior creation contracts
the entire augmented row. If it is empty, the empty cover index remains.
This gives exactly the relative face module B/(union of the cover), with
the actual projected simplicial differential after perturbation.
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

def missing (F : Finset V) : Finset R := Finset.univ.filter (fun r => Disjoint F (U r))

theorem mem_missing (F : Finset V) (r : R) : r∈missing U F ↔ Disjoint F (U r) := by
  simp only [missing,Finset.mem_filter,Finset.mem_univ,true_and]

theorem intersection_iff_subset (Q : Finset R) (F : Finset V) :
    intersectionFaces B U Q F ↔ B F ∧ Q⊆missing U F := by
  simp only [intersectionFaces,Finset.subset_iff,mem_missing]

theorem missing_mono {F G : Finset V} (hGF : G⊆F) : missing U F⊆missing U G := by
  intro r hr
  exact (mem_missing U G r).mpr (((mem_missing U F r).mp hr).mono_left hGF)

def coverFaces (F : Finset V) : Prop := (missing U F).Nonempty
def relativeFaces (F : Finset V) : Prop := B F ∧ missing U F=∅

theorem relativeFaces_iff (F : Finset V) :
    relativeFaces B U F ↔ B F ∧ ¬coverFaces U F := by
  simp only [relativeFaces,coverFaces,Finset.not_nonempty_iff_eq_empty]

abbrev FiberModule := ⨁ F : {F : Finset V // B F},
  TotalFaceModule (k:=k) (FullSimplex.faces (missing U F.val))

def fiberBasis : Module.Basis
    (Σ F : {F : Finset V // B F},{Q : Finset R // FullSimplex.faces (missing U F.val) Q})
    k (FiberModule (k:=k) B U) :=
  DFinsupp.basis (fun F : {F : Finset V // B F} =>
    totalFaceBasis (FullSimplex.faces (missing U F.val)))

def fiberIndexEquiv : {a : Finset R × Finset V // pairFaces B U a} ≃
    Σ F : {F : Finset V // B F},{Q : Finset R // FullSimplex.faces (missing U F.val) Q} where
  toFun a := ⟨⟨a.val.2,a.property.1⟩,a.val.1,
    ((intersection_iff_subset B U _ _).mp a.property).2⟩
  invFun a := ⟨(a.2.val,a.1.val),(intersection_iff_subset B U _ _).mpr ⟨a.1.property,a.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def fiberEquiv : totalModule (k:=k) B U ≃ₗ[k] FiberModule (k:=k) B U :=
  (totalBasis B U).equiv (fiberBasis B U) (fiberIndexEquiv B U)

theorem fiberEquiv_basis (F : {F : Finset V // B F})
    (Q : {Q : Finset R // FullSimplex.faces (missing U F.val) Q}) :
    fiberEquiv (k:=k) B U
      (totalBasis B U ⟨(Q.val,F.val),(intersection_iff_subset B U _ _).mpr ⟨F.property,Q.property⟩⟩)=
        fiberBasis B U ⟨F,Q⟩ :=
  Module.Basis.equiv_apply (b := totalBasis (k := k) B U) (b' := fiberBasis (k := k) B U)
    (e := fiberIndexEquiv B U)
    (i := ⟨(Q.val,F.val),(intersection_iff_subset B U _ _).mpr ⟨F.property,Q.property⟩⟩)

theorem fiberEquiv_basis_lof (F : {F : Finset V // B F})
    (Q : {Q : Finset R // FullSimplex.faces (missing U F.val) Q}) :
    fiberEquiv (k := k) B U
      (totalBasis (k := k) B U
        ⟨(Q.val,F.val),(intersection_iff_subset B U _ _).mpr ⟨F.property,Q.property⟩⟩) =
      DirectSum.lof k {F : Finset V // B F}
        (fun F => TotalFaceModule (k := k) (FullSimplex.faces (missing U F.val))) F
          (totalFaceBasis (k := k) (FullSimplex.faces (missing U F.val)) Q) := by
  calc
    _ = fiberBasis (k := k) B U ⟨F,Q⟩ := fiberEquiv_basis (k := k) B U F Q
    _ = _ := FourPapers.directSum_basis_apply
      (fun F : {F : Finset V // B F} =>
        totalFaceBasis (k := k) (FullSimplex.faces (missing U F.val))) F Q

theorem fiberEquiv_symm_lof_val (F : {F : Finset V // B F})
    (z : TotalFaceModule (k:=k) (FullSimplex.faces (missing U F.val))) :
    ((fiberEquiv B U).symm (DirectSum.lof k _
      (fun F : {F : Finset V // B F} => TotalFaceModule (FullSimplex.faces (missing U F.val))) F z)).val=
        z.val ⊗ₜ[k] Simplicial.basis F.val := by
  have he : (totalModule (k:=k) B U).subtype.comp ((fiberEquiv B U).symm.toLinearMap.comp
      (DirectSum.lof k _ (fun F : {F : Finset V // B F} =>
        TotalFaceModule (FullSimplex.faces (missing U F.val))) F))=
      ((TensorProduct.mk k (Simplicial.Ambient R k) (Simplicial.Ambient V k)).flip
        (Simplicial.basis F.val)).comp
          (TotalFaceModule (k:=k) (FullSimplex.faces (missing U F.val))).subtype := by
    apply (totalFaceBasis (k:=k) (FullSimplex.faces (missing U F.val))).ext
    intro Q
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,Submodule.subtype_apply]
    rw [← fiberEquiv_basis_lof (k := k) B U F Q,
      LinearEquiv.symm_apply_apply,totalBasis_val,totalFaceBasis_val]
    change ambientBasis (k := k) (Q.val,F.val)=
      Simplicial.basis Q.val ⊗ₜ[k] Simplicial.basis F.val
    exact Module.Basis.tensorProduct_apply _ _ _ _
  exact LinearMap.congr_fun he z

def horizontalContraction : LinearContraction (R:=k) (M:=FiberModule (k:=k) B U)
    (H:=⨁F : {F : Finset V // B F},FullSimplex.HomologyModule (k:=k) (missing U F.val)) :=
  LinearContraction.directSum (fun F : {F : Finset V // B F} =>
    FullSimplex.contraction (k := k) (missing U F.val))

def fiberVertical (hB : Simplicial.Downward B) : Module.End k (FiberModule (k:=k) B U) :=
  (fiberEquiv B U).toLinearMap.comp ((vertical B U hB).comp (fiberEquiv B U).symm.toLinearMap)

theorem horizontalContraction_actual (z : totalModule (k:=k) B U) :
    (horizontalContraction B U).d (fiberEquiv B U z)=fiberEquiv B U (horizontal B U z) := by
  have he : (horizontalContraction (k:=k) B U).d.comp (fiberEquiv B U).toLinearMap=
      (fiberEquiv B U).toLinearMap.comp (horizontal B U) := by
    apply (totalBasis (k:=k) B U).ext
    rintro ⟨⟨Q,F⟩,hF⟩
    have hQ := ((intersection_iff_subset B U Q F).mp hF).2
    change (horizontalContraction (k := k) B U).d
        (fiberEquiv (k := k) B U (totalBasis (k := k) B U ⟨(Q,F),hF⟩))=
      fiberEquiv (k := k) B U
        (horizontal (k := k) B U (totalBasis (k := k) B U ⟨(Q,F),hF⟩))
    erw [fiberEquiv_basis_lof (k := k) B U ⟨F,hF.1⟩ ⟨Q,hQ⟩,
      horizontalContraction,LinearContraction.directSum_d_lof,FullSimplex.contraction_d]
    apply (fiberEquiv B U).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    rw [fiberEquiv_symm_lof_val,idealTotalDifferential_val,totalFaceBasis_val]
    simp only [horizontal,LinearMap.codRestrict_apply,LinearMap.domRestrict_apply,
      totalBasis_val,ambientHorizontal,ambientBasis,Module.Basis.tensorProduct_apply,
      LinearMap.rTensor_tmul]
  exact LinearMap.congr_fun he z

def eraseVertexIndex (hB : Simplicial.Downward B)
    (a : Σ F : {F : Finset V // B F},{Q : Finset R // FullSimplex.faces (missing U F.val) Q})
    (v : {v // v∈a.1.val}) :
    Σ F : {F : Finset V // B F},{Q : Finset R // FullSimplex.faces (missing U F.val) Q} :=
  ⟨⟨a.1.val.erase v.val,hB (Finset.erase_subset _ _) a.1.property⟩,
    a.2.val,a.2.property.trans (missing_mono U (Finset.erase_subset _ _))⟩

theorem fiberVertical_basis (hB : Simplicial.Downward B)
    (a : Σ F : {F : Finset V // B F},{Q : Finset R // FullSimplex.faces (missing U F.val) Q}) :
    fiberVertical (k:=k) B U hB (fiberBasis B U a)=
      (-1:k)^a.2.val.card •
        ∑ v : {v // v∈a.1.val},TauCeti.ExteriorAlgebra.basisEraseSign v.val a.1.val •
          fiberBasis B U (eraseVertexIndex B U hB a v) := by
  apply (fiberEquiv B U).symm.injective
  simp only [fiberVertical,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply,map_smul,map_sum,map_zsmul_unit]
  apply Subtype.ext
  simp only [Submodule.coe_smul,Submodule.coe_sum,Submodule.coe_smul_of_tower]
  rw [show (fiberEquiv (k:=k) B U).symm (fiberBasis B U a)=
      totalBasis B U ⟨(a.2.val,a.1.val),
        (intersection_iff_subset B U _ _).mpr ⟨a.1.property,a.2.property⟩⟩ by
    apply (fiberEquiv B U).injective
    rw [LinearEquiv.apply_symm_apply,fiberEquiv_basis]]
  simp only [vertical,LinearMap.codRestrict_apply,LinearMap.domRestrict_apply,totalBasis_val]
  rw [ambientVertical_basis]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  rw [show (fiberEquiv (k:=k) B U).symm (fiberBasis B U (eraseVertexIndex B U hB a v))=
      totalBasis B U ⟨((eraseVertexIndex B U hB a v).2.val,(eraseVertexIndex B U hB a v).1.val),
        (intersection_iff_subset B U _ _).mpr
          ⟨(eraseVertexIndex B U hB a v).1.property,(eraseVertexIndex B U hB a v).2.property⟩⟩ by
    apply (fiberEquiv B U).injective
    rw [LinearEquiv.apply_symm_apply,fiberEquiv_basis]]
  rw [totalBasis_val]
  rfl

theorem fiberVertical_decreases (hB : Simplicial.Downward B) :
    DegreeDecreasing (fiberBasis (k:=k) B U) (fun a => a.1.val.card) (fiberVertical B U hB) := by
  apply degreeDecreasing_of_mem_span
  intro a
  rw [fiberVertical_basis]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro v _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨eraseVertexIndex B U hB a v,
    Finset.card_erase_lt_of_mem v.property,rfl⟩

theorem horizontalHomotopy_nonincreasing :
    DegreeNonincreasing (fiberBasis (k:=k) B U) (fun a => a.1.val.card)
      (horizontalContraction B U).h := by
  intro a b hab
  change a.1.val.card < b.1.val.card at hab
  have hne : a.1≠b.1 := by
    intro h
    rw [h] at hab
    exact Nat.lt_irrefl _ hab
  rw [show fiberBasis (k := k) B U a=
      DirectSum.lof k {F : Finset V // B F}
        (fun F => TotalFaceModule (k := k) (FullSimplex.faces (missing U F.val))) a.1
          (totalFaceBasis (k := k) (FullSimplex.faces (missing U a.1.val)) a.2) from
      FourPapers.directSum_basis_apply
        (fun F : {F : Finset V // B F} =>
          totalFaceBasis (k := k) (FullSimplex.faces (missing U F.val))) a.1 a.2,
    horizontalContraction,LinearContraction.directSum_h_lof]
  change (totalFaceBasis (FullSimplex.faces (missing U b.1.val))).repr
    ((DirectSum.lof k _ (fun F : {F : Finset V // B F} =>
      TotalFaceModule (FullSimplex.faces (missing U F.val))) a.1
        ((FullSimplex.contraction (missing U a.1.val)).h
          (totalFaceBasis (FullSimplex.faces (missing U a.1.val)) a.2))) b.1) b.2=0
  simp only [DirectSum.lof_eq_of,DirectSum.of_eq_of_ne _ _ _ (Ne.symm hne),map_zero,Finsupp.zero_apply]

theorem horizontalPerturbed_square (hB : Simplicial.Downward B) :
    (((horizontalContraction (k:=k) B U).d+fiberVertical (k:=k) B U hB :
        Module.End k (FiberModule (k:=k) B U)) *
      ((horizontalContraction (k:=k) B U).d+fiberVertical (k:=k) B U hB :
        Module.End k (FiberModule (k:=k) B U)))=0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨x,rfl⟩ := (fiberEquiv (k:=k) B U).surjective z
  have hc (x : totalModule (k:=k) B U) :
      (((horizontalContraction (k := k) B U).d+fiberVertical (k := k) B U hB :
        Module.End k (FiberModule (k := k) B U))) (fiberEquiv (k := k) B U x)=
        fiberEquiv (k := k) B U
          ((horizontal (k := k) B U+vertical (k := k) B U hB :
            Module.End k (totalModule (k := k) B U)) x) := by
    simp only [LinearMap.add_apply,horizontalContraction_actual,fiberVertical,
      LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply,map_add]
  have hsquare : (horizontal (k := k) B U+vertical (k := k) B U hB :
      Module.End k (totalModule (k := k) B U))
      ((horizontal (k := k) B U+vertical (k := k) B U hB :
        Module.End k (totalModule (k := k) B U)) x)=0 :=
    LinearMap.congr_fun (differential_square (k := k) B U hB) x
  change ((horizontalContraction (k := k) B U).d+fiberVertical (k := k) B U hB :
      Module.End k (FiberModule (k := k) B U))
    (((horizontalContraction (k := k) B U).d+fiberVertical (k := k) B U hB :
      Module.End k (FiberModule (k := k) B U)) (fiberEquiv (k := k) B U x))=0
  rw [hc,hc,hsquare,map_zero]

def horizontalTransferred (hB : Simplicial.Downward B) : LinearDeformationRetract (R:=k)
    (M:=FiberModule (k:=k) B U)
    (H:=⨁F : {F : Finset V // B F},FullSimplex.HomologyModule (k:=k) (missing U F.val)) :=
  (horizontalContraction B U).perturbByDegree (fiberBasis B U) (fun a => a.1.val.card)
    (fiberVertical B U hB) (fiberVertical_decreases B U hB)
    (horizontalHomotopy_nonincreasing B U) (horizontalPerturbed_square B U hB)

def relativeIndexEquiv :
    (Σ F : {F : Finset V // B F},FullSimplex.HomologyIndex (missing U F.val)) ≃
      {F : Finset V // relativeFaces B U F} where
  toFun a := ⟨a.1.val,a.1.property,a.2.property⟩
  invFun F := ⟨⟨F.val,F.property.1⟩,PUnit.unit,F.property.2⟩
  left_inv a := by rcases a with ⟨F,⟨z,h⟩⟩; cases z; rfl
  right_inv _ := rfl

/-- The surviving horizontal module is the literal relative face module,
not a newly declared copy of its homology. -/
def relativeEquiv :
    (⨁F : {F : Finset V // B F},FullSimplex.HomologyModule (k:=k) (missing U F.val)) ≃ₗ[k]
      TotalFaceModule (k:=k) (relativeFaces B U) :=
  (DFinsupp.basis (fun F : {F : Finset V // B F} =>
    (Finsupp.basisSingleOne : Module.Basis (FullSimplex.HomologyIndex (missing U F.val)) k _))).equiv
      (totalFaceBasis (relativeFaces B U)) (relativeIndexEquiv B U)

theorem fiberBasis_lof
    (a : Σ F : {F : Finset V // B F},{Q : Finset R // FullSimplex.faces (missing U F.val) Q}) :
    fiberBasis (k := k) B U a=
      DirectSum.lof k {F : Finset V // B F}
        (fun F => TotalFaceModule (k := k) (FullSimplex.faces (missing U F.val))) a.1
          (totalFaceBasis (k := k) (FullSimplex.faces (missing U a.1.val)) a.2) :=
  FourPapers.directSum_basis_apply
    (fun F : {F : Finset V // B F} =>
      totalFaceBasis (k := k) (FullSimplex.faces (missing U F.val))) a.1 a.2

def horizontalProjection : FiberModule (k:=k) B U →ₗ[k] TotalFaceModule (k := k) (relativeFaces B U) :=
  (relativeEquiv (k := k) B U).toLinearMap.comp (horizontalContraction (k := k) B U).projection

theorem horizontalProjection_basis
    (a : Σ F : {F : Finset V // B F},{Q : Finset R // FullSimplex.faces (missing U F.val) Q}) :
    horizontalProjection (k:=k) B U (fiberBasis B U a)=
      if hF : missing U a.1.val=∅ then totalFaceBasis (relativeFaces B U) ⟨a.1.val,a.1.property,hF⟩
      else 0 := by
  rw [fiberBasis_lof (k := k) B U a]
  change relativeEquiv (k := k) B U ((horizontalContraction (k := k) B U).projection _)=_
  rw [horizontalContraction,LinearContraction.directSum_projection_lof,
    FullSimplex.contraction_projection_basis]
  split_ifs with hF
  · have hb :
        (DFinsupp.basis (fun F : {F : Finset V // B F} =>
          (Finsupp.basisSingleOne : Module.Basis
            (FullSimplex.HomologyIndex (missing U F.val)) k
            (FullSimplex.HomologyModule (k := k) (missing U F.val)))))
          ⟨a.1,⟨PUnit.unit,hF⟩⟩ =
        DirectSum.lof k {F : Finset V // B F}
          (fun F => FullSimplex.HomologyModule (k := k) (missing U F.val)) a.1
            (Finsupp.single ⟨PUnit.unit,hF⟩ 1) :=
      FourPapers.directSum_basis_apply
        (fun F : {F : Finset V // B F} =>
          (Finsupp.basisSingleOne : Module.Basis
            (FullSimplex.HomologyIndex (missing U F.val)) k
            (FullSimplex.HomologyModule (k := k) (missing U F.val))))
        a.1 ⟨PUnit.unit,hF⟩
    rw [← hb]
    exact Module.Basis.equiv_apply
      (b := DFinsupp.basis (fun F : {F : Finset V // B F} =>
        (Finsupp.basisSingleOne : Module.Basis (FullSimplex.HomologyIndex (missing U F.val)) k _)))
      (b' := totalFaceBasis (k := k) (relativeFaces B U))
      (e := relativeIndexEquiv B U) (i := ⟨a.1,⟨PUnit.unit,hF⟩⟩)
  · simp only [map_zero]

theorem horizontalProjection_natural (hB : Simplicial.Downward B) :
    (horizontalProjection (k:=k) B U).comp (fiberVertical (k := k) B U hB)=
      (projectedTotalDifferential (k := k) (relativeFaces B U)).comp (horizontalProjection (k := k) B U) := by
  apply (fiberBasis (k:=k) B U).ext
  intro a
  simp only [LinearMap.comp_apply]
  by_cases hF : missing U a.1.val=∅
  · have hQ : a.2.val=∅ := Finset.subset_empty.mp (hF ▸ a.2.property)
    rw [fiberVertical_basis,map_smul,map_sum,horizontalProjection_basis,dif_pos hF,hQ]
    simp only [Finset.card_empty,pow_zero,one_smul,map_zsmul_unit]
    apply Subtype.ext
    rw [projectedTotalDifferential_val,totalFaceBasis_val,face_boundary_basis_sum,map_sum]
    simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower,map_zsmul_unit]
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    rw [horizontalProjection_basis]
    split_ifs with hv
    · dsimp only [eraseVertexIndex] at hv ⊢
      calc
        _ = Simplicial.basis (a.1.val.erase v.val) :=
          totalFaceBasis_val (k := k) (relativeFaces B U)
            ⟨a.1.val.erase v.val,hB (Finset.erase_subset _ _) a.1.property,hv⟩
        _ = _ := by
          simp only [faceProjection_basis,relativeFaces,
            hB (Finset.erase_subset _ _) a.1.property,hv,and_self,if_true]
    · dsimp only [eraseVertexIndex] at hv ⊢
      simp only [ZeroMemClass.coe_zero,faceProjection_basis,relativeFaces,
        hB (Finset.erase_subset _ _) a.1.property,hv,and_false,if_false]
  · rw [horizontalProjection_basis,dif_neg hF,map_zero,fiberVertical_basis,map_smul,map_sum]
    refine (congrArg (fun z : TotalFaceModule (k:=k) (relativeFaces B U) =>
      (-1:k)^a.2.val.card • z) ?_).trans (smul_zero _)
    apply Finset.sum_eq_zero
    intro v _
    rw [map_zsmul_unit,horizontalProjection_basis]
    have hv : missing U (a.1.val.erase v.val)≠∅ := by
      intro h
      apply hF
      exact Finset.subset_empty.mp (h ▸ missing_mono U (Finset.erase_subset _ _))
    dsimp only [eraseVertexIndex]
    rw [dif_neg hv,smul_zero]

def relativeDifferentialOnFibers : Module.End k
    (⨁F : {F : Finset V // B F},FullSimplex.HomologyModule (k:=k) (missing U F.val)) :=
  (relativeEquiv (k := k) B U).symm.toLinearMap.comp
    ((projectedTotalDifferential (k := k) (relativeFaces B U)).comp (relativeEquiv (k := k) B U).toLinearMap)

theorem horizontalProjection_block_natural (hB : Simplicial.Downward B) :
    (horizontalContraction (k:=k) B U).projection.comp (fiberVertical (k := k) B U hB)=
      (relativeDifferentialOnFibers (k := k) B U).comp (horizontalContraction (k := k) B U).projection := by
  apply LinearMap.ext
  intro x
  apply (relativeEquiv (k := k) B U).injective
  change horizontalProjection (k := k) B U (fiberVertical (k := k) B U hB x)=
    relativeEquiv (k := k) B U ((relativeEquiv (k := k) B U).symm
      (projectedTotalDifferential (k := k) (relativeFaces B U) (horizontalProjection (k := k) B U x)))
  rw [LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun (horizontalProjection_natural B U hB) x

theorem horizontalTransferred_target (hB : Simplicial.Downward B) :
    (horizontalTransferred (k:=k) B U hB).targetD=relativeDifferentialOnFibers (k := k) B U :=
  (horizontalContraction (k := k) B U).transferredDifferential_eq_of_natural_projection
    (fiberVertical (k := k) B U hB) (relativeDifferentialOnFibers (k := k) B U)
    (horizontalProjection_block_natural B U hB) _
    ((horizontalContraction (k := k) B U).leftPerturbationUnit_val (fiberBasis B U)
      (fun a => a.1.val.card) (fiberVertical (k := k) B U hB) (fiberVertical_decreases B U hB)
      (horizontalHomotopy_nonincreasing B U))

/-- The source is the literal Čech tensor-face module and the target is
the actual relative face module. The following theorem identifies its
target differential with the literal projected simplicial boundary. -/
def relativeDeformation (hB : Simplicial.Downward B) : LinearDeformationRetract (R:=k)
    (M:=totalModule (k:=k) B U) (H:=TotalFaceModule (k := k) (relativeFaces B U)) :=
  ((horizontalTransferred (k := k) B U hB).changeTarget (relativeEquiv (k := k) B U)).changeSource (fiberEquiv (k := k) B U).symm

theorem relativeDeformation_target (hB : Simplicial.Downward B) :
    (relativeDeformation (k:=k) B U hB).targetD=projectedTotalDifferential (k := k) (relativeFaces B U) := by
  apply LinearMap.ext
  intro x
  change relativeEquiv (k := k) B U ((horizontalTransferred (k := k) B U hB).targetD ((relativeEquiv (k := k) B U).symm x))=_
  rw [horizontalTransferred_target]
  change relativeEquiv (k := k) B U ((relativeEquiv (k := k) B U).symm
    (projectedTotalDifferential (k := k) (relativeFaces B U)
      (relativeEquiv (k := k) B U ((relativeEquiv (k := k) B U).symm x))))=_
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

theorem relativeDeformation_source (hB : Simplicial.Downward B) :
    (relativeDeformation (k:=k) B U hB).sourceD=horizontal B U+vertical B U hB := by
  apply LinearMap.ext
  intro x
  change (fiberEquiv (k := k) B U).symm
    (((horizontalContraction (k := k) B U).d+fiberVertical (k := k) B U hB) (fiberEquiv (k := k) B U x))=_
  rw [LinearMap.add_apply,horizontalContraction_actual,map_add]
  simp only [fiberVertical,LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply,LinearMap.add_apply]

end FourPapers.CechFace

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.CechGradedHorizontal -/
section

/-! # Homological degrees in the horizontal Čech comparison -/

section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.CechFace
open Classical CommAlg FourPapers.Sublattice HomologicalPerturbation
open scoped TensorProduct DirectSum
universe u
variable {k V R : Type u} [CommRing k] [Fintype V] [LinearOrder V]
  [Fintype R] [LinearOrder R]
  (B : Finset V → Prop) (U : R → Finset V)

def pairDegree (a : {a : Finset R × Finset V // pairFaces B U a}) : ℤ :=
  (a.val.1.card:ℤ)+a.val.2.card

def fiberDegree
    (a : Σ F : {F : Finset V // B F},{Q : Finset R // FullSimplex.faces (missing U F.val) Q}) : ℤ :=
  (a.2.val.card:ℤ)+a.1.val.card

def horizontalTargetBasis : Module.Basis
    (ΣF : {F : Finset V // B F},FullSimplex.HomologyIndex (missing U F.val)) k
    (⨁F : {F : Finset V // B F},FullSimplex.HomologyModule (k:=k) (missing U F.val)) :=
  DFinsupp.basis (fun F => Finsupp.basisSingleOne)

theorem horizontalTargetBasis_lof
    (a : ΣF : {F : Finset V // B F},FullSimplex.HomologyIndex (missing U F.val)) :
    horizontalTargetBasis (k := k) B U a=
      DirectSum.lof k {F : Finset V // B F}
        (fun F => FullSimplex.HomologyModule (k := k) (missing U F.val)) a.1
          (Finsupp.single a.2 1) :=
  FourPapers.directSum_basis_apply
    (fun F : {F : Finset V // B F} =>
      (Finsupp.basisSingleOne : Module.Basis
        (FullSimplex.HomologyIndex (missing U F.val)) k
        (FullSimplex.HomologyModule (k := k) (missing U F.val)))) a.1 a.2

def horizontalTargetDegree
    (a : ΣF : {F : Finset V // B F},FullSimplex.HomologyIndex (missing U F.val)) : ℤ := a.1.val.card

def totalPiece (p : ℕ) : Submodule k (totalModule (k:=k) B U) :=
  Grading.Piece (totalBasis (k := k) B U) (pairDegree B U) p

theorem fiber_lof_degree (F : {F : Finset V // B F}) (q : ℕ)
    (x : TotalFaceModule (k:=k) (FullSimplex.faces (missing U F.val)))
    (hx : x∈totalFacePiece (k := k) (FullSimplex.faces (missing U F.val)) q) :
    DirectSum.lof k _ (fun F : {F : Finset V // B F} =>
      TotalFaceModule (k := k) (FullSimplex.faces (missing U F.val))) F x ∈
        Grading.Piece (fiberBasis (k := k) B U) (fiberDegree B U) ((q:ℤ)+F.val.card) := by
  have hx' : x∈Grading.Piece (totalFaceBasis (k := k) (FullSimplex.faces (missing U F.val)))
      (fun Q : {Q // FullSimplex.faces (missing U F.val) Q} => (Q.val.card:ℤ)+F.val.card)
      ((q:ℤ)+F.val.card) :=
    piece_regrade (totalFaceBasis (k := k) (FullSimplex.faces (missing U F.val)))
      (fun Q : {Q : Finset R // FullSimplex.faces (missing U F.val) Q} => Q.val.card)
      q (fun q : ℕ => (q : ℤ) + F.val.card)
      (by simpa only [totalFacePiece_eq_basis_span] using! hx)
  apply map_mem_piece_of_basis (totalFaceBasis (k := k) (FullSimplex.faces (missing U F.val)))
    (fiberBasis (k := k) B U)
    (fun Q : {Q : Finset R // FullSimplex.faces (missing U F.val) Q} =>
      (Q.val.card : ℤ) + F.val.card) (fiberDegree B U)
    (DirectSum.lof k _ (fun F : {F : Finset V // B F} =>
      TotalFaceModule (k := k) (FullSimplex.faces (missing U F.val))) F) _ ((q : ℤ) + F.val.card) hx'
  intro Q
  have hm : fiberBasis (k := k) B U ⟨F,Q⟩ ∈
      Grading.Piece (fiberBasis (k := k) B U) (fiberDegree B U)
        ((Q.val.card : ℤ) + F.val.card) :=
    Grading.basis_mem_piece (fiberBasis (k := k) B U) (fiberDegree B U) ⟨F,Q⟩
  exact Eq.mp (congrArg (fun y : FiberModule (k := k) B U =>
    y ∈ Grading.Piece (fiberBasis (k := k) B U) (fiberDegree B U)
      ((Q.val.card : ℤ) + F.val.card)) (fiberBasis_lof (k := k) B U ⟨F,Q⟩)) hm

theorem horizontal_h_degree
    (a : Σ F : {F : Finset V // B F},{Q : Finset R // FullSimplex.faces (missing U F.val) Q}) :
    (horizontalContraction (k:=k) B U).h (fiberBasis (k := k) B U a)∈
      Grading.Piece (fiberBasis (k := k) B U) (fiberDegree B U) (fiberDegree B U a+1) := by
  rw [fiberBasis_lof,horizontalContraction,LinearContraction.directSum_h_lof]
  have hface : totalFaceBasis (k := k) (FullSimplex.faces (missing U a.1.val)) a.2 ∈
      totalFacePiece (k := k) (FullSimplex.faces (missing U a.1.val)) a.2.val.card := by
    change (totalFaceBasis (k := k) (FullSimplex.faces (missing U a.1.val)) a.2).val ∈
      Simplicial.Chains (FullSimplex.faces (missing U a.1.val)) a.2.val.card
    rw [totalFaceBasis_val]
    exact Simplicial.basis_mem a.2.property rfl
  have hh := fiber_lof_degree (k := k) B U a.1 (a.2.val.card+1)
    ((FullSimplex.contraction (k := k) (missing U a.1.val)).h
      (totalFaceBasis (k := k) (FullSimplex.faces (missing U a.1.val)) a.2))
    (FullSimplex.contraction_h_raises (k := k) (missing U a.1.val) a.2.val.card _ hface)
  simpa only [fiberDegree,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm] using! hh

theorem fiberVertical_degree (hB : Simplicial.Downward B)
    (a : Σ F : {F : Finset V // B F},{Q : Finset R // FullSimplex.faces (missing U F.val) Q}) :
    fiberVertical (k:=k) B U hB (fiberBasis (k := k) B U a)∈
      Grading.Piece (fiberBasis (k := k) B U) (fiberDegree B U) (fiberDegree B U a-1) := by
  rw [fiberVertical_basis]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro v _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨eraseVertexIndex B U hB a v,?_,rfl⟩
  change (a.2.val.card:ℤ)+(a.1.val.erase v.val).card=(a.2.val.card:ℤ)+a.1.val.card-1
  have hc := Finset.card_erase_add_one v.property
  omega

theorem horizontal_inclusion_degree
    (a : ΣF : {F : Finset V // B F},FullSimplex.HomologyIndex (missing U F.val)) :
    (horizontalContraction (k:=k) B U).inclusion (horizontalTargetBasis (k := k) B U a)∈
      Grading.Piece (fiberBasis (k := k) B U) (fiberDegree B U) (horizontalTargetDegree B U a) := by
  rw [horizontalTargetBasis_lof,horizontalContraction,LinearContraction.directSum_inclusion_lof]
  change DirectSum.lof k {F : Finset V // B F}
    (fun F => TotalFaceModule (k := k) (FullSimplex.faces (missing U F.val))) a.1
    ((FullSimplex.contraction (k := k) (missing U a.1.val)).inclusion (Finsupp.single a.2 1))∈_
  rw [FullSimplex.contraction_inclusion_basis,
    ← fiberBasis_lof (k := k) B U ⟨a.1,⟨∅,Finset.empty_subset _⟩⟩]
  apply Submodule.subset_span
  exact ⟨⟨a.1,∅,Finset.empty_subset _⟩,by simp only [Set.mem_setOf_eq,fiberDegree,horizontalTargetDegree,
    Finset.card_empty,Nat.cast_zero,zero_add],rfl⟩

theorem horizontal_projection_degree
    (a : Σ F : {F : Finset V // B F},{Q : Finset R // FullSimplex.faces (missing U F.val) Q}) :
    (horizontalContraction (k:=k) B U).projection (fiberBasis (k := k) B U a)∈
      Grading.Piece (horizontalTargetBasis (k := k) B U) (horizontalTargetDegree B U) (fiberDegree B U a) := by
  rw [fiberBasis_lof,horizontalContraction,LinearContraction.directSum_projection_lof,
    FullSimplex.contraction_projection_basis]
  split_ifs with hF
  · have hQ : a.2.val=∅ := Finset.subset_empty.mp (hF ▸ a.2.property)
    rw [← horizontalTargetBasis_lof (k := k) B U ⟨a.1,⟨PUnit.unit,hF⟩⟩]
    apply Submodule.subset_span
    exact ⟨⟨a.1,⟨PUnit.unit,hF⟩⟩,by simp only [Set.mem_setOf_eq,fiberDegree,horizontalTargetDegree,hQ,
      Finset.card_empty,Nat.cast_zero,zero_add],rfl⟩
  · rw [map_zero]
    exact Submodule.zero_mem _

theorem fiberEquiv_preserves (p : ℤ) (x : totalModule (k:=k) B U)
    (hx : x∈Grading.Piece (totalBasis (k := k) B U) (pairDegree B U) p) :
    fiberEquiv (k := k) B U x∈Grading.Piece (fiberBasis (k := k) B U) (fiberDegree B U) p := by
  refine map_mem_piece_of_basis (totalBasis (k := k) B U) (fiberBasis (k := k) B U)
    (pairDegree B U) (fiberDegree B U) (fiberEquiv (k := k) B U).toLinearMap ?_ p hx
  intro a
  have he : fiberEquiv (k := k) B U (totalBasis (k := k) B U a)=
      fiberBasis (k := k) B U (fiberIndexEquiv B U a) :=
    Module.Basis.equiv_apply (b := totalBasis (k := k) B U)
      (b' := fiberBasis (k := k) B U) (e := fiberIndexEquiv B U) (i := a)
  simp only [LinearEquiv.coe_coe]
  erw [he]
  simpa only [fiberDegree,pairDegree,fiberIndexEquiv] using!
    (Grading.basis_mem_piece (fiberBasis (k := k) B U) (fiberDegree B U)
      (fiberIndexEquiv B U a))

theorem fiberEquiv_symm_preserves (p : ℤ) (x : FiberModule (k:=k) B U)
    (hx : x∈Grading.Piece (fiberBasis (k := k) B U) (fiberDegree B U) p) :
    (fiberEquiv (k := k) B U).symm x∈Grading.Piece (totalBasis (k := k) B U) (pairDegree B U) p := by
  refine map_mem_piece_of_basis (fiberBasis (k := k) B U) (totalBasis (k := k) B U)
    (fiberDegree B U) (pairDegree B U) (fiberEquiv (k := k) B U).symm.toLinearMap ?_ p hx
  intro a
  have he : (fiberEquiv (k := k) B U).symm (fiberBasis (k := k) B U a)=
      totalBasis (k := k) B U ((fiberIndexEquiv B U).symm a) := by
    apply (fiberEquiv (k := k) B U).injective
    rw [LinearEquiv.apply_symm_apply]
    symm
    calc
      _ = fiberBasis (k := k) B U
          (fiberIndexEquiv B U ((fiberIndexEquiv B U).symm a)) :=
        Module.Basis.equiv_apply (b := totalBasis (k := k) B U)
          (b' := fiberBasis (k := k) B U) (e := fiberIndexEquiv B U)
          (i := (fiberIndexEquiv B U).symm a)
      _ = _ := congrArg (fiberBasis (k := k) B U)
        ((fiberIndexEquiv B U).apply_symm_apply a)
  simp only [LinearEquiv.coe_coe]
  erw [he]
  simpa only [fiberDegree,pairDegree,fiberIndexEquiv] using!
    (Grading.basis_mem_piece (totalBasis (k := k) B U) (pairDegree B U)
      ((fiberIndexEquiv B U).symm a))

theorem relativeEquiv_preserves (p : ℕ)
    (x : ⨁F : {F : Finset V // B F},FullSimplex.HomologyModule (k:=k) (missing U F.val))
    (hx : x∈Grading.Piece (horizontalTargetBasis (k := k) B U) (horizontalTargetDegree B U) (p:ℤ)) :
    relativeEquiv (k := k) B U x∈totalFacePiece (k := k) (relativeFaces B U) p := by
  rw [totalFacePiece_eq_basis_span]
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨a,ha,rfl⟩ := hz
      have he : relativeEquiv (k := k) B U (horizontalTargetBasis (k := k) B U a)=
          totalFaceBasis (k := k) (relativeFaces B U) (relativeIndexEquiv B U a) :=
        Module.Basis.equiv_apply (b := horizontalTargetBasis (k := k) B U)
          (b' := totalFaceBasis (k := k) (relativeFaces B U))
          (e := relativeIndexEquiv B U) (i := a)
      apply Submodule.subset_span
      refine ⟨relativeIndexEquiv B U a,?_,he.symm⟩
      change (a.1.val.card : ℤ) = (p : ℤ) at ha
      change a.1.val.card = p
      exact Int.ofNat_inj.mp ha
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add z w hz hw ihz ihw =>
      simpa only [map_add] using Submodule.add_mem _ ihz ihw
  | smul c z hz ih =>
      simpa only [map_smul] using Submodule.smul_mem _ c ih

theorem relativeEquiv_symm_preserves (p : ℕ)
    (x : TotalFaceModule (k:=k) (relativeFaces B U))
    (hx : x∈totalFacePiece (k := k) (relativeFaces B U) p) :
    (relativeEquiv (k := k) B U).symm x∈
      Grading.Piece (horizontalTargetBasis (k := k) B U) (horizontalTargetDegree B U) (p:ℤ) := by
  rw [totalFacePiece_eq_basis_span] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨F,hF,rfl⟩ := hz
      have he : (relativeEquiv (k := k) B U).symm
          (totalFaceBasis (k := k) (relativeFaces B U) F)=
          horizontalTargetBasis (k := k) B U ((relativeIndexEquiv B U).symm F) := by
        apply (relativeEquiv (k := k) B U).injective
        rw [LinearEquiv.apply_symm_apply]
        symm
        calc
          _ = totalFaceBasis (k := k) (relativeFaces B U)
              (relativeIndexEquiv B U ((relativeIndexEquiv B U).symm F)) :=
            Module.Basis.equiv_apply (b := horizontalTargetBasis (k := k) B U)
              (b' := totalFaceBasis (k := k) (relativeFaces B U))
              (e := relativeIndexEquiv B U) (i := (relativeIndexEquiv B U).symm F)
          _ = _ := congrArg (totalFaceBasis (k := k) (relativeFaces B U))
            ((relativeIndexEquiv B U).apply_symm_apply F)
      apply Submodule.subset_span
      refine ⟨(relativeIndexEquiv B U).symm F,?_,he.symm⟩
      change F.val.card = p at hF
      change (F.val.card : ℤ) = (p : ℤ)
      exact congrArg (fun q : ℕ => (q : ℤ)) hF
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add z w hz hw ihz ihw =>
      simpa only [map_add] using Submodule.add_mem _ ihz ihw
  | smul c z hz ih =>
      simpa only [map_smul] using Submodule.smul_mem _ c ih

theorem horizontal_d_degree
    (a : Σ F : {F : Finset V // B F},{Q : Finset R // FullSimplex.faces (missing U F.val) Q}) :
    (horizontalContraction (k:=k) B U).d (fiberBasis (k := k) B U a)∈
      Grading.Piece (fiberBasis (k := k) B U) (fiberDegree B U) (fiberDegree B U a-1) := by
  rw [fiberBasis_lof,horizontalContraction,LinearContraction.directSum_d_lof,
    FullSimplex.contraction_d]
  cases hp : a.2.val.card with
  | zero =>
      have hQ : a.2.val=∅ := Finset.card_eq_zero.mp hp
      have hz : idealTotalDifferential (k := k) (FullSimplex.downward (missing U a.1.val))
          (totalFaceBasis (k:=k) (FullSimplex.faces (missing U a.1.val)) a.2)=0 := by
        apply Subtype.ext
        change Simplicial.boundary
          (totalFaceBasis (k := k) (FullSimplex.faces (missing U a.1.val)) a.2).val = 0
        rw [totalFaceBasis_val]
        exact Simplicial.boundary_zero_degree_zero (Simplicial.basis_mem a.2.property hp)
      rw [hz,map_zero]
      exact Submodule.zero_mem _
  | succ q =>
      have hx : idealTotalDifferential (k := k) (FullSimplex.downward (missing U a.1.val))
          (totalFaceBasis (k:=k) (FullSimplex.faces (missing U a.1.val)) a.2)∈
          totalFacePiece (k := k) (FullSimplex.faces (missing U a.1.val)) q := by
        change Simplicial.boundary
          (totalFaceBasis (k := k) (FullSimplex.faces (missing U a.1.val)) a.2).val ∈
            Simplicial.Chains (FullSimplex.faces (missing U a.1.val)) q
        rw [totalFaceBasis_val]
        exact Simplicial.boundary_mem (FullSimplex.downward _)
          (Simplicial.basis_mem a.2.property hp)
      have he := fiber_lof_degree (k := k) B U a.1 q _ hx
      convert he using 1
      simp only [fiberDegree,hp,Nat.cast_add,Nat.cast_one]
      congr 1
      omega

theorem relativeDeformation_inclusion_degree (hB : Simplicial.Downward B)
    (p : ℕ) (x : TotalFaceModule (k:=k) (relativeFaces B U))
    (hx : x∈totalFacePiece (k := k) (relativeFaces B U) p) :
    (relativeDeformation (k := k) B U hB).inclusion x∈totalPiece (k := k) B U p := by
  apply fiberEquiv_symm_preserves (k := k) B U (p:ℤ)
  apply (horizontalContraction (k := k) B U).transferredInclusion_mem_piece
    (fiberBasis (k := k) B U) (horizontalTargetBasis (k := k) B U) (fiberDegree B U) (horizontalTargetDegree B U)
    (fiberVertical (k := k) B U hB) _
    ((horizontalContraction (k := k) B U).leftPerturbationUnit_val _ _ _
      (fiberVertical_decreases (k := k) B U hB) (horizontalHomotopy_nonincreasing (k := k) B U))
    (horizontal_h_degree (k := k) B U) (fiberVertical_degree (k := k) B U hB)
    (horizontal_inclusion_degree (k := k) B U) (p:ℤ)
  exact relativeEquiv_symm_preserves (k := k) B U p x hx

theorem relativeDeformation_projection_degree (hB : Simplicial.Downward B)
    (p : ℕ) (x : totalModule (k:=k) B U) (hx : x∈totalPiece (k := k) B U p) :
    (relativeDeformation (k := k) B U hB).projection x∈totalFacePiece (k := k) (relativeFaces B U) p := by
  apply relativeEquiv_preserves (k := k) B U p
  apply (horizontalContraction (k := k) B U).transferredProjection_mem_piece
    (fiberBasis (k := k) B U) (horizontalTargetBasis (k := k) B U) (fiberDegree B U) (horizontalTargetDegree B U)
    (fiberVertical (k := k) B U hB) _
    ((horizontalContraction (k := k) B U).leftPerturbationUnit_val _ _ _
      (fiberVertical_decreases (k := k) B U hB) (horizontalHomotopy_nonincreasing (k := k) B U))
    (horizontal_h_degree (k := k) B U) (fiberVertical_degree (k := k) B U hB)
    (horizontal_projection_degree (k := k) B U) (p:ℤ)
  exact fiberEquiv_preserves (k := k) B U (p:ℤ) x hx

theorem relativeDeformation_homotopy_degree (hB : Simplicial.Downward B)
    (p : ℕ) (x : totalModule (k:=k) B U) (hx : x∈totalPiece (k := k) B U p) :
    (relativeDeformation (k := k) B U hB).homotopy x∈totalPiece (k := k) B U (p+1) := by
  apply fiberEquiv_symm_preserves (k := k) B U ((p+1:ℕ):ℤ)
  simp only [Nat.cast_add,Nat.cast_one]
  apply (horizontalContraction (k := k) B U).transferredHomotopy_mem_piece
    (fiberBasis (k := k) B U) (fiberDegree B U) (fiberVertical (k := k) B U hB) _
    ((horizontalContraction (k := k) B U).leftPerturbationUnit_val _ _ _
      (fiberVertical_decreases (k := k) B U hB) (horizontalHomotopy_nonincreasing (k := k) B U))
    (horizontal_h_degree (k := k) B U) (fiberVertical_degree (k := k) B U hB) (p:ℤ)
  exact fiberEquiv_preserves (k := k) B U (p:ℤ) x hx

theorem totalDifferential_lowers (hB : Simplicial.Downward B) (p : ℕ)
    (x : totalModule (k:=k) B U) (hx : x∈totalPiece (k := k) B U (p+1)) :
    (horizontal (k := k) B U+vertical (k := k) B U hB) x∈totalPiece (k := k) B U p := by
  rw [← relativeDeformation_source (k := k) B U hB]
  apply fiberEquiv_symm_preserves (k := k) B U (p:ℤ)
  have hx' := fiberEquiv_preserves (k := k) B U ((p+1:ℕ):ℤ) x hx
  have hx'' := piece_regrade (fiberBasis (k := k) B U) (fiberDegree B U) ((p+1:ℕ):ℤ)
    (fun p:ℤ=>p-1) hx'
  simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hx''
  apply map_mem_piece_of_basis (fiberBasis (k := k) B U) (fiberBasis (k := k) B U)
    (fun a=>fiberDegree B U a-1) (fiberDegree B U)
    ((horizontalContraction (k := k) B U).d+fiberVertical (k := k) B U hB) _ (p:ℤ) hx''
  intro a
  exact Submodule.add_mem _ (horizontal_d_degree (k := k) B U a) (fiberVertical_degree (k := k) B U hB a)

theorem relativeDifferential_square (hB : Simplicial.Downward B) :
    projectedTotalDifferential (k:=k) (relativeFaces B U)*
      projectedTotalDifferential (k := k) (relativeFaces B U)=0 := by
  rw [← relativeDeformation_target (k := k) B U hB]
  exact (relativeDeformation (k := k) B U hB).target_square

abbrev TotalHomology (hB : Simplicial.Downward B) (p : ℕ) :=
  GradedRetractionHomology.Homology (totalPiece (k:=k) B U)
    (horizontal (k := k) B U+vertical (k := k) B U hB) (differential_square (k := k) B U hB)
    (totalDifferential_lowers (k := k) B U hB) p

abbrev RelativeHomology (hB : Simplicial.Downward B) (p : ℕ) :=
  GradedRetractionHomology.Homology (totalFacePiece (k:=k) (relativeFaces B U))
    (projectedTotalDifferential (k := k) (relativeFaces B U)) (relativeDifferential_square (k := k) B U hB)
    (projectedTotalDifferential_lowers_piece (k := k) (relativeFaces B U)) p

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
/-- The horizontal comparison is a degreewise homology equivalence with
the literal relative face complex, retaining all augmented degrees. -/
def horizontalHomologyEquiv (hB : Simplicial.Downward B) (p : ℕ) :
    TotalHomology (k:=k) B U hB p ≃ₗ[k] RelativeHomology (k:=k) B U hB p := by
  have hsource : ∀p x,x∈totalPiece (k := k) B U (p+1)→
      (relativeDeformation (k:=k) B U hB).sourceD x∈totalPiece (k := k) B U p := by
    rw [relativeDeformation_source]
    exact totalDifferential_lowers (k := k) B U hB
  have htarget : ∀p x,x∈totalFacePiece (k := k) (relativeFaces B U) (p+1)→
      (relativeDeformation (k:=k) B U hB).targetD x∈totalFacePiece (k := k) (relativeFaces B U) p := by
    rw [relativeDeformation_target]
    exact projectedTotalDifferential_lowers_piece (k := k) (relativeFaces B U)
  let e := GradedRetractionHomology.deformationEquiv
    (totalPiece (k := k) B U) (totalFacePiece (k := k) (relativeFaces B U))
    (relativeDeformation (k := k) B U hB) hsource htarget
    (relativeDeformation_inclusion_degree (k := k) B U hB)
    (relativeDeformation_projection_degree (k := k) B U hB)
    (relativeDeformation_homotopy_degree (k := k) B U hB) p
  let es := GradedRetractionHomology.homologyEquivOfDifferential
    (totalPiece (k := k) B U) (relativeDeformation (k := k) B U hB).sourceD
    (relativeDeformation (k := k) B U hB).source_square hsource
    (horizontal (k := k) B U + vertical (k := k) B U hB)
    (relativeDeformation_source (k := k) B U hB)
    (differential_square (k := k) B U hB) (totalDifferential_lowers (k := k) B U hB) p
  let et := GradedRetractionHomology.homologyEquivOfDifferential
    (totalFacePiece (k := k) (relativeFaces B U)) (relativeDeformation (k := k) B U hB).targetD
    (relativeDeformation (k := k) B U hB).target_square htarget
    (projectedTotalDifferential (k := k) (relativeFaces B U))
    (relativeDeformation_target (k := k) B U hB)
    (relativeDifferential_square (k := k) B U hB)
    (projectedTotalDifferential_lowers_piece (k := k) (relativeFaces B U)) p
  exact es.symm.trans (e.trans et)

end FourPapers.CechFace

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.RelativeFaceCone -/
section

/-!
# Removing a genuine cone subcomplex

The relative complex has the actual remaining faces and projected boundary.
Exterior creation on the cone, extended by its coordinate projection,
provides the comparison homotopy. This keeps the augmented empty-face term
and all integer incidence signs.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.RelativeFaceCone
open Classical CommAlg FourPapers.Sublattice HomologicalPerturbation
universe u
variable {k V : Type u} [CommRing k] [Fintype V] [LinearOrder V]
  (G U : Finset V → Prop) (hG : Simplicial.Downward G) (hU : Simplicial.Downward U)
  (hUG : ∀F,U F→G F) (a : V) (ha : ∀F,U F→U (insert a F))

def remaining (F : Finset V) : Prop := G F ∧ ¬U F

def projection : TotalFaceModule (k:=k) G →ₗ[k] TotalFaceModule (k:=k) (remaining G U) :=
  ((faceProjection (remaining G U)).comp (TotalFaceModule (k:=k) G).subtype).codRestrict _
    (fun x => faceProjection_mem _ _)

def rawInclusion : TotalFaceModule (k:=k) (remaining G U) →ₗ[k] TotalFaceModule (k:=k) G :=
  (TotalFaceModule (k:=k) (remaining G U)).subtype.codRestrict _
    (fun x => Submodule.span_mono (Set.image_mono (fun F hF => hF.1)) x.property)

theorem projection_zero_on_discarded {x : Simplicial.Ambient V k}
    (hx : x∈TotalFaceModule (k:=k) U) : faceProjection (remaining G U) x=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hF,rfl⟩ := hx
      rw [faceProjection_basis,if_neg (fun h => h.2 hF)]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy,add_zero]
  | smul c x hx ih => rw [map_smul,ih,smul_zero]

theorem discarded_zero_on_remaining {x : Simplicial.Ambient V k}
    (hx : x∈TotalFaceModule (k:=k) (remaining G U)) : faceProjection U x=0 := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨F,hF,rfl⟩ := hx; rw [faceProjection_basis,if_neg hF.2]
  | zero => exact map_zero _
  | add x y hx hy ihx ihy => rw [map_add,ihx,ihy,add_zero]
  | smul c x hx ih => rw [map_smul,ih,smul_zero]

theorem split_faces {x : Simplicial.Ambient V k} (hx : x∈TotalFaceModule (k:=k) G) :
    x=faceProjection U x+faceProjection (remaining G U) x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hF,rfl⟩ := hx
      change G F at hF
      by_cases hu : U F <;> simp only [faceProjection_basis,remaining,hF,hu,
        true_and,not_true_eq_false,not_false_eq_true,if_true,if_false,zero_add,add_zero]
  | zero => simp
  | add x y hx hy ihx ihy =>
      calc
        x+y=(faceProjection U x+faceProjection (remaining G U) x)+
            (faceProjection U y+faceProjection (remaining G U) y) := congrArg₂ (·+·) ihx ihy
        _=faceProjection U (x+y)+faceProjection (remaining G U) (x+y) := by
          rw [map_add,map_add]
          abel
  | smul c x hx ih =>
      calc
        c • x=c • (faceProjection U x+faceProjection (remaining G U) x) :=
          congrArg (fun z : Simplicial.Ambient V k => c • z) ih
        _=faceProjection U (c • x)+faceProjection (remaining G U) (c • x) := by
          rw [map_smul,map_smul,smul_add]

theorem raw_retract : (projection (k:=k) G U).comp (rawInclusion G U)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact faceProjection_eq_self _ x.property

include hU in
theorem projection_chain :
    (projectedTotalDifferential (k:=k) (remaining G U)).comp (projection G U)=
      (projection G U).comp (idealTotalDifferential hG) := by
  apply (totalFaceBasis (k:=k) G).ext
  intro F
  apply Subtype.ext
  change faceProjection (remaining G U)
    (Simplicial.boundary (faceProjection (remaining G U) (totalFaceBasis (k := k) G F).val))=
      faceProjection (remaining G U)
        (Simplicial.boundary (totalFaceBasis (k := k) G F).val)
  rw [totalFaceBasis_val]
  by_cases hu : U F.val
  · rw [faceProjection_basis,if_neg (fun h => h.2 hu),map_zero,map_zero]
    symm
    exact projection_zero_on_discarded G U
      (boundary_mem_basisSpan hU (Submodule.subset_span ⟨F.val,hu,rfl⟩))
  · rw [faceProjection_basis,if_pos ⟨F.property,hu⟩]

include hG hU in
theorem relative_square : projectedTotalDifferential (k:=k) (remaining G U)*
    projectedTotalDifferential (remaining G U)=0 := by
  apply LinearMap.ext
  intro x
  have hr : projection (k:=k) G U (rawInclusion G U x)=x :=
    LinearMap.congr_fun (raw_retract (k:=k) G U) x
  have hc (z : TotalFaceModule (k:=k) G) :
      projectedTotalDifferential (remaining G U) (projection G U z)=
        projection G U (idealTotalDifferential hG z) :=
    LinearMap.congr_fun (projection_chain G U hG hU) z
  change projectedTotalDifferential (remaining G U)
    (projectedTotalDifferential (remaining G U) x)=0
  rw [← hr,hc,hc]
  have hz : idealTotalDifferential hG (idealTotalDifferential hG (rawInclusion G U x))=0 :=
    Subtype.ext (Simplicial.boundary_boundary _)
  rw [hz,map_zero]

include ha in
theorem creation_discarded_mem {x : Simplicial.Ambient V k}
    (hx : x∈TotalFaceModule (k:=k) U) : Simplicial.creation a x∈TotalFaceModule U := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,hF,rfl⟩ := hx
      rw [Simplicial.creation_basis]
      split_ifs
      · exact Submodule.zero_mem _
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨insert a F,ha F hF,rfl⟩)
  | zero => simpa only [map_zero] using (TotalFaceModule (k:=k) U).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

def homotopy : Module.End k (TotalFaceModule (k:=k) G) :=
  ((Simplicial.creation a).comp ((faceProjection U).comp
    (TotalFaceModule (k:=k) G).subtype)).codRestrict _ (fun x =>
      Submodule.span_mono (Set.image_mono (fun F hF => hUG F hF))
        (creation_discarded_mem U a ha (faceProjection_mem U x.val)))

theorem homotopy_projection_zero :
    (projection (k:=k) G U).comp (homotopy G U hUG a ha)=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact projection_zero_on_discarded G U
    (creation_discarded_mem U a ha (faceProjection_mem U x.val))

def inclusion : TotalFaceModule (k:=k) (remaining G U) →ₗ[k] TotalFaceModule (k:=k) G :=
  rawInclusion G U-(homotopy G U hUG a ha).comp
    ((idealTotalDifferential hG).comp (rawInclusion G U))

include hU in
theorem homotopy_identity :
    idealTotalDifferential (k:=k) hG*homotopy G U hUG a ha+
      homotopy G U hUG a ha*idealTotalDifferential hG=
        1-(inclusion G U hG hUG a ha).comp (projection G U) := by
  apply (totalFaceBasis (k:=k) G).ext
  intro F
  apply Subtype.ext
  change Simplicial.boundary
      (Simplicial.creation a (faceProjection U (totalFaceBasis (k := k) G F).val))+
    Simplicial.creation a
      (faceProjection U (Simplicial.boundary (totalFaceBasis (k := k) G F).val))=
    (totalFaceBasis (k := k) G F).val-
      (faceProjection (remaining G U) (totalFaceBasis (k := k) G F).val-
        Simplicial.creation a (faceProjection U (Simplicial.boundary
          (faceProjection (remaining G U) (totalFaceBasis (k := k) G F).val))))
  rw [totalFaceBasis_val]
  by_cases hu : U F.val
  · have hb : Simplicial.boundary (Simplicial.basis (k:=k) F.val)∈TotalFaceModule (k := k) U :=
      boundary_mem_basisSpan hU (Submodule.subset_span ⟨F.val,hu,rfl⟩)
    simp only [faceProjection_basis,remaining,F.property,hu,not_true_eq_false,
      true_and,and_false,if_true,if_false,map_zero,sub_zero]
    rw [faceProjection_eq_self U hb,Simplicial.boundary_creation,sub_add_cancel]
  · simp only [faceProjection_basis,remaining,F.property,hu,not_false_eq_true,
      true_and,and_true,if_true,if_false,map_zero,zero_add]
    abel

/-- Actual deformation retract onto the relative face complex. -/
def deformation : LinearDeformationRetract (R:=k)
    (M:=TotalFaceModule (k:=k) G) (H:=TotalFaceModule (k:=k) (remaining G U)) where
  sourceD := idealTotalDifferential hG
  targetD := projectedTotalDifferential (remaining G U)
  inclusion := inclusion G U hG hUG a ha
  projection := projection G U
  homotopy := homotopy G U hUG a ha
  source_square := by apply LinearMap.ext; intro x; exact Subtype.ext (Simplicial.boundary_boundary x.val)
  target_square := relative_square G U hG hU
  projection_chain := (projection_chain G U hG hU).symm
  retract := by
    rw [inclusion,LinearMap.comp_sub,raw_retract,
      ← LinearMap.comp_assoc,homotopy_projection_zero,LinearMap.zero_comp]
    apply LinearMap.ext
    intro x
    exact sub_zero x
  deformation := homotopy_identity G U hG hU hUG a ha
  inclusion_chain := by
    let D := idealTotalDifferential (k:=k) hG
    let H := homotopy (k:=k) G U hUG a ha
    let I := inclusion (k:=k) G U hG hUG a ha
    let P := projection (k:=k) G U
    let d := projectedTotalDifferential (k:=k) (remaining G U)
    have hDD : D*D=0 := by apply LinearMap.ext; intro x; exact Subtype.ext (Simplicial.boundary_boundary x.val)
    have hid : D*H+H*D=1-I.comp P := homotopy_identity G U hG hU hUG a ha
    have hc : D*(I.comp P)=(I.comp P)*D := by
      apply (sub_right_inj (a:=D)).mp
      calc
        D-D*(I.comp P)=D*(1-I.comp P) := by
          change D-D.comp (I.comp P)=D.comp (LinearMap.id-I.comp P)
          rw [LinearMap.comp_sub,LinearMap.comp_id]
        _=D*(D*H+H*D) := congrArg (fun x => D*x) hid.symm
        _=(D*H)*D := by
          simp only [mul_add,← mul_assoc,hDD,zero_mul,zero_add]
        _=(D*H+H*D)*D := by
          simp only [add_mul,mul_assoc,hDD,mul_zero,add_zero]
        _=(1-I.comp P)*D := congrArg (fun x => x*D) hid
        _=D-(I.comp P)*D := by
          change (LinearMap.id-I.comp P).comp D=D-(I.comp P).comp D
          rw [LinearMap.sub_comp,LinearMap.id_comp]
    apply LinearMap.ext
    intro x
    have he := LinearMap.congr_fun hc (rawInclusion G U x)
    change D (I (P (rawInclusion G U x)))=I (P (D (rawInclusion G U x))) at he
    have hr : P (rawInclusion (k:=k) G U x)=x :=
      LinearMap.congr_fun (raw_retract (k:=k) G U) x
    have hp : d (P (rawInclusion (k:=k) G U x))=
        P (D (rawInclusion G U x)) :=
      LinearMap.congr_fun (projection_chain (k:=k) G U hG hU) (rawInclusion G U x)
    rw [hr,← hp,hr] at he
    exact he

theorem projection_preserves (p : ℕ) (x : TotalFaceModule (k:=k) G)
    (hx : x∈totalFacePiece G p) : projection G U x∈totalFacePiece (remaining G U) p :=
  faceProjection_preserves_degree (remaining G U) G p hx

theorem homotopy_raises (p : ℕ) (x : TotalFaceModule (k:=k) G)
    (hx : x∈totalFacePiece G p) : homotopy G U hUG a ha x∈totalFacePiece G (p+1) := by
  change Simplicial.creation a (faceProjection U x.val)∈Simplicial.Chains G (p+1)
  apply Simplicial.chains_mono hUG
  exact creation_mem_chains a ha (faceProjection_preserves_degree U G p hx)

theorem rawInclusion_preserves (p : ℕ) (x : TotalFaceModule (k:=k) (remaining G U))
    (hx : x∈totalFacePiece (remaining G U) p) : rawInclusion G U x∈totalFacePiece G p :=
  Simplicial.chains_mono (fun F hF=>hF.1) p hx

theorem inclusion_preserves (p : ℕ) (x : TotalFaceModule (k:=k) (remaining G U))
    (hx : x∈totalFacePiece (remaining G U) p) : inclusion G U hG hUG a ha x∈totalFacePiece G p := by
  change rawInclusion G U x-homotopy G U hUG a ha
    (idealTotalDifferential hG (rawInclusion G U x))∈_
  apply Submodule.sub_mem _ (rawInclusion_preserves G U p x hx)
  cases p with
  | zero =>
      have hd : idealTotalDifferential hG (rawInclusion G U x)=0 := by
        apply Subtype.ext
        exact Simplicial.boundary_zero_degree_zero (rawInclusion_preserves G U 0 x hx)
      rw [hd,map_zero]
      exact Submodule.zero_mem _
  | succ p =>
      apply homotopy_raises G U hUG a ha p
      exact Simplicial.boundary_mem hG (rawInclusion_preserves G U (p+1) x hx)

set_option backward.isDefEq.respectTransparency true in
/-- Degreewise homology of Γ is the actual relative homology Γ/U,
including its augmented degree zero; no ungraded-to-graded inference occurs. -/
def homologyEquiv (p : ℕ) :
    GradedRetractionHomology.Homology (totalFacePiece (k:=k) G)
      (idealTotalDifferential hG)
      (by apply LinearMap.ext; intro x; exact Subtype.ext (Simplicial.boundary_boundary x.val))
      (fun p x hx=>Simplicial.boundary_mem hG hx) p ≃ₗ[k]
    GradedRetractionHomology.Homology (totalFacePiece (k:=k) (remaining G U))
      (projectedTotalDifferential (remaining G U)) (relative_square G U hG hU)
      (projectedTotalDifferential_lowers_piece (remaining G U)) p :=
  GradedRetractionHomology.deformationEquiv
    (totalFacePiece (k := k) G) (totalFacePiece (k := k) (remaining G U))
    (deformation G U hG hU hUG a ha)
    (fun p x hx=>Simplicial.boundary_mem hG hx)
    (projectedTotalDifferential_lowers_piece (remaining G U))
    (inclusion_preserves G U hG hUG a ha)
    (projection_preserves G U) (homotopy_raises G U hUG a ha) p

end FourPapers.RelativeFaceCone

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.CechCoverHomology -/
section

/-!
# The actual cover union and augmented Čech homology

The outside cover is a cone, and the horizontal Čech contraction identifies
the remaining relative chain complex with the genuine Čech tensor complex.
Both comparisons are degreewise and retain the augmented degree zero.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.CechFace
open Classical CommAlg FourPapers.Sublattice
universe u
variable {k V R : Type u} [CommRing k] [Fintype V] [LinearOrder V]
  [Fintype R] [LinearOrder R]

def actualFaceCyclesEquiv (P : Finset V→Prop) (hP : Simplicial.Downward P) (p : ℕ) :
    GradedRetractionHomology.cycles (totalFacePiece (k:=k) P) (idealTotalDifferential (k := k) hP) p ≃ₗ[k]
      augmentedFaceCycles (k:=k) P p where
  toFun x := ⟨x.val.val,x.property.1,congrArg Subtype.val x.property.2⟩
  invFun x := ⟨⟨x.val,chains_mem_basisSpan x.property.1⟩,x.property.1,Subtype.ext x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
def actualFaceHomologyEquiv (P : Finset V→Prop) (hP : Simplicial.Downward P) (p : ℕ) :
    GradedRetractionHomology.Homology (totalFacePiece (k:=k) P) (idealTotalDifferential (k := k) hP)
      (by apply LinearMap.ext; intro x; exact Subtype.ext (Simplicial.boundary_boundary x.val))
      (fun p x hx=>Simplicial.boundary_mem hP hx) p ≃ₗ[k]
        AugmentedFaceHomology (k:=k) P hP p := by
  apply Submodule.Quotient.equiv (R := k) (R₂ := k)
    (M := GradedRetractionHomology.cycles (totalFacePiece (k := k) P)
      (idealTotalDifferential (k := k) hP) p)
    (N := augmentedFaceCycles (k := k) P p)
    (σ₁₂ := RingHom.id k) (σ₂₁ := RingHom.id k)
    _ _ (actualFaceCyclesEquiv (k := k) P hP p)
  apply Submodule.ext
  intro z
  constructor
  · rintro ⟨x,⟨y,rfl⟩,rfl⟩
    exact ⟨⟨y.val.val,y.property⟩,Subtype.ext rfl⟩
  · rintro ⟨y,rfl⟩
    let y' : totalFacePiece (k:=k) P (p+1) :=
      ⟨⟨y.val,chains_mem_basisSpan y.property⟩,y.property⟩
    exact ⟨_,⟨y',rfl⟩,Subtype.ext rfl⟩

/-- Equality of the actual face predicates transports the projected chain
complex and its degreewise quotient homology. -/
def projectedFaceHomologyEquivOfFaces (P Q : Finset V → Prop) (h : P = Q)
    (hP : projectedTotalDifferential (k := k) P * projectedTotalDifferential (k := k) P = 0)
    (hQ : projectedTotalDifferential (k := k) Q * projectedTotalDifferential (k := k) Q = 0)
    (p : ℕ) :
    GradedRetractionHomology.Homology (totalFacePiece (k := k) P)
      (projectedTotalDifferential (k := k) P) hP
      (projectedTotalDifferential_lowers_piece P) p ≃ₗ[k]
    GradedRetractionHomology.Homology (totalFacePiece (k := k) Q)
      (projectedTotalDifferential (k := k) Q) hQ
      (projectedTotalDifferential_lowers_piece Q) p := by
  subst Q
  exact LinearEquiv.refl k _

variable (B : Finset V→Prop) (U : R→Finset V) (S : Finset V)

def outsideCover (F : Finset V) : Prop := F⊆S ∧ coverFaces U F
def coverUnion (F : Finset V) : Prop := B F ∨ outsideCover U S F

theorem outsideCover_downward : Simplicial.Downward (outsideCover U S) := by
  intro F G hGF hF
  exact ⟨hGF.trans hF.1,hF.2.mono (missing_mono U hGF)⟩

theorem coverUnion_downward (hB : Simplicial.Downward B) :
    Simplicial.Downward (coverUnion B U S) := by
  intro F G hGF hF
  exact hF.elim (fun h=>Or.inl (hB hGF h))
    (fun h=>Or.inr (outsideCover_downward U S hGF h))

theorem outsideCover_cone (a : V) (ha : a∈S) (hUa : ∀r,a∉U r)
    (F : Finset V) (hF : outsideCover U S F) : outsideCover U S (insert a F) := by
  obtain ⟨r,hr⟩ := hF.2
  refine ⟨Finset.insert_subset ha hF.1,⟨r,(mem_missing U _ r).mpr ?_⟩⟩
  rw [Finset.disjoint_insert_left]
  exact ⟨hUa r,(mem_missing U F r).mp hr⟩

theorem coverRemaining_eq (hBS : ∀F,B F→F⊆S) :
    RelativeFaceCone.remaining (coverUnion B U S) (outsideCover U S)=relativeFaces B U := by
  funext F
  apply propext
  constructor
  · rintro ⟨hF,hn⟩
    have hb : B F := hF.elim id (fun h=>(hn h).elim)
    exact ⟨hb,Finset.not_nonempty_iff_eq_empty.mp (fun h=>hn ⟨hBS F hb,h⟩)⟩
  · rintro ⟨hB,hF⟩
    refine ⟨Or.inl hB,?_⟩
    intro h
    have hm : (missing U F).Nonempty := h.2
    rw [hF] at hm
    exact Finset.not_nonempty_empty hm

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
/-- The full cover comparison, not just equality of Betti ranks. -/
def coverUnionHomologyEquiv (hB : Simplicial.Downward B) (hBS : ∀F,B F→F⊆S)
    (a : V) (ha : a∈S) (hUa : ∀r,a∉U r) (p : ℕ) :
    AugmentedFaceHomology (k:=k) (coverUnion B U S) (coverUnion_downward B U S hB) p ≃ₗ[k]
      TotalHomology (k:=k) B U hB p := by
  let G := coverUnion B U S
  let A := outsideCover U S
  let hG := coverUnion_downward B U S hB
  let hA := outsideCover_downward U S
  have e := RelativeFaceCone.homologyEquiv (k:=k) G A hG hA
    (fun _ h=>Or.inr h) a (outsideCover_cone U S a ha hUa) p
  have er :
      GradedRetractionHomology.Homology (totalFacePiece (k:=k) G)
        (idealTotalDifferential (k := k) hG)
        (by apply LinearMap.ext; intro x; exact Subtype.ext (Simplicial.boundary_boundary x.val))
        (fun p x hx=>Simplicial.boundary_mem hG hx) p ≃ₗ[k]
          RelativeHomology (k:=k) B U hB p := by
    exact e.trans (projectedFaceHomologyEquivOfFaces (k := k)
      (RelativeFaceCone.remaining G A) (relativeFaces B U)
      (coverRemaining_eq B U S hBS)
      (RelativeFaceCone.relative_square (k := k) G A hG hA)
      (relativeDifferential_square (k := k) B U hB) p)
  exact (actualFaceHomologyEquiv (k := k) G hG p).symm.trans
    (er.trans (horizontalHomologyEquiv (k := k) B U hB p).symm)

end FourPapers.CechFace

end
end
end

/- BEGIN EXACT BODY: FourPapers.Common.CechGradedNerve -/
section

/-!
# The degreewise integral incidence-cover theorem

Intersection contractions concentrated in one actual face degree give
the precise homological shift. The hypotheses concern the already
constructed chain maps, and are discharged for the incidence intersections
in the separate standard and expanded incidence modules.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.CechFace.NerveReduction
open Classical CommAlg FourPapers.Sublattice HomologicalPerturbation
universe u
variable {k V R : Type u} [CommRing k] [Fintype V] [LinearOrder V]
  [Fintype R] [LinearOrder R]
  (B : Finset V→Prop) (U : R→Finset V) (K : Finset R→Prop)
  (C : ∀Q : Finset R,LinearContraction (R:=k)
    (M:=TotalFaceModule (k:=k) (intersectionFaces B U Q))
    (H:=CoefficientLineSum.line (k:=k) K Q))
  (hB : Simplicial.Downward B) (hK : Simplicial.Downward K)
  (hd : ∀Q,(C Q).d=idealTotalDifferential (k := k) (intersectionFaces_downward B U hB Q))
  (hnat : ∀P Q (hPQ : P⊆Q) (x : TotalFaceModule (k:=k) (intersectionFaces B U Q)),
    ((C P).projection (intersectionInclusion B U P Q hPQ x)).val=((C Q).projection x).val)
  (ℓ : ℕ)
  (hh : ∀Q p (x : TotalFaceModule (k:=k) (intersectionFaces B U Q)),
    x∈totalFacePiece (k := k) (intersectionFaces B U Q) p→
      (C Q).h x∈totalFacePiece (k := k) (intersectionFaces B U Q) (p+1))
  (hi : ∀Q (r : CoefficientLineSum.line (k:=k) K Q),
    (C Q).inclusion r∈totalFacePiece (k := k) (intersectionFaces B U Q) ℓ)
  (hp : ∀Q (F : {F : Finset V // intersectionFaces B U Q F}),
    F.val.card≠ℓ→((C Q).projection (totalFaceBasis (k := k) (intersectionFaces B U Q) F)).val=0)

def blockDegree (a : ΣQ : Finset R,{F : Finset V // intersectionFaces B U Q F}) : ℤ :=
  (a.1.card:ℤ)+a.2.val.card

def nerveDegree (F : {F : Finset R // K F}) : ℤ := (F.val.card:ℤ)+ℓ

def gradedContraction : LinearContraction (R:=k)
    (M:=BlockModule (k:=k) B U) (H:=TotalFaceModule (k:=k) K) :=
  (intersectionContraction B U C).changeTarget (targetEquiv (k := k) K)

theorem blockBasis_lof
    (a : ΣQ : Finset R,{F : Finset V // intersectionFaces B U Q F}) :
    blockBasis (k := k) B U a=
      DirectSum.lof k (Finset R)
        (fun Q => TotalFaceModule (k := k) (intersectionFaces B U Q)) a.1
          (totalFaceBasis (k := k) (intersectionFaces B U a.1) a.2) :=
  FourPapers.directSum_basis_apply
    (fun Q : Finset R => totalFaceBasis (k := k) (intersectionFaces B U Q)) a.1 a.2

theorem block_lof_degree (Q : Finset R) (p : ℕ)
    (x : TotalFaceModule (k:=k) (intersectionFaces B U Q))
    (hx : x∈totalFacePiece (k := k) (intersectionFaces B U Q) p) :
    DirectSum.lof k (Finset R) (fun Q=>TotalFaceModule (k := k) (intersectionFaces B U Q)) Q x∈
      Grading.Piece (blockBasis (k := k) B U) (blockDegree B U) ((Q.card:ℤ)+p) := by
  have hx' : x ∈ Grading.Piece (totalFaceBasis (k := k) (intersectionFaces B U Q))
      (fun F : {F : Finset V // intersectionFaces B U Q F} =>
        (Q.card : ℤ) + F.val.card) ((Q.card : ℤ) + p) :=
    piece_regrade (totalFaceBasis (k := k) (intersectionFaces B U Q))
      (fun F : {F : Finset V // intersectionFaces B U Q F} => F.val.card)
      p (fun p : ℕ => (Q.card : ℤ) + p)
      (by simpa only [totalFacePiece_eq_basis_span,basisDegreePiece,Grading.Piece] using hx)
  apply map_mem_piece_of_basis (totalFaceBasis (k := k) (intersectionFaces B U Q))
    (blockBasis (k := k) B U)
    (fun F : {F : Finset V // intersectionFaces B U Q F} =>
      (Q.card : ℤ) + F.val.card) (blockDegree B U)
    (DirectSum.lof k (Finset R)
      (fun Q => TotalFaceModule (k := k) (intersectionFaces B U Q)) Q)
    _ ((Q.card : ℤ) + p) hx'
  intro F
  have hm : blockBasis (k := k) B U ⟨Q,F⟩ ∈
      Grading.Piece (blockBasis (k := k) B U) (blockDegree B U)
        ((Q.card : ℤ) + F.val.card) :=
    Grading.basis_mem_piece (blockBasis (k := k) B U) (blockDegree B U) ⟨Q,F⟩
  exact Eq.mp (congrArg (fun y : BlockModule (k := k) B U =>
    y ∈ Grading.Piece (blockBasis (k := k) B U) (blockDegree B U)
      ((Q.card : ℤ) + F.val.card)) (blockBasis_lof (k := k) B U ⟨Q,F⟩)) hm

include hh in
theorem homotopy_degree (a : ΣQ : Finset R,{F : Finset V // intersectionFaces B U Q F}) :
    (gradedContraction B U K C).h (blockBasis (k := k) B U a)∈
      Grading.Piece (blockBasis (k := k) B U) (blockDegree B U) (blockDegree B U a+1) := by
  change (intersectionContraction B U C).h (blockBasis (k := k) B U a)∈_
  rw [blockBasis_lof,intersectionContraction,LinearContraction.directSum_h_lof]
  have hmem : (signedBlockContraction B U C a.1).h
      (totalFaceBasis (k := k) (intersectionFaces B U a.1) a.2)∈
        totalFacePiece (k := k) (intersectionFaces B U a.1) (a.2.val.card+1) := by
    have hface : totalFaceBasis (k := k) (intersectionFaces B U a.1) a.2 ∈
        totalFacePiece (k := k) (intersectionFaces B U a.1) a.2.val.card := by
      change (totalFaceBasis (k := k) (intersectionFaces B U a.1) a.2).val ∈
        Simplicial.Chains (intersectionFaces B U a.1) a.2.val.card
      rw [totalFaceBasis_val]
      exact Simplicial.basis_mem a.2.property rfl
    unfold signedBlockContraction
    split_ifs
    · exact hh a.1 _ _ hface
    · exact Submodule.neg_mem _ (hh a.1 _ _ hface)
  have he := block_lof_degree B U a.1 (a.2.val.card+1) _ hmem
  simpa only [blockDegree,Nat.cast_add,Nat.cast_one,add_assoc] using he

theorem perturbation_degree (a : ΣQ : Finset R,{F : Finset V // intersectionFaces B U Q F}) :
    blockHorizontal (k:=k) B U (blockBasis (k := k) B U a)∈
      Grading.Piece (blockBasis (k := k) B U) (blockDegree B U) (blockDegree B U a-1) := by
  rw [blockHorizontal_basis]
  apply Submodule.sum_mem
  intro r _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨eraseCoverIndex B U a r,?_,rfl⟩
  change ((a.1.erase r.val).card:ℤ)+a.2.val.card=(a.1.card:ℤ)+a.2.val.card-1
  have he := Finset.card_erase_add_one r.property
  omega

def lineOne (Q : Finset R) (hQ : K Q) : CoefficientLineSum.line (k:=k) K Q :=
  ⟨1,by simp only [CoefficientLineSum.line,if_pos hQ,Submodule.mem_top]⟩

theorem targetEquiv_symm_basis (Q : {Q : Finset R // K Q}) :
    (targetEquiv (k:=k) K).symm (totalFaceBasis (k := k) K Q)=
      DirectSum.lof k (Finset R) (fun Q => ↥(CoefficientLineSum.line (k := k) K Q)) Q.val (lineOne K Q.val Q.property) := by
  apply (targetEquiv (k := k) K).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [totalFaceBasis_val,targetEquiv_lof_val]
  exact (one_smul k _).symm

include hi in
theorem inclusion_degree (Q : {Q : Finset R // K Q}) :
    (gradedContraction (k:=k) B U K C).inclusion (totalFaceBasis (k := k) K Q)∈
      Grading.Piece (blockBasis (k := k) B U) (blockDegree B U) (nerveDegree K ℓ Q) := by
  change (intersectionContraction B U C).inclusion
    ((targetEquiv (k := k) K).symm (totalFaceBasis (k := k) K Q))∈_
  rw [targetEquiv_symm_basis,intersectionContraction,LinearContraction.directSum_inclusion_lof]
  have he : (signedBlockContraction B U C Q.val).inclusion=(C Q.val).inclusion := by
    unfold signedBlockContraction
    split_ifs <;> rfl
  rw [he]
  exact block_lof_degree B U Q.val ℓ _ (hi Q.val _)

include hp in
theorem projection_degree (a : ΣQ : Finset R,{F : Finset V // intersectionFaces B U Q F}) :
    (gradedContraction (k:=k) B U K C).projection (blockBasis (k := k) B U a)∈
      Grading.Piece (totalFaceBasis (k := k) K) (nerveDegree K ℓ) (blockDegree B U a) := by
  change projection B U K C (blockBasis (k := k) B U a)∈_
  by_cases hF : a.2.val.card=ℓ
  · by_cases hQ : K a.1
    · have he : projection (k:=k) B U K C (blockBasis (k := k) B U a)=
          ((C a.1).projection (totalFaceBasis (k := k) (intersectionFaces B U a.1) a.2)).val •
            totalFaceBasis (k := k) K ⟨a.1,hQ⟩ := by
        apply Subtype.ext
        rw [projection_basis_val,Submodule.coe_smul,totalFaceBasis_val]
      rw [he]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨⟨a.1,hQ⟩,by
        change (a.1.card:ℤ)+ℓ=(a.1.card:ℤ)+a.2.val.card
        rw [hF],rfl⟩
    · have he : projection (k:=k) B U K C (blockBasis (k := k) B U a)=0 := by
        apply Subtype.ext
        rw [projection_basis_val,CoefficientLineSum.val_zero K a.1 hQ,zero_smul]
        rfl
      rw [he]
      exact Submodule.zero_mem _
  · have he : projection (k:=k) B U K C (blockBasis (k := k) B U a)=0 := by
      apply Subtype.ext
      rw [projection_basis_val,hp a.1 a.2 hF,zero_smul]
      rfl
    rw [he]
    exact Submodule.zero_mem _

def gradedDeformation : LinearDeformationRetract (R:=k)
    (M:=BlockModule (k:=k) B U) (H:=TotalFaceModule (k:=k) K) :=
  (gradedContraction B U K C).perturbByDegree (blockBasis (k := k) B U) (fun a=>a.1.card)
    (blockHorizontal B U) (blockHorizontal_decreases B U)
    (intersectionHomotopy_nonincreasing B U C) (perturbed_square B U C hB hd)

include hnat in
theorem gradedDeformation_target :
    (gradedDeformation B U K C hB hd).targetD=idealTotalDifferential (k := k) hK :=
  (gradedContraction B U K C).transferredDifferential_eq_of_natural_projection
    (blockHorizontal B U) (idealTotalDifferential (k := k) hK) (projection_horizontal B U K C hK hnat) _
    ((gradedContraction B U K C).leftPerturbationUnit_val _ _ _
      (blockHorizontal_decreases B U) (intersectionHomotopy_nonincreasing B U C))

def gradedTotalDeformation : LinearDeformationRetract (R:=k)
    (M:=totalModule (k:=k) B U) (H:=TotalFaceModule (k:=k) K) :=
  (gradedDeformation B U K C hB hd).changeSource (blockEquiv (k := k) B U).symm

theorem gradedTotal_source :
    (gradedTotalDeformation B U K C hB hd).sourceD=horizontal B U+vertical B U hB := by
  exact totalDeformation_source B U K C hB hd

include hnat in
theorem gradedTotal_target :
    (gradedTotalDeformation B U K C hB hd).targetD=idealTotalDifferential (k := k) hK :=
  gradedDeformation_target B U K C hB hK hd hnat

theorem blockEquiv_preserves (p : ℤ) (x : totalModule (k:=k) B U)
    (hx : x∈Grading.Piece (totalBasis (k := k) B U) (pairDegree B U) p) :
    blockEquiv (k := k) B U x∈Grading.Piece (blockBasis (k := k) B U) (blockDegree B U) p := by
  apply map_mem_piece_of_basis (totalBasis (k := k) B U) (blockBasis (k := k) B U) (pairDegree B U) (blockDegree B U)
    (blockEquiv (k := k) B U).toLinearMap _ p hx
  intro a
  have he : blockEquiv (k := k) B U (totalBasis (k := k) B U a)=
      blockBasis (k := k) B U (blockIndexEquiv B U a) :=
    Module.Basis.equiv_apply (b := totalBasis (k := k) B U)
      (b' := blockBasis (k := k) B U) (e := blockIndexEquiv B U) (i := a)
  simp only [LinearEquiv.coe_coe]
  erw [he]
  simpa only [blockDegree,pairDegree,blockIndexEquiv] using!
    (Grading.basis_mem_piece (blockBasis (k := k) B U) (blockDegree B U)
      (blockIndexEquiv B U a))

theorem blockEquiv_symm_preserves (p : ℤ) (x : BlockModule (k:=k) B U)
    (hx : x∈Grading.Piece (blockBasis (k := k) B U) (blockDegree B U) p) :
    (blockEquiv (k := k) B U).symm x∈Grading.Piece (totalBasis (k := k) B U) (pairDegree B U) p := by
  apply map_mem_piece_of_basis (blockBasis (k := k) B U) (totalBasis (k := k) B U) (blockDegree B U) (pairDegree B U)
    (blockEquiv (k := k) B U).symm.toLinearMap _ p hx
  intro a
  have he : (blockEquiv (k := k) B U).symm (blockBasis (k := k) B U a)=
      totalBasis (k := k) B U ((blockIndexEquiv B U).symm a) := by
    apply (blockEquiv (k := k) B U).injective
    rw [LinearEquiv.apply_symm_apply]
    symm
    calc
      _ = blockBasis (k := k) B U
          (blockIndexEquiv B U ((blockIndexEquiv B U).symm a)) :=
        Module.Basis.equiv_apply (b := totalBasis (k := k) B U)
          (b' := blockBasis (k := k) B U) (e := blockIndexEquiv B U)
          (i := (blockIndexEquiv B U).symm a)
      _ = _ := congrArg (blockBasis (k := k) B U)
        ((blockIndexEquiv B U).apply_symm_apply a)
  simp only [LinearEquiv.coe_coe]
  erw [he]
  simpa only [blockDegree,pairDegree,blockIndexEquiv] using!
    (Grading.basis_mem_piece (totalBasis (k := k) B U) (pairDegree B U)
      ((blockIndexEquiv B U).symm a))

theorem nervePiece_shift (p : ℕ) :
    Grading.Piece (totalFaceBasis (k:=k) K) (nerveDegree K ℓ) ((p+ℓ:ℕ):ℤ)=
      totalFacePiece (k := k) K p := by
  rw [totalFacePiece_eq_basis_span]
  unfold Grading.Piece nerveDegree
  congr 1
  ext F
  simp only [Set.mem_setOf_eq,Nat.cast_add,add_left_inj,Nat.cast_inj]

include hh hi in
theorem total_inclusion_degree (p : ℕ) (x : TotalFaceModule (k:=k) K)
    (hx : x∈totalFacePiece (k := k) K p) :
    (gradedTotalDeformation B U K C hB hd).inclusion x∈totalPiece B U (p+ℓ) := by
  apply blockEquiv_symm_preserves B U ((p+ℓ:ℕ):ℤ)
  apply (gradedContraction B U K C).transferredInclusion_mem_piece
    (blockBasis (k := k) B U) (totalFaceBasis (k := k) K) (blockDegree B U) (nerveDegree K ℓ)
    (blockHorizontal B U) _
    ((gradedContraction B U K C).leftPerturbationUnit_val _ _ _
      (blockHorizontal_decreases B U) (intersectionHomotopy_nonincreasing B U C))
    (homotopy_degree B U K C hh) (perturbation_degree B U)
    (inclusion_degree B U K C ℓ hi) ((p+ℓ:ℕ):ℤ)
  rwa [nervePiece_shift]

include hh hp in
theorem total_projection_degree (p : ℕ) (x : totalModule (k:=k) B U)
    (hx : x∈totalPiece B U (p+ℓ)) :
    (gradedTotalDeformation B U K C hB hd).projection x∈totalFacePiece (k := k) K p := by
  rw [← nervePiece_shift K ℓ p]
  apply (gradedContraction B U K C).transferredProjection_mem_piece
    (blockBasis (k := k) B U) (totalFaceBasis (k := k) K) (blockDegree B U) (nerveDegree K ℓ)
    (blockHorizontal B U) _
    ((gradedContraction B U K C).leftPerturbationUnit_val _ _ _
      (blockHorizontal_decreases B U) (intersectionHomotopy_nonincreasing B U C))
    (homotopy_degree B U K C hh) (perturbation_degree B U)
    (projection_degree B U K C ℓ hp) ((p+ℓ:ℕ):ℤ)
  exact blockEquiv_preserves B U _ x hx

include hh in
theorem total_homotopy_degree (p : ℕ) (x : totalModule (k:=k) B U)
    (hx : x∈totalPiece B U (p+ℓ)) :
    (gradedTotalDeformation B U K C hB hd).homotopy x∈totalPiece B U ((p+1)+ℓ) := by
  apply blockEquiv_symm_preserves B U (((p+1)+ℓ:ℕ):ℤ)
  have hdegree : (((p+1)+ℓ : ℕ) : ℤ)=((p+ℓ : ℕ) : ℤ)+1 := by omega
  rw [hdegree]
  apply (gradedContraction B U K C).transferredHomotopy_mem_piece
    (blockBasis (k := k) B U) (blockDegree B U) (blockHorizontal B U) _
    ((gradedContraction B U K C).leftPerturbationUnit_val _ _ _
      (blockHorizontal_decreases B U) (intersectionHomotopy_nonincreasing B U C))
    (homotopy_degree B U K C hh) (perturbation_degree B U) ((p+ℓ:ℕ):ℤ)
  exact blockEquiv_preserves (k := k) B U _ x hx

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
/-- Actual degreewise homology of the Čech complex, with the full shift ℓ. -/
def homologyEquiv (q : ℕ) :
    TotalHomology (k:=k) B U hB (q+ℓ) ≃ₗ[k] AugmentedFaceHomology (k:=k) K hK q := by
  let P := fun p=>totalPiece (k:=k) B U (p+ℓ)
  let Q := totalFacePiece (k:=k) K
  let D := gradedTotalDeformation B U K C hB hd
  have hsource : ∀p x,x∈P (p+1)→D.sourceD x∈P p := by
    intro p x hx
    rw [gradedTotal_source]
    apply totalDifferential_lowers B U hB (p+ℓ) x
    simpa only [P,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hx
  have htarget : ∀p x,x∈Q (p+1)→D.targetD x∈Q p := by
    rw [gradedTotal_target B U K C hB hK hd hnat]
    exact fun p x hx=>Simplicial.boundary_mem hK hx
  have he := GradedRetractionHomology.deformationEquiv P Q D hsource htarget
    (total_inclusion_degree B U K C hB hd ℓ hh hi)
    (total_projection_degree B U K C hB hd ℓ hh hp)
    (total_homotopy_degree B U K C hB hd ℓ hh) q
  have hshift : ∀ p x, x ∈ totalPiece (k := k) B U ((p+1)+ℓ) →
      (horizontal (k := k) B U+vertical (k := k) B U hB) x ∈
        totalPiece (k := k) B U (p+ℓ) := by
    intro p x hx
    apply totalDifferential_lowers (k := k) B U hB (p+ℓ) x
    have hindex : (p+1)+ℓ=(p+ℓ)+1 := by omega
    simpa only [hindex] using hx
  let shift := GradedRetractionHomology.homologyShiftEquiv
    (R := k) (M := totalModule (k := k) B U)
    (totalPiece (k := k) B U)
    (horizontal (k := k) B U+vertical (k := k) B U hB)
    (differential_square (k := k) B U hB)
    (totalDifferential_lowers (k := k) B U hB) ℓ hshift q
  let source := GradedRetractionHomology.homologyEquivOfDifferential
    (R := k) (M := totalModule (k := k) B U)
    P D.sourceD D.source_square hsource
    (horizontal (k := k) B U+vertical (k := k) B U hB)
    (gradedTotal_source (k := k) B U K C hB hd)
    (differential_square (k := k) B U hB) hshift q
  let target := GradedRetractionHomology.homologyEquivOfDifferential
    (R := k) (M := TotalFaceModule (k := k) K)
    Q D.targetD D.target_square htarget (idealTotalDifferential (k := k) hK)
    (gradedTotal_target (k := k) B U K C hB hK hd hnat)
    (by apply LinearMap.ext; intro x; exact Subtype.ext (Simplicial.boundary_boundary x.val))
    (fun p x hx => Simplicial.boundary_mem hK hx) q
  exact shift.symm.trans (source.symm.trans
    (he.trans (target.trans (actualFaceHomologyEquiv (k := k) K hK q))))

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
/-- The actual integral incidence-cover homology theorem, independent of
any choice of field or characteristic. -/
def coverHomologyEquiv (S : Finset V) (hBS : ∀F,B F→F⊆S)
    (a : V) (ha : a∈S) (hUa : ∀r,a∉U r) (q : ℕ) :
    AugmentedFaceHomology (k:=k) (coverUnion B U S) (coverUnion_downward B U S hB) (q+ℓ) ≃ₗ[k]
      AugmentedFaceHomology (k:=k) K hK q :=
  (coverUnionHomologyEquiv (k := k) B U S hB hBS a ha hUa (q+ℓ)).trans
    (homologyEquiv (k := k) B U K C hB hK hd hnat ℓ hh hi hp q)

include hh hp in
theorem total_projection_integer_degree (p : ℕ) (x : totalModule (k:=k) B U)
    (hx : x∈totalPiece B U p) :
    (gradedTotalDeformation B U K C hB hd).projection x∈
      Grading.Piece (totalFaceBasis (k := k) K) (nerveDegree K ℓ) (p:ℤ) := by
  apply (gradedContraction B U K C).transferredProjection_mem_piece
    (blockBasis (k := k) B U) (totalFaceBasis (k := k) K) (blockDegree B U) (nerveDegree K ℓ)
    (blockHorizontal B U) _
    ((gradedContraction B U K C).leftPerturbationUnit_val _ _ _
      (blockHorizontal_decreases B U) (intersectionHomotopy_nonincreasing B U C))
    (homotopy_degree B U K C hh) (perturbation_degree B U)
    (projection_degree B U K C ℓ hp) (p:ℤ)
  exact blockEquiv_preserves B U _ x hx

include hh in
theorem total_homotopy_degree_all (p : ℕ) (x : totalModule (k:=k) B U)
    (hx : x∈totalPiece B U p) :
    (gradedTotalDeformation B U K C hB hd).homotopy x∈totalPiece B U (p+1) := by
  apply blockEquiv_symm_preserves B U ((p+1:ℕ):ℤ)
  simp only [Nat.cast_add,Nat.cast_one]
  apply (gradedContraction B U K C).transferredHomotopy_mem_piece
    (blockBasis (k := k) B U) (blockDegree B U) (blockHorizontal B U) _
    ((gradedContraction B U K C).leftPerturbationUnit_val _ _ _
      (blockHorizontal_decreases B U) (intersectionHomotopy_nonincreasing B U C))
    (homotopy_degree B U K C hh) (perturbation_degree B U) (p:ℤ)
  exact blockEquiv_preserves B U _ x hx

theorem nervePiece_below (p : ℕ) (hpℓ : p<ℓ) :
    Grading.Piece (totalFaceBasis (k:=k) K) (nerveDegree K ℓ) (p:ℤ)=⊥ := by
  unfold Grading.Piece
  have he : {Q : {Q : Finset R // K Q} | nerveDegree K ℓ Q=(p:ℤ)}=∅ := by
    ext Q
    simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
    unfold nerveDegree
    omega
  rw [he,Set.image_empty,Submodule.span_empty]

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
include K C hd hh hp in
/-- The comparison includes all degrees below the shift: their actual
cycles are filled by the displayed transferred homotopy. -/
theorem totalHomology_subsingleton_below (p : ℕ) (hpℓ : p<ℓ) :
    Subsingleton (TotalHomology (k:=k) B U hB p) := by
  let D : LinearDeformationRetract (R := k)
      (M := totalModule (k := k) B U) (H := TotalFaceModule (k := k) K) :=
    gradedTotalDeformation (k := k) B U K C hB hd
  have hsource : ∀ q (x : totalModule (k := k) B U),
      x ∈ totalPiece (k := k) B U (q+1) → D.sourceD x ∈ totalPiece (k := k) B U q := by
    intro q x hx
    change (gradedTotalDeformation (k := k) B U K C hB hd).sourceD x ∈ _
    rw [gradedTotal_source (k := k) B U K C hB hd]
    exact totalDifferential_lowers (k := k) B U hB q x hx
  have hzero : ∀ x : totalModule (k := k) B U,
      x ∈ totalPiece (k := k) B U p → D.projection x=0 := by
    intro x hx
    have hm : D.projection x ∈
        Grading.Piece (totalFaceBasis (k := k) K) (nerveDegree K ℓ) (p:ℤ) :=
      total_projection_integer_degree (k := k) B U K C hB hd ℓ hh hp p x hx
    rw [nervePiece_below (k := k) K ℓ p hpℓ] at hm
    exact hm
  have hraise : ∀ x : totalModule (k := k) B U,
      x ∈ totalPiece (k := k) B U p → D.homotopy x ∈ totalPiece (k := k) B U (p+1) :=
    total_homotopy_degree_all (k := k) B U K C hB hd hh p
  letI : Subsingleton (GradedRetractionHomology.Homology (totalPiece (k := k) B U)
      D.sourceD D.source_square hsource p) :=
    GradedRetractionHomology.homology_subsingleton_of_zero_projection
      (R := k) (M := totalModule (k := k) B U) (N := TotalFaceModule (k := k) K)
      (totalPiece (k := k) B U) D hsource p hzero hraise
  let e : GradedRetractionHomology.Homology (totalPiece (k := k) B U)
      D.sourceD D.source_square hsource p ≃ₗ[k] TotalHomology (k := k) B U hB p :=
    GradedRetractionHomology.homologyEquivOfDifferential
      (R := k) (M := totalModule (k := k) B U)
      (totalPiece (k := k) B U) D.sourceD D.source_square hsource
      (horizontal (k := k) B U+vertical (k := k) B U hB)
      (gradedTotal_source (k := k) B U K C hB hd)
      (differential_square (k := k) B U hB)
      (totalDifferential_lowers (k := k) B U hB) p
  exact e.symm.injective.subsingleton

include K C hd hh hp in
theorem coverHomology_subsingleton_below (S : Finset V) (hBS : ∀F,B F→F⊆S)
    (a : V) (ha : a∈S) (hUa : ∀r,a∉U r) (p : ℕ) (hpℓ : p<ℓ) :
    Subsingleton (AugmentedFaceHomology (k:=k) (coverUnion B U S)
      (coverUnion_downward B U S hB) p) := by
  letI := totalHomology_subsingleton_below (k := k) B U K C hB hd ℓ hh hp p hpℓ
  exact (coverUnionHomologyEquiv (k := k) B U S hB hBS a ha hUa p).injective.subsingleton

end FourPapers.CechFace.NerveReduction

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegerAugmentedFaceHomology -/
section

/-! # Reduced homology in every integer degree

Negative degrees are represented by actual zero chain modules, so the
all-index realization formula does not use an unexplained truncation.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Simplicial
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

def integerFaceChains (P : Finset V → Prop) (t : ℤ) : Submodule k (Ambient V k) :=
  Submodule.span k (basis '' {F | P F ∧ (F.card:ℤ)=t})

theorem integerFaceChains_nat (P : Finset V → Prop) (p : ℕ) :
    integerFaceChains (k := k) P (p:ℤ)=Chains P p := by
  simp only [integerFaceChains,Chains,Nat.cast_inj]

theorem integerFaceChains_negative (P : Finset V → Prop) (t : ℤ) (ht : t<0) :
    integerFaceChains (k := k) P t=⊥ := by
  have hs : {F : Finset V | P F ∧ (F.card:ℤ)=t}=∅ := by
    ext F
    simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false,not_and]
    intro _ hF
    omega
  rw [integerFaceChains,hs,Set.image_empty,Submodule.span_empty]

theorem integerFaceBoundary_mem (P : Finset V → Prop) (hP : Downward P)
    (t : ℤ) (x : Ambient V k) (hx : x∈integerFaceChains P (t+1)) :
    boundary x∈integerFaceChains P t := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨F,⟨hF,hcard⟩,rfl⟩ := hx
      rw [face_boundary_basis_sum]
      apply Submodule.sum_mem
      intro v _
      apply Submodule.smul_mem
      apply Submodule.subset_span
      refine ⟨F.erase v.val,⟨hP (Finset.erase_subset _ _) hF,?_⟩,rfl⟩
      have he := Finset.card_erase_add_one v.property
      omega
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

def integerFaceCycles (P : Finset V → Prop) (t : ℤ) : Submodule k (Ambient V k) :=
  integerFaceChains P t ⊓ LinearMap.ker boundary

def integerFaceBoundary (P : Finset V → Prop) (hP : Downward P) (t : ℤ) :
    integerFaceChains (k := k) P (t+1) →ₗ[k] integerFaceCycles (k := k) P t :=
  (boundary.domRestrict (integerFaceChains P (t+1))).codRestrict _
    (fun x => ⟨integerFaceBoundary_mem P hP t x.val x.property,boundary_boundary x.val⟩)

abbrev IntegerAugmentedFaceHomology (P : Finset V → Prop) (hP : Downward P) (t : ℤ) :=
  integerFaceCycles (k := k) P t ⧸ LinearMap.range (integerFaceBoundary (k := k) P hP t)

abbrev ReducedFaceHomology (P : Finset V → Prop) (hP : Downward P) (j : ℤ) :=
  IntegerAugmentedFaceHomology (k := k) P hP (j+1)

/-- Literal equality of face predicates induces equality of the integer
chain complexes, including every negative reduced degree. -/
def reducedFaceHomologyEquivOfFaces (P Q : Finset V → Prop)
    (hP : Downward P) (hQ : Downward Q) (h : P = Q) (j : ℤ) :
    ReducedFaceHomology (k := k) P hP j ≃ₗ[k]
      ReducedFaceHomology (k := k) Q hQ j := by
  subst Q
  exact LinearEquiv.refl k _

set_option maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency true in
def integerAugmentedNatEquiv (P : Finset V → Prop) (hP : Downward P) (p : ℕ) :
    IntegerAugmentedFaceHomology (k := k) P hP (p:ℤ) ≃ₗ[k]
      AugmentedFaceHomology (k := k) P hP p := by
  have hc : integerFaceCycles (k := k) P (p:ℤ)=augmentedFaceCycles (k := k) P p := by
    rw [integerFaceCycles,augmentedFaceCycles,integerFaceChains_nat]
  have hb : integerFaceChains (k := k) P ((p : ℤ) + 1) = Chains P (p+1) := by
    rw [show (p : ℤ) + 1 = ((p+1 : ℕ) : ℤ) by omega,integerFaceChains_nat]
  let e : integerFaceCycles (k := k) P (p:ℤ) ≃ₗ[k] augmentedFaceCycles (k := k) P p :=
    LinearEquiv.ofEq _ _ hc
  have he_val (z : integerFaceCycles (k := k) P (p:ℤ)) : (e z).val=z.val :=
    LinearEquiv.coe_ofEq_apply hc z
  apply Submodule.Quotient.equiv (R := k) (R₂ := k)
    (M := integerFaceCycles (k := k) P (p:ℤ))
    (N := augmentedFaceCycles (k := k) P p)
    (σ₁₂ := RingHom.id k) (σ₂₁ := RingHom.id k) _ _ e
  apply Submodule.ext
  intro z
  constructor
  · rintro ⟨x,⟨y,rfl⟩,rfl⟩
    refine ⟨⟨y.val,?_⟩,?_⟩
    · exact Eq.mp (congrArg (fun T : Submodule k (Ambient V k) => y.val ∈ T) hb)
        y.property
    · apply Subtype.ext
      change boundary y.val =
        (e (integerFaceBoundary (k := k) P hP (p : ℤ) y)).val
      exact (he_val (integerFaceBoundary (k := k) P hP (p : ℤ) y)).symm
  · rintro ⟨y,rfl⟩
    let y' : integerFaceChains (k := k) P ((p:ℤ)+1) :=
      ⟨y.val,Eq.mpr (congrArg (fun T : Submodule k (Ambient V k) => y.val ∈ T) hb)
        y.property⟩
    refine ⟨_,⟨y',rfl⟩,?_⟩
    apply Subtype.ext
    change (e (integerFaceBoundary (k := k) P hP (p : ℤ) y')).val = boundary y.val
    exact he_val (integerFaceBoundary (k := k) P hP (p : ℤ) y')

theorem integerAugmented_negative (P : Finset V → Prop) (hP : Downward P)
    (t : ℤ) (ht : t<0) : Subsingleton (IntegerAugmentedFaceHomology (k := k) P hP t) := by
  have hc : integerFaceCycles (k := k) P t=⊥ := by
    rw [integerFaceCycles,integerFaceChains_negative P t ht,bot_inf_eq]
  letI : Subsingleton (integerFaceCycles (k := k) P t) := by rw [hc]; infer_instance
  infer_instance

end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IncidenceLemma101 -/
section

/-!
# The literal integral incidence comparison of Lemma 10.1

The quotient is identified with the displayed ideal by
`incidenceColonFamily_ideal`. The two endpoint theorems cover all natural
homological degrees: a shifted equivalence and vanishing below the shift.
The target index q is face cardinality, hence reduced homological degree
q-1. The final endpoint states the same comparison using integer reduced degrees.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid

universe u
variable {L R T k : Type u} [Fintype L] [Fintype R] [Fintype T]
  [DecidableEq L] [LinearOrder R] [LinearOrder (L ⊕ T)] [CommRing k]
  (left : T→L) (right : T→R)

theorem incidenceSingletonOutsideCover_iff (F : Finset (L ⊕ T)) :
    CechFace.outsideCover (incidenceRightSupport (L:=L) right) Finset.univ F ↔
      incidenceCoverFaces right F := by
  constructor
  · rintro ⟨hF,r,hr⟩
    refine ⟨r,fun t ht htF => ?_⟩
    exact Finset.disjoint_left.mp ((CechFace.mem_missing _ _ _).mp hr) htF
      ((incidenceRightSupport_inr right r t).mpr ht)
  · rintro ⟨r,hr⟩
    refine ⟨Finset.subset_univ F,r,(CechFace.mem_missing _ _ _).mpr ?_⟩
    apply Finset.disjoint_left.mpr
    intro v hvF hvU
    cases v with
    | inl a => exact incidenceRightSupport_inl right r a hvU
    | inr t => exact hr t ((incidenceRightSupport_inr right r t).mp hvU) hvF

theorem incidenceSingletonGamma_eq_cover :
    alexanderDualFaces (incidenceColonFamily left right)=
      CechFace.coverUnion (incidenceJoinFaces left) (incidenceRightSupport (L:=L) right) Finset.univ := by
  funext F
  apply propext
  rw [incidenceAlexanderDual_faces,CechFace.coverUnion,incidenceSingletonOutsideCover_iff]

variable [Nonempty L]

def incidenceSingletonAlexanderNerveEquiv (q : ℕ) :
    AugmentedFaceHomology (k:=k) (alexanderDualFaces (incidenceColonFamily left right))
      (alexanderDualFaces_downward _) (q+Fintype.card L) ≃ₗ[k]
      AugmentedFaceHomology (k:=k) (incidenceNerveFaces left right)
        (incidenceNerveFaces_downward left right) q := by
  let a : L := Classical.choice inferInstance
  have he := CechFace.NerveReduction.coverHomologyEquiv (k:=k)
    (incidenceJoinFaces left) (incidenceRightSupport (L:=L) right) (incidenceNerveFaces left right)
    (IncidenceSingletonJoin.cechContraction left right) (incidenceJoinFaces_downward left)
    (incidenceNerveFaces_downward left right) (IncidenceSingletonJoin.cechContraction_d left right)
    (IncidenceSingletonJoin.cechProjection_natural left right) (Fintype.card L)
    (IncidenceSingletonJoin.cechHomotopy_raises left right)
    (IncidenceSingletonJoin.cechInclusion_degree left right)
    (by
      intro Q F hF
      exact congrArg Subtype.val (IncidenceSingletonJoin.cechProjection_zero_off_degree
        left right Q F.val.card hF (totalFaceBasis (k := k) _ F) (by
          change (totalFaceBasis (k := k) _ F).val ∈ Simplicial.Chains _ F.val.card
          rw [totalFaceBasis_val]
          exact Simplicial.basis_mem F.property rfl)))
    Finset.univ (fun F _=>Finset.subset_univ F) (Sum.inl a) (Finset.mem_univ _)
    (fun r=>incidenceRightSupport_inl right r a) q
  exact (augmentedFaceHomologyEquivOfFaces (k := k)
    (alexanderDualFaces (incidenceColonFamily left right))
    (CechFace.coverUnion (incidenceJoinFaces left)
      (incidenceRightSupport (L := L) right) Finset.univ)
    (alexanderDualFaces_downward _)
    (CechFace.coverUnion_downward (incidenceJoinFaces left)
      (incidenceRightSupport (L := L) right) Finset.univ (incidenceJoinFaces_downward left))
    (incidenceSingletonGamma_eq_cover left right) (q+Fintype.card L)).trans he

theorem incidenceSingletonAlexander_below (p : ℕ) (hp : p<Fintype.card L) :
    Subsingleton (AugmentedFaceHomology (k:=k)
      (alexanderDualFaces (incidenceColonFamily left right)) (alexanderDualFaces_downward _) p) := by
  let a : L := Classical.choice inferInstance
  have he := CechFace.NerveReduction.coverHomology_subsingleton_below (k:=k)
    (incidenceJoinFaces left) (incidenceRightSupport (L:=L) right) (incidenceNerveFaces left right)
    (IncidenceSingletonJoin.cechContraction left right) (incidenceJoinFaces_downward left)
    (IncidenceSingletonJoin.cechContraction_d left right) (Fintype.card L)
    (IncidenceSingletonJoin.cechHomotopy_raises left right)
    (by
      intro Q F hF
      exact congrArg Subtype.val (IncidenceSingletonJoin.cechProjection_zero_off_degree
        left right Q F.val.card hF (totalFaceBasis (k := k) _ F) (by
          change (totalFaceBasis (k := k) _ F).val ∈ Simplicial.Chains _ F.val.card
          rw [totalFaceBasis_val]
          exact Simplicial.basis_mem F.property rfl)))
    Finset.univ (fun F _=>Finset.subset_univ F) (Sum.inl a) (Finset.mem_univ _)
    (fun r=>incidenceRightSupport_inl right r a) p hp
  letI := he
  let e := augmentedFaceHomologyEquivOfFaces (k := k)
    (alexanderDualFaces (incidenceColonFamily left right))
    (CechFace.coverUnion (incidenceJoinFaces left)
      (incidenceRightSupport (L := L) right) Finset.univ)
    (alexanderDualFaces_downward _)
    (CechFace.coverUnion_downward (incidenceJoinFaces left)
      (incidenceRightSupport (L := L) right) Finset.univ (incidenceJoinFaces_downward left))
    (incidenceSingletonGamma_eq_cover left right) p
  exact ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

/-- Lemma 10.1 in actual derived fine Tor. The displayed degree is
q+ℓ+1, while the target is reduced degree q-1, exactly i-ℓ-2. -/
def lemma101 [Nontrivial k] (q : ℕ) :
    quotientGradedTor (k:=k) (incidenceColonFamily left right)
      (faceExponent (Finset.univ : Finset (L ⊕ T))) (q+Fintype.card L+1) ≃ₗ[k]
      AugmentedFaceHomology (k:=k) (incidenceNerveFaces left right)
        (incidenceNerveFaces_downward left right) q :=
  (quotientGradedTorIso _ _ _).symm.toLinearEquiv.trans
    ((squarefreeAlexanderDuality _ (Sum.inl (Classical.choice inferInstance)) _).trans
      (incidenceSingletonAlexanderNerveEquiv left right q))

/-- The remaining degrees are genuinely zero; natural subtraction is
not used to turn negative reduced degrees into degree zero. -/
theorem lemma101_lowDegrees [Nontrivial k] (p : ℕ) (hp : p<Fintype.card L+1) :
    Subsingleton (quotientGradedTor (k:=k) (incidenceColonFamily left right)
      (faceExponent (Finset.univ : Finset (L ⊕ T))) p) := by
  let a : L := Classical.choice inferInstance
  cases p with
  | zero =>
      letI := squarefreeQuotientHomology_zero (k:=k) (incidenceColonFamily left right) (Sum.inl a)
      let e := (quotientGradedTorIso (k:=k) (incidenceColonFamily left right)
        (faceExponent Finset.univ) 0).symm.toLinearEquiv.trans
          (quotientCategoricalDegreeHomologyEquiv _ _ 0)
      exact ⟨fun x y=>e.injective (Subsingleton.elim _ _)⟩
  | succ p =>
      letI := incidenceSingletonAlexander_below (k:=k) left right p (by omega)
      let e := (quotientGradedTorIso (k:=k) (incidenceColonFamily left right)
        (faceExponent Finset.univ) (p+1)).symm.toLinearEquiv.trans
          (squarefreeAlexanderDuality _ (Sum.inl a) p)
      exact ⟨fun x y=>e.injective (Subsingleton.elim _ _)⟩

/-- The manuscript's integral degree convention, for every i≥0.
The equivalence `incidenceColonFamily_ideal` identifies its quotient
with A/(prod_a (z_a,X_a)+(W_r)). No field hypothesis is used. -/
def lemma101_all_degrees [Nontrivial k] (p : ℕ) :
    quotientGradedTor (k:=k) (incidenceColonFamily left right)
      (faceExponent (Finset.univ : Finset (L ⊕ T))) p ≃ₗ[k]
      ReducedFaceHomology (k:=k) (incidenceNerveFaces left right)
        (incidenceNerveFaces_downward left right) ((p:ℤ)-Fintype.card L-2) := by
  by_cases hp : Fintype.card L+1≤p
  · let q := p-(Fintype.card L+1)
    have hpq : p=q+Fintype.card L+1 := by dsimp [q]; omega
    have ht : (p:ℤ)-Fintype.card L-2+1=(q:ℤ) := by omega
    change quotientGradedTor (k := k) (incidenceColonFamily left right)
      (faceExponent (Finset.univ : Finset (L ⊕ T))) p ≃ₗ[k]
        IntegerAugmentedFaceHomology (k := k) (incidenceNerveFaces left right)
          (incidenceNerveFaces_downward left right) ((p : ℤ)-Fintype.card L-2+1)
    rw [ht,hpq]
    exact (lemma101 (k := k) left right q).trans
      (integerAugmentedNatEquiv (k := k) _ _ q).symm
  · letI := lemma101_lowDegrees (k:=k) left right p (by omega)
    letI := integerAugmented_negative (k:=k) (incidenceNerveFaces left right)
      (incidenceNerveFaces_downward left right) ((p:ℤ)-Fintype.card L-2+1) (by omega)
    exact LinearEquiv.ofSubsingleton _ _
end FourPapers.Sublattice

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IncidencePowerIsolation -/
section

/-!
# The single top-colon summand in every positive power

The fine degree has exponent one at levels zero and one and exponent m
at level two. Every nonconstant-top multichain leaves a positive level-two
coordinate in its residual degree. Coordinate predecessor generators
never use level two, so an explicit creation contraction kills that
summand. The all-power chain comparison then leaves exactly the actual
top predecessor colon, integrally and in every homological degree.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CategoryTheory.Limits CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u

section Contraction
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

theorem quotientDegreeHomology_subsingleton_of_unused_equivalent
    {B C : Family V} {α : Exponent V} {e : V}
    (h : ∀ v,Contains C v ↔ Contains B v) (he : UnusedVariable C e) (hα : 0 < α e) (p : ℕ) :
    Subsingleton (ClosedGraphDegreeHomology (k := k) B α p) := by
  constructor
  intro x y
  obtain ⟨z,rfl⟩ := (LinearMap.range (closedGraphDegreeBoundary B α p)).mkQ_surjective x
  obtain ⟨w,rfl⟩ := (LinearMap.range (closedGraphDegreeBoundary B α p)).mkQ_surjective y
  apply (Submodule.Quotient.eq _).mpr
  let c := z.val-w.val
  have hc : quotientTotalDifferential B α c = 0 := by
    dsimp only [c]
    rw [map_sub,z.property.1,w.property.1,sub_self]
  have hcp : c ∈ totalFacePiece (quotientKoszulFaces B α) p :=
    Submodule.sub_mem _ z.property.2 w.property.2
  refine ⟨⟨quotientTotalCreation B α e c,
    quotientTotalCreation_raises_of_contains h he hα p c hcp⟩,?_⟩
  apply Subtype.ext
  change quotientTotalDifferential B α (quotientTotalCreation B α e c) = c
  have hh := LinearMap.congr_fun (quotientTotalCreation_contracts_of_contains (k := k) h he hα) c
  simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply,hc,map_zero,add_zero]
    using hh

theorem quotientHomology_isZero_of_unused_equivalent
    {B C : Family V} {α : Exponent V} {e : V}
    (h : ∀ v,Contains C v ↔ Contains B v) (he : UnusedVariable C e) (hα : 0 < α e) (p : ℕ) :
    IsZero ((quotientHomogeneousComplex (k := k) B α).homology p) := by
  letI := quotientDegreeHomology_subsingleton_of_unused_equivalent (k := k) h he hα p
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (quotientCategoricalDegreeHomologyEquiv B α p).injective.subsingleton

end Contraction

section Rows
variable {M : ℕ} {E : Finset (FiniteTuple (IncidenceRows M))}
variable {k : Type u} [CommRing k]

def incidenceRealizationDegree (m : ℕ) : Exponent (FiniteVariable.{u} (IncidenceRows M)) :=
  Finsupp.equivFunOnFinite.symm fun v => if v.2.down = 2 then m else 1

def incidenceResidualDegree : Exponent (FiniteVariable.{u} (IncidenceRows M)) :=
  Finsupp.equivFunOnFinite.symm fun v => if v.2.down = 2 then 0 else 1

@[simp] theorem incidenceRealizationDegree_apply (m : ℕ) (v : FiniteVariable.{u} (IncidenceRows M)) :
    incidenceRealizationDegree (M := M) m v = if v.2.down = 2 then m else 1 := rfl

@[simp] theorem incidenceResidualDegree_apply (v : FiniteVariable.{u} (IncidenceRows M)) :
    incidenceResidualDegree (M := M) v = if v.2.down = 2 then 0 else 1 := rfl

def constantIncidenceTopChain (htop : incidenceTop (M := M) ∈ E) (m : ℕ) :
    FiniteMultichain (IncidenceRows M) E m :=
  ⟨fun _ => ⟨incidenceTop,htop⟩,fun _ _ _ => le_rfl⟩

theorem constantIncidenceTopChain_coefficient (htop : incidenceTop (M := M) ∈ E)
    (m : ℕ) (hm : 0 < m) :
    finiteChainCoefficientFamily (IncidenceRows M) (constantIncidenceTopChain htop m) =
      finitePredecessorFamily (IncidenceRows M) E incidenceTop := by
  ext b
  constructor
  · intro hb
    obtain ⟨s,_,hs⟩ := Finset.mem_biUnion.mp hb
    exact hs
  · intro hb
    exact Finset.mem_biUnion.mpr ⟨⟨0,hm⟩,Finset.mem_univ _,hb⟩

theorem constantIncidenceTopChain_shift (htop : incidenceTop (M := M) ∈ E)
    (m : ℕ) (v : FiniteVariable.{u} (IncidenceRows M)) :
    finiteChainShift (IncidenceRows M) (constantIncidenceTopChain htop m) v =
      if v.2.down = 2 then m else 0 := by
  rcases v with ⟨e,⟨j⟩⟩
  by_cases hj : j = 2 <;>
    simp [finiteChainShift,constantIncidenceTopChain,Finsupp.finsetSum_apply,
      finiteRowExponent_apply,incidenceTop,hj,eq_comm]

theorem constantIncidenceTopChain_admissible (htop : incidenceTop (M := M) ∈ E) (m : ℕ) :
    finiteChainShift (IncidenceRows M) (constantIncidenceTopChain htop m) ≤
      incidenceRealizationDegree (M := M) m := by
  intro v
  rw [constantIncidenceTopChain_shift,incidenceRealizationDegree_apply]
  split_ifs <;> omega

theorem constantIncidenceTopChain_residual (htop : incidenceTop (M := M) ∈ E) (m : ℕ) :
    incidenceRealizationDegree (M := M) m -
      finiteChainShift (IncidenceRows M) (constantIncidenceTopChain htop m) =
        incidenceResidualDegree (M := M) := by
  ext v
  rw [Finsupp.tsub_apply,constantIncidenceTopChain_shift,
    incidenceRealizationDegree_apply,incidenceResidualDegree_apply]
  split_ifs <;> simp

theorem finiteChainCoordinate_unused_top (m : ℕ)
    (w : FiniteMultichain (IncidenceRows M) E m) (e : Fin M) :
    UnusedVariable (finiteChainCoordinateFamily w) (⟨e,ULift.up 2⟩ : FiniteVariable.{u} (IncidenceRows M)) := by
  intro c hc
  obtain ⟨s,_,hs⟩ := Finset.mem_biUnion.mp hc
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
  have hba := (Finset.mem_filter.mp hb).2.1 e
  simp only [Finsupp.tsub_apply,finiteRowExponent_apply]
  by_cases hb2 : b e = 2
  · have ha2 : (w.val s).val e = 2 := by
      apply Fin.ext
      change ((w.val s).val e).val = 2
      have ha : ((w.val s).val e).val < 3 := ((w.val s).val e).isLt
      simp only [hb2] at hba
      change 2 ≤ ((w.val s).val e).val at hba
      omega
    simp [hb2,ha2]
  · simp [hb2]

theorem nonTopChain_positive_top_residual (htop : incidenceTop (M := M) ∈ E)
    (m : ℕ) (w : FiniteMultichain (IncidenceRows M) E m)
    (hne : w ≠ constantIncidenceTopChain htop m) :
    ∃ e : Fin M, 0 < (incidenceRealizationDegree (M := M) m-
      finiteChainShift (IncidenceRows M) w) ⟨e,ULift.up 2⟩ := by
  obtain ⟨s,hs⟩ : ∃ s : Fin m, (w.val s).val ≠ incidenceTop (M := M) := by
    by_contra! hh
    apply hne
    apply Subtype.ext
    funext s
    exact Subtype.ext (hh s)
  obtain ⟨e,he⟩ : ∃ e : Fin M, (w.val s).val e ≠ 2 := by
    by_contra! hh
    exact hs (funext hh)
  refine ⟨e,?_⟩
  have hslt : (∑ j : Fin m, if (w.val j).val e = 2 then (1 : ℕ) else 0) < m := by
    have hh := Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin m)))
      (f := fun j => if (w.val j).val e = 2 then (1 : ℕ) else 0)
      (g := fun _ => (1 : ℕ))
      (fun j _ => by split_ifs <;> omega)
      ⟨s,Finset.mem_univ _,by simp [he]⟩
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using hh
  rw [Finsupp.tsub_apply,incidenceRealizationDegree_apply]
  change 0 < m - finiteChainShift (IncidenceRows M) w ⟨e,ULift.up 2⟩
  rw [Nat.sub_pos_iff_lt]
  simpa only [finiteChainShift,Finsupp.finsetSum_apply,finiteRowExponent_apply] using hslt

theorem nonTopChain_homology_isZero (hE : finiteLatticeClosed (IncidenceRows M) E)
    (htop : incidenceTop (M := M) ∈ E) (m : ℕ)
    (w : FiniteMultichain (IncidenceRows M) E m)
    (hne : w ≠ constantIncidenceTopChain htop m) (p : ℕ) :
    IsZero ((quotientHomogeneousComplex (k := k) (finiteChainCoefficientFamily (IncidenceRows M) w)
      (incidenceRealizationDegree (M := M) m-finiteChainShift (IncidenceRows M) w)).homology p) := by
  obtain ⟨e,he⟩ := nonTopChain_positive_top_residual htop m w hne
  exact quotientHomology_isZero_of_unused_equivalent
    (finiteChainCoordinate_contains_iff hE w) (finiteChainCoordinate_unused_top m w e) he p

def piHomologySingleEquiv {J : Type*} (A : J → Type u)
    [∀ j,AddCommGroup (A j)] [∀ j,Module k (A j)] (j₀ : J)
    (hz : ∀ j,j ≠ j₀ → Subsingleton (A j)) : (∀ j,A j) ≃ₗ[k] A j₀ :=
  LinearEquiv.ofBijective (LinearMap.proj j₀)
    ⟨by
      intro x y h
      funext j
      by_cases hj : j=j₀
      · subst j
        exact h
      · exact (hz j hj).allEq _ _,
      fun x => ⟨Pi.single j₀ x,by simp⟩⟩

/-- The all-power integral chain formula really has one surviving
homology summand at this fine degree. -/
def incidencePowerTopHomologyEquiv (hE : finiteLatticeClosed (IncidenceRows M) E)
    (htop : incidenceTop (M := M) ∈ E) (m : ℕ) (hm : 0 < m) (p : ℕ) :
    (homogeneousComplex (k := k) (exponentPowerFamily (finiteRowFamily (IncidenceRows M) E) m)
      (incidenceRealizationDegree (M := M) m)).homology p ≃ₗ[k]
        (quotientHomogeneousComplex (k := k) (finitePredecessorFamily (IncidenceRows M) E incidenceTop)
          (incidenceResidualDegree (M := M))).homology p := by
  let w₀ : AdmissibleChain (IncidenceRows M) E m (incidenceRealizationDegree.{u} (M := M) m) :=
    ⟨constantIncidenceTopChain htop m,constantIncidenceTopChain_admissible htop m⟩
  let A : AdmissibleChain (IncidenceRows M) E m (incidenceRealizationDegree.{u} (M := M) m) → Type u :=
    fun w => (quotientHomogeneousComplex (k := k) (finiteChainCoefficientFamily (IncidenceRows M) w.val)
      (incidenceRealizationDegree (M := M) m-finiteChainShift (IncidenceRows M) w.val)).homology p
  have hz : ∀ w,w ≠ w₀ → Subsingleton (A w) := by
    intro w hw
    exact ModuleCat.isZero_iff_subsingleton.mp
      (nonTopChain_homology_isZero hE htop m w.val
        (fun he => hw (Subtype.ext he)) p)
  have e := (allPowerHomogeneousHomologyIso (k := k) hE m hm (incidenceRealizationDegree (M := M) m) p).toLinearEquiv.trans
    (piHomologySingleEquiv (k := k) A w₀ hz)
  have hC :
      quotientHomogeneousComplex (k := k)
        (finiteChainCoefficientFamily (IncidenceRows M) (constantIncidenceTopChain htop m))
        (incidenceRealizationDegree (M := M) m -
          finiteChainShift (IncidenceRows M) (constantIncidenceTopChain htop m)) =
      quotientHomogeneousComplex (k := k)
        (finitePredecessorFamily (IncidenceRows M) E incidenceTop)
        (incidenceResidualDegree (M := M)) :=
    congrArg₂
      (quotientHomogeneousComplex (V := FiniteVariable.{u} (IncidenceRows M)) (k := k))
      (constantIncidenceTopChain_coefficient htop m hm)
      (constantIncidenceTopChain_residual htop m)
  exact e.trans
    (eqToIso (congrArg
      (fun D : ChainComplex (ModuleCat.{u} k) ℕ => D.homology p) hC)).toLinearEquiv

/-- The same isolated group inside genuine derived Tor, over every
nontrivial coefficient ring, in particular over the integers. -/
def incidencePowerTopTorEquiv [Nontrivial k]
    (hE : finiteLatticeClosed (IncidenceRows M) E) (htop : incidenceTop (M := M) ∈ E)
    (m : ℕ) (hm : 0 < m) (p : ℕ) :
    gradedTor (k := k) (exponentPowerFamily (finiteRowFamily (IncidenceRows M) E) m)
      (incidenceRealizationDegree (M := M) m) p ≃ₗ[k]
        (quotientHomogeneousComplex (k := k) (finitePredecessorFamily (IncidenceRows M) E incidenceTop)
          (incidenceResidualDegree (M := M))).homology p :=
  (gradedTorIso _ _ p).symm.toLinearEquiv.trans (incidencePowerTopHomologyEquiv hE htop m hm p)

end Rows
end FourPapers.Sublattice
end

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IncidenceExpandedAlexander -/
section

/-! # The expanded incidence cover in the original row variables

Each old z_a is replaced by its nonempty zero-level incidence block.
The resulting Alexander-dual factor is a disjoint union of two full
simplices. The exact face identity below permits an integral chain
calculation directly in this expanded complex, without assuming a flat
substitution or an unproved Tor base-change theorem.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {M : ℕ} (left : Fin M → L) (right : Fin M → R)

def incidenceLowerSupport : Finset (FiniteVariable.{u} (IncidenceRows M)) :=
  Finset.univ.filter fun v => v.2.down ≠ 2

@[simp] theorem incidenceLowerSupport_mem (v : FiniteVariable.{u} (IncidenceRows M)) :
    v ∈ incidenceLowerSupport (M := M) ↔ v.2.down ≠ 2 := by
  simp [incidenceLowerSupport]

theorem incidenceResidualDegree_eq_face :
    incidenceResidualDegree (M := M) = faceExponent (incidenceLowerSupport (M := M)) := by
  ext v
  by_cases hv : v.2.down = 2 <;> simp [incidenceResidualDegree_apply,faceExponent_apply,hv]

def incidenceRowJoinFaces (F : Finset (FiniteVariable.{u} (IncidenceRows M))) : Prop :=
  F ⊆ incidenceLowerSupport (M := M) ∧
    ∀ e f : Fin M, left e = left f → ⟨e,ULift.up 0⟩ ∈ F → ⟨f,ULift.up 1⟩ ∉ F

def incidenceRowCoverFaces (F : Finset (FiniteVariable.{u} (IncidenceRows M))) : Prop :=
  F ⊆ incidenceLowerSupport (M := M) ∧
    ∃ r : R, ∀ e : Fin M, right e = r → ⟨e,ULift.up 1⟩ ∉ F

def incidenceRowIntersectionFaces (Q : Finset R)
    (F : Finset (FiniteVariable.{u} (IncidenceRows M))) : Prop :=
  incidenceRowJoinFaces left F ∧ ∀ e : Fin M,right e ∈ Q → ⟨e,ULift.up 1⟩ ∉ F

theorem incidenceLowerExponent_complement_iff (D : Finset L)
    (F : Finset (FiniteVariable.{u} (IncidenceRows M))) :
    finiteRowExponent (IncidenceRows M) (incidenceLower left D) ≤
      faceExponent (incidenceLowerSupport (M := M) \ F) ↔
        ∀ e : Fin M, ⟨e,ULift.up (incidenceLower left D e)⟩ ∉ F := by
  constructor
  · intro h e he
    have hh := h ⟨e,ULift.up (incidenceLower left D e)⟩
    simp [finiteRowExponent_apply,faceExponent_apply,he] at hh
  · intro h v
    rcases v with ⟨e,⟨j⟩⟩
    simp only [finiteRowExponent_apply,faceExponent_apply]
    by_cases hej : incidenceLower left D e = j
    · subst j
      have hl : incidenceLower left D e ≠ 2 := by
        by_cases he : left e ∈ D <;> simp [incidenceLower,he]
      simp [h e,hl]
    · simp [hej]

theorem incidenceLowerChoices_complement_iff
    (F : Finset (FiniteVariable.{u} (IncidenceRows M))) :
    (∃ D : Finset L,finiteRowExponent (IncidenceRows M) (incidenceLower left D) ≤
      faceExponent (incidenceLowerSupport (M := M) \ F)) ↔
        ∀ e f : Fin M,left e=left f → ⟨e,ULift.up 0⟩∈F → ⟨f,ULift.up 1⟩∉F := by
  simp_rw [incidenceLowerExponent_complement_iff]
  constructor
  · rintro ⟨D,hD⟩ e f hef he hf
    by_cases hd : left e ∈ D
    · have hdf : left f ∈ D := by simpa only [← hef] using hd
      exact hD f (by simpa only [incidenceLower,if_pos hdf] using hf)
    · exact hD e (by simpa only [incidenceLower,if_neg hd] using he)
  · intro h
    let D := Finset.univ.filter fun a : L =>
      ∃ e : Fin M,left e=a ∧ (⟨e,ULift.up 0⟩ : FiniteVariable.{u} (IncidenceRows M))∈F
    refine ⟨D,?_⟩
    intro f hf
    by_cases hd : left f ∈ D
    · obtain ⟨e,hef,he⟩ := (Finset.mem_filter.mp hd).2
      exact h e f hef he (by simpa only [incidenceLower,if_pos hd] using hf)
    · have hf0 : (⟨f,ULift.up 0⟩ : FiniteVariable.{u} (IncidenceRows M)) ∈ F := by
        simpa only [incidenceLower,if_neg hd] using hf
      exact hd (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨f,rfl,hf0⟩⟩)

theorem incidenceRightExponent_complement_iff (r : R)
    (F : Finset (FiniteVariable.{u} (IncidenceRows M))) :
    incidenceRowRightExponent right r ≤ faceExponent (incidenceLowerSupport (M := M) \ F) ↔
      ∀ e : Fin M,right e=r → (⟨e,ULift.up 1⟩ : FiniteVariable.{u} (IncidenceRows M))∉F := by
  constructor
  · intro h e he hf
    have hh := h ⟨e,ULift.up 1⟩
    simp [incidenceRowRightExponent_apply,faceExponent_apply,he,hf] at hh
  · intro h v
    rcases v with ⟨e,⟨j⟩⟩
    by_cases he : right e = r
    · by_cases hj : j=1
      · subst j
        simp [incidenceRowRightExponent_apply,faceExponent_apply,he,h e he]
      · simp [incidenceRowRightExponent_apply,hj]
    · simp [incidenceRowRightExponent_apply,he]

/-- Exact Alexander-dual decomposition after the disjoint block expansion. -/
theorem incidenceExpandedAlexander_faces
    (F : Finset (FiniteVariable.{u} (IncidenceRows M))) :
    supportedAlexanderDualFaces (incidenceTopFamily left right) (incidenceLowerSupport (M := M)) F ↔
      incidenceRowJoinFaces left F ∨ incidenceRowCoverFaces right F := by
  have hcontains : Contains (incidenceTopFamily left right)
      (faceExponent (incidenceLowerSupport (M := M) \ F)) ↔
        (∃ D : Finset L,finiteRowExponent (IncidenceRows M) (incidenceLower left D) ≤
          faceExponent (incidenceLowerSupport (M := M) \ F)) ∨
        ∃ r : R,incidenceRowRightExponent right r ≤
          faceExponent (incidenceLowerSupport (M := M) \ F) := by
    constructor
    · rintro ⟨a,ha,hle⟩
      rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨D,_,rfl⟩ := Finset.mem_image.mp ha
        exact Or.inl ⟨D,hle⟩
      · obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp ha
        exact Or.inr ⟨r,hle⟩
    · rintro (⟨D,hD⟩ | ⟨r,hr⟩)
      · exact ⟨_,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨D,Finset.mem_univ _,rfl⟩),hD⟩
      · exact ⟨_,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩),hr⟩
  have hfaces := hcontains.trans
    (or_congr (incidenceLowerChoices_complement_iff left F)
      (exists_congr fun r => incidenceRightExponent_complement_iff right r F))
  -- The chosen orientation and the Sigma type supply different equality
  -- decisions; the finite difference is independent of that choice.
  have hdiff :
      @sdiff (Finset (FiniteVariable.{u} (IncidenceRows M)))
        (@Finset.instSDiff (FiniteVariable.{u} (IncidenceRows M))
          (finiteVariableLinearOrder.{u} (IncidenceRows M)).toDecidableEq)
        (incidenceLowerSupport (M := M)) F =
      incidenceLowerSupport (M := M) \ F := by
    exact congrArg
      (fun dec : DecidableEq (FiniteVariable.{u} (IncidenceRows M)) =>
        @sdiff (Finset (FiniteVariable.{u} (IncidenceRows M)))
          (@Finset.instSDiff (FiniteVariable.{u} (IncidenceRows M)) dec)
          (incidenceLowerSupport (M := M)) F)
      (Subsingleton.elim
        (finiteVariableLinearOrder.{u} (IncidenceRows M)).toDecidableEq
        (inferInstance : DecidableEq (FiniteVariable.{u} (IncidenceRows M))))
  simp only [supportedAlexanderDualFaces,stanleyReisnerFaces,not_not]
  rw [hdiff]
  simpa only [incidenceRowJoinFaces,incidenceRowCoverFaces,and_or_left] using
    (and_congr (Iff.rfl : F ⊆ incidenceLowerSupport (M := M) ↔
      F ⊆ incidenceLowerSupport (M := M)) hfaces)

def incidenceZeroBlock (a : L) : Finset (FiniteVariable.{u} (IncidenceRows M)) :=
  Finset.univ.filter fun v => left v.1=a ∧ v.2.down=0

def incidenceOneBlock (Q : Finset R) (a : L) : Finset (FiniteVariable.{u} (IncidenceRows M)) :=
  Finset.univ.filter fun v => left v.1=a ∧ v.2.down=1 ∧ right v.1∉Q

theorem incidenceZeroBlock_nonempty (hl : Function.Surjective left) (a : L) :
    (incidenceZeroBlock left a).Nonempty := by
  obtain ⟨e,he⟩ := hl a
  exact ⟨⟨e,ULift.up 0⟩,by simp [incidenceZeroBlock,he]⟩

theorem incidenceOneBlock_nonempty_iff (Q : Finset R) (a : L) :
    (incidenceOneBlock left right Q a).Nonempty ↔ ∃ e : Fin M,left e=a ∧ right e∉Q := by
  constructor
  · rintro ⟨⟨e,⟨j⟩⟩,he⟩
    exact ⟨e,(Finset.mem_filter.mp he).2.1,(Finset.mem_filter.mp he).2.2.2⟩
  · rintro ⟨e,he,hr⟩
    exact ⟨⟨e,ULift.up 1⟩,by simp [incidenceOneBlock,he,hr]⟩

theorem incidenceBlocks_pairwise_disjoint (Q : Finset R) :
    Pairwise (fun a b : L => Disjoint (incidenceZeroBlock left a ∪ incidenceOneBlock left right Q a)
      (incidenceZeroBlock left b ∪ incidenceOneBlock left right Q b)) := by
  intro a b hab
  apply Finset.disjoint_left.mpr
  intro v hva hvb
  have ha : left v.1=a := by
    rcases Finset.mem_union.mp hva with h | h <;> exact (Finset.mem_filter.mp h).2.1
  have hb : left v.1=b := by
    rcases Finset.mem_union.mp hvb with h | h <;> exact (Finset.mem_filter.mp h).2.1
  exact hab (ha.symm.trans hb)

theorem incidenceZeroOne_disjoint (Q : Finset R) (a : L) :
    Disjoint (incidenceZeroBlock left a) (incidenceOneBlock left right Q a) := by
  apply Finset.disjoint_left.mpr
  intro v hv0 hv1
  have h0 := (Finset.mem_filter.mp hv0).2.2
  have h1 := (Finset.mem_filter.mp hv1).2.2.1
  have hh : (0 : Fin 3)=1 := h0.symm.trans h1
  exact (by decide : (0 : Fin 3)≠1) hh

end FourPapers.Sublattice
end

end
end


end
