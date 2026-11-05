module
public import paper_results.part006
public import paper_results.part003
public import shared_results.part020
public import Mathlib.Data.ZMod.QuotientRing
public import paper_results.part007
public import paper_results.part009

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.RP2FaceCoordinates -/
section

/-!
# The manuscript's six-vertex complex in actual exterior coordinates

The vertex lift changes only the Lean universe level. The ten facets are
exactly the printed facets, with labels decreased by one. The finite
enumerations account for every actual face in each degree.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice.RP2
open Classical CommAlg CommAlg.Simplicial

universe u
abbrev Vertex := ULift.{u} (Fin 6)

def plainFacet : Fin 10 → Finset (Fin 6) :=
  ![{0,1,2},{0,1,3},{0,2,4},{0,3,5},{0,4,5},
    {1,2,5},{1,3,4},{1,4,5},{2,3,4},{2,3,5}]

def plainEdge : Fin 15 → Finset (Fin 6) :=
  ![{0,1},{0,2},{0,3},{0,4},{0,5},{1,2},{1,3},{1,4},
    {1,5},{2,3},{2,4},{2,5},{3,4},{3,5},{4,5}]

def facet (i : Fin 10) : Finset Vertex.{u} := (plainFacet i).map Equiv.ulift.symm.toEmbedding

def faces : Finset (Finset Vertex.{u}) := Finset.univ.biUnion (fun i : Fin 10 => (facet i).powerset)

def Face (F : Finset Vertex.{u}) : Prop := F∈faces

instance : DecidablePred (Face.{u}) := fun F => inferInstanceAs (Decidable (F∈faces))

theorem downward : Simplicial.Downward (Face.{u}) := by
  intro F G hGF hF
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hF
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
    Finset.mem_powerset.mpr (hGF.trans (Finset.mem_powerset.mp hi))⟩

theorem face_card_le (F : Finset Vertex.{u}) (hF : Face F) : F.card≤3 := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hF
  have h := Finset.card_le_card (Finset.mem_powerset.mp hi)
  rw [facet, Finset.card_map] at h
  have hc : (plainFacet i).card = 3 := by fin_cases i <;> decide
  omega

abbrev size : ℕ → ℕ
  | 0 => 1
  | 1 => 6
  | 2 => 15
  | 3 => 10
  | _ => 0

def face : (p : ℕ) → Fin (size p) → Finset Vertex.{u}
  | 0,_ => ∅
  | 1,i => {ULift.up i}
  | 2,i => (plainEdge i).map Equiv.ulift.symm.toEmbedding
  | 3,i => facet i
  | p+4,i => Fin.elim0 i

theorem face_mem_card (p : ℕ) (i : Fin (size p)) : Face (face p i) ∧ (face p i).card=p := by
  match p with
  | 0 => revert i; decide
  | 1 => revert i; decide
  | 2 => revert i; decide
  | 3 => revert i; decide
  | p+4 => exact Fin.elim0 i

def faceIndexMap (p : ℕ) (i : Fin (size p)) : {F : Finset Vertex.{u} // Face F ∧ F.card=p} :=
  ⟨face p i,face_mem_card p i⟩

theorem faceIndexMap_bijective (p : ℕ) : Function.Bijective (faceIndexMap.{u} p) := by
  match p with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | p+4 =>
      constructor
      · intro i; exact Fin.elim0 i
      · intro F
        have h := face_card_le F.val F.property.1
        have hc := F.property.2
        omega

def faceIndexEquiv (p : ℕ) : Fin (size p) ≃ {F : Finset Vertex.{u} // Face F ∧ F.card=p} :=
  Equiv.ofBijective (faceIndexMap p) (faceIndexMap_bijective p)

variable {k : Type u} [CommRing k]

def chainBasis (p : ℕ) : Module.Basis (Fin (size p)) k (Simplicial.Chains (k:=k) Face.{u} p) :=
  (Grading.restrictedBasis Simplicial.basis (fun F : Finset Vertex.{u} => Face F ∧ F.card=p)).reindex
    (faceIndexEquiv p).symm

@[simp] theorem chainBasis_val (p : ℕ) (i : Fin (size p)) :
    (chainBasis (k:=k) p i).val=Simplicial.basis (face p i) := by
  let b := Grading.restrictedBasis (Simplicial.basis (V := Vertex.{u}) (k := k))
    (fun F : Finset (Vertex.{u}) => Face F ∧ F.card = p)
  have h := congrArg Subtype.val
    (Module.Basis.reindex_apply b (faceIndexEquiv.{u} p).symm i)
  exact h.trans (Grading.restrictedBasis_val _ _ _)

def boundaryMap (p : ℕ) :
    Simplicial.Chains (k:=k) Face (p+1) →ₗ[k] Simplicial.Chains (k:=k) Face p :=
  ((Simplicial.boundary (V := Vertex.{u}) (k := k)).domRestrict
    (Simplicial.Chains (k := k) (Face.{u}) (p+1))).codRestrict
      (Simplicial.Chains (k := k) (Face.{u}) p)
      (fun x => Simplicial.boundary_mem downward x.property)

@[simp] theorem boundaryMap_val (p : ℕ) (x : Simplicial.Chains (k:=k) Face (p+1)) :
    (boundaryMap p x).val=Simplicial.boundary x.val := rfl

theorem boundaryMap_comp (p : ℕ) : (boundaryMap (k:=k) p).comp (boundaryMap (p+1))=0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact Simplicial.boundary_boundary x.val

def previous : (p : ℕ) → Simplicial.Chains (k:=k) Face p →ₗ[k] Simplicial.Chains (k:=k) Face p.pred
  | 0 => 0
  | p+1 => boundaryMap p

theorem previous_comp (p : ℕ) : (previous (k:=k) p).comp (boundaryMap p)=0 := by
  cases p with
  | zero => simp [previous]
  | succ p => exact boundaryMap_comp p

def cyclesEquiv (p : ℕ) :
    LinearMap.ker (previous (k:=k) p) ≃ₗ[k] augmentedFaceCycles (k:=k) Face p where
  toFun x := ⟨x.val.val,⟨x.val.property,by
    cases p with
    | zero => exact Simplicial.boundary_zero_degree_zero x.val.property
    | succ p => exact congrArg Subtype.val x.property⟩⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,by
    cases p with
    | zero => rfl
    | succ p => exact Subtype.ext x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cyclesEquiv_boundaries (p : ℕ) :
    (LinearMap.range (FourPapers.FilteredHomology.boundaryMap (boundaryMap (k:=k) p)
      (previous p) (previous_comp p))).map (cyclesEquiv p).toLinearMap=
      LinearMap.range (augmentedFaceBoundary (k:=k) Face downward p) := by
  ext z
  constructor
  · rintro ⟨x,⟨y,rfl⟩,rfl⟩
    exact ⟨y,rfl⟩
  · rintro ⟨y,rfl⟩
    exact ⟨FourPapers.FilteredHomology.boundaryMap (boundaryMap p)
      (previous p) (previous_comp p) y,⟨y,rfl⟩,rfl⟩

def actualHomologyEquiv (p : ℕ) :
    FourPapers.FilteredHomology.Homology (boundaryMap (k:=k) p) (previous p) (previous_comp p) ≃ₗ[k]
      AugmentedFaceHomology (k:=k) Face downward p :=
  Submodule.Quotient.equiv _ _ (cyclesEquiv p) (cyclesEquiv_boundaries p)

/-- Integer coefficients obtained from the actual signed face boundary. -/
def integerBoundaryMatrix (p : ℕ) : Matrix (Fin (size p)) (Fin (size (p+1))) ℤ :=
  fun i j => ∑ v : Vertex.{u},
    if v∈face (p+1) j ∧ (face (p+1) j).erase v=face p i then
      (TauCeti.ExteriorAlgebra.basisEraseSign v (face (p+1) j) : ℤ) else 0

theorem chainBasis_repr_apply (p : ℕ) (x : Simplicial.Chains (k:=k) Face p)
    (i : Fin (size p)) :
    (chainBasis p).repr x i=Simplicial.basis.repr x.val (face p i) := by
  have hi : Function.Injective (face.{u} p) := by
    intro a b hab
    apply (faceIndexEquiv p).injective
    exact Subtype.ext hab
  have he : (chainBasis (k:=k) p).coord i=
      (Simplicial.basis.coord (face p i)).comp (Simplicial.Chains (k := k) (Face.{u}) p).subtype := by
    apply (chainBasis p).ext
    intro j
    simp only [LinearMap.comp_apply,Submodule.subtype_apply,Module.Basis.coord_apply,
      chainBasis_val,Module.Basis.repr_self,Finsupp.single_apply,hi.eq_iff]
  exact LinearMap.congr_fun he x

/-- The finite integer matrix represents the literal exterior boundary,
over every commutative coefficient ring. -/
theorem boundaryMap_toMatrix (p : ℕ) :
    LinearMap.toMatrix (chainBasis (k:=k) (p+1)) (chainBasis p) (boundaryMap p)=
      (integerBoundaryMatrix.{u} p).map (Int.castRingHom k) := by
  ext i j
  rw [LinearMap.toMatrix_apply,chainBasis_repr_apply,boundaryMap_val,
    chainBasis_val,Simplicial.boundary_eq_sum]
  simp only [map_sum,Finsupp.finsetSum_apply,Matrix.map_apply,integerBoundaryMatrix]
  apply Finset.sum_congr rfl
  intro v _
  rw [Simplicial.contraction_basis]
  by_cases hv : v ∈ face (p+1) j
  · rw [if_pos hv, map_zsmul_unit, Module.Basis.repr_self, Finsupp.smul_apply]
    simp only [Finsupp.single_apply, Finset.ext_iff, Finset.mem_erase, hv, true_and]
    by_cases he : ∀ w : Vertex.{u},
        (w ≠ v ∧ w ∈ face (p+1) j) ↔ w ∈ face p i
    · simp only [he, forall_const, ite_true, Units.smul_def, Int.smul_one_eq_cast,
        Int.coe_castRingHom]
    · simp only [he, ite_false, smul_zero, map_zero]
  · simp [hv]

/-- A directly evaluable integer entry of the signed face boundary. -/
theorem integerBoundaryMatrix_apply (p : ℕ) (i : Fin (size p))
    (j : Fin (size (p+1))) :
    integerBoundaryMatrix.{u} p i j = ∑ v : Vertex.{u},
      if v ∈ face (p+1) j ∧ (face (p+1) j).erase v = face p i then
        (((-1 : ℤˣ) ^ ((face (p+1) j).filter (fun w => w < v)).card : ℤˣ) : ℤ)
      else 0 := by
  unfold integerBoundaryMatrix
  apply Finset.sum_congr rfl
  intro v _
  split_ifs with h
  · exact congrArg (fun ε : ℤˣ => (ε : ℤ))
      (TauCeti.ExteriorAlgebra.basisEraseSign_eq_neg_one_pow_card_filter_lt
        v (face (p+1) j))
  · rfl

theorem integerBoundaryMatrix_zero : integerBoundaryMatrix.{u} 0=RP2Matrices.D1 := by
  funext i j
  rw [integerBoundaryMatrix_apply]
  revert i j
  decide

theorem integerBoundaryMatrix_one : integerBoundaryMatrix.{u} 1=RP2Matrices.D2 := by
  funext i j
  rw [integerBoundaryMatrix_apply]
  revert i j
  decide

theorem integerBoundaryMatrix_two : integerBoundaryMatrix.{u} 2=RP2Matrices.D3 := by
  funext i j
  rw [integerBoundaryMatrix_apply]
  revert i j
  decide

end FourPapers.Sublattice.RP2

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.RP2NormalComplex -/
section

/-! # Integral change of basis in the actual six-vertex chain complex

All coordinate changes have displayed integer inverses. The resulting
normal complex has one multiplication-by-two map, nine identity pairs
in degrees 3→2, five in degrees 2→1, and one in degrees 1→0.
The chain comparison is valid over every commutative coefficient ring.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice.RP2
open Classical CommAlg Matrix
universe u

def transform : (p : ℕ) → Matrix (Fin (size p)) (Fin (size p)) ℤ
  | 0 => 1
  | 1 => RP2Matrices.T1
  | 2 => RP2Matrices.T2
  | 3 => RP2Matrices.T3
  | _ => 1

def inverseTransform : (p : ℕ) → Matrix (Fin (size p)) (Fin (size p)) ℤ
  | 0 => 1
  | 1 => RP2Matrices.R1
  | 2 => RP2Matrices.R2
  | 3 => RP2Matrices.R3
  | _ => 1

theorem transform_inverse (p : ℕ) : transform p*inverseTransform p=1 := by
  match p with
  | 0 => exact one_mul _
  | 1 => exact RP2Matrices.T1_R1
  | 2 => exact RP2Matrices.T2_R2
  | 3 => exact RP2Matrices.T3_R3
  | p+4 => exact one_mul _

theorem inverse_transform (p : ℕ) : inverseTransform p*transform p=1 := by
  match p with
  | 0 => exact one_mul _
  | 1 => exact RP2Matrices.R1_T1
  | 2 => exact RP2Matrices.R2_T2
  | 3 => exact RP2Matrices.R3_T3
  | p+4 => exact one_mul _

def normalMatrix : (p : ℕ) → Matrix (Fin (size p)) (Fin (size (p+1))) ℤ
  | 0 => RP2Matrices.N1
  | 1 => RP2Matrices.N2
  | 2 => RP2Matrices.N3
  | _ => 0

theorem normal_form (p : ℕ) :
    inverseTransform p*integerBoundaryMatrix.{u} p*transform (p+1)=normalMatrix p := by
  match p with
  | 0 => simpa only [inverseTransform,transform,normalMatrix,Matrix.one_mul,
      integerBoundaryMatrix_zero.{u}] using RP2Matrices.normal1
  | 1 => simpa only [inverseTransform,transform,normalMatrix,
      integerBoundaryMatrix_one.{u}] using RP2Matrices.normal2
  | 2 => simpa only [inverseTransform,transform,normalMatrix,
      integerBoundaryMatrix_two.{u}] using RP2Matrices.normal3
  | p+3 => ext i j; exact Fin.elim0 j

theorem normal_chain_matrix (p : ℕ) :
    inverseTransform p*integerBoundaryMatrix.{u} p=normalMatrix p*inverseTransform (p+1) := by
  calc
    _ = (inverseTransform p*integerBoundaryMatrix.{u} p)*(transform (p+1)*inverseTransform (p+1)) := by
      rw [transform_inverse,Matrix.mul_one]
    _ = (inverseTransform p*integerBoundaryMatrix.{u} p*transform (p+1))*inverseTransform (p+1) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [normal_form.{u}]

variable {k : Type u} [CommRing k]

def coordinateChange (p : ℕ) : (Fin (size p)→k) ≃ₗ[k] (Fin (size p)→k) :=
  Matrix.toLin'OfInv
    (show (transform p).map (Int.castRingHom k)*(inverseTransform p).map (Int.castRingHom k)=1 by
      rw [← Matrix.map_mul,transform_inverse]; simp)
    (show (inverseTransform p).map (Int.castRingHom k)*(transform p).map (Int.castRingHom k)=1 by
      rw [← Matrix.map_mul,inverse_transform]; simp)

def chainCoordinates (p : ℕ) :
    Simplicial.Chains (k:=k) Face p ≃ₗ[k] (Fin (size p)→k) :=
  (chainBasis p).equivFun.trans (coordinateChange p)

def normalDifferential (p : ℕ) : (Fin (size (p+1))→k) →ₗ[k] (Fin (size p)→k) :=
  ((normalMatrix p).map (Int.castRingHom k)).mulVecLin

theorem chainCoordinates_boundary (p : ℕ) (x : Simplicial.Chains (k:=k) Face (p+1)) :
    chainCoordinates p (boundaryMap p x)=normalDifferential p (chainCoordinates (p+1) x) := by
  change (inverseTransform p).map (Int.castRingHom k) *ᵥ (chainBasis p).repr (boundaryMap p x)=
    (normalMatrix p).map (Int.castRingHom k) *ᵥ
      ((inverseTransform (p+1)).map (Int.castRingHom k) *ᵥ (chainBasis (p+1)).repr x)
  rw [← LinearMap.toMatrix_mulVec_repr (chainBasis (p+1)) (chainBasis p) (boundaryMap p) x,
    boundaryMap_toMatrix.{u},Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,← Matrix.map_mul,
    normal_chain_matrix.{u},Matrix.map_mul]

theorem normalDifferential_comp (p : ℕ) :
    (normalDifferential (k:=k) p).comp (normalDifferential (p+1))=0 := by
  apply LinearMap.ext
  intro x
  change normalDifferential (k := k) p (normalDifferential (p+1) x) = 0
  obtain ⟨y,rfl⟩ := (chainCoordinates (k := k) (p+1+1)).surjective x
  rw [← chainCoordinates_boundary,← chainCoordinates_boundary]
  have h := LinearMap.congr_fun (boundaryMap_comp (k:=k) p) y
  change boundaryMap p (boundaryMap (p+1) y)=0 at h
  rw [h,map_zero]

def normalPrevious : (p : ℕ) → (Fin (size p)→k) →ₗ[k] (Fin (size p.pred)→k)
  | 0 => 0
  | p+1 => normalDifferential p

theorem normalPrevious_comp (p : ℕ) :
    (normalPrevious (k:=k) p).comp (normalDifferential p)=0 := by
  cases p with
  | zero => simp [normalPrevious]
  | succ p => exact normalDifferential_comp p

abbrev NormalHomology (p : ℕ) := FourPapers.FilteredHomology.Homology
  (normalDifferential (k:=k) p) (normalPrevious p) (normalPrevious_comp p)

/-- The literal augmented simplicial homology is transported to the
displayed normal chain complex in every degree. -/
def normalHomologyEquiv (p : ℕ) :
    AugmentedFaceHomology (k:=k) Face downward p ≃ₗ[k] NormalHomology (k:=k) p :=
  (actualHomologyEquiv (k := k) p).symm.trans
    (FourPapers.FilteredHomology.threeTermHomologyEquiv
      (R := k)
      (X := ↥(Simplicial.Chains (k := k) Face.{u} (p+1)))
      (Y := ↥(Simplicial.Chains (k := k) Face.{u} p))
      (Z := ↥(Simplicial.Chains (k := k) Face.{u} p.pred))
      (X' := Fin (size (p+1)) → k)
      (Y' := Fin (size p) → k)
      (Z' := Fin (size p.pred) → k)
      (boundaryMap (k := k) p) (previous (k := k) p) (previous_comp (k := k) p)
      (normalDifferential (k := k) p) (normalPrevious (k := k) p)
      (normalPrevious_comp (k := k) p)
      (chainCoordinates (k := k) (p+1)) (chainCoordinates (k := k) p)
      (chainCoordinates (k := k) p.pred)
      (chainCoordinates_boundary (k := k) p) (by
        intro x
        cases p with
        | zero =>
            change chainCoordinates (k := k) 0
              (0 : Simplicial.Chains (k := k) Face.{u} 0) = 0
            exact map_zero _
        | succ p => exact chainCoordinates_boundary (k := k) p x))

end FourPapers.Sublattice.RP2

end
end
end


/- BEGIN EXACT BODY: FourPapers.Sublattice.RP2IntegralHomology -/
section

/-! # The integral torsion group in the six-vertex complex

The cokernel below is the literal quotient by the actual boundary range.
All matrix changes and the comparison to augmented exterior chains are
included in the dependency chain.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice.RP2
open Classical CommAlg Matrix FourPapers.FilteredHomology
universe u
variable {k : Type u} [CommRing k]

theorem normal_d0 (x : Fin 6→k) : normalDifferential 0 x 0=x 0 := by
  change ((RP2Matrices.N1.map (Int.castRingHom k)) *ᵥ x) (0 : Fin 1) = x 0
  simp [RP2Matrices.N1, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem normal_d1 (x : Fin 15→k) (i : Fin 6) :
    normalDifferential 1 x i=if h : i.val=0 then 0 else x ⟨i.val-1,by omega⟩ := by
  change ((RP2Matrices.N2.map (Int.castRingHom k)) *ᵥ x) i = _
  fin_cases i <;>
    simp [RP2Matrices.N2, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem normal_d2 (x : Fin 10→k) (i : Fin 15) :
    normalDifferential 2 x i=
      if h : (5 : ℕ) ≤ i.val then
        (if i.val = 14 then (2 : k) else 1) * x ⟨i.val - 5, by omega⟩ else 0 := by
  change ((RP2Matrices.N3.map (Int.castRingHom k)) *ᵥ x) i = _
  fin_cases i <;>
    simp [RP2Matrices.N3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

def cycleTwoEquiv : LinearMap.ker (normalPrevious (k:=k) 2) ≃ₗ[k] (Fin 10→k) where
  toFun x j := x.val (⟨j.val+5,by omega⟩ : Fin 15)
  invFun y := ⟨fun i : Fin 15 => if hi : 5 ≤ i.val then y ⟨i.val-5,by omega⟩ else 0,by
    funext i
    change normalDifferential 1 _ i=0
    fin_cases i <;> simp [normal_d1]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have hi_lt : i.val < 15 := by simpa only [size] using i.isLt
    by_cases hi : 5 ≤ i.val
    · simp only [dif_pos hi]
      apply congrArg x.val
      apply Fin.ext
      change i.val - 5 + 5 = i.val
      omega
    · simp only [dif_neg hi]
      have hx := congrFun x.property (⟨i.val+1,by omega⟩ : Fin 6)
      change normalDifferential 1 x.val (⟨i.val+1,by omega⟩ : Fin 6)=0 at hx
      rw [normal_d1, dif_neg (show ¬i.val + 1 = 0 by omega)] at hx
      simpa only [Nat.add_sub_cancel, Fin.eta] using hx.symm
  right_inv y := by
    funext j
    simp only [show 5 ≤ j.val+5 by omega,dif_pos,Nat.add_sub_cancel]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def doubleLast : (Fin 10→k) →ₗ[k] (Fin 10→k) :=
  (Matrix.diagonal (fun j : Fin 10 => if j=9 then (2:k) else 1)).mulVecLin

@[simp] theorem doubleLast_apply (x : Fin 10→k) (j : Fin 10) :
    doubleLast x j=(if j=9 then (2:k) else 1)*x j := by
  change ((Matrix.diagonal (fun i : Fin 10 => if i = 9 then (2 : k) else 1)) *ᵥ x) j = _
  exact Matrix.mulVec_diagonal _ _ _

theorem cycleTwo_boundary :
    cycleTwoEquiv.toLinearMap.comp
      (FourPapers.FilteredHomology.boundaryMap (normalDifferential (k:=k) 2)
        (normalPrevious 2) (normalPrevious_comp 2))=doubleLast := by
  apply LinearMap.ext
  intro x
  funext j
  change normalDifferential (k := k) 2 x (⟨j.val + 5, by omega⟩ : Fin 15) = doubleLast (k := k) x j
  rw [normal_d2, doubleLast_apply]
  simp only [Fin.val_mk]
  rw [dif_pos (by omega)]
  have he : j.val+5=14 ↔ j=9 := by
    constructor
    · intro h
      apply Fin.ext
      omega
    · intro h
      subst j
      rfl
  simp only [he, Nat.add_sub_cancel, Fin.eta]

def normalH2CokernelEquiv : NormalHomology (k:=k) 2 ≃ₗ[k]
    ((Fin 10→k) ⧸ LinearMap.range (doubleLast (k:=k))) :=
  Submodule.Quotient.equiv
    (LinearMap.range (FourPapers.FilteredHomology.boundaryMap
      (normalDifferential (k := k) 2) (normalPrevious (k := k) 2)
      (normalPrevious_comp (k := k) 2)))
    (LinearMap.range (doubleLast (k := k))) (cycleTwoEquiv (k := k)) (by
      rw [← LinearMap.range_comp, cycleTwo_boundary (k := k)])

def twoIdeal : Ideal k := Ideal.span {(2:k)}

def lastModuloTwo : (Fin 10→k) →ₗ[k] (k ⧸ twoIdeal) :=
  (twoIdeal (k := k) : Submodule k k).mkQ.comp (LinearMap.proj 9)

theorem lastModuloTwo_surjective : Function.Surjective (lastModuloTwo (k:=k)) := by
  intro z
  obtain ⟨r,rfl⟩ := (twoIdeal (k := k) : Submodule k k).mkQ_surjective z
  exact ⟨Pi.single 9 r,by simp [lastModuloTwo]⟩

theorem lastModuloTwo_kernel : LinearMap.ker (lastModuloTwo (k:=k))=LinearMap.range doubleLast := by
  ext x
  constructor
  · intro hx
    have hx9 : x 9 ∈ twoIdeal (k := k) := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨c,hc⟩ := Ideal.mem_span_singleton'.mp hx9
    refine ⟨fun j => if j=9 then c else x j,?_⟩
    funext j
    by_cases hj : j=9
    · subst j
      simpa [doubleLast_apply,mul_comm] using hc
    · simp [doubleLast_apply,hj]
  · rintro ⟨y,rfl⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Ideal.mem_span_singleton'.mpr ⟨y 9,by simp [doubleLast_apply,mul_comm]⟩

/-- Reduced degree one is exactly the coefficient ring modulo 2. -/
def normalH2Equiv : NormalHomology (k:=k) 2 ≃ₗ[k] (k ⧸ twoIdeal) :=
  (normalH2CokernelEquiv (k := k)).trans
    ((Submodule.quotEquivOfEq _ _ (lastModuloTwo_kernel (k := k)).symm).trans
      ((lastModuloTwo (k := k)).quotKerEquivOfSurjective (lastModuloTwo_surjective (k := k))))

private theorem homology_subsingleton_of_fill
    {X Y Z : Type*} [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] [AddCommGroup Z] [Module k Z]
    (f : X→ₗ[k]Y) (g : Y→ₗ[k]Z) (hfg : g.comp f=0)
    (hfill : ∀ z : LinearMap.ker g,∃ y,f y=z.val) : Subsingleton (Homology f g hfg) := by
  apply subsingleton_of_forall_eq 0
  intro z
  obtain ⟨x,rfl⟩ := (LinearMap.range (FourPapers.FilteredHomology.boundaryMap f g hfg)).mkQ_surjective z
  obtain ⟨y,hy⟩ := hfill x
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y,Subtype.ext hy⟩

theorem normalH0_zero : Subsingleton (NormalHomology (k:=k) 0) := by
  apply homology_subsingleton_of_fill
  intro z
  refine ⟨Pi.single 0 (z.val 0),?_⟩
  funext i
  fin_cases i
  simp [normal_d0]

theorem normalH1_zero : Subsingleton (NormalHomology (k:=k) 1) := by
  apply homology_subsingleton_of_fill
  intro z
  have hz : z.val 0=0 := by
    have h := congrFun z.property (0 : Fin 1)
    exact (normal_d0 z.val).symm.trans h
  refine ⟨fun j : Fin 15 => if hj : j.val<5 then z.val (⟨j.val+1,by omega⟩ : Fin 6) else 0,?_⟩
  funext i
  fin_cases i <;> simp [normal_d1,hz] <;> rfl

theorem normalH_high_zero (p : ℕ) (hp : 4≤p) : Subsingleton (NormalHomology (k:=k) p) := by
  have hs : size p=0 := by match p with | 0 | 1 | 2 | 3 => omega | p+4 => rfl
  letI : IsEmpty (Fin (size p)) := by rw [hs]; infer_instance
  unfold NormalHomology FourPapers.FilteredHomology.Homology
  infer_instance

theorem normalH3_zero_of_two_regular
    (h2 : ∀ a : k,(2:k)*a=0 → a=0) : Subsingleton (NormalHomology (k:=k) 3) := by
  apply homology_subsingleton_of_fill
  intro z
  have hz : z.val=0 := by
    change (fun j : Fin 10 => z.val j) = (fun _ : Fin 10 => (0 : k))
    funext j
    have h := congrFun z.property (⟨j.val+5,by omega⟩ : Fin 15)
    change normalDifferential 2 z.val (⟨j.val+5,by omega⟩ : Fin 15)=0 at h
    rw [normal_d2] at h
    simp only [Fin.val_mk] at h
    rw [dif_pos (by omega)] at h
    by_cases hj : j=(9 : Fin 10)
    · subst j
      exact h2 _ (by simpa using h)
    · have hjv : j.val ≠ 9 := by
        intro he
        apply hj
        exact Fin.ext he
      have hshift : j.val+5 ≠ 14 := by omega
      simpa [hshift, hjv, Nat.add_sub_cancel] using h
  exact ⟨0,by rw [map_zero,hz]⟩

def twoKernel : Submodule k k := LinearMap.ker ((2:k) • (LinearMap.id : k→ₗ[k]k))

def cycleThreeEquiv : LinearMap.ker (normalPrevious (k:=k) 3) ≃ₗ[k] twoKernel (k:=k) where
  toFun x := ⟨x.val (9 : Fin 10),by
    have h := congrFun x.property (14 : Fin 15)
    change normalDifferential 2 x.val 14=0 at h
    simpa [normal_d2,twoKernel] using h⟩
  invFun y := ⟨Pi.single (9 : Fin 10) y.val,by
    have hy : (2:k)*y.val=0 := y.property
    funext i
    change normalDifferential 2 (Pi.single (9 : Fin 10) y.val) i=0
    fin_cases i <;> simp [normal_d2,hy]⟩
  left_inv x := by
    apply Subtype.ext
    change (Pi.single (9 : Fin 10) (x.val (9 : Fin 10)) : Fin 10 → k) = x.val
    funext j
    by_cases hj : j=(9 : Fin 10)
    · simp [hj]
    · have hjv : j.val ≠ 9 := by
        intro he
        apply hj
        exact Fin.ext he
      have h := congrFun x.property (⟨j.val+5,by omega⟩ : Fin 15)
      change normalDifferential 2 x.val (⟨j.val+5,by omega⟩ : Fin 15)=0 at h
      have hne : j.val+5≠14 := by omega
      have hz : x.val j=0 := by simpa [normal_d2,hne,hjv] using h
      simp [hj,hz]
  right_inv y := by apply Subtype.ext; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem degreeThree_boundary_range :
    LinearMap.range (FourPapers.FilteredHomology.boundaryMap (normalDifferential (k:=k) 3)
      (normalPrevious 3) (normalPrevious_comp 3))=⊥ := by
  apply le_antisymm _ bot_le
  rintro z ⟨x,rfl⟩
  have hx : x=0 := by
    funext i
    exact Fin.elim0 i
  rw [hx,map_zero]
  exact Submodule.zero_mem _

/-- Reduced degree two is the actual annihilator of 2, including for
coefficient rings where 2 is a zero divisor. -/
def normalH3Equiv : NormalHomology (k:=k) 3 ≃ₗ[k] twoKernel (k:=k) :=
  (Submodule.quotEquivOfEqBot _ (degreeThree_boundary_range (k := k))).trans
    (cycleThreeEquiv (k := k))

def twoKernelEquivOfTwoZero (h2 : (2:k)=0) : twoKernel (k:=k) ≃ₗ[k] k where
  toFun x := x.val
  invFun x := ⟨x,by simp [twoKernel,h2]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def normalH2EquivOfTwoZero (h2 : (2:k)=0) : NormalHomology (k:=k) 2 ≃ₗ[k] k :=
  (normalH2Equiv (k := k)).trans
    (Submodule.quotEquivOfEqBot (twoIdeal (k := k) : Submodule k k)
      (by simp [twoIdeal, h2]))

def normalH3EquivOfTwoZero (h2 : (2:k)=0) : NormalHomology (k:=k) 3 ≃ₗ[k] k :=
  (normalH3Equiv (k := k)).trans (twoKernelEquivOfTwoZero h2)

theorem normalH2_zero_of_two_unit (h2 : IsUnit (2:k)) : Subsingleton (NormalHomology (k:=k) 2) := by
  have hI : twoIdeal (k:=k)=⊤ := Ideal.span_singleton_eq_top.mpr h2
  have hI' : (twoIdeal (k := k) : Submodule k k)=⊤ := congrArg (fun I : Ideal k => (I : Submodule k k)) hI
  letI : Subsingleton (k ⧸ twoIdeal (k := k)) := by rw [hI']; infer_instance
  exact ⟨fun x y => (normalH2Equiv (k := k)).injective (Subsingleton.elim _ _)⟩

section Field
variable {K : Type u} [Field K]

/-- Both field contributions of the integral 2-torsion have the correct
adjacent degrees. Face indices 2 and 3 mean reduced degrees 1 and 2. -/
theorem field_homology_finrank (p : ℕ) :
    Module.finrank K (AugmentedFaceHomology (k:=K) Face downward p)=
      if (2:K)=0 ∧ (p=2 ∨ p=3) then 1 else 0 := by
  rw [(normalHomologyEquiv (k := K) p).finrank_eq]
  by_cases h2 : (2:K)=0
  · match p with
    | 0 => letI := normalH0_zero (k:=K); simp [h2, Module.finrank_zero_of_subsingleton]
    | 1 => letI := normalH1_zero (k:=K); simp [h2, Module.finrank_zero_of_subsingleton]
    | 2 => rw [(normalH2EquivOfTwoZero h2).finrank_eq]; simp [h2]
    | 3 => rw [(normalH3EquivOfTwoZero h2).finrank_eq]; simp [h2]
    | p+4 => letI := normalH_high_zero (k:=K) (p+4) (by omega); simp [h2, Module.finrank_zero_of_subsingleton]
  · match p with
    | 0 => letI := normalH0_zero (k:=K); simp [h2, Module.finrank_zero_of_subsingleton]
    | 1 => letI := normalH1_zero (k:=K); simp [h2, Module.finrank_zero_of_subsingleton]
    | 2 => letI := normalH2_zero_of_two_unit (k:=K) (isUnit_iff_ne_zero.mpr h2); simp [h2, Module.finrank_zero_of_subsingleton]
    | 3 =>
        letI := normalH3_zero_of_two_regular (k:=K)
          (fun a ha => (mul_eq_zero.mp ha).resolve_left h2)
        simp [h2, Module.finrank_zero_of_subsingleton]
    | p+4 => letI := normalH_high_zero (k:=K) (p+4) (by omega); simp [h2, Module.finrank_zero_of_subsingleton]

end Field

/-- The exact integral group claimed for the six-vertex input complex.
The face-cardinality index 2 is reduced simplicial degree 1. -/
def integralH1Equiv :
    AugmentedFaceHomology (k:=ℤ) Face downward 2 ≃ₗ[ℤ] ZMod 2 :=
  (normalHomologyEquiv (k := ℤ) 2).trans
    ((normalH2Equiv (k := ℤ)).trans (Int.quotientSpanNatEquivZMod 2).toAddEquiv.toIntLinearEquiv)

theorem integral_other_homology_zero (p : ℕ) (hp : p≠2) :
    Subsingleton (AugmentedFaceHomology (k:=ℤ) Face downward p) := by
  have h : Subsingleton (NormalHomology (k:=ℤ) p) := by
    match p with
    | 0 => exact normalH0_zero
    | 1 => exact normalH1_zero
    | 2 => exact (hp rfl).elim
    | 3 => exact normalH3_zero_of_two_regular (by intro a ha; omega)
    | p+4 => exact normalH_high_zero _ (by omega)
  letI := h
  exact ⟨fun x y => (normalHomologyEquiv (k := ℤ) p).injective (Subsingleton.elim _ _)⟩

end FourPapers.Sublattice.RP2

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.RP2IncidenceIdentification -/
section

/-!
# The literal incidence nerve in Proposition 10.2

The maps below are universe lifts of the printed thirty incidences, not
alternative examples. The finite proposition identifies all 64 subsets
of the six vertices with the actual face predicate used in the integral
chain calculation.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice.RP2
open Classical CommAlg

universe u

abbrev LeftVertex := ULift.{u} (Fin 10)
abbrev Incidence := ULift.{u} (Fin 30)

def left (e : Incidence.{u}) : LeftVertex.{u} :=
  ULift.up (projectivePlaneIncidenceLeft e.down)

def right (e : Incidence.{u}) : Vertex.{u} :=
  ULift.up (projectivePlaneIncidenceRight e.down)

theorem left_surjective : Function.Surjective (left.{u}) := by
  intro a
  obtain ⟨e,he⟩ := projectivePlaneIncidenceLeft_surjective a.down
  exact ⟨ULift.up e,congrArg (fun x : Fin 10 => (ULift.up x : LeftVertex.{u})) he⟩

theorem right_surjective : Function.Surjective (right.{u}) := by
  intro r
  obtain ⟨e,he⟩ := projectivePlaneIncidenceRight_surjective r.down
  exact ⟨ULift.up e,congrArg (fun x : Fin 6 => (ULift.up x : Vertex.{u})) he⟩

/-- The nerve defined by the ten listed minimal nonfaces is exactly the
six-vertex complex whose actual integer boundary matrices were reduced. -/
theorem nerve_iff_face : ∀ Q : Finset Vertex.{u},
    incidenceNerveFaces (left.{u}) (right.{u}) Q ↔ Face.{u} Q := by
  unfold incidenceNerveFaces
  decide

theorem nerve_eq_face : incidenceNerveFaces (left.{u}) right=Face := by
  funext Q
  exact propext (nerve_iff_face.{u} Q)

theorem nerve_has_vertex : incidenceNerveFaces (left.{u}) right {ULift.up 0} := by
  rw [nerve_iff_face]
  decide

theorem incidence_card : Fintype.card (Incidence.{u})=30 := by simp [Incidence]
theorem left_card : Fintype.card (LeftVertex.{u})=10 := by simp [LeftVertex]
theorem right_card : Fintype.card (Vertex.{u})=6 := by simp [Vertex]

variable {k : Type u} [CommRing k]

/-- Predicate transport is the identity on actual exterior chains. -/
def nerveHomologyEquiv (p : ℕ) :
    AugmentedFaceHomology (k:=k) (incidenceNerveFaces left right)
      (incidenceRowNerve_downward left right) p ≃ₗ[k]
    AugmentedFaceHomology (k:=k) Face downward p :=
  augmentedFaceHomologyEquivOfFaces (V := Vertex.{u}) (k := k)
    (incidenceNerveFaces (left.{u}) (right.{u})) Face.{u}
    (incidenceRowNerve_downward (left.{u}) (right.{u})) downward.{u} nerve_eq_face.{u} p

def nerveIntegralH1Equiv :
    AugmentedFaceHomology (k:=ℤ) (incidenceNerveFaces left right)
      (incidenceRowNerve_downward left right) 2 ≃ₗ[ℤ] ZMod 2 :=
  (nerveHomologyEquiv (k := ℤ) 2).trans integralH1Equiv

theorem nerveIntegral_other_homology_zero (p : ℕ) (hp : p≠2) :
    Subsingleton (AugmentedFaceHomology (k:=ℤ) (incidenceNerveFaces left right)
      (incidenceRowNerve_downward left right) p) := by
  letI := integral_other_homology_zero p hp
  exact ⟨fun x y => (nerveHomologyEquiv (k := ℤ) p).injective (Subsingleton.elim _ _)⟩

section Field
variable {K : Type u} [Field K]

theorem nerve_field_homology_finrank (p : ℕ) :
    Module.finrank K (AugmentedFaceHomology (k:=K) (incidenceNerveFaces left right)
      (incidenceRowNerve_downward left right) p)=
      if (2:K)=0 ∧ (p=2 ∨ p=3) then 1 else 0 := by
  rw [(nerveHomologyEquiv (k := K) p).finrank_eq]
  exact field_homology_finrank p

end Field
end FourPapers.Sublattice.RP2

end
end
end



end
