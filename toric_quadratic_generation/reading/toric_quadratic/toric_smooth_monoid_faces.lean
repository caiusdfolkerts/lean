module

public import PaperVerification.ToricOrbitQuotientCoordinates

@[expose] public section

/-!
# Additive faces of an actual smooth full cone

A full smooth dual cone is the nonnegative integer span of an integral
basis. Every additive face is obtained by forcing a subset of those
coordinates to zero. This is proved by basis expansion and the actual
additive-face property.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open scoped BigOperators Classical

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup E] [Module ℤ E]
    (b : Module.Basis ι ℤ E)

abbrev fullCoordinateMonoid := coordinateConeMonoid b Finset.univ

def fullConeBasisVector (i : ι) : fullCoordinateMonoid b :=
  ⟨b i,by
    intro j hj
    rw [b.repr_self_apply]
    split_ifs <;> norm_num⟩

@[simp] theorem fullConeBasisVector_repr (i j : ι) :
    b.repr (fullConeBasisVector b i).val j=if i=j then 1 else 0 :=
  b.repr_self_apply (i := i) j

theorem fullCoordinate_nonneg (x : fullCoordinateMonoid b) (i : ι) :
    0≤b.repr x.val i := x.property i (Finset.mem_univ i)

theorem fullCoordinate_basis_sum (x : fullCoordinateMonoid b) :
    (∑ i,(b.repr x.val i).toNat • fullConeBasisVector b i)=x := by
  apply Subtype.ext
  change (fullCoordinateMonoid b).subtype
    (∑ i,(b.repr x.val i).toNat • fullConeBasisVector b i) = x.val
  rw [map_sum]
  simp only [map_nsmul]
  change (∑ i,(b.repr x.val i).toNat • b i)=x.val
  calc
    _=(∑ i,b.repr x.val i • b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← natCast_zsmul,Int.toNat_of_nonneg (fullCoordinate_nonneg b x i)]
    _=x.val :=
      (Finset.sum_congr rfl (fun i _ =>
        (int_smul_eq_zsmul (inferInstance : Module ℤ E)
          (b.repr x.val i) (b i)).symm)).trans (b.sum_repr x.val)

def fullConeSubtractBasis (x : fullCoordinateMonoid b) (i : ι)
    (hi : 0<b.repr x.val i) : fullCoordinateMonoid b :=
  ⟨x.val-b i,by
    intro j hj
    rw [map_sub,Finsupp.sub_apply,b.repr_self_apply]
    by_cases h : i=j
    · subst j
      simp only [if_pos rfl]
      omega
    · simp only [if_neg h,sub_zero]
      exact fullCoordinate_nonneg b x j⟩

theorem fullConeSubtractBasis_add (x : fullCoordinateMonoid b) (i : ι)
    (hi : 0<b.repr x.val i) :
    fullConeBasisVector b i+fullConeSubtractBasis b x i hi=x := by
  apply Subtype.ext
  change b i+(x.val-b i)=x.val
  abel

theorem additiveFace_basis_mem_of_coordinate_pos
    (F : AddSubmonoid (fullCoordinateMonoid b)) (hF : IsAdditiveFace F)
    {x : fullCoordinateMonoid b} (hx : x∈F) (i : ι)
    (hi : 0<b.repr x.val i) : fullConeBasisVector b i∈F := by
  have hsum : fullConeBasisVector b i+fullConeSubtractBasis b x i hi∈F := by
    rwa [fullConeSubtractBasis_add]
  exact (hF _ _ hsum).1

/-- Exactly the coordinates omitted by an additive face. -/
def forbiddenFaceCoordinates (F : AddSubmonoid (fullCoordinateMonoid b)) : Finset ι :=
  Finset.univ.filter (fun i=>fullConeBasisVector b i∉F)

theorem additiveFace_mem_iff_zero_coordinates
    (F : AddSubmonoid (fullCoordinateMonoid b)) (hF : IsAdditiveFace F)
    (x : fullCoordinateMonoid b) :
    x∈F ↔ ∀ i∈forbiddenFaceCoordinates b F,b.repr x.val i=0 := by
  constructor
  · intro hx i hi
    have hnot := (Finset.mem_filter.mp hi).2
    have hn := fullCoordinate_nonneg b x i
    by_contra hz
    have hp : 0<b.repr x.val i := lt_of_le_of_ne hn (Ne.symm hz)
    exact hnot (additiveFace_basis_mem_of_coordinate_pos b F hF hx i hp)
  · intro hx
    rw [← fullCoordinate_basis_sum b x]
    apply F.sum_mem
    intro i hi
    by_cases hmem : fullConeBasisVector b i∈F
    · exact F.nsmul_mem hmem _
    · have hz := hx i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hmem⟩)
      simp only [hz,Int.toNat_zero,zero_nsmul,F.zero_mem]

end PaperVerification.ToricCharacters

namespace PaperVerification.ToricGeometry

open PaperVerification.ToricCharacters
open scoped BigOperators Classical

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))

def fullDualConeBasisVector (i : Fin n) :
    dualConeMonoid (Finset.univ.image b) :=
  ⟨integralDualBasis b i,by
    intro u hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hu
    rw [integerPairing_basis_eq_dualCoordinate,(integralDualBasis b).repr_self_apply]
    split_ifs <;> norm_num⟩

def fullDualForbiddenCoordinates
    (F : AddSubmonoid (dualConeMonoid (Finset.univ.image b))) : Finset (Fin n) :=
  Finset.univ.filter (fun i=>fullDualConeBasisVector b i∉F)

/-- Every actual additive face of a smooth full dual cone is the face
annihilating an actual subset of the original primitive cone rays. -/
theorem fullDual_additiveFace_eq_orbitFace
    (F : AddSubmonoid (dualConeMonoid (Finset.univ.image b)))
    (hF : IsAdditiveFace F) :
    F=orbitCharacterFace (Finset.univ.image b)
      ((fullDualForbiddenCoordinates b F).image b) := by
  have he : dualConeMonoid (Finset.univ.image b)=
      fullCoordinateMonoid (integralDualBasis b) := dualConeMonoid_basis_eq b Finset.univ
  let e : dualConeMonoid (Finset.univ.image b)≃+
      fullCoordinateMonoid (integralDualBasis b) :=
    { toFun x := ⟨x.val,he ▸ x.property⟩
      invFun x := ⟨x.val,he.symm ▸ x.property⟩
      left_inv x := Subtype.ext rfl
      right_inv x := Subtype.ext rfl
      map_add' x y := Subtype.ext rfl }
  let F' := F.map e.toAddMonoidHom
  have hF' : IsAdditiveFace F' := by
    intro x y h
    obtain ⟨z,hz,hzxy⟩ := h
    have heq : z=e.symm x+e.symm y := by
      apply e.injective
      simpa using hzxy
    have hm := hF _ _ (heq ▸ hz)
    exact ⟨⟨e.symm x,hm.1,e.apply_symm_apply x⟩,
      ⟨e.symm y,hm.2,e.apply_symm_apply y⟩⟩
  have hmem (x : dualConeMonoid (Finset.univ.image b)) : e x∈F'↔x∈F := by
    constructor
    · rintro ⟨y,hy,he⟩
      exact e.injective he ▸ hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  have haxis (i : Fin n) : e (fullDualConeBasisVector b i)=
      fullConeBasisVector (integralDualBasis b) i := by
    apply Subtype.ext
    rfl
  have hind : forbiddenFaceCoordinates (integralDualBasis b) F'=
      fullDualForbiddenCoordinates b F := by
    ext i
    simp only [forbiddenFaceCoordinates,fullDualForbiddenCoordinates,Finset.mem_filter,
      Finset.mem_univ,true_and,← haxis,hmem]
  ext x
  rw [← hmem x,additiveFace_mem_iff_zero_coordinates _ F' hF',hind]
  change (∀ i∈fullDualForbiddenCoordinates b F,
    (integralDualBasis b).repr x.val i=0) ↔
      ∀ u∈(fullDualForbiddenCoordinates b F).image b,integerPairing u x.val=0
  constructor
  · intro hx u hu
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    rw [integerPairing_basis_eq_dualCoordinate]
    exact hx i hi
  · intro hx i hi
    rw [← integerPairing_basis_eq_dualCoordinate]
    exact hx (b i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.fullDual_additiveFace_eq_orbitFace
