module

public import PaperVerification.AlternatingFormsBarCutDifferential
public import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Literal bar fibers for arbitrary quadratic word relations

A bar tensor is a list of actual positive basis indices. The equivalence
of each positive factor with its normal word identifies fixed-concatenation
tensor indices with the admissible factorizations used in the cut complex.
No tensor factors, internal degrees, or basis words are discarded.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PaperVerification.QuadraticWordBar

open PaperVerification.AlternatingForms.BarCompositions


/-- A nonempty word whose literal adjacent pairs are allowed. No reflexivity
or order structure is required, so square-zero generators are included. -/
def PositiveWord {J : Type*} (R : J → J → Prop) :=
  {W : List J // 0 < W.length ∧ W.IsChain R}

variable {C J : Type*} {R : J → J → Prop} (e : C ≃ PositiveWord R)

def flattenBarWord (L : List C) : List J :=
  (L.map (fun c ↦ (e c).val)).flatten

def ActualBarIndex (W : List J) (r : ℕ) :=
  {L : List C // flattenBarWord e L=W ∧ L.length=r}

def actualFactorization (W : List J) (r : ℕ) (L : ActualBarIndex e W r) :
    BarIndex R W r :=
  ⟨⟨⟨L.val.map (fun c ↦ (e c).val),L.property.1,by
    intro T hT
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hT
    exact (e c).property.1⟩,by
      intro T hT
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hT
      exact (e c).property.2⟩,by
        simpa only [List.length_map] using L.property.2⟩

def factorizationBarWord (W : List J) (L : AdmissibleFactorization R W) : List C :=
  L.val.val.attach.map (fun T ↦ e.symm
    ⟨T.val,L.val.property.2 T.val T.property,L.property T.val T.property⟩)

theorem factorizationBarWord_map (W : List J)
    (L : AdmissibleFactorization R W) :
    (factorizationBarWord e W L).map (fun c ↦ (e c).val)=L.val.val := by
  simp only [factorizationBarWord,List.map_map,Function.comp_def]
  calc
    _ = L.val.val.attach.map Subtype.val := by
      apply List.map_congr_left
      intro T hT
      exact congrArg (fun Z : PositiveWord R => Z.val)
        (e.apply_symm_apply ⟨T.val,L.val.property.2 T.val T.property,
          L.property T.val T.property⟩)
    _ = _ := List.attach_map_subtype_val _

theorem factorizationBarWord_flatten (W : List J)
    (L : AdmissibleFactorization R W) :
    flattenBarWord e (factorizationBarWord e W L)=W := by
  rw [flattenBarWord,factorizationBarWord_map,L.val.property.1]

theorem factorizationBarWord_length (W : List J)
    (L : AdmissibleFactorization R W) :
    (factorizationBarWord e W L).length=L.val.val.length := by
  simp only [factorizationBarWord,List.length_map,List.length_attach]

def actualBarIndexEquiv (W : List J) (r : ℕ) :
    ActualBarIndex e W r ≃ BarIndex R W r where
  toFun := actualFactorization e W r
  invFun L := ⟨factorizationBarWord e W L.val,
    factorizationBarWord_flatten e W L.val,
    (factorizationBarWord_length e W L.val).trans L.property⟩
  left_inv L := by
    apply Subtype.ext
    apply (List.map_injective_iff.mpr
      (show Function.Injective (fun c : C ↦ (e c).val) from
        fun c d h ↦ e.injective (Subtype.ext h)))
    rw [factorizationBarWord_map]
    rfl
  right_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact factorizationBarWord_map e W L.val

@[simp] theorem actualBarIndexEquiv_length (W : List J) (r : ℕ)
    (L : ActualBarIndex e W r) :
    (actualBarIndexEquiv e W r L).val.val.val.length=L.val.length :=
  List.length_map _

def InternalDegreeIndex (r N : ℕ) :=
  {L : List C // L.length=r ∧ (flattenBarWord e L).length=N}

def internalDegreeFiberEquiv (r N : ℕ) :
    InternalDegreeIndex e r N ≃
      Σ W : {W : List J // W.length=N},ActualBarIndex e W.val r where
  toFun L := ⟨⟨flattenBarWord e L.val,L.property.2⟩,⟨L.val,rfl,L.property.1⟩⟩
  invFun L := ⟨L.2.val,L.2.property.2,by
    rw [L.2.property.1]
    exact L.1.property⟩
  left_inv L := rfl
  right_inv L := by
    rcases L with ⟨⟨W,hW⟩,⟨L,hL,hlen⟩⟩
    dsimp only at hL
    subst W
    rfl

def internalDegreeCutFiberEquiv (r N : ℕ) :
    InternalDegreeIndex e r N ≃
      Σ W : {W : List J // W.length=N},BarIndex R W.val r :=
  (internalDegreeFiberEquiv e r N).trans
    (Equiv.sigmaCongrRight (fun W ↦ actualBarIndexEquiv e W.val r))

variable {K : Type*} [CommRing K]

def internalDegreePiece (r N : ℕ) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | L.length=r ∧ (flattenBarWord e L).length=N}

def internalDegreeCoordinates (r N : ℕ) :
    internalDegreePiece (K := K) e r N ≃ₗ[K] (InternalDegreeIndex e r N →₀ K) :=
  Finsupp.supportedEquivFinsupp (R := K) _

def internalDegreeCutCoordinates (r N : ℕ) :
    internalDegreePiece (K := K) e r N ≃ₗ[K]
      ((Σ W : {W : List J // W.length=N},BarIndex R W.val r) →₀ K) :=
  (internalDegreeCoordinates e r N).trans
    (Finsupp.domLCongr (internalDegreeCutFiberEquiv e r N))

end PaperVerification.QuadraticWordBar

