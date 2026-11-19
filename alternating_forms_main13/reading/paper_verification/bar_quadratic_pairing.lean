module

public import PaperVerification.DiagonalBarRelations
public import PaperVerification.FreeAlgebraWordDegree

/-!
# The actual finite pairing between diagonal bar words and quadratic words

The pairing is the coefficient pairing on the literal degree-one letters.
It identifies the actual outgoing differential kernel with the dual of
an actual RingQuot homogeneous piece. The defining quadratic relations
are the multiplication rows of the given algebra, not an assumed Koszul
Hilbert identity or a definition of homology.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.BarQuadraticPairing

open WeightedBar DiagonalBarWords DiagonalBarRelations AugmentedAlgebraBasis
open QuadraticWordFunctionals

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hpos : ∀ i,0<δ i)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

local notation "J₁" => DegreeOne δ
local notation "F" => FreeAlgebra K J₁
local notation "b" => (FreeAlgebraWordDegree.basis (K := K) (J := J₁))

def wordSpaceBasis (n : ℕ) : Module.Basis (PureWord δ n) K (degreeSpace b n) := by
  let v : PureWord δ n → F := fun L ↦ b L.val
  have hli : LinearIndependent K v :=
    (b).linearIndependent.comp Subtype.val Subtype.val_injective
  have hs : Submodule.span K (Set.range v)=degreeSpace b n := by
    congr 1
    ext x
    constructor
    · rintro ⟨L,rfl⟩
      exact ⟨L.val,L.property,rfl⟩
    · rintro ⟨L,hL,rfl⟩
      exact ⟨⟨L,hL⟩,rfl⟩
  exact (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hs)

@[simp] theorem wordSpaceBasis_val (n : ℕ) (L : PureWord δ n) :
    (wordSpaceBasis (K := K) δ n L).val=b L.val := by
  simp only [wordSpaceBasis,Module.Basis.map_apply]
  exact (LinearEquiv.coe_ofEq_apply _ _).trans (Module.Basis.coe_span_apply _ L)

/-- Finite coefficient pairing on the actual diagonal word basis. -/
def pairing (n : ℕ) : piece (K := K) δ n n ≃ₗ[K] Module.Dual K (degreeSpace b n) :=
  (diagonalBasis δ hpos n).repr.trans (wordSpaceBasis δ n).dualBasis.repr.symm

@[simp] theorem pairing_basis (n : ℕ) (z : piece (K := K) δ n n)
    (L : PureWord δ n) :
    pairing δ hpos n z (wordSpaceBasis δ n L)=z.val (embedWord δ L.val) := by
  rw [←Module.Basis.dualBasis_repr]
  change (wordSpaceBasis δ n).dualBasis.repr
    ((wordSpaceBasis δ n).dualBasis.repr.symm ((diagonalBasis δ hpos n).repr z)) L=_
  rw [LinearEquiv.apply_symm_apply,diagonalBasis_repr]

/-- Extend a homogeneous functional by the genuine word-degree projection. -/
def extendedPairing (n : ℕ) (z : piece (K := K) δ n n) : F →ₗ[K] K :=
  (pairing δ hpos n z).comp (projectionToPiece b n)

@[simp] theorem extendedPairing_basis (n : ℕ) (z : piece (K := K) δ n n)
    (L : List J₁) : extendedPairing δ hpos n z (b L)=z.val (embedWord δ L) := by
  by_cases hL : L.length=n
  · have he : projectionToPiece b n (b L)=wordSpaceBasis δ n ⟨L,hL⟩ := by
      apply Subtype.ext
      rw [projectionToPiece_val,projection_basis,if_pos hL,wordSpaceBasis_val]
    change pairing δ hpos n z (projectionToPiece b n (b L))=_
    rw [he,pairing_basis]
  · have he : projectionToPiece b n (b L)=0 := by
      apply Subtype.ext
      rw [projectionToPiece_val,projection_basis,if_neg hL]
      rfl
    change pairing δ hpos n z (projectionToPiece b n (b L))=_
    rw [he,map_zero]
    symm
    by_contra hn
    have hz := z.property (Finsupp.mem_support_iff.mpr hn)
    exact hL ((embedWord_length δ L).symm.trans hz.1)

/-- Literal multiplication-row relation in the actual free algebra. -/
def rowRelation (c : DegreeTwo δ) : F :=
  ∑ a : J₁,∑ d : J₁,productCoefficients B a.val d.val c.val • b [a,d]

def relationSpace : Submodule K F := Submodule.span K (Set.range (rowRelation B δ))

theorem relationSpace_homogeneous : relationSpace B δ≤degreeSpace b 2 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨c,rfl⟩
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.sum_mem
  intro d hd
  exact Submodule.smul_mem _ _ (basis_mem_degreeSpace b [a,d])

include hpos in
theorem extendedPairing_row (n : ℕ) (z : piece (K := K) δ n n)
    (P : List J₁) (c : DegreeTwo δ) (Q : List J₁) :
    extendedPairing δ hpos n z (b P*rowRelation B δ c*b Q)=
      contextRow B δ z.val P c Q := by
  simp only [rowRelation,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    map_sum,map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro d hd
  rw [←FreeAlgebraWordDegree.basis_append,←FreeAlgebraWordDegree.basis_append,
    extendedPairing_basis]
  simp only [embedWord,List.map_append,List.map_cons,List.map_nil,
    List.append_assoc,List.cons_append,List.nil_append]

include hpos in
theorem pairing_mem_relationFunctionals_iff (n : ℕ) (z : piece (K := K) δ n n) :
    pairing δ hpos n z∈relationFunctionals b (relationSpace B δ) n ↔
      ∀ P : List J₁,∀ c : DegreeTwo δ,∀ Q : List J₁,contextRow B δ z.val P c Q=0 := by
  constructor
  · intro h P c Q
    have he := h P Q (rowRelation B δ c) (Submodule.subset_span ⟨c,rfl⟩)
    exact (extendedPairing_row B δ hpos n z P c Q).symm.trans he
  · intro h P Q q hq
    change extendedPairing δ hpos n z (b P*q*b Q)=0
    induction hq using Submodule.span_induction with
    | mem q hq =>
        obtain ⟨c,rfl⟩ := hq
        exact (extendedPairing_row B δ hpos n z P c Q).trans (h P c Q)
    | zero => simp only [mul_zero,zero_mul,map_zero]
    | add x y hx hy ihx ihy =>
        simp only [mul_add,add_mul,map_add,ihx,ihy,add_zero]
    | smul a x hx ih =>
        simp only [mul_smul_comm,smul_mul_assoc,map_smul,ih,smul_zero]

/-- Kernel of the actual reduced-bar outgoing differential, in its original degree. -/
def diagonalCycles (n : ℕ) : Submodule K (piece (K := K) δ n n) :=
  LinearMap.ker ((ReducedBarBasis.differential B).comp (piece δ n n).subtype)

include hpos hδ in
theorem diagonalCycles_eq_comap (r : ℕ) :
    diagonalCycles B δ (r+1)=
      (relationFunctionals b (relationSpace B δ) (r+1)).comap
        (pairing δ hpos (r+1)).toLinearMap := by
  ext z
  change ReducedBarBasis.differential B z.val=0 ↔
    pairing δ hpos (r+1) z∈relationFunctionals b (relationSpace B δ) (r+1)
  rw [differential_eq_zero_iff_contexts B δ hpos hδ,
    pairing_mem_relationFunctionals_iff B δ hpos]

/-- Actual diagonal cycles are dual to the actual multiplication-row quotient piece. -/
def cyclesDualQuotientEquiv (r : ℕ) :
    diagonalCycles B δ (r+1) ≃ₗ[K]
      Module.Dual K (quotientPiece b (relationSpace B δ) (r+1)) :=
  ((LinearEquiv.ofEq _ _ (diagonalCycles_eq_comap B δ hpos hδ r)).trans
    ((pairing δ hpos (r+1)).ofSubmodule'
      (relationFunctionals b (relationSpace B δ) (r+1)))).trans
    (dualPieceEquiv b FreeAlgebraWordDegree.basis_append (relationSpace B δ)
      (relationSpace_homogeneous B δ) (r+1)).symm

end PaperVerification.BarQuadraticPairing
