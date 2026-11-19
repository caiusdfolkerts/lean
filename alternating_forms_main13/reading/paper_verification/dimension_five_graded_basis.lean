module

public import PaperVerification.KoszulBarObstruction
public import PaperVerification.WeightedBarTor
public import TauCeti.Algebra.Module.GradedModule.Internal
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# A genuine homogeneous augmented basis for the dimension-five Hilbert profile

The grading is supplied independently as an internal direct sum in an actual
algebra. The basis is assembled from its genuine homogeneous components;
its product coefficients are proved homogeneous from multiplication in that
algebra. The resulting obstruction lies in ordinary augmentation Tor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.DimensionFiveGradedBasis

universe u

abbrev rankProfile : ℕ → ℕ
  | 0 => 1
  | 1 => 5
  | 2 => 8
  | 3 => 1
  | _+4 => 0

abbrev PositiveIndex := ULift.{u} (Fin 5 ⊕ (Fin 8 ⊕ Fin 1))

def positiveDegree : PositiveIndex.{u} → ℕ
  | ⟨.inl _⟩ => 1
  | ⟨.inr (.inl _)⟩ => 2
  | ⟨.inr (.inr _)⟩ => 3

theorem positiveDegree_pos (i : PositiveIndex.{u}) : 0<positiveDegree i := by
  rcases i with ⟨i | i | i⟩ <;> simp only [positiveDegree] <;> omega

def indexEquiv : (Σ d,Fin (rankProfile d)) ≃ Option PositiveIndex.{u} where
  toFun
    | ⟨0,_⟩ => none
    | ⟨1,i⟩ => some ⟨.inl i⟩
    | ⟨2,i⟩ => some ⟨.inr (.inl i)⟩
    | ⟨3,i⟩ => some ⟨.inr (.inr i)⟩
    | ⟨_+4,i⟩ => Fin.elim0 i
  invFun
    | none => ⟨0,0⟩
    | some ⟨.inl i⟩ => ⟨1,i⟩
    | some ⟨.inr (.inl i)⟩ => ⟨2,i⟩
    | some ⟨.inr (.inr i)⟩ => ⟨3,i⟩
  left_inv := by
    rintro ⟨d,i⟩
    rcases d with _ | _ | _ | _ | d
    · have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rfl
    · rfl
    · rfl
    · rfl
    · exact Fin.elim0 i
  right_inv := by
    rintro (_ | ⟨i | i | i⟩) <;> rfl

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  (G : TauCeti.InternalGrading K A ℕ) (ε : A →ₐ[K] K)
  (hzero : G.piece 0=(1 : Submodule K A))

/-- The degree-zero isomorphism is the actual scalar inclusion. -/
def scalarPieceMap : K →ₗ[K] G.piece 0 :=
  LinearMap.codRestrict _ (Algebra.ofId K A).toLinearMap (fun c => by
    rw [hzero]
    exact Submodule.mem_one.mpr ⟨c,rfl⟩)

@[simp] theorem scalarPieceMap_val (c : K) :
    (scalarPieceMap G hzero c).val=algebraMap K A c := rfl

def scalarPieceEquiv : K ≃ₗ[K] G.piece 0 :=
  LinearEquiv.ofBijective (scalarPieceMap G hzero) (by
    constructor
    · intro c d h
      have he := congrArg (fun x : G.piece 0 => ε x.val) h
      simpa only [scalarPieceMap_val,AlgHom.commutes,Algebra.algebraMap_self,
        RingHom.id_apply] using he
    · intro x
      have hx : x.val∈(1 : Submodule K A) := hzero ▸ x.property
      obtain ⟨c,hc⟩ := Submodule.mem_one.mp hx
      exact ⟨c,Subtype.ext hc⟩)

@[simp] theorem scalarPieceEquiv_val (c : K) :
    (scalarPieceEquiv G ε hzero c).val=algebraMap K A c := rfl

variable [∀ d,Module.Finite K (G.piece d)]
  (hprofile : ∀ d,Module.finrank K (G.piece d)=rankProfile d)

def degreeBasis : (d : ℕ) → Module.Basis (Fin (rankProfile d)) K (G.piece d)
  | 0 => (Module.Basis.singleton (Fin 1) K).map (scalarPieceEquiv G ε hzero)
  | d+1 => Module.finBasisOfFinrankEq K (G.piece (d+1)) (hprofile (d+1))

def basis : Module.Basis (Option PositiveIndex.{u}) K A :=
  (G.isInternal.collectedBasis (degreeBasis G ε hzero hprofile)).reindex indexEquiv

theorem basis_none : basis G ε hzero hprofile none=1 := by
  rw [basis,Module.Basis.reindex_apply,DirectSum.IsInternal.collectedBasis_coe]
  change ((degreeBasis G ε hzero hprofile 0) 0 : A)=1
  simp only [degreeBasis,Module.Basis.map_apply,Module.Basis.singleton_apply,
    scalarPieceEquiv_val,map_one]

theorem basis_positive_mem (i : PositiveIndex.{u}) :
    basis G ε hzero hprofile (some i)∈G.piece (positiveDegree i) := by
  rw [basis,Module.Basis.reindex_apply]
  rcases i with ⟨i | i | i⟩
  · change (G.isInternal.collectedBasis (degreeBasis G ε hzero hprofile)) ⟨1,i⟩∈G.piece 1
    exact G.isInternal.collectedBasis_mem (degreeBasis G ε hzero hprofile) ⟨1,i⟩
  · change (G.isInternal.collectedBasis (degreeBasis G ε hzero hprofile)) ⟨2,i⟩∈G.piece 2
    exact G.isInternal.collectedBasis_mem (degreeBasis G ε hzero hprofile) ⟨2,i⟩
  · change (G.isInternal.collectedBasis (degreeBasis G ε hzero hprofile)) ⟨3,i⟩∈G.piece 3
    exact G.isInternal.collectedBasis_mem (degreeBasis G ε hzero hprofile) ⟨3,i⟩

theorem basis_repr_of_mem_ne {d : ℕ} {x : A} (hx : x∈G.piece d)
    (i : PositiveIndex.{u}) (hi : d≠positiveDegree i) :
    (basis G ε hzero hprofile).repr x (some i)=0 := by
  rw [basis,Module.Basis.repr_reindex_apply]
  rcases i with ⟨i | i | i⟩ <;>
    exact G.isInternal.collectedBasis_repr_of_mem_ne
      (degreeBasis G ε hzero hprofile) hi hx

variable (hε : ∀ d,0<d → ∀ x,x∈G.piece d → ε x=0)
  (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))

include hε in
theorem basis_positive_augmentation (i : PositiveIndex.{u}) :
    ε (basis G ε hzero hprofile (some i))=0 :=
  hε _ (positiveDegree_pos i) _ (basis_positive_mem G ε hzero hprofile i)

include hmul in
theorem product_homogeneous (a b c : PositiveIndex.{u})
    (h : AugmentedAlgebraBasis.productCoefficients (basis G ε hzero hprofile) a b c≠0) :
    positiveDegree c=positiveDegree a+positiveDegree b := by
  by_contra hc
  apply h
  change (basis G ε hzero hprofile).repr
    (basis G ε hzero hprofile (some a)*basis G ε hzero hprofile (some b)) (some c)=0
  exact basis_repr_of_mem_ne G ε hzero hprofile
    (hmul _ _ _ _ (basis_positive_mem G ε hzero hprofile a)
      (basis_positive_mem G ε hzero hprofile b)) c (Ne.symm hc)

theorem positiveSeries_eq :
    WeightedBar.positiveSeries positiveDegree.{u}=KoszulBarObstruction.dimensionFivePositiveSeries := by
  have he : WeightedBar.positiveSeries positiveDegree.{u}=
      5 • (PowerSeries.X : ℤ⟦X⟧)+8 • PowerSeries.X^2+PowerSeries.X^3 := by
    change (∑ i : PositiveIndex.{u},PowerSeries.X^(positiveDegree i))=_
    calc
      _ = ∑ i : Fin 5 ⊕ (Fin 8 ⊕ Fin 1),
          (PowerSeries.X : ℤ⟦X⟧)^(positiveDegree (ULift.up i : PositiveIndex.{u})) :=
        Fintype.sum_equiv (Equiv.ulift : PositiveIndex.{u} ≃ _) _ _ (fun _ => rfl)
      _ = _ := by simp [Fintype.sum_sum_type,positiveDegree,add_assoc]
  rw [he]
  apply PowerSeries.ext
  intro d
  rw [map_add,map_add,map_nsmul,map_nsmul]
  rw [←pow_one (PowerSeries.X : ℤ⟦X⟧)]
  simp only [PowerSeries.coeff_X_pow,KoszulBarObstruction.dimensionFivePositiveSeries,
    PowerSeries.coeff_mk]
  split_ifs <;> simp_all

set_option maxHeartbeats 800000 in
/-- The degree-six obstruction survives as a nonzero subspace of ordinary Tor. -/
theorem ordinaryTor_off_diagonal :
    ∃ r,r<6 ∧ WeightedBar.torPiece ε (basis G ε hzero hprofile)
      (basis_none G ε hzero hprofile)
      (basis_positive_augmentation G ε hzero hprofile hε)
      positiveDegree (product_homogeneous G ε hzero hprofile hmul) r 6≠⊥ := by
  obtain ⟨r,hr,hn⟩ := KoszulBarObstruction.dimensionFive_actual_bar_off_diagonal
    ε (basis G ε hzero hprofile) (basis_none G ε hzero hprofile)
      (basis_positive_augmentation G ε hzero hprofile hε)
      positiveDegree (product_homogeneous G ε hzero hprofile hmul)
      positiveDegree_pos positiveSeries_eq
  refine ⟨r,hr,?_⟩
  intro hz
  exact hn ((WeightedBar.torPiece_eq_bot_iff ε (basis G ε hzero hprofile)
    (basis_none G ε hzero hprofile)
    (basis_positive_augmentation G ε hzero hprofile hε)
    positiveDegree (product_homogeneous G ε hzero hprofile hmul) r 6).mp hz)

end PaperVerification.DimensionFiveGradedBasis
