module

public import PaperVerification.DimensionFiveGradedBasis
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The positive Hilbert series is independent of a homogeneous basis

Actual projections in an internal grading show that the vectors of any
homogeneous basis of a fixed degree form a basis of that genuine graded
piece. Thus the dimension-five ordinary Tor obstruction holds for every
homogeneous augmented basis, rather than only for the chosen construction.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.HomogeneousBasisProfile

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (G : TauCeti.InternalGrading K A ℕ)
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hzero : G.piece 0=(1 : Submodule K A)) (hunit : B none=1)
  (hhom : ∀ i,B (some i)∈G.piece (δ i))

def projection (d : ℕ) : A →ₗ[K] A :=
  (G.piece d).subtype.comp
    ((DirectSum.component K ℕ (fun j => G.piece j) d).comp
      (DirectSum.decomposeLinearEquiv (ℳ := G.piece)).toLinearMap)

@[simp] theorem projection_apply (d : ℕ) (x : A) :
    projection G d x=(DirectSum.decompose G.piece x d : A) := rfl

theorem projection_self {d : ℕ} {x : A} (hx : x∈G.piece d) :
    projection G d x=x := DirectSum.decompose_of_mem_same G.piece hx

include hzero hunit in
theorem projection_none (d : ℕ) (hd : 0<d) : projection G d (B none)=0 := by
  apply DirectSum.decompose_of_mem_ne G.piece (i := 0)
  · rw [hunit,hzero]
    exact Submodule.mem_one.mpr ⟨1,map_one _⟩
  · omega

include hhom in
theorem projection_positive (d : ℕ) (i : I) :
    projection G d (B (some i))=if δ i=d then B (some i) else 0 := by
  by_cases hi : δ i=d
  · rw [if_pos hi]
    exact DirectSum.decompose_of_mem_same G.piece (hi ▸ hhom i)
  · rw [if_neg hi]
    exact DirectSum.decompose_of_mem_ne G.piece (hhom i) hi

include hzero hunit hhom in
/-- The positive vectors in degree d span exactly the original degree-d piece. -/
theorem span_degree (d : ℕ) (hd : 0<d) :
    Submodule.span K (Set.range (fun i : {i : I // δ i=d} => B (some i.val)))=G.piece d := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change B (some i.val)∈G.piece d
    exact Eq.mp (congrArg (fun n : ℕ => B (some i.val)∈G.piece n) i.property)
      (hhom i.val)
  · intro x hx
    rw [←projection_self G hx,←B.sum_repr x,map_sum]
    apply Submodule.sum_mem
    intro i hi
    rw [map_smul]
    cases i with
    | none =>
        rw [projection_none G B hzero hunit d hd,smul_zero]
        exact Submodule.zero_mem _
    | some i =>
        rw [projection_positive G B δ hhom]
        split_ifs with he
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i,he⟩,rfl⟩)
        · rw [smul_zero]
          exact Submodule.zero_mem _

include hzero hunit hhom in
theorem card_degree (d : ℕ) (hd : 0<d) :
    Fintype.card {i : I // δ i=d}=Module.finrank K (G.piece d) := by
  rw [←span_degree G B δ hzero hunit hhom d hd]
  exact (finrank_span_eq_card (B.linearIndependent.comp
    (fun i : {i : I // δ i=d} => some i.val)
    (fun i j h => Subtype.ext (Option.some.inj h)))).symm

theorem coeff_positiveSeries (d : ℕ) :
    PowerSeries.coeff d (WeightedBar.positiveSeries δ)=
      (Fintype.card {i : I // δ i=d} : ℤ) := by
  simp only [WeightedBar.positiveSeries,map_sum,PowerSeries.coeff_X_pow]
  rw [show (∑ i : I,if d=δ i then (1 : ℤ) else 0)=
      ∑ i : I,if δ i=d then (1 : ℤ) else 0 by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [eq_comm]]
  simp only [Finset.sum_boole,Fintype.card_subtype]

variable (hpos : ∀ i,0<δ i)
  (hprofile : ∀ d,Module.finrank K (G.piece d)=DimensionFiveGradedBasis.rankProfile d)

include hzero hunit hhom hpos hprofile in
theorem positiveSeries_eq_dimensionFive :
    WeightedBar.positiveSeries δ=KoszulBarObstruction.dimensionFivePositiveSeries := by
  apply PowerSeries.ext
  intro d
  by_cases hd : d=0
  · subst d
    have hn : ∀ i,δ i≠0 := fun i => Nat.ne_of_gt (hpos i)
    simp [coeff_positiveSeries,KoszulBarObstruction.dimensionFivePositiveSeries,hn]
  · have hdpos : 0<d := Nat.pos_of_ne_zero hd
    rw [coeff_positiveSeries,card_degree G B δ hzero hunit hhom d hdpos,hprofile]
    rcases d with _ | _ | _ | _ | d <;>
      simp_all [DimensionFiveGradedBasis.rankProfile,
        KoszulBarObstruction.dimensionFivePositiveSeries]

variable (ε : A →ₐ[K] K) (hε : ∀ i,ε (B (some i))=0)
  (hδ : ∀ a b c,AugmentedAlgebraBasis.productCoefficients B a b c≠0 → δ c=δ a+δ b)

include hzero hhom hpos hprofile in
set_option maxHeartbeats 800000 in
/-- Every actual homogeneous augmented basis gives nonzero off-diagonal
ordinary Tor. Thus choosing another basis cannot remove the obstruction. -/
theorem every_basis_ordinaryTor_off_diagonal :
    ∃ r,r<6 ∧ WeightedBar.torPiece ε B hunit hε δ hδ r 6≠⊥ := by
  obtain ⟨r,hr,hn⟩ := KoszulBarObstruction.dimensionFive_actual_bar_off_diagonal
    ε B hunit hε δ hδ hpos
    (positiveSeries_eq_dimensionFive G B δ hzero hunit hhom hpos hprofile)
  exact ⟨r,hr,fun hz => hn ((WeightedBar.torPiece_eq_bot_iff
    ε B hunit hε δ hδ r 6).mp hz)⟩

include hzero hhom hpos hprofile in
set_option maxHeartbeats 800000 in
theorem not_hasDiagonalTor : ¬WeightedBar.HasDiagonalTor ε B hunit hε δ hδ := by
  intro hdiag
  obtain ⟨r,hr,hn⟩ := every_basis_ordinaryTor_off_diagonal
    G B δ hzero hunit hhom hpos hprofile ε hε hδ
  exact hn (hdiag r 6 (Nat.ne_of_lt hr))

end PaperVerification.HomogeneousBasisProfile
