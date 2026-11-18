module

public import Papers.GraphicalZonotopes.WeightedBooleanCircuits
public import Papers.GraphicalZonotopes.BlockPairCoordinates
public import Papers.GraphicalZonotopes.ThresholdResponse

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

def anchoredWeights (w : J → ℤ) : Option J → ℤ
  | none => 1
  | some j => w j

theorem anchored_weighted_relation (F₀ : SetFunction H) (F : J → SetFunction H)
    (w : J → ℤ) (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (hsum : responseClass F₀+∑ j,(w j : ℝ) • responseClass (F j)=0) :
    (fun j => (anchoredWeights w j : ℝ))∈LinearMap.ker (quotientRelation (anchoredFamily F₀ F)) ∧
      UniqueIntegrableRelation (anchoredFamily F₀ F) (fun j => (anchoredWeights w j : ℝ)) := by
  constructor
  · change quotientRelation (anchoredFamily F₀ F) _=0
    rw [quotientRelation_apply_eq_sum,Fintype.sum_option]
    simpa only [anchoredWeights,Int.cast_one,one_smul,anchoredFamily] using hsum
  · intro t ht
    have ht0 : quotientRelation (anchoredFamily F₀ F) t=0 :=
      (mem_quotientRelation_ker_iff _ _).mpr ht
    rw [quotientRelation_apply_eq_sum,Fintype.sum_option] at ht0
    change t none • responseClass F₀+∑ j,t (some j) • responseClass (F j)=0 at ht0
    have hsub : (∑ j,(t (some j)-t none*(w j : ℝ)) • responseClass (F j))=0 := by
      calc
        _ = (t none • responseClass F₀+∑ j,t (some j) • responseClass (F j))-
            t none • (responseClass F₀+∑ j,(w j : ℝ) • responseClass (F j)) := by
          simp only [sub_smul,sum_sub_distrib,smul_add,smul_sum,mul_smul]
          abel
        _ = 0 := by rw [ht0,hsum,smul_zero,sub_self]
    have hcoeff := (Fintype.linearIndependent_iff.mp hind) _ hsub
    refine ⟨t none,?_⟩
    funext i
    cases i with
    | none => simp [anchoredWeights]
    | some j =>
      simpa only [Pi.smul_apply,smul_eq_mul,anchoredWeights] using sub_eq_zero.mp (hcoeff j)

theorem lattice_book_of_anchored_weighted_circuit {s k : ℕ} (hs : 0<s)
    (F₀ : SetFunction (Fin s)) (F : J → SetFunction (Fin s))
    (hF₀ : IsMonotoneBoolean F₀) (hF : ∀ j,IsMonotoneBoolean (F j))
    (hess₀ : ∀ a,Essential F₀ a) (hess : ∀ j,∃ a,Essential (F j) a)
    (w : J → ℤ) (hw : ∀ j,0<w j) (M : ℤ) (hM₀ : 1≤M) (hM : ∀ j,w j≤M)
    (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (hsum : responseClass F₀+∑ j,(w j : ℝ) • responseClass (F j)=0)
    (hcard : Fintype.card J+1=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=((M*k : ℤ) : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  obtain ⟨hrel,huniq⟩ := anchored_weighted_relation F₀ F w hind hsum
  let G := anchoredFamily F₀ F
  have hG : ∀ j,IsMonotoneBoolean (G j) := by
    intro j
    cases j with
    | none => exact hF₀
    | some j => exact hF j
  have hbranch : ∀ j,∃ a,Essential (G j) a := by
    intro j
    cases j with
    | none => exact ⟨⟨0,hs⟩,hess₀ ⟨0,hs⟩⟩
    | some j => exact hess j
  have hw' : ∀ j,0<anchoredWeights w j := by
    intro j
    cases j with
    | none => norm_num [anchoredWeights]
    | some j => exact hw j
  have hb : ∀ j,anchoredWeights w j≤M := by
    intro j
    cases j with
    | none => exact hM₀
    | some j => exact hM j
  have hcard' : Fintype.card (Option J)=k := by simpa only [Fintype.card_option] using hcard
  apply lattice_book_of_finite_weighted_circuit hs G hG none hess₀ hbranch
    (anchoredWeights w) hw' hrel huniq hcard' (M*k)
  calc
    _ ≤ ∑ _ : Option J,M := sum_le_sum (fun j _ => hb j)
    _ = _ := by simp [hcard',mul_comm]

/-- Two genuine response coordinates detect the relative scales of two
threshold modules. The statement concerns their full integrability quotient;
no private row equations are omitted. -/
theorem two_threshold_coefficients_equal (a b : H)
    (r t : HubResponseRow H) (hrt : rowCliqueIndex r=rowCliqueIndex t)
    (har : thresholdSignedStar a r=1) (hat : thresholdSignedStar a t=0)
    (hbr : thresholdSignedStar b r=0) (hbt : thresholdSignedStar b t=1)
    (C : J → Finset H) (x : (j : J) → PairIn (C j) → ℝ)
    (hxt : ∀ j,blockCoordinates (C j) (x j) r=blockCoordinates (C j) (x j) t)
    (α β : ℝ) (w : J → ℝ)
    (hz : α • responseClass (thresholdStar a)+β • responseClass (thresholdStar b)+
      ∑ j,w j • blockClass (C j) (x j)=0) : α=β := by
  have hclass : coefficientClass (α • thresholdSignedStar a+β • thresholdSignedStar b+
      ∑ j,w j • blockCoordinates (C j) (x j))=0 := by
    simpa only [map_add,map_smul,map_sum,← thresholdStar_response_class,blockClass,
      LinearMap.comp_apply] using hz
  have he := (coefficientClass_eq_zero_iff _).mp hclass r t hrt
  simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,har,hat,hbr,hbt,
    mul_one,mul_zero,add_zero,zero_add] at he
  have hsum : (∑ j,w j*blockCoordinates (C j) (x j) r)=
      ∑ j,w j*blockCoordinates (C j) (x j) t := sum_congr rfl (fun j _ => by rw [hxt j])
  rw [hsum] at he
  exact add_right_cancel he

theorem second_threshold_and_pure_independent (a b : H)
    (C : J → Finset H) (x : (j : J) → PairIn (C j) → ℝ)
    (F : J → SetFunction H) (hF : ∀ j,responseClass (F j)=blockClass (C j) (x j))
    (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (r t : HubResponseRow H) (hrt : rowCliqueIndex r=rowCliqueIndex t)
    (har : thresholdSignedStar a r=1) (hat : thresholdSignedStar a t=0)
    (hbr : thresholdSignedStar b r=0) (hbt : thresholdSignedStar b t=1)
    (hxt : ∀ j,blockCoordinates (C j) (x j) r=blockCoordinates (C j) (x j) t) :
    LinearIndependent ℝ (fun j => responseClass (anchoredFamily (thresholdStar b) F j)) := by
  rw [Fintype.linearIndependent_iff]
  intro w hw j
  rw [Fintype.sum_option] at hw
  change w none • responseClass (thresholdStar b)+∑ i,w (some i) • responseClass (F i)=0 at hw
  have hz : (0 : ℝ) • responseClass (thresholdStar a)+
      w none • responseClass (thresholdStar b)+
      ∑ i,w (some i) • blockClass (C i) (x i)=0 := by
    simpa only [zero_smul,zero_add,← hF] using hw
  have hnone : w none=0 := (two_threshold_coefficients_equal a b r t hrt har hat hbr hbt
    C x hxt 0 (w none) (fun i => w (some i)) hz).symm
  cases j with
  | none => exact hnone
  | some j =>
    rw [hnone,zero_smul,zero_add] at hw
    exact (Fintype.linearIndependent_iff.mp hind) _ hw j

end BooleanModule
end GraphicalZonotopes
