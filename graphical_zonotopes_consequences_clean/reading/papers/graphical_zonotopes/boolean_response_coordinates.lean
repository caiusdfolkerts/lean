module

public import Papers.GraphicalZonotopes.BooleanResponseQuotient
public import Papers.GraphicalZonotopes.FinitePowersetTransform

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset PowersetTransform
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

/-- The multilinear expansion is the full powerset zeta transform separately
on each genuine pair row. This is an invertible change of coordinates. -/
def rowLowerEquiv : (HubResponseRow H → ℝ) ≃ₗ[ℝ] (HubResponseRow H → ℝ) where
  toFun y r := lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)
    (fun T => y ⟨r.1,T⟩) r.2
  invFun y r := (lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)).symm
    (fun T => y ⟨r.1,T⟩) r.2
  left_inv y := by
    funext r
    rcases r with ⟨e,S⟩
    exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) e.1.1 e.1.2)).symm_apply_apply
      (fun T => y ⟨e,T⟩)) S
  right_inv y := by
    funext r
    rcases r with ⟨e,S⟩
    exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) e.1.1 e.1.2)).apply_symm_apply
      (fun T => y ⟨e,T⟩)) S
  map_add' y z := by
    funext r
    exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)).map_add
      (fun T => y ⟨r.1,T⟩) (fun T => z ⟨r.1,T⟩)) r.2
  map_smul' c y := by
    funext r
    exact congrFun ((lowerEquiv (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2)).map_smul c
      (fun T => y ⟨r.1,T⟩)) r.2

def rowClique (r : HubResponseRow H) : Finset H:=
  insert r.1.1.1 (insert r.1.1.2 r.2.1)

theorem rowClique_card (r : HubResponseRow H) : 2≤(rowClique r).card := by
  have hsub : ({r.1.1.1,r.1.1.2} : Finset H)⊆rowClique r := by
    simp only [rowClique,insert_subset_iff,singleton_subset_iff,mem_insert,true_or,or_true,and_self]
  have hc:=card_le_card hsub
  rwa [card_pair (ne_of_lt r.1.2.1)] at hc

def rowCliqueIndex (r : HubResponseRow H) : CliqueIndex (⊤ : SimpleGraph H) :=
  ⟨rowClique r,rowClique_card r,by
    intro u hu v hv huv
    exact (SimpleGraph.top_adj u v).mpr huv⟩

theorem rowCliqueIndex_surjective : Function.Surjective (rowCliqueIndex (H:=H)) := by
  intro C
  have hpair : ∀ u v,u∈C.1 → v∈C.1 → u<v → ∃ r : HubResponseRow H,rowCliqueIndex r=C := by
    intro u v huC hvC huv
    let T:=(C.1.erase u).erase v
    have hT : T⊆commonNeighbors (⊤ : SimpleGraph H) u v := by
      intro a ha
      have hne:=mem_erase.mp ha
      have hne':=mem_erase.mp hne.2
      exact (mem_commonNeighbors _ _ _ _).mpr
        ⟨(SimpleGraph.top_adj _ _).mpr hne'.1.symm,(SimpleGraph.top_adj _ _).mpr hne.1.symm⟩
    let e : OrientedEdge (⊤ : SimpleGraph H):=
      ⟨(u,v),huv,(SimpleGraph.top_adj u v).mpr (ne_of_lt huv)⟩
    let r : HubResponseRow H:=⟨e,⟨T,mem_powerset.mpr hT⟩⟩
    refine ⟨r,Subtype.ext ?_⟩
    change insert u (insert v ((C.1.erase u).erase v))=C.1
    ext a
    by_cases hau : a=u
    · subst a
      simp [huC]
    · by_cases hav : a=v
      · subst a
        simp [hvC]
      · simp [hau,hav]
  have hcard : 2≤C.1.card := C.2.1
  obtain ⟨u,hu,v,hv,huv⟩:=one_lt_card.mp (show 1<C.1.card by omega)
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact hpair u v hu hv hlt
  · exact hpair v u hv hu hgt

/-- A central Möbius coefficient is repeated once for each pair contained in
its clique. This map includes the pair blocks as well as all higher blocks. -/
def repeatCoefficients : (CliqueIndex (⊤ : SimpleGraph H) → ℝ) →ₗ[ℝ]
    (HubResponseRow H → ℝ) where
  toFun c r := c (rowCliqueIndex r)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coefficient_at_row (c : CliqueIndex (⊤ : SimpleGraph H) → ℝ)
    (r : HubResponseRow H) :
    coefficientsFromCoordinates ⊤ c (rowClique r)=c (rowCliqueIndex r) := by
  unfold coefficientsFromCoordinates
  split_ifs with h
  · rfl
  · exact (h (rowCliqueIndex r).2).elim

/-- This is the actual central elemental map in multilinear response
coordinates, not an independently postulated compatibility condition. -/
theorem rowLower_repeatCoefficients (c : CliqueIndex (⊤ : SimpleGraph H) → ℝ) :
    rowLowerEquiv (repeatCoefficients c)=centralCoefficientSlack c := by
  funext r
  let B:=commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2
  let y:=coefficientsFromCoordinates (⊤ : SimpleGraph H) c
  have hu : r.1.1.1∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_left ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  have hv : r.1.1.2∉r.2.1 := by
    intro h
    exact not_mem_commonNeighbors_right ⊤ _ _ ((mem_powerset.mp r.2.2) h)
  change lowerSum B (fun T => c (rowCliqueIndex ⟨r.1,T⟩)) r.2=
    delta (zeta y) r.1.1.1 r.1.1.2 r.2.1
  calc
    _=lowerSum B (fun T => y (insert r.1.1.1 (insert r.1.1.2 T.1))) r.2 := by
      have he : (fun T : SubsetIndex B => c (rowCliqueIndex ⟨r.1,T⟩))=
          (fun T : SubsetIndex B => y (insert r.1.1.1 (insert r.1.1.2 T.1))) := by
        funext T
        exact (coefficient_at_row c ⟨r.1,T⟩).symm
      rw [he]
    _=∑ T∈r.2.1.powerset,y (insert r.1.1.1 (insert r.1.1.2 T)) :=
      lowerSum_restriction B (fun T => y (insert r.1.1.1 (insert r.1.1.2 T))) r.2
    _=_ := (delta_zeta_reduced (ne_of_lt r.1.2.1) hu hv y).symm

/-- Being in the diagonal line of each clique block means exactly that all
copies of the same central Möbius coefficient agree. -/
def BlockConstant (x : HubResponseRow H → ℝ) : Prop :=
  ∀ r t,rowCliqueIndex r=rowCliqueIndex t → x r=x t

theorem blockConstant_iff_range_repeatCoefficients (x : HubResponseRow H → ℝ) :
    BlockConstant x ↔ x∈LinearMap.range (repeatCoefficients (H:=H)) := by
  constructor
  · intro hx
    choose pick hpick using (rowCliqueIndex_surjective (H:=H))
    refine ⟨fun C => x (pick C),?_⟩
    funext r
    exact hx (pick (rowCliqueIndex r)) r (hpick (rowCliqueIndex r))
  · rintro ⟨c,rfl⟩ r t he
    exact congrArg c he

/-- Integrability is equivalent to independent within-block agreement after
the invertible pairwise Möbius expansion. Consequently there are no hidden
relations between different clique blocks. -/
theorem central_range_iff_blockConstant (x : HubResponseRow H → ℝ) :
    x∈LinearMap.range (centralCoefficientSlack (H:=H)) ↔
      BlockConstant (rowLowerEquiv.symm x) := by
  rw [blockConstant_iff_range_repeatCoefficients]
  constructor
  · rintro ⟨c,rfl⟩
    refine ⟨c,?_⟩
    rw [← rowLower_repeatCoefficients,rowLowerEquiv.symm_apply_apply]
  · rintro ⟨c,hc⟩
    refine ⟨c,?_⟩
    rw [← rowLower_repeatCoefficients,hc,rowLowerEquiv.apply_symm_apply]

theorem integrable_iff_blockConstant (F : J → SetFunction H) (w : J → ℝ) :
    (∃ z : SetFunction H,TranslationNormalized z ∧ Compatible z F w) ↔
      BlockConstant (rowLowerEquiv.symm (weightedResponse F w)) := by
  rw [← mem_quotientRelation_ker_iff]
  change (LinearMap.range (centralCoefficientSlack (H:=H))).mkQ
    (weightedResponse F w)=0 ↔ _
  rw [← LinearMap.mem_ker,Submodule.ker_mkQ,central_range_iff_blockConstant]

end BooleanModule
end GraphicalZonotopes
