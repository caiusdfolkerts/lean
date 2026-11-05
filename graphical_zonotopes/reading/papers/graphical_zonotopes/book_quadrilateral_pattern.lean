module

public import Papers.GraphicalZonotopes.BookQuadrilateralModules

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

/-- The `s-2` quadrilaterals in the paper's upper-interval construction. -/
def connectorLabels {s : ℕ} (i : Fin (s-2)) : Fin 4 → ℕ :=
  if i.val=0 then ![0,1,2,3]
  else if i.val=1 then ![0,1,3,4]
  else if i.val=2 then ![1,2,3,4]
  else ![0,1,i.val+1,i.val+2]

theorem connectorLabels_lt {s : ℕ} (hs : 5≤s) (i : Fin (s-2)) (j : Fin 4) :
    connectorLabels i j<s := by
  have hi := i.isLt
  by_cases h0 : i.val=0 <;> by_cases h1 : i.val=1 <;> by_cases h2 : i.val=2 <;>
    fin_cases j <;> simp [connectorLabels,h0,h1,h2] <;> omega

theorem connectorLabels_strictMono {s : ℕ} (i : Fin (s-2)) :
    StrictMono (connectorLabels i) := by
  intro u v huv
  by_cases h0 : i.val=0 <;> by_cases h1 : i.val=1 <;> by_cases h2 : i.val=2 <;>
    fin_cases u <;> fin_cases v <;> norm_num at huv
  all_goals simp [connectorLabels,h0,h1,h2] <;> omega

theorem connectorLabels_balanced {s : ℕ} (i : Fin (s-2)) :
    connectorLabels i 0+connectorLabels i 3=connectorLabels i 1+connectorLabels i 2 := by
  by_cases h0 : i.val=0 <;> by_cases h1 : i.val=1 <;> by_cases h2 : i.val=2 <;>
    simp [connectorLabels,h0,h1,h2] <;> omega

def bookConnector {s : ℕ} (hs : 5≤s) (i : Fin (s-2)) : BalancedQuad s where
  point j := ⟨connectorLabels i j,connectorLabels_lt hs i j⟩
  ordered := connectorLabels_strictMono i
  balanced := connectorLabels_balanced i

theorem BalancedQuad.point_le_last {s : ℕ} (Q : BalancedQuad s) {a : Fin s}
    (ha : a∈Q.clique) : a≤Q.point 3 := by
  obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
  exact Q.ordered.monotone (by omega)

theorem connector_zero_mem {s : ℕ} (hs : 5≤s) (i : Fin (s-2)) :
    (⟨0,by omega⟩ : Fin s)∈(bookConnector hs i).clique ↔ i.val≠2 := by
  have hmem : (⟨0,by omega⟩ : Fin s)∈(bookConnector hs i).clique ↔
      ∃ j : Fin 4,connectorLabels i j=0 := by
    simp only [BalancedQuad.clique,mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨j,congrArg Fin.val hj⟩
    · rintro ⟨j,hj⟩
      exact ⟨j,Fin.ext hj⟩
  rw [hmem]
  by_cases h0 : i.val=0
  · constructor
    · intro h
      omega
    · intro h
      exact ⟨0,by simp [connectorLabels,h0]⟩
  by_cases h1 : i.val=1
  · constructor
    · intro h
      omega
    · intro h
      exact ⟨0,by simp [connectorLabels,h0,h1]⟩
  by_cases h2 : i.val=2
  · simp only [h2,ne_eq,not_true_eq_false,iff_false]
    rintro ⟨j,hj⟩
    fin_cases j <;> norm_num [connectorLabels,h0,h1,h2] at hj
  · refine ⟨fun _ => h2,fun _ => ⟨0,?_⟩⟩
    simp [connectorLabels,h0,h1,h2]

theorem bookConnector_clique_injective {s : ℕ} (hs : 5≤s) :
    Function.Injective (fun i : Fin (s-2) => (bookConnector hs i).clique) := by
  intro i j h
  change (bookConnector hs i).clique=(bookConnector hs j).clique at h
  have hle : (bookConnector hs i).point 3≤(bookConnector hs j).point 3 := by
    apply BalancedQuad.point_le_last
    rw [← h]
    exact BalancedQuad.point_mem _ _
  have hge : (bookConnector hs j).point 3≤(bookConnector hs i).point 3 := by
    apply BalancedQuad.point_le_last
    rw [h]
    exact BalancedQuad.point_mem _ _
  have hmax : connectorLabels i 3=connectorLabels j 3 := congrArg Fin.val (le_antisymm hle hge)
  have hz : i.val≠2 ↔ j.val≠2 := by
    rw [← connector_zero_mem hs i,← connector_zero_mem hs j,h]
  apply Fin.ext
  by_cases hi0 : i.val=0 <;> by_cases hi1 : i.val=1 <;> by_cases hi2 : i.val=2 <;>
    by_cases hj0 : j.val=0 <;> by_cases hj1 : j.val=1 <;> by_cases hj2 : j.val=2 <;>
    simp [connectorLabels,hi0,hi1,hi2,hj0,hj1,hj2] at hmax <;> omega

/-- The three initial equal-endpoint-sum relations and the subsequent chain
force the complete prescribed hub scale vector for every `s≥5`. -/
theorem quadrilateral_endpoint_rigidity (s : ℕ) (hs : 5≤s) (d : ℕ → ℝ)
    (h0 : d 0=0) (h03 : d 0+d 3=d 1+d 2)
    (h04 : d 0+d 4=d 1+d 3) (h14 : d 1+d 4=d 2+d 3)
    (hstep : ∀ j,5≤j → j<s → d 0+d j=d 1+d (j-1)) :
    ∀ j,j<s → d j=(j : ℝ)*d 1 := by
  have h2 : d 2=2*d 1 := by linarith
  have h3 : d 3=3*d 1 := by linarith
  have h4 : d 4=4*d 1 := by linarith
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hsmall : j≤4
    · interval_cases j <;> norm_num [h0,h2,h3,h4]
    · have h5 : 5≤j := by omega
      have hr := hstep j h5 hj
      have hp := ih (j-1) (by omega) (by omega)
      have hc : ((j-1 : ℕ) : ℝ)=(j : ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
      rw [hc] at hp
      linarith

theorem bookConnector_scale_rigidity {s : ℕ} (hs : 5≤s)
    (d : Fin s → ℝ) (h0 : d ⟨0,by omega⟩=0)
    (hconn : ∀ i : Fin (s-2),
      d ((bookConnector hs i).point 0)+d ((bookConnector hs i).point 3)=
      d ((bookConnector hs i).point 1)+d ((bookConnector hs i).point 2)) :
    ∀ j : Fin s,d j=(j.val : ℝ)*d ⟨1,by omega⟩ := by
  let D : ℕ → ℝ := fun j => if h : j<s then d ⟨j,h⟩ else 0
  have hD : ∀ j : Fin s,D j.val=d j := by
    intro j
    simp only [D,dite_eq_left j.isLt]
  have hb0 := hconn ⟨0,by omega⟩
  have hb1 := hconn ⟨1,by omega⟩
  have hb2 := hconn ⟨2,by omega⟩
  have h03 : D 0+D 3=D 1+D 2 := by simpa [D,bookConnector,connectorLabels,(show 0<s by omega),
    (show 1<s by omega),(show 2<s by omega),(show 3<s by omega)] using hb0
  have h04 : D 0+D 4=D 1+D 3 := by simpa [D,bookConnector,connectorLabels,(show 0<s by omega),
    (show 1<s by omega),(show 3<s by omega),(show 4<s by omega)] using hb1
  have h14 : D 1+D 4=D 2+D 3 := by simpa [D,bookConnector,connectorLabels,(show 1<s by omega),
    (show 2<s by omega),(show 3<s by omega),(show 4<s by omega)] using hb2
  have hstep : ∀ j,5≤j → j<s → D 0+D j=D 1+D (j-1) := by
    intro j hj hjs
    let i : Fin (s-2) := ⟨j-2,by omega⟩
    have hh := hconn i
    have hia : i.val+1=j-1 := by dsimp [i]; omega
    have hib : i.val+2=j := by dsimp [i]; omega
    have hi0 : i.val≠0 := by dsimp [i]; omega
    have hi1 : i.val≠1 := by dsimp [i]; omega
    have hi2 : i.val≠2 := by dsimp [i]; omega
    simpa [D,bookConnector,connectorLabels,hi0,hi1,hi2,hia,hib,(show 0<s by omega),
      (show 1<s by omega),hjs,(show j-1<s by omega)] using hh
  have h := quadrilateral_endpoint_rigidity s hs D
    (by simpa [D,(show 0<s by omega)] using h0) h03 h04 h14 hstep
  intro j
  have hj := h j.val j.isLt
  rw [hD j] at hj
  simpa [D,(show 1<s by omega)] using hj

end BooleanModule
end GraphicalZonotopes
