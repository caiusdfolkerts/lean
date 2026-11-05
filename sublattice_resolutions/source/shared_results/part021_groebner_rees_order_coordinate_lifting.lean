module
public import graph_foundation.part014
public import shared_results.part020

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.GroebnerReesOrderCoordinateLifting -/
section

/-! # Coordinate lifting in the original term order -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice

open Classical CommAlg CommAlg.Koszul MvPolynomial FilteredHomology

universe u
variable {K V : Type u} [CommRing K] [Nontrivial K] [Fintype V] [LinearOrder V]
  (m : MonomialOrder V) (J : Ideal (MvPolynomial V K))
  (G : ℕ → Set (MvPolynomial V K))
  (hG : ∀ s,m.IsGroebnerBasis (G s) (J^s))
  (hu : ∀ s g,g∈G s → g≠0 → IsUnit (m.leadingCoeff g))

def PowerOrderedCoordinateLifts (s p : ℕ) : Prop :=
  BasisCycleLifting.LinearLifts (K := K)
    (X := PowerIdealCoordinates J s p) (Y := PowerIdealCoordinates J s p.pred)
    (I := PowerIdealIndex m J s p) (J := PowerIdealIndex m J s p.pred) (Γ := m.syn)
    (powerIdealCoefficientBasis m J G hG hu s p)
    (powerIdealCoefficientBasis m J G hG hu s p.pred)
    (fun a : PowerIdealIndex m J s p => m.toSyn (a.2.val + faceExponent a.1.val))
    (fun b : PowerIdealIndex m J s p.pred => m.toSyn (b.2.val + faceExponent b.1.val))
    (powerPreviousDifferential J s p)

section
attribute [local irreducible] powerIdealCoefficientBasis groebnerReesKoszulBasis
  idealReesKoszulDGA

set_option diagnostics true in
set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency true in
theorem power_ordered_coordinate_lifts_iff (s p : ℕ) :
    PowerOrderedCoordinateLifts m J G hG hu s p ↔
      BasisCycleLifting.LiftsOn (groebnerReesKoszulBasis m J G hG hu)
        (reesKoszulWeight m J) (idealReesKoszulDGA J).d
        (Submodule.span K ((groebnerReesKoszulBasis m J G hG hu) ''
          Set.range (powerIdealReesIndex m J s p))) := by
  have he := BasisEmbedding.ordered_coordinate_lifts_iff (K := K)
    (X := PowerIdealCoordinates J s p) (Y := PowerIdealCoordinates J s p.pred)
    (M := IdealReesKoszul J)
    (I := PowerIdealIndex m J s p) (J := PowerIdealIndex m J s p.pred)
    (T := IdealReesKoszulIndex m J) (Γ := m.syn)
    (powerIdealCoefficientBasis m J G hG hu s p)
    (powerIdealCoefficientBasis m J G hG hu s p.pred)
    (groebnerReesKoszulBasis m J G hG hu)
    (powerIdealReesIndex m J s p) (powerIdealReesIndex_injective m J s p)
    (powerIdealReesIndex m J s p.pred) (powerIdealReesIndex_injective m J s p.pred)
    (powerCoordinateInclusion J s p) (powerCoordinateInclusion J s p.pred)
    (powerCoordinateInclusion_basis m J G hG hu s p)
    (powerCoordinateInclusion_basis m J G hG hu s p.pred)
    (reesKoszulWeight m J) (powerPreviousDifferential J s p)
    (idealReesKoszulDGA J).d (powerCoordinateInclusion_d J s p)

  simpa only [PowerOrderedCoordinateLifts, Function.comp_def,
    powerIdealReesIndex_order_weight] using he

end

theorem auxiliary_ordered_basis_lifts (s : ℕ)
    (hlift : ∀ p,PowerOrderedCoordinateLifts m J G hG hu s p) :
    BasisCycleLifting.LiftsOn (groebnerReesKoszulBasis m J G hG hu)
      (reesKoszulWeight m J) (idealReesKoszulDGA J).d
      (WeightedRees.auxiliaryPiece m J G hG hu s) := by
  apply BasisCycleLifting.liftsOn_of_homogeneous_lifts
    (K := K) (M := IdealReesKoszul J) (I := IdealReesKoszulIndex m J)
    (A := ℤ) (Γ := m.syn)
    (groebnerReesKoszulBasis m J G hG hu) (reesKoszulWeight m J)
    (idealReesKoszulDGA J).d {a | a.1.1=s} (fun a => (a.2.card : ℤ))
    (fun p : ℤ => p-1) (by
      intro r t h
      change r - 1 = t - 1 at h
      omega)
    (groebnerReesKoszul_d_exterior m J G hG hu)
  intro p
  by_cases hp : 0≤p
  · obtain ⟨r,rfl⟩ := Int.eq_ofNat_of_zero_le hp
    rw [basisSpan_inf_piece]
    simpa only [powerIdealReesIndex_range, Set.mem_setOf_eq] using
      (power_ordered_coordinate_lifts_iff m J G hG hu s r).mp (hlift r)
  · intro n x hx hxF hdx
    have hx0 : x=0 := by
      apply (groebnerReesKoszulBasis m J G hG hu).repr.injective
      ext a
      rw [map_zero,Finsupp.zero_apply]
      by_contra ha
      have he := (Grading.mem_piece _ _ p x).mp hx.2 a ha
      exact hp (he ▸ Int.natCast_nonneg a.2.card)
    refine ⟨0,Submodule.zero_mem _,Submodule.zero_mem _,map_zero _,?_⟩
    rw [hx0,sub_self]
    exact Submodule.zero_mem _

variable (I : Ideal (MvPolynomial V K))
  (hinit : ∀ s,initialIdealForBasis m (J^s)=I^s)

local notation "F" => idealReesKoszulFiltration m J I hinit G hG hu
local notation "b" => groebnerReesKoszulBasis m J G hG hu
local notation "w" => reesKoszulWeight m J

theorem ordered_relative_lifts_of_power_coordinate_lifts (s : ℕ)
    (hlift : ∀ p,PowerOrderedCoordinateLifts m J G hG hu s p) :
    (F).RelativeLiftsCycles (idealReesKoszulDGA J) (WeightedRees.auxiliaryPiece m J G hG hu s) := by
  apply (OrderedBasis.relativeLiftsCycles_iff_basisLifts b w
    (fun a ha => (groebnerReesKoszul_one_weight m J G hG hu a ha).le)
    (OrderedBasis.product_nonincreasing b (initialReesKoszulBasis m J I hinit G hG hu) w
      (initialReesKoszul_product_homogeneous m J I hinit G hG hu)
      (groebnerReesKoszul_product_leading m J I hinit G hG hu))
    (idealReesKoszulDGA J) (WeightedRees.auxiliaryPiece m J G hG hu s)).mpr
  exact auxiliary_ordered_basis_lifts m J G hG hu s hlift

set_option backward.isDefEq.respectTransparency true in
theorem ordered_power_coordinate_lifts_of_all_lifts
    (hlift : (F).LiftsCycles (idealReesKoszulDGA J)) (s p : ℕ) :
    PowerOrderedCoordinateLifts m J G hG hu s p := by
  apply (power_ordered_coordinate_lifts_iff m J G hG hu s p).mpr
  rw [powerIdealReesIndex_range_degree]
  let deg := fun a : IdealReesKoszulIndex m J => (a.1.1,(a.2.card : ℤ))
  let shift := fun a : ℕ × ℤ => (a.1,a.2-1)
  have hshift : Function.Injective shift := by
    rintro ⟨a,r⟩ ⟨a',t⟩ h
    have hq : r - 1 = t - 1 := congrArg Prod.snd h
    have ha : a = a' := congrArg Prod.fst h
    exact Prod.ext ha (by omega)
  have hD : ∀ a,(idealReesKoszulDGA J).d (b a)∈Grading.Piece b deg (shift (deg a)) :=
    groebnerReesKoszul_d_auxiliary_exterior_piece m J G hG hu
  intro n x hx hxF hdx
  have hdx' : (idealReesKoszulDGA J).d x∈(F).lower n := by
    rw [idealReesKoszulFiltration, OrderedBasis.comparisonFiltration,
      OrderedBasis.filtration_lower]
    exact hdx
  obtain ⟨y,hyF,hdy,herr⟩ := hlift n x hxF hdx'
  have herr' : x-y∈BasisCycleLifting.lower b w n := by
    rw [idealReesKoszulFiltration, OrderedBasis.comparisonFiltration,
      OrderedBasis.filtration_lower] at herr
    exact herr
  have hxPiece : x ∈ Grading.Piece b deg (s,(p:ℤ)) := hx
  let z := Grading.projection b deg (s,(p:ℤ)) y
  refine ⟨z,Grading.projection_mem b deg (s,(p:ℤ)) y,
    projection_preserves_basisSpan b deg (s,(p:ℤ)) {a | w a≤n} y hyF,?_,?_⟩
  · have hcomm :
        (idealReesKoszulDGA J).d.comp (Grading.projection b deg (s,(p:ℤ))) =
          (Grading.projection b deg (shift (s,(p:ℤ)))).comp (idealReesKoszulDGA J).d := by
      apply (groebnerReesKoszulBasis m J G hG hu).ext
      intro a
      simp only [LinearMap.comp_apply, Grading.projection_basis]
      by_cases ha : deg a = (s,(p:ℤ))
      · rw [if_pos ha]
        exact (Grading.projection_eq_self (ha ▸ hD a)).symm
      · rw [if_neg ha, map_zero]
        exact (Grading.projection_eq_zero
          (show shift (s,(p:ℤ)) ≠ shift (deg a) from
            fun h => ha (hshift h).symm) (hD a)).symm
    have he := LinearMap.congr_fun hcomm y
    simpa only [LinearMap.comp_apply,hdy,map_zero] using he
  · have he := projection_preserves_basisSpan b deg (s,(p:ℤ)) {a | w a<n} (x-y) herr'
    simpa only [z, BasisCycleLifting.lower, map_sub,
      Grading.projection_eq_self hxPiece] using he

theorem all_power_ordered_coordinate_lifts
    (hgen : Algebra.adjoin K
      (IntegerFiltered.MultiplicativeFiltration.selectedHomologyClasses (idealReesKoszulDGA I)
        (WeightedRees.initialAuxiliaryPiece m J I hinit G hG hu 1))=⊤)
    (hfirst : ∀ p,PowerOrderedCoordinateLifts m J G hG hu 1 p) (s p : ℕ) :
    PowerOrderedCoordinateLifts m J G hG hu s p :=
  ordered_power_coordinate_lifts_of_all_lifts m J G hG hu I hinit
    (OrderedRees.all_cycle_lifts m J I hinit G hG hu hgen
      (ordered_relative_lifts_of_power_coordinate_lifts m J G hG hu I hinit 1 hfirst)) s p

end FourPapers.Sublattice

end
end
end


end
