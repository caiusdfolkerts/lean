module

public import Papers.GraphicalZonotopes.BooleanResponseCoordinates
public import Papers.GraphicalZonotopes.BookModuleGeometry

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset PowersetTransform
open scoped BigOperators
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

def integerSubring : Subring ℝ:=(Int.castRingHom ℝ).range

theorem mem_integerSubring_iff (x : ℝ) :
    x∈integerSubring ↔ ∃ a : ℤ,x=(a : ℝ) := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,ha.symm⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,ha.symm⟩

theorem rowLower_symm_mem_subring (K : Subring ℝ) (x : HubResponseRow H → ℝ)
    (hx : ∀ r,x r∈K) : ∀ r,rowLowerEquiv.symm x r∈K := by
  intro r
  exact lowerEquiv_symm_mem_subring
    (commonNeighbors (⊤ : SimpleGraph H) r.1.1.1 r.1.1.2) K
    (fun T => x ⟨r.1,T⟩) (fun T => hx ⟨r.1,T⟩) r.2

theorem weightedResponse_integer (F : J → SetFunction H)
    (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℤ) :
    ∀ r,weightedResponse F (fun j => (w j : ℝ)) r∈integerSubring := by
  intro r
  apply integerSubring.sum_mem
  intro j hj
  apply integerSubring.mul_mem
  · exact (mem_integerSubring_iff _).mpr ⟨w j,rfl⟩
  · rcases negativeResponse_values (hF j) r.1.1.1 r.1.1.2 r.2.1 with h | h
    · change negativeResponse (F j) _ _ _∈integerSubring
      rw [h]
      exact integerSubring.zero_mem
    · change negativeResponse (F j) _ _ _∈integerSubring
      rw [h]
      exact integerSubring.one_mem

/-- Whenever integral pair-response coefficients are integrable over the
reals, their central lift already has integral Möbius coefficients. No
unproved rationality or saturation assertion is used. -/
theorem central_integral_lift (x : HubResponseRow H → ℝ)
    (hx : ∀ r,x r∈integerSubring)
    (hblock : BlockConstant (rowLowerEquiv.symm x)) :
    ∃ c : CliqueIndex (⊤ : SimpleGraph H) → ℝ,
      (∀ C,c C∈integerSubring) ∧ centralCoefficientSlack c=x := by
  obtain ⟨c,hc⟩:=(blockConstant_iff_range_repeatCoefficients _).mp hblock
  have hi:=rowLower_symm_mem_subring integerSubring x hx
  refine ⟨c,?_,?_⟩
  · intro C
    obtain ⟨r,hr⟩:=rowCliqueIndex_surjective C
    have he:=congrFun hc r
    change c (rowCliqueIndex r)=rowLowerEquiv.symm x r at he
    rw [hr] at he
    rw [he]
    exact hi r
  · rw [← rowLower_repeatCoefficients,hc,rowLowerEquiv.apply_symm_apply]

/-- The integral central lift used by every Boolean-module construction in
Section7, stated for arbitrary finite hub and branch sets. -/
theorem integral_compatible_lift (F : J → SetFunction H)
    (hF : ∀ j,IsMonotoneBoolean (F j)) (w : J → ℤ)
    (hrel : (fun j => (w j : ℝ))∈LinearMap.ker (quotientRelation F)) :
    ∃ z : SetFunction H,TranslationNormalized z ∧ IntegerValued z ∧
      Compatible z F (fun j => (w j : ℝ)) := by
  have hi:=weightedResponse_integer F hF w
  have hb : BlockConstant (rowLowerEquiv.symm (weightedResponse F (fun j => (w j : ℝ)))) :=
    (integrable_iff_blockConstant F _).mp ((mem_quotientRelation_ker_iff F _).mp hrel)
  obtain ⟨c,hci,hc⟩:=central_integral_lift _ hi hb
  let y:=coefficientsFromCoordinates (⊤ : SimpleGraph H) c
  let z:=zeta y
  have hn : TranslationNormalized z:=(graphicalCoordinatesEquiv ⊤ c).2.1
  have hyi : IntegerValued y := by
    intro C
    by_cases hC : IsCliqueCoordinate (⊤ : SimpleGraph H) C
    · change (∃ a : ℤ,coefficientsFromCoordinates ⊤ c C=(a : ℝ))
      rw [coefficientsFromCoordinates,dif_pos hC]
      exact (mem_integerSubring_iff _).mp (hci ⟨C,hC⟩)
    · exact ⟨0,by simp only [y,coefficientsFromCoordinates,dif_neg hC,Int.cast_zero]⟩
  refine ⟨z,hn,zeta_integerValued hyi,?_⟩
  apply (compatible_iff_rows hn F _).mpr
  exact hc

end BooleanModule
end GraphicalZonotopes
