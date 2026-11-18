module

public import Papers.GraphicalZonotopes.WeightedBookGeometry
public import Papers.GraphicalZonotopes.ResponseBlockHelpers
public import Papers.GraphicalZonotopes.PureResponseClasses
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {H J : Type*} [Fintype H] [LinearOrder H] [Fintype J] [DecidableEq J]

theorem quotientRelation_apply_eq_sum (F : J → SetFunction H) (w : J → ℝ) :
    quotientRelation F w=∑ j,w j • responseClass (F j) := by
  have he : weightedResponse F w=∑ j,w j • responseVector (F j) := by
    funext r
    simp only [weightedResponse,LinearMap.coe_mk,AddHom.coe_mk,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  change (LinearMap.range centralCoefficientSlack).mkQ (weightedResponse F w)=_
  rw [he,map_sum]
  simp only [map_smul,responseClass]

def anchoredFamily (F₀ : SetFunction H) (F : J → SetFunction H) : Option J → SetFunction H
  | none => F₀
  | some j => F j

/-- One distinguished column plus an independent family with vanishing
unit sum has precisely the unit relation line in the full quotient. -/
theorem anchored_unit_relation (F₀ : SetFunction H) (F : J → SetFunction H)
    (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (hsum : responseClass F₀+∑ j,responseClass (F j)=0) :
    (fun _ : Option J => (1 : ℝ))∈LinearMap.ker (quotientRelation (anchoredFamily F₀ F)) ∧
      UniqueIntegrableRelation (anchoredFamily F₀ F) (fun _ => 1) := by
  constructor
  · change quotientRelation (anchoredFamily F₀ F) (fun _ => 1)=0
    rw [quotientRelation_apply_eq_sum,Fintype.sum_option]
    simpa only [one_smul,anchoredFamily] using hsum
  · intro t ht
    have ht0 : quotientRelation (anchoredFamily F₀ F) t=0 :=
      (mem_quotientRelation_ker_iff _ _).mpr ht
    rw [quotientRelation_apply_eq_sum,Fintype.sum_option] at ht0
    change t none • responseClass F₀+∑ j,t (some j) • responseClass (F j)=0 at ht0
    have hsub : (∑ j,(t (some j)-t none) • responseClass (F j))=0 := by
      calc
        _ = (t none • responseClass F₀+∑ j,t (some j) • responseClass (F j))-
            t none • (responseClass F₀+∑ j,responseClass (F j)) := by
          simp only [sub_smul,sum_sub_distrib,smul_add,smul_sum]
          abel
        _ = 0 := by rw [ht0,hsum,smul_zero,sub_self]
    have hcoeff := (Fintype.linearIndependent_iff.mp hind) _ hsub
    refine ⟨t none,?_⟩
    funext i
    cases i with
    | none => simp
    | some j =>
      have hj : t (some j)=t none := sub_eq_zero.mp (hcoeff j)
      simpa only [Pi.smul_apply,smul_eq_mul,mul_one] using hj

/-- Relabeling a positive unit circuit with one all-hub anchor produces an
actual full lattice summand in exactly `k` times the graphical zonotope.
The other modules may have any nonempty proper essential hub sets. -/
theorem lattice_book_of_anchored_circuit {s k : ℕ} (hs : 0<s)
    (F₀ : SetFunction (Fin s)) (F : J → SetFunction (Fin s))
    (hF₀ : IsMonotoneBoolean F₀) (hF : ∀ j,IsMonotoneBoolean (F j))
    (hess₀ : ∀ a,Essential F₀ a) (hess : ∀ j,∃ a,Essential (F j) a)
    (hind : LinearIndependent ℝ (fun j => responseClass (F j)))
    (hsum : responseClass F₀+∑ j,responseClass (F j)=0)
    (hcard : Fintype.card J+1=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(k : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
  have hk : 0<k := by omega
  have hJ : Fintype.card (Option J)=k := by simpa only [Fintype.card_option] using hcard
  let e : Fin k ≃ Option J := (finCongr hJ.symm).trans (Fintype.equivFin (Option J)).symm
  let G := anchoredFamily F₀ F
  let F' : Fin k → SetFunction (Fin s) := fun i => G (e i)
  have hG : ∀ j,IsMonotoneBoolean (G j) := by
    intro j
    cases j with
    | none => exact hF₀
    | some j => exact hF j
  have hF' : ∀ i,IsMonotoneBoolean (F' i) := fun i => hG (e i)
  have hconn : (essentialSpokeGraph F').Connected := by
    apply essentialSpokeGraph_connected_of_anchor F' (e.symm none)
    · intro a
      simpa only [F',e.apply_symm_apply,G,anchoredFamily] using hess₀ a
    · intro i
      cases he : e i with
      | none => exact ⟨⟨0,hs⟩,by simpa only [F',he,G,anchoredFamily] using hess₀ ⟨0,hs⟩⟩
      | some j => simpa only [F',he,G,anchoredFamily] using hess j
  obtain ⟨hrel,huniq⟩ := anchored_unit_relation F₀ F hind hsum
  obtain ⟨z,hzn,hzc⟩ := (mem_quotientRelation_ker_iff G _).mp hrel
  have hc : Compatible z F' (fun _ => 1) :=
    (compatible_reindex e z G (fun _ => 1)).mpr hzc
  have huniq' : UniqueIntegrableRelation F' (fun _ => 1) := by
    intro t ht
    obtain ⟨u,hun,huc⟩ := ht
    have hold : Compatible u G (fun j => t (e.symm j)) :=
      (compatible_reindex e u G t).mp huc
    obtain ⟨c,hc⟩ := huniq (fun j => t (e.symm j)) ⟨u,hun,hold⟩
    refine ⟨c,?_⟩
    funext i
    simpa only [e.symm_apply_apply,Pi.smul_apply,smul_eq_mul,mul_one] using congrFun hc (e i)
  have hkrel : (fun _ : Fin k => (1 : ℝ))∈LinearMap.ker (quotientRelation F') :=
    (mem_quotientRelation_ker_iff F' _).mpr ⟨z,hzn,hc⟩
  obtain ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,hR⟩ :=
    lattice_book_of_weighted_modules hk F' hF' (fun _ => (1 : ℤ)) (fun _ => by norm_num)
      hconn (by simpa only [Int.cast_one] using hkrel)
      (by simpa only [Int.cast_one] using huniq') (k : ℤ) (by simp)
  exact ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,by simpa only [Int.cast_natCast] using hR⟩

end BooleanModule
end GraphicalZonotopes
