module

public import Papers.GraphicalZonotopes.ScopedBookGeometry
public import Papers.GraphicalZonotopes.BookCircuitAssembly

@[expose] public section
noncomputable section
open scoped Classical
namespace GraphicalZonotopes.BooleanModule
open Finset
open scoped BigOperators

variable {s : ℕ}

def coefficientExtension (A : Finset (Fin s)) (t : A → ℝ) : Fin s → ℝ :=
  fun a => if h : a∈A then t ⟨a,h⟩ else 0

@[simp] theorem coefficientExtension_subtype (A : Finset (Fin s)) (t : A → ℝ) (a : A) :
    coefficientExtension A t a.1=t a := by simp [coefficientExtension,a.2]

theorem coefficientExtension_not_mem (A : Finset (Fin s)) (t : A → ℝ) {a : Fin s}
    (ha : a∉A) : coefficientExtension A t a=0 := by simp [coefficientExtension,ha]

theorem sum_coefficientExtension {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (A : Finset (Fin s)) (t : A → ℝ) (v : Fin s → W) :
    (∑ a : A,t a • v a.1)=∑ a,coefficientExtension A t a • v a := by
  have hfirst : (∑ a : A,t a • v a.1)=∑ a∈A,coefficientExtension A t a • v a := by
    rw [←sum_coe_sort A (fun a => coefficientExtension A t a • v a)]
    exact sum_congr rfl (fun a _ => by rw [coefficientExtension_subtype])
  rw [hfirst]
  apply sum_subset (subset_univ _)
  intro a ha hn
  rw [coefficientExtension_not_mem A t hn,zero_smul]

abbrev ScopedAnchorIndex (A : Finset (Fin s)) (r : BookBlock (Fin s) → ℕ) :=
  A ⊕ (Σ C : BookBlock (Fin s),Fin (r C))

def scopedAnchorScope (A : Finset (Fin s)) (r : BookBlock (Fin s) → ℕ) :
    ScopedAnchorIndex A r → Finset (Fin s)
  | .inl _ => univ
  | .inr j => j.1.1

section Circuit
variable (A : Finset (Fin s)) (η : ℝ) (FA : A → SetFunction (Fin s))
    (hFA : ∀ a,responseClass (FA a)=η • responseClass (thresholdStar a.1))
    (wA : A → ℤ) (M : ℤ) (r : BookBlock (Fin s) → ℕ)
    (P : ∀ C : BookBlock (Fin s),WeightedPureBlock C.1 M
      (-((η*((-1 : ℝ)^(C.1.card-3))) • blockClass C.1
        (endpointCoefficients C.1 (coefficientExtension A (fun a => (wA a : ℝ)))))) (r C))

def scopedAnchorVector : ScopedAnchorIndex A r → ResponseQuotient (Fin s)
  | .inl a => responseClass (FA a)
  | .inr j => blockClass j.1.1 ((P j.1).column j.2)

def scopedAnchorWeight : ScopedAnchorIndex A r → ℤ
  | .inl a => wA a
  | .inr j => (P j.1).weight j.2

def scopedAnchorCombination (t : ScopedAnchorIndex A r → ℝ) (C : BookBlock (Fin s)) : PairIn C.1 → ℝ :=
  (η*((-1 : ℝ)^(C.1.card-3))) • endpointCoefficients C.1
    (coefficientExtension A (fun a => t (.inl a)))+
    ∑ j : Fin (r C),t (.inr ⟨C,j⟩) • (P C).column j

include hFA in
theorem scopedAnchor_sum_blocks (t : ScopedAnchorIndex A r → ℝ) :
    (∑ j,t j • scopedAnchorVector A η FA wA M r P j)=
      ∑ C : BookBlock (Fin s),blockClass C.1 (scopedAnchorCombination A η wA M r P t C) := by
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  change (∑ a : A,t (.inl a) • responseClass (FA a))+
    (∑ C,∑ j : Fin (r C),t (.inr ⟨C,j⟩) • blockClass C.1 ((P C).column j))=_
  simp_rw [hFA]
  have ha : (∑ a : A,t (.inl a) • η • responseClass (thresholdStar a.1))=
      η • (∑ a : A,t (.inl a) • responseClass (thresholdStar a.1)) := by
    rw [smul_sum]
    exact sum_congr rfl (fun a _ => smul_comm _ _ _)
  rw [ha,sum_coefficientExtension A (fun a => t (.inl a))
    (fun a => responseClass (thresholdStar a)),weighted_threshold_response,smul_sum]
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro C hC
  simp only [scopedAnchorCombination,map_add,map_smul,map_sum,mul_smul]

include hFA in
theorem scopedAnchor_weighted_sum :
    (∑ j,(scopedAnchorWeight A η wA M r P j : ℝ) • scopedAnchorVector A η FA wA M r P j)=0 := by
  rw [scopedAnchor_sum_blocks A η FA hFA wA M r P]
  apply sum_eq_zero
  intro C hC
  simp only [scopedAnchorCombination,map_add,map_smul,map_sum,scopedAnchorWeight]
  rw [(P C).weighted_sum]
  exact add_neg_cancel _

theorem scopedAnchor_pure_independent :
    LinearIndependent ℝ (fun j : Σ C : BookBlock (Fin s),Fin (r C) =>
      blockClass j.1.1 ((P j.1).column j.2)) := by
  have hpair : ∀ C : BookBlock (Fin s),∃ p : PairIn C.1,True := by
    intro C
    obtain ⟨p,hp⟩ := cliquePairs_nonempty C.1 C.1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp C.2).2; omega)
    exact ⟨p,trivial⟩
  exact block_families_independent Subtype.val Subtype.val_injective
    (fun C => (hpair C).choose) (fun C => (P C).column) (fun C => (P C).independent)

def ScopedAnchorRigidity : Prop :=
  ∀ t : ScopedAnchorIndex A r → ℝ,
    (∀ C : BookBlock (Fin s),blockClass C.1 (scopedAnchorCombination A η wA M r P t C)=0) →
      ∃ c : ℝ,∀ a : A,t (.inl a)=c*(wA a : ℝ)

include hFA in
theorem scopedAnchor_unique (hrigid : ScopedAnchorRigidity A η wA M r P)
    (t : ScopedAnchorIndex A r → ℝ)
    (ht : (∑ j,t j • scopedAnchorVector A η FA wA M r P j)=0) :
    ∃ c : ℝ,t=c • (fun j => (scopedAnchorWeight A η wA M r P j : ℝ)) := by
  rw [scopedAnchor_sum_blocks A η FA hFA wA M r P] at ht
  have hpair : ∀ C : BookBlock (Fin s),∃ p : PairIn C.1,True := by
    intro C
    obtain ⟨p,hp⟩ := cliquePairs_nonempty C.1 C.1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp C.2).2; omega)
    exact ⟨p,trivial⟩
  have hb := block_sum_zero_component Subtype.val Subtype.val_injective
    (fun C => (hpair C).choose) (scopedAnchorCombination A η wA M r P t) ht
  obtain ⟨c,hc⟩ := hrigid t hb
  have hz : (∑ j : ScopedAnchorIndex A r,
      (t j-c*(scopedAnchorWeight A η wA M r P j : ℝ)) •
        scopedAnchorVector A η FA wA M r P j)=0 := by
    simp only [sub_smul,mul_smul,sum_sub_distrib,←smul_sum]
    rw [scopedAnchor_sum_blocks A η FA hFA wA M r P,ht,
      scopedAnchor_weighted_sum A η FA hFA wA M r P,smul_zero,sub_self]
  rw [Fintype.sum_sum_type] at hz
  have ha : (∑ a : A,(t (.inl a)-c*(scopedAnchorWeight A η wA M r P (.inl a) : ℝ)) •
      scopedAnchorVector A η FA wA M r P (.inl a))=0 := by
    apply sum_eq_zero
    intro a ha
    rw [scopedAnchorWeight,hc,sub_self,zero_smul]
  rw [ha,zero_add] at hz
  have hp := Fintype.linearIndependent_iff.mp (scopedAnchor_pure_independent A η wA M r P)
    (fun j => t (.inr j)-c*(scopedAnchorWeight A η wA M r P (.inr j) : ℝ)) hz
  refine ⟨c,?_⟩
  funext j
  cases j with
  | inl a => exact hc a
  | inr j => exact sub_eq_zero.mp (hp j)

include hFA in
/-- The complete circuit theorem retaining its exact essential-variable
scopes; the final principal constructions supply every algebraic premise. -/
theorem scoped_book_of_anchor_circuit (hs : 3≤s)
    (hAb : ∀ a,IsMonotoneBoolean (FA a)) (hAe : ∀ a i,Essential (FA a) i)
    (a₀ : A) (hwA : ∀ a,0<wA a)
    (hrigid : ScopedAnchorRigidity A η wA M r P)
    {k : ℕ} (hcard : Fintype.card (ScopedAnchorIndex A r)=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      LatticePolytope (basePolytope f) ∧
      ∀ a : Fin s,(univ.filter (fun j : Fin k =>
        ActualRootEdge (basePolytope f) (Sum.inl a) (Sum.inr j))).card=
        (univ.filter (fun j : ScopedAnchorIndex A r => a∈scopedAnchorScope A r j)).card := by
  have hF : ∀ C j,∃ F : SetFunction (Fin s),IsMonotoneBoolean F ∧
      (∀ a,a∈C.1 → Essential F a) ∧
      (∀ a,a∉C.1 → ∀ X,F (insert a X)=F X) ∧
      responseClass F=blockClass C.1 ((P C).column j) := fun C j => (P C).realizable j
  choose F hFb hFe hFi hFc using hF
  let G : ScopedAnchorIndex A r → SetFunction (Fin s)
    | .inl a => FA a
    | .inr j => F j.1 j.2
  have hGb : ∀ j,IsMonotoneBoolean (G j) := by
    intro j
    cases j with
    | inl a => exact hAb a
    | inr j => exact hFb j.1 j.2
  have hGe : ∀ j a,a∈scopedAnchorScope A r j → Essential (G j) a := by
    intro j a ha
    cases j with
    | inl b => exact hAe b a
    | inr j => exact hFe j.1 j.2 a ha
  have hGi : ∀ j a,a∉scopedAnchorScope A r j → ∀ X,G j (insert a X)=G j X := by
    intro j a ha X
    cases j with
    | inl b => exact False.elim (ha (mem_univ _))
    | inr j => exact hFi j.1 j.2 a ha X
  have hGc : ∀ j,responseClass (G j)=scopedAnchorVector A η FA wA M r P j := by
    intro j
    cases j with
    | inl a => rfl
    | inr j => exact hFc j.1 j.2
  have hnon : ∀ j,(scopedAnchorScope A r j).Nonempty := by
    intro j
    cases j with
    | inl a => exact ⟨⟨0,by omega⟩,mem_univ _⟩
    | inr j =>
      change j.1.1.Nonempty
      exact card_pos.mp (by have h := (mem_largeBlocks.mp j.1.2).2; omega)
  have hw : ∀ j,0<scopedAnchorWeight A η wA M r P j := by
    intro j
    cases j with
    | inl a => exact hwA a
    | inr j => exact (P j.1).positive j.2
  have hrel : (fun j => (scopedAnchorWeight A η wA M r P j : ℝ))∈LinearMap.ker (quotientRelation G) := by
    change quotientRelation G _=0
    rw [quotientRelation_apply_eq_sum]
    simp_rw [hGc]
    exact scopedAnchor_weighted_sum A η FA hFA wA M r P
  have huniq : UniqueIntegrableRelation G (fun j => (scopedAnchorWeight A η wA M r P j : ℝ)) := by
    intro t ht
    have ht0 : quotientRelation G t=0 := (mem_quotientRelation_ker_iff G t).mpr ht
    rw [quotientRelation_apply_eq_sum] at ht0
    simp_rw [hGc] at ht0
    exact scopedAnchor_unique A η FA hFA wA M r P hrigid t ht0
  exact scoped_book_of_finite_circuit (by omega) G hGb (scopedAnchorScope A r)
    hGe hGi (.inl a₀) rfl hnon (scopedAnchorWeight A η wA M r P) hw hrel huniq hcard

end Circuit
end GraphicalZonotopes.BooleanModule
