module

public import Papers.GraphicalZonotopes.WeightedPureBlocks
public import Papers.GraphicalZonotopes.BookBlockCoordinates
public import Papers.GraphicalZonotopes.WeightedBooleanCircuits

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise

variable {s : ℕ} (hs : 3≤s)

def bookZero : Fin s := ⟨0,by omega⟩
abbrev BookAnchor := ↥((univ : Finset (Fin s)).erase (bookZero hs))

def anchorExtension (t : BookAnchor hs → ℝ) : Fin s → ℝ :=
  erasedHubWeight univ (bookZero hs) t

@[simp] theorem anchorExtension_zero (t : BookAnchor hs → ℝ) :
    anchorExtension hs t (bookZero hs)=0 := erasedHubWeight_self _ _ _

@[simp] theorem anchorExtension_subtype (t : BookAnchor hs → ℝ) (a : BookAnchor hs) :
    anchorExtension hs t a.1=t a := erasedHubWeight_subtype _ _ _ _

theorem anchorExtension_labels :
    anchorExtension hs (fun a => (a.1.val : ℝ))=(fun a : Fin s => (a.val : ℝ)) := by
  funext a
  by_cases h : a=bookZero hs
  · subst a
    rw [anchorExtension_zero]
    norm_num [bookZero]
  · have ha : a∈(univ : Finset (Fin s)).erase (bookZero hs) := mem_erase.mpr ⟨h,mem_univ _⟩
    exact anchorExtension_subtype hs _ ⟨a,ha⟩

theorem sum_anchor_extension {W : Type*} [AddCommMonoid W] [Module ℝ W]
    (t : BookAnchor hs → ℝ) (v : Fin s → W) :
    (∑ a : BookAnchor hs,t a • v a.1)=∑ a,anchorExtension hs t a • v a := by
  have he : (∑ a : BookAnchor hs,t a • v a.1)=
      ∑ a∈(univ : Finset (Fin s)).erase (bookZero hs),anchorExtension hs t a • v a := by
    rw [← sum_coe_sort ((univ : Finset (Fin s)).erase (bookZero hs))
      (fun a : Fin s => anchorExtension hs t a • v a)]
    exact sum_congr rfl (fun a _ => by rw [anchorExtension_subtype])
  rw [he]
  have hz : anchorExtension hs t (bookZero hs) • v (bookZero hs)=0 := by simp
  have hsum := sum_erase_add (s:=(univ : Finset (Fin s)))
    (f:=fun a => anchorExtension hs t a • v a) (mem_univ (bookZero hs))
  simpa only [hz,add_zero] using hsum

theorem weighted_anchor_response (t : BookAnchor hs → ℝ) :
    (∑ a : BookAnchor hs,t a • responseClass (thresholdStar a.1))=
      ∑ C : BookBlock (Fin s),(-1 : ℝ)^(C.1.card-3) •
        blockClass C.1 (endpointCoefficients C.1 (anchorExtension hs t)) := by
  rw [sum_anchor_extension hs t (fun a => responseClass (thresholdStar a)),weighted_threshold_response]

section Family
variable {B : Type*} [Fintype B] [DecidableEq B]
    (e : B ≃ BookBlock (Fin s)) (r : B → ℕ)
    (P : ∀ b,WeightedPureBlock (e b).1 ((s-1 : ℕ) : ℤ)
      (ordinaryBookTarget (e b).1) (r b))

abbrev BookCircuitIndex := BookAnchor hs ⊕ (Σ b,Fin (r b))

def bookCircuitVector : BookCircuitIndex hs r → ResponseQuotient (Fin s)
  | .inl a => responseClass (thresholdStar a.1)
  | .inr j => blockClass (e j.1).1 ((P j.1).column j.2)

def bookCircuitWeight : BookCircuitIndex hs r → ℤ
  | .inl a => (a.1.val : ℤ)
  | .inr j => (P j.1).weight j.2

def bookBlockCombination (t : BookCircuitIndex hs r → ℝ) (b : B) : PairIn (e b).1 → ℝ :=
  (-1 : ℝ)^((e b).1.card-3) • endpointCoefficients (e b).1
    (anchorExtension hs (fun a => t (.inl a)))+
    ∑ j : Fin (r b),t (.inr ⟨b,j⟩) • (P b).column j

theorem bookCircuit_sum_blocks (t : BookCircuitIndex hs r → ℝ) :
    (∑ j,t j • bookCircuitVector hs e r P j)=
      ∑ b,blockClass (e b).1 (bookBlockCombination hs e r P t b) := by
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  change (∑ a : BookAnchor hs,t (.inl a) • responseClass (thresholdStar a.1))+
    (∑ b,∑ j : Fin (r b),t (.inr ⟨b,j⟩) • blockClass (e b).1 ((P b).column j))=_
  rw [weighted_anchor_response]
  have heq : (∑ C : BookBlock (Fin s),(-1 : ℝ)^(C.1.card-3) •
      blockClass C.1 (endpointCoefficients C.1 (anchorExtension hs (fun a => t (.inl a)))))=
      ∑ b,(-1 : ℝ)^((e b).1.card-3) • blockClass (e b).1
        (endpointCoefficients (e b).1 (anchorExtension hs (fun a => t (.inl a)))) := by
    exact (e.sum_comp _).symm
  rw [heq,← sum_add_distrib]
  apply sum_congr rfl
  intro b hb
  simp only [bookBlockCombination,map_add,map_smul,map_sum]

theorem bookCircuit_weighted_sum :
    (∑ j,(bookCircuitWeight hs e r P j : ℝ) • bookCircuitVector hs e r P j)=0 := by
  rw [bookCircuit_sum_blocks]
  apply sum_eq_zero
  intro b hb
  have hd : anchorExtension hs (fun a => (bookCircuitWeight hs e r P (.inl a) : ℝ))=
      (fun a : Fin s => (a.val : ℝ)) := by
    simpa only [bookCircuitWeight,Int.cast_natCast] using anchorExtension_labels hs
  simp only [bookBlockCombination,map_add,map_smul,map_sum,bookCircuitWeight,Int.cast_natCast]
  rw [anchorExtension_labels,(P b).weighted_sum]
  change (-1 : ℝ)^((e b).1.card-3) • blockClass (e b).1 (endpointLabels (e b).1)+
    -((-1 : ℝ)^((e b).1.card-3) • blockClass (e b).1 (endpointLabels (e b).1))=0
  exact add_neg_cancel _

theorem bookCircuit_pure_independent :
    LinearIndependent ℝ (fun j : Σ b,Fin (r b) =>
      blockClass (e j.1).1 ((P j.1).column j.2)) := by
  classical
  have hpair : ∀ b,∃ p : PairIn (e b).1,True := by
    intro b
    obtain ⟨p,hp⟩ := cliquePairs_nonempty (e b).1 (e b).1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp (e b).2).2; omega)
    exact ⟨p,trivial⟩
  apply block_families_independent (fun b => (e b).1)
    (Subtype.val_injective.comp e.injective) (fun b => (hpair b).choose)
    (fun b => (P b).column) (fun b => (P b).independent)

/-- The only nonlocal condition needed from the connectors: their block
constant equations force the prescribed arithmetic progression of hub scales. -/
def BookScaleRigidity : Prop :=
  ∀ (d : Fin s → ℝ) (t : (b : B) → Fin (r b) → ℝ),d (bookZero hs)=0 →
    (∀ b,blockClass (e b).1
      ((-1 : ℝ)^((e b).1.card-3) • endpointCoefficients (e b).1 d+
        ∑ j : Fin (r b),t b j • (P b).column j)=0) →
    ∃ c : ℝ,∀ a,d a=c*(a.val : ℝ)

theorem bookCircuit_unique_relation
    (hscale : BookScaleRigidity hs e r P)
    (t : BookCircuitIndex hs r → ℝ)
    (ht : (∑ j,t j • bookCircuitVector hs e r P j)=0) :
    ∃ c : ℝ,t=c • (fun j => (bookCircuitWeight hs e r P j : ℝ)) := by
  classical
  have hpair : ∀ b,∃ p : PairIn (e b).1,True := by
    intro b
    obtain ⟨p,hp⟩ := cliquePairs_nonempty (e b).1 (e b).1 (Subset.refl _)
      (by have h := (mem_largeBlocks.mp (e b).2).2; omega)
    exact ⟨p,trivial⟩
  rw [bookCircuit_sum_blocks] at ht
  have hblock := block_sum_zero_component (fun b => (e b).1)
    (Subtype.val_injective.comp e.injective) (fun b => (hpair b).choose)
    (bookBlockCombination hs e r P t) ht
  obtain ⟨c,hc⟩ := hscale (anchorExtension hs (fun a => t (.inl a)))
    (fun b j => t (.inr ⟨b,j⟩)) (anchorExtension_zero hs _) hblock
  have hanchor : ∀ a : BookAnchor hs,t (.inl a)=c*(a.1.val : ℝ) := by
    intro a
    simpa only [anchorExtension_subtype] using hc a.1
  have hzero : (∑ j : BookCircuitIndex hs r,
      (t j-c*(bookCircuitWeight hs e r P j : ℝ)) • bookCircuitVector hs e r P j)=0 := by
    simp only [sub_smul,mul_smul,sum_sub_distrib,← smul_sum]
    rw [bookCircuit_sum_blocks,ht,bookCircuit_weighted_sum,smul_zero,sub_self]
  rw [Fintype.sum_sum_type] at hzero
  have haz : (∑ a : BookAnchor hs,
      (t (.inl a)-c*(bookCircuitWeight hs e r P (.inl a) : ℝ)) •
        bookCircuitVector hs e r P (.inl a))=0 := by
    apply sum_eq_zero
    intro a ha
    simp only [bookCircuitWeight,Int.cast_natCast,hanchor,sub_self,zero_smul]
  rw [haz,zero_add] at hzero
  have hpure := Fintype.linearIndependent_iff.mp (bookCircuit_pure_independent e r P)
    (fun j => t (.inr j)-c*(bookCircuitWeight hs e r P (.inr j) : ℝ)) hzero
  refine ⟨c,?_⟩
  funext j
  cases j with
  | inl a => simpa only [Pi.smul_apply,smul_eq_mul,bookCircuitWeight,Int.cast_natCast] using hanchor a
  | inr j => simpa only [Pi.smul_apply,smul_eq_mul] using sub_eq_zero.mp (hpure j)

/-- A complete family of pure blocks and actual connector rigidity yields
an indecomposable full lattice book summand at the paper's stated scale. -/
theorem lattice_book_of_block_circuit (hscale : BookScaleRigidity hs e r P)
    {k : ℕ} (hcard : Fintype.card (BookCircuitIndex hs r)=k) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((s-1)*k : ℕ) : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  have hF : ∀ b j,∃ F : SetFunction (Fin s),IsMonotoneBoolean F ∧
      (∀ a,a∈(e b).1 → Essential F a) ∧
      (∀ a,a∉(e b).1 → ∀ X,F (insert a X)=F X) ∧
      responseClass F=blockClass (e b).1 ((P b).column j) := fun b j => (P b).realizable j
  choose F hFb hFe hFi hFc using hF
  let G : BookCircuitIndex hs r → SetFunction (Fin s)
    | .inl a => thresholdStar a.1
    | .inr j => F j.1 j.2
  have hG : ∀ j,IsMonotoneBoolean (G j) := by
    intro j
    cases j with
    | inl a => exact thresholdStar_boolean a.1
    | inr j => exact hFb j.1 j.2
  have hGc : ∀ j,responseClass (G j)=bookCircuitVector hs e r P j := by
    intro j
    cases j with
    | inl a => rfl
    | inr j => exact hFc j.1 j.2
  let a₁ : BookAnchor hs := ⟨⟨1,by omega⟩,mem_erase.mpr ⟨by
    intro h
    have h' := congrArg Fin.val h
    simp [bookZero] at h',mem_univ _⟩⟩
  have ha₁ : ∀ a,Essential (G (.inl a₁)) a :=
    thresholdStar_essential (by simpa using hs) a₁.1
  have hbranch : ∀ j,∃ a,Essential (G j) a := by
    intro j
    cases j with
    | inl a => exact ⟨a.1,thresholdStar_essential (by simpa using hs) a.1 a.1⟩
    | inr j =>
      have hne : (e j.1).1.Nonempty := card_pos.mp (by
        have h := (mem_largeBlocks.mp (e j.1).2).2
        omega)
      obtain ⟨a,ha⟩ := hne
      exact ⟨a,hFe j.1 j.2 a ha⟩
  have hw : ∀ j,0<bookCircuitWeight hs e r P j := by
    intro j
    cases j with
    | inl a =>
      change 0<(a.1.val : ℤ)
      have hne : a.1≠bookZero hs := (mem_erase.mp a.2).1
      have hv : a.1.val≠0 := fun h => hne (Fin.ext h)
      omega
    | inr j => exact (P j.1).positive j.2
  have hb : ∀ j,bookCircuitWeight hs e r P j≤((s-1 : ℕ) : ℤ) := by
    intro j
    cases j with
    | inl a =>
      change (a.1.val : ℤ)≤((s-1 : ℕ) : ℤ)
      have h := a.1.isLt
      omega
    | inr j => exact (P j.1).bounded j.2
  have hrel : (fun j => (bookCircuitWeight hs e r P j : ℝ))∈LinearMap.ker (quotientRelation G) := by
    change quotientRelation G _=0
    rw [quotientRelation_apply_eq_sum]
    simp_rw [hGc]
    exact bookCircuit_weighted_sum hs e r P
  have huniq : UniqueIntegrableRelation G (fun j => (bookCircuitWeight hs e r P j : ℝ)) := by
    intro t ht
    have ht0 : quotientRelation G t=0 := (mem_quotientRelation_ker_iff G t).mpr ht
    rw [quotientRelation_apply_eq_sum] at ht0
    simp_rw [hGc] at ht0
    exact bookCircuit_unique_relation hs e r P hscale t ht0
  have hM : (∑ j,bookCircuitWeight hs e r P j)≤(((s-1)*k : ℕ) : ℤ) := by
    calc
      _ ≤ ∑ _ : BookCircuitIndex hs r,((s-1 : ℕ) : ℤ) := sum_le_sum (fun j _ => hb j)
      _ = _ := by simp [hcard,Nat.cast_mul,mul_comm]
  obtain ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,hR⟩ :=
    lattice_book_of_finite_weighted_circuit (by omega) G hG (.inl a₁) ha₁ hbranch
      (bookCircuitWeight hs e r P) hw hrel huniq hcard (((s-1)*k : ℕ) : ℤ) hM
  exact ⟨f,hfn,hfi,hfe,hfg,hfd,hfm,hfl,R,hRl,hRn,by simpa only [Int.cast_natCast] using hR⟩

end Family
end BooleanModule
end GraphicalZonotopes
