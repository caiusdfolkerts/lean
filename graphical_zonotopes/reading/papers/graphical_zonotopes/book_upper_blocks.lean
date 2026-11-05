module

public import Papers.GraphicalZonotopes.BookCircuitAssembly
public import Papers.GraphicalZonotopes.BookQuadrilateralPattern
public import Papers.GraphicalZonotopes.BookBlockCounts

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators Pointwise
variable {s : ℕ} (hs : 5≤s)

def connectorBlock (i : Fin (s-2)) : BookBlock (Fin s) :=
  ⟨(bookConnector hs i).clique,mem_largeBlocks.mpr
    ⟨subset_univ _,by rw [BalancedQuad.card_clique]; omega⟩⟩

theorem connectorBlock_injective : Function.Injective (connectorBlock hs) := by
  intro i j h
  exact bookConnector_clique_injective hs (congrArg Subtype.val h)

def connectorBlockSet : Finset (BookBlock (Fin s)) := univ.image (connectorBlock hs)

@[simp] theorem connectorBlock_mem (i : Fin (s-2)) :
    connectorBlock hs i∈connectorBlockSet hs := mem_image.mpr ⟨i,mem_univ _,rfl⟩

@[simp] theorem connectorBlockSet_card : (connectorBlockSet hs).card=s-2 := by
  rw [connectorBlockSet,card_image_of_injective _ (connectorBlock_injective hs),card_univ,Fintype.card_fin]

abbrev OrdinaryBookBlock := {C : BookBlock (Fin s) // C∉connectorBlockSet hs}
abbrev UpperBookBlock := Fin (s-2) ⊕ OrdinaryBookBlock hs

def upperBlockMap : UpperBookBlock hs → BookBlock (Fin s)
  | .inl i => connectorBlock hs i
  | .inr C => C.1

theorem upperBlockMap_bijective : Function.Bijective (upperBlockMap hs) := by
  constructor
  · intro b c h
    cases b with
    | inl i =>
      cases c with
      | inl j => exact congrArg Sum.inl (connectorBlock_injective hs h)
      | inr C =>
        change connectorBlock hs i=C.1 at h
        exact False.elim (C.2 (h ▸ connectorBlock_mem hs i))
    | inr C =>
      cases c with
      | inl i =>
        change C.1=connectorBlock hs i at h
        exact False.elim (C.2 (h.symm ▸ connectorBlock_mem hs i))
      | inr D => exact congrArg Sum.inr (Subtype.ext h)
  · intro C
    by_cases h : C∈connectorBlockSet hs
    · obtain ⟨i,hi,he⟩ := mem_image.mp h
      exact ⟨.inl i,he⟩
    · exact ⟨.inr ⟨C,h⟩,rfl⟩

def upperBlockEquiv : UpperBookBlock hs ≃ BookBlock (Fin s) :=
  Equiv.ofBijective (upperBlockMap hs) (upperBlockMap_bijective hs)

@[simp] theorem upperBlockEquiv_inl (i : Fin (s-2)) :
    upperBlockEquiv hs (.inl i)=connectorBlock hs i := rfl

@[simp] theorem upperBlockEquiv_inr (C : OrdinaryBookBlock hs) :
    upperBlockEquiv hs (.inr C)=C.1 := rfl

theorem sum_upperBlock_partition {W : Type*} [AddCommMonoid W]
    (v : BookBlock (Fin s) → W) :
    (∑ C : BookBlock (Fin s),v C)=
      (∑ i : Fin (s-2),v (connectorBlock hs i))+
        ∑ C : OrdinaryBookBlock hs,v C.1 := by
  have h := (upperBlockEquiv hs).sum_comp v
  rw [Fintype.sum_sum_type] at h
  exact h.symm

def upperPureRank (r : OrdinaryBookBlock hs → ℕ) : UpperBookBlock hs → ℕ
  | .inl _ => 4
  | .inr C => r C

def upperPureBlock (r : OrdinaryBookBlock hs → ℕ)
    (P : ∀ C,WeightedPureBlock C.1.1 ((s-1 : ℕ) : ℤ)
      (ordinaryBookTarget C.1.1) (r C)) :
    ∀ b : UpperBookBlock hs,WeightedPureBlock (upperBlockEquiv hs b).1
      ((s-1 : ℕ) : ℤ) (ordinaryBookTarget (upperBlockEquiv hs b).1) (upperPureRank hs r b)
  | .inl i => (bookConnector hs i).pureBlock
  | .inr C => P C

/-- The literal omitted coordinates of the selected quadrilaterals supply
all connector equations, hence force a one-dimensional hub scale space. -/
theorem upper_book_scale_rigidity (r : OrdinaryBookBlock hs → ℕ)
    (P : ∀ C,WeightedPureBlock C.1.1 ((s-1 : ℕ) : ℤ)
      (ordinaryBookTarget C.1.1) (r C)) :
    BookScaleRigidity (show 3≤s by omega) (upperBlockEquiv hs)
      (upperPureRank hs r) (upperPureBlock hs r P) := by
  intro d t hd hblock
  have hconn : ∀ i : Fin (s-2),
      d ((bookConnector hs i).point 0)+d ((bookConnector hs i).point 3)=
        d ((bookConnector hs i).point 1)+d ((bookConnector hs i).point 2) := by
    intro i
    let Q := bookConnector hs i
    have hi := hblock (.inl i)
    change blockClass Q.clique
      ((-1 : ℝ)^(Q.clique.card-3) • endpointCoefficients Q.clique d+
        ∑ j : Fin 4,t (.inl i) j • Q.column j)=0 at hi
    obtain ⟨c,hc⟩ := (blockClass_eq_zero_iff Q.clique Q.reference _).mp hi
    have hr := hc Q.reference
    have ho := hc Q.opposite
    simp only [Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul,
      BalancedQuad.column_reference,BalancedQuad.column_opposite,mul_zero,
      sum_const_zero,add_zero] at hr ho
    have he := hr.trans ho.symm
    simp only [Q.card_clique] at he
    have he' : -(d (Q.point 0)+d (Q.point 3))= -(d (Q.point 1)+d (Q.point 2)) := by
      simpa [endpointCoefficients,BalancedQuad.reference,BalancedQuad.opposite,
        BalancedQuad.pair,orderedPair] using he
    exact neg_injective he'
  have h := bookConnector_scale_rigidity hs d hd hconn
  exact ⟨d ⟨1,by omega⟩,fun a => by simpa only [mul_comm] using h a⟩

/-- Exact ordinary-block lower count after removing the `s-2` connectors. -/
theorem ordinary_lower_count :
    3*(s-2)+(∑ C : OrdinaryBookBlock hs,(C.1.1.card-1))+s.choose 2=
      (s-2)*2^(s-1)+1 := by
  have h := BookBlock_lower_sum (show 2≤s by omega)
  rw [sum_upperBlock_partition hs] at h
  have he : (∑ i : Fin (s-2),((connectorBlock hs i).1.card-1))=3*(s-2) := by
    simp only [connectorBlock,BalancedQuad.card_clique]
    norm_num [Nat.choose]
    ring
  rw [he] at h
  exact h

theorem ordinary_upper_count :
    5*(s-2)+(∑ C : OrdinaryBookBlock hs,(C.1.1.card.choose 2-1))+1=cliqueCapacity s := by
  have h := BookBlock_dimension_sum (H:=Fin s)
  simp only [Fintype.card_fin] at h
  rw [sum_upperBlock_partition hs] at h
  have he : (∑ i : Fin (s-2),((connectorBlock hs i).1.card.choose 2-1))=5*(s-2) := by
    simp only [connectorBlock,BalancedQuad.card_clique]
    norm_num [Nat.choose]
    ring
  rw [he] at h
  exact h

def bookUpperIntervalStart (s : ℕ) : ℕ :=
  (s-2)*2^(s-1)+2*s-2-s.choose 2

theorem bookUpperIntervalStart_eq :
    bookUpperIntervalStart s=(s-1)+4*(s-2)+∑ C : OrdinaryBookBlock hs,(C.1.1.card-1) := by
  have h := ordinary_lower_count hs
  unfold bookUpperIntervalStart
  omega

theorem cliqueCapacity_upper_ordinary :
    cliqueCapacity s=(s-1)+4*(s-2)+∑ C : OrdinaryBookBlock hs,(C.1.1.card.choose 2-1) := by
  have h := ordinary_upper_count hs
  omega

private theorem card_le_choose_two {n : ℕ} (hn : 3≤n) : n≤n.choose 2 := by
  rw [Nat.choose_two_right]
  apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left n (show 2≤n-1 by omega)

/-- The full uniform upper interval of Theorem 7.10, with the paper's exact
integral dilation and an explicit integral Minkowski complement. -/
theorem book_upper_interval (hs : 5≤s) {k : ℕ} (hklo : bookUpperIntervalStart s≤k)
    (hkhi : k≤cliqueCapacity s) :
    ∃ f : SetFunction (Fin s⊕Fin k),
      TranslationNormalized f ∧ IntegerValued f ∧ ExtremeSupermodular f ∧
      Graphical (cliqueBook s k) f ∧ FullDimension (basePolytope f) ∧
      MinkowskiIndecomposable (basePolytope f) ∧ LatticePolytope (basePolytope f) ∧
      ∃ R : Set ((Fin s⊕Fin k) → ℝ),LatticePolytope R ∧ R.Nonempty ∧
        basePolytope f+R=(((s-1)*k : ℕ) : ℝ) • graphicalZonotope (cliqueBook s k) := by
  classical
  let N := (s-1)+4*(s-2)
  let l : OrdinaryBookBlock hs → ℕ := fun C => C.1.1.card-1
  let u : OrdinaryBookBlock hs → ℕ := fun C => C.1.1.card.choose 2-1
  have hlu : ∀ C,l C≤u C := by
    intro C
    have hsize := (mem_largeBlocks.mp C.1.2).2
    have hchoose := card_le_choose_two hsize
    dsimp only [l,u]
    omega
  have hlo : N+(∑ C,l C)≤k := by
    rw [bookUpperIntervalStart_eq hs] at hklo
    exact hklo
  have hhi : k≤N+∑ C,u C := by
    rw [cliqueCapacity_upper_ordinary hs] at hkhi
    exact hkhi
  obtain ⟨r,hr,hrsum⟩ := interval_sum_composition l u hlu (n:=k-N) (by omega) (by omega)
  have hP : ∀ C : OrdinaryBookBlock hs,Nonempty
      (WeightedPureBlock C.1.1 ((s-1 : ℕ) : ℤ) (ordinaryBookTarget C.1.1) (r C)) := by
    intro C
    exact ordinary_book_pure_block C.1.1 (mem_largeBlocks.mp C.1.2).2 (hr C).1 (hr C).2
  let P := fun C => Classical.choice (hP C)
  apply lattice_book_of_block_circuit (show 3≤s by omega) (upperBlockEquiv hs)
    (upperPureRank hs r) (upperPureBlock hs r P) (upper_book_scale_rigidity hs r P)
  have ha : Fintype.card (BookAnchor (show 3≤s by omega))=s-1 := by
    simp only [BookAnchor,Fintype.card_coe,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_fin]
  change Fintype.card (BookAnchor (show 3≤s by omega) ⊕
    (Σ b : UpperBookBlock hs,Fin (upperPureRank hs r b)))=k
  rw [Fintype.card_sum,Fintype.card_sigma]
  simp only [Fintype.card_fin,ha,Fintype.sum_sum_type]
  simp only [upperPureRank,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,hrsum]
  dsimp only [N] at hlo ⊢
  omega

end BooleanModule
end GraphicalZonotopes
