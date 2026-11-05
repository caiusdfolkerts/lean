module

public import PaperVerification.NoncommutativeBarCoinvariants
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Actual internal degrees and finite dimensions in the noncommutative bar complex

The subcomplex of degree N is defined by the sum of the actual homogeneous
basis degrees. Its differential is the original multiplication differential.
Finite word counting proves its term dimensions; positivity proves the length
bound. These are supporting results, not a Koszulness assertion.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators PowerSeries

namespace PaperVerification.WeightedBar

open PaperVerification.ReducedBarBasis PaperVerification.AugmentedAlgebraBasis

variable {K A C : Type*} [CommRing K] [Ring A] [Algebra K A]
  (B : Module.Basis (Option C) K A) (δ : C → ℕ)

def totalDegree (L : List C) : ℕ := (L.map δ).sum

@[simp] theorem totalDegree_nil : totalDegree δ []=0 := rfl

@[simp] theorem totalDegree_cons (c : C) (L : List C) :
    totalDegree δ (c::L)=δ c+totalDegree δ L := rfl

theorem totalDegree_append (L T : List C) :
    totalDegree δ (L++T)=totalDegree δ L+totalDegree δ T := by
  simp only [totalDegree,List.map_append,List.sum_append]

def degreePiece (N : ℕ) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | totalDegree δ L=N}

theorem degreePiece_eq_span (N : ℕ) :
    degreePiece (K := K) δ N=Submodule.span K
      ((fun L : List C ↦ Finsupp.single L (1 : K)) '' {L | totalDegree δ L=N}) :=
  Finsupp.supported_eq_span_single K _

theorem prefix_mem_degreePiece (c : C) {N : ℕ} (z : List C →₀ K)
    (hz : z∈degreePiece δ N) : prepend c z∈degreePiece δ (δ c+N) := by
  rw [degreePiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [prefix_single]
    apply Finsupp.single_mem_supported K 1
    change totalDegree δ (c::L)=δ c+N
    change totalDegree δ L=N at hL
    rw [totalDegree_cons,hL]
  | zero => simpa only [map_zero] using (degreePiece (K := K) δ (δ c+N)).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (degreePiece (K := K) δ (δ c+N)).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (degreePiece (K := K) δ (δ c+N)).smul_mem a ih

variable (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

include hδ in
theorem product_appendTail_mem_degreePiece (a b : C) (L : List C) :
    appendTail L (productCoefficients B a b)∈degreePiece δ (δ a+δ b+totalDegree δ L) := by
  rw [appendTail,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro c hc
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported K 1
  change totalDegree δ (c::L)=δ a+δ b+totalDegree δ L
  rw [totalDegree_cons,hδ a b c (Finsupp.mem_support_iff.mp hc)]

include hδ in
theorem differentialBasis_mem_degreePiece (L : List C) :
    differentialBasis B L∈degreePiece δ (totalDegree δ L) := by
  induction L with
  | nil => exact Submodule.zero_mem _
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [differentialBasis,merge_single,mergeBasis,smul_zero,map_zero,sub_zero]
      exact Submodule.zero_mem _
    | cons b L =>
      rw [differentialBasis]
      apply Submodule.sub_mem
      · rw [merge_single,one_smul,mergeBasis]
        simpa only [totalDegree_cons,Nat.add_assoc] using
          product_appendTail_mem_degreePiece B δ hδ a b L
      · exact prefix_mem_degreePiece δ a _ ih

include hδ in
theorem differential_mem_degreePiece {N : ℕ} (z : List C →₀ K)
    (hz : z∈degreePiece δ N) : differential B z∈degreePiece δ N := by
  rw [degreePiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [differential_single,one_smul]
    change totalDegree δ L=N at hL
    simpa only [hL] using differentialBasis_mem_degreePiece B δ hδ L
  | zero => simpa only [map_zero] using (degreePiece (K := K) δ N).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (degreePiece (K := K) δ N).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (degreePiece (K := K) δ N).smul_mem a ih

end PaperVerification.WeightedBar

namespace PaperVerification.WeightedBar

open CategoryTheory CategoryTheory.Limits
open PaperVerification.AugmentedAlgebraBasis
open PaperVerification.NoncommutativeBar

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)
  (δ : I → ℕ)
  (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

def Index (r N : ℕ) := {L : List I // L.length=r ∧ totalDegree δ L=N}

def piece (r N : ℕ) : Submodule K (List I →₀ K) :=
  Finsupp.supported K K {L | L.length=r ∧ totalDegree δ L=N}

theorem piece_eq_inf (r N : ℕ) :
    piece (K := K) δ r N=lengthPiece I K r ⊓ degreePiece δ N := by
  ext z
  change ((z.support : Set (List I))⊆{L | L.length=r ∧ totalDegree δ L=N}) ↔
    ((z.support : Set (List I))⊆{L | L.length=r}) ∧
      ((z.support : Set (List I))⊆{L | totalDegree δ L=N})
  simp only [Set.subset_def,Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨fun L hL ↦ (h L hL).1,fun L hL ↦ (h L hL).2⟩
  · rintro ⟨h₁,h₂⟩ L hL
    exact ⟨h₁ L hL,h₂ L hL⟩

def coordinates (r N : ℕ) :
    piece (K := K) δ r N ≃ₗ[K] (Index δ r N →₀ K) :=
  Finsupp.supportedEquivFinsupp (R := K) _

def basis (r N : ℕ) : Module.Basis (Index δ r N) K (piece (K := K) δ r N) :=
  .ofRepr (coordinates δ r N)

instance indexFinite [Finite I] (r N : ℕ) : Finite (Index δ r N) :=
  Finite.of_injective
    (fun L : Index δ r N ↦ (Equiv.vectorEquivFin I r)
      (⟨L.val,L.property.1⟩ : List.Vector I r))
    (by
      intro L T h
      apply Subtype.ext
      exact congrArg (fun v : List.Vector I r ↦ v.val)
        ((Equiv.vectorEquivFin I r).injective h))

instance indexFintype [Fintype I] (r N : ℕ) : Fintype (Index δ r N) := Fintype.ofFinite _

instance pieceFinite [Fintype I] (r N : ℕ) : Module.Finite K (piece (K := K) δ r N) :=
  Module.Finite.of_basis (basis δ r N)

theorem piece_finrank [Fintype I] (r N : ℕ) :
    Module.finrank K (piece (K := K) δ r N)=Nat.card (Index δ r N) := by
  rw [Nat.card_eq_fintype_card]
  exact Module.finrank_eq_card_basis (basis δ r N)

include hδ in
theorem differential_mem_piece {r N : ℕ} (z : List I →₀ K)
    (hz : z∈piece δ (r+1) N) :
    PaperVerification.ReducedBarBasis.differential B z∈piece δ r N := by
  rw [piece_eq_inf] at hz ⊢
  exact ⟨reducedDifferential_mem_lengthPiece B z hz.1,
    differential_mem_degreePiece B δ hδ z hz.2⟩

def internalDifferential (r N : ℕ) : piece (K := K) δ (r+1) N →ₗ[K] piece (K := K) δ r N where
  toFun z := ⟨-PaperVerification.ReducedBarBasis.differential B z.val,
    Submodule.neg_mem _ (differential_mem_piece B δ hδ z.val z.property)⟩
  map_add' z w := by
    apply Subtype.ext
    change -PaperVerification.ReducedBarBasis.differential B (z.val+w.val)=
      -PaperVerification.ReducedBarBasis.differential B z.val+
        -PaperVerification.ReducedBarBasis.differential B w.val
    rw [map_add,neg_add]
  map_smul' c z := by
    apply Subtype.ext
    change -PaperVerification.ReducedBarBasis.differential B (c • z.val)=
      c • -PaperVerification.ReducedBarBasis.differential B z.val
    rw [map_smul,smul_neg]

include hunit hε in
theorem internalDifferential_squared (r N : ℕ) :
    (internalDifferential B δ hδ r N).comp (internalDifferential B δ hδ (r+1) N)=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change -PaperVerification.ReducedBarBasis.differential B
    (-PaperVerification.ReducedBarBasis.differential B z.val)=0
  rw [map_neg,neg_neg,PaperVerification.ReducedBarBasis.differential_squared ε B hunit hε]

def internalComplex (N : ℕ) : ChainComplex (ModuleCat K) ℕ :=
  ChainComplex.of (fun r ↦ ModuleCat.of K (piece (K := K) δ r N))
    (fun r ↦ ModuleCat.ofHom (internalDifferential B δ hδ r N))
    (fun r ↦ ModuleCat.hom_ext (internalDifferential_squared ε B hunit hε δ hδ r N))

@[simp] theorem internalComplex_d (r N : ℕ) :
    (internalComplex ε B hunit hε δ hδ N).d (r+1) r=
      ModuleCat.ofHom (internalDifferential B δ hδ r N) := by
  simp [internalComplex]

theorem length_le_totalDegree (hpos : ∀ i,0<δ i) (L : List I) :
    L.length≤totalDegree δ L := by
  induction L with
  | nil => rfl
  | cons i L ih =>
      have hi := hpos i
      simp only [List.length_cons,totalDegree_cons]
      omega

theorem piece_eq_bot_of_lt (hpos : ∀ i,0<δ i) (r N : ℕ) (hNr : N<r) :
    piece (K := K) δ r N=⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  change z=0
  apply Finsupp.ext
  intro L
  by_contra hL
  have h := hz (Finsupp.mem_support_iff.mpr hL)
  have bound := length_le_totalDegree δ hpos L
  change L.length=r ∧ totalDegree δ L=N at h
  omega

theorem internalComplex_top_differential (hpos : ∀ i,0<δ i) (N : ℕ) :
    (internalComplex ε B hunit hε δ hδ N).d (N+1) N=0 := by
  have hbot := piece_eq_bot_of_lt (K := K) δ hpos (N+1) N (by omega)
  haveI : Subsingleton (piece (K := K) δ (N+1) N) := by rw [hbot]; infer_instance
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of K (piece (K := K) δ (N+1) N))).eq_of_src _ _

/-- The finite word index is identified with tuples of exactly the same
length and total actual degree. -/
def indexTupleEquiv (r N : ℕ) :
    Index δ r N ≃ {f : Fin r → I // (∑ i,δ (f i))=N} where
  toFun L := ⟨List.Vector.get (⟨L.val,L.property.1⟩ : List.Vector I r),by
    have he : List.ofFn (List.Vector.get (⟨L.val,L.property.1⟩ : List.Vector I r))=L.val :=
      by simpa only [List.Vector.toList_ofFn,List.Vector.toList_mk] using
        congrArg List.Vector.toList (List.Vector.ofFn_get (⟨L.val,L.property.1⟩ : List.Vector I r))
    have hd : totalDegree δ
        (List.ofFn (List.Vector.get (⟨L.val,L.property.1⟩ : List.Vector I r)))=N := by
      rw [he]
      exact L.property.2
    simpa only [totalDegree,List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hd⟩
  invFun f := ⟨(List.Vector.ofFn f.val).val,by
    constructor
    · exact (List.Vector.ofFn f.val).property
    · rw [show (List.Vector.ofFn f.val).val=List.ofFn f.val from
        List.Vector.toList_ofFn f.val]
      simpa only [totalDegree,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
        using f.property⟩
  left_inv L := by
    apply Subtype.ext
    exact congrArg (fun v : List.Vector I r ↦ v.val)
      (List.Vector.ofFn_get (⟨L.val,L.property.1⟩ : List.Vector I r))
  right_inv f := by
    apply Subtype.ext
    funext i
    exact List.Vector.get_ofFn f.val i

def positiveSeries [Fintype I] : ℤ⟦X⟧ := ∑ i,PowerSeries.X^(δ i)

theorem coeff_positiveSeries_pow [Fintype I] (r N : ℕ) :
    PowerSeries.coeff N (positiveSeries δ^r)=(Nat.card (Index δ r N) : ℤ) := by
  rw [positiveSeries,Fintype.sum_pow,map_sum]
  simp only [Finset.prod_pow_eq_pow_sum,PowerSeries.coeff_X_pow]
  rw [show (∑ f : Fin r → I,if N=(∑ i,δ (f i)) then (1 : ℤ) else 0)=
      ∑ f : Fin r → I,if (∑ i,δ (f i))=N then (1 : ℤ) else 0 by
        apply Finset.sum_congr rfl
        intro f hf
        simp only [eq_comm]]
  rw [Finset.sum_boole,Nat.card_congr (indexTupleEquiv δ r N),
    Nat.card_eq_fintype_card,Fintype.card_subtype]

theorem internalComplex_term_rank [Fintype I] (r N : ℕ) :
    (Module.finrank K ((internalComplex ε B hunit hε δ hδ N).X r) : ℤ)=
      PowerSeries.coeff N (positiveSeries δ^r) := by
  rw [coeff_positiveSeries_pow]
  exact congrArg (fun n : ℕ ↦ (n : ℤ)) (piece_finrank (K := K) δ r N)

theorem positiveSeries_constantCoeff [Fintype I] (hpos : ∀ i,0<δ i) :
    PowerSeries.constantCoeff (positiveSeries δ)=0 := by
  have hne : ∀ i,δ i≠0 := fun i ↦ Nat.ne_of_gt (hpos i)
  simp [positiveSeries,hne]

end PaperVerification.WeightedBar
