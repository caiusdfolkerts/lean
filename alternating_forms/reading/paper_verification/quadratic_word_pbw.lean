module

public import PaperVerification.QuadraticWordBarCoordinates
public import PaperVerification.WeightedBarTor
public import PaperVerification.AlternatingFormsFilteredComparison
public import PaperVerification.AlternatingFormsPBWInversions

/-!
# Koszul concentration from actual signed quadratic normal words

The basis is a basis of the original augmented algebra. Normal products
concatenate with coefficient one; all other nonzero products have the
same multiset of generators. Sorting strictly lowers the finite number
of forbidden ordered pairs. The actual bar differential therefore has
the proved monomial cut differential as its leading map. Filtered
exactness proves off-diagonal homology vanishing in the actual internal
degree complexes. No PBW-to-Koszul theorem is assumed.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.QuadraticWordPBW

open PaperVerification.QuadraticWordBar
open PaperVerification.AlternatingForms.BarCoefficientFormula
open PaperVerification.AlternatingForms.PBWWords
open PaperVerification.AlternatingForms.FilteredComparison
open PaperVerification.ReducedBarBasis PaperVerification.AugmentedAlgebraBasis
open PaperVerification.Fermion.BasisFiltered
open CategoryTheory CategoryTheory.Limits

universe u
variable {K A C J : Type u} [Field K] [Ring A] [Algebra K A]
  [Fintype J] {R : J → J → Prop} [IsTrans J R]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option C) K A)
  (hunit : B none=1) (hε : ∀ c,ε (B (some c))=0)
  (e : C ≃ PositiveWord R)
  (hnormal : ∀ a b (h : ((e a).val++(e b).val).IsChain R),
    productCoefficients B a b=Finsupp.single (concatenateNormal e a b h) 1)
  (hperm : ∀ a b c,productCoefficients B a b c≠0 →
    (e c).val.Perm ((e a).val++(e b).val))

def wordDegree (c : C) : ℕ := (e c).val.length

include hperm in
theorem product_degree (a b c : C) (h : productCoefficients B a b c≠0) :
    wordDegree e c=wordDegree e a+wordDegree e b := by
  simpa only [wordDegree,List.length_append] using (hperm a b c h).length_eq

theorem flatten_length (L : List C) :
    (flattenBarWord e L).length=WeightedBar.totalDegree (wordDegree e) L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change ((e a).val++flattenBarWord e L).length=
      wordDegree e a+WeightedBar.totalDegree (wordDegree e) L
    rw [List.length_append,ih]
    rfl

theorem internalPiece_eq (r N : ℕ) :
    internalDegreePiece (K := K) e r N=WeightedBar.piece (K := K) (wordDegree e) r N := by
  unfold internalDegreePiece WeightedBar.piece
  congr 1
  ext L
  simp only [Set.mem_setOf_eq,flatten_length]

def strictWordPiece (W : List J) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | (flattenBarWord e L).Perm W ∧
    badPairs R (flattenBarWord e L)<badPairs R W}

def sameWordPiece (W : List J) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | flattenBarWord e L=W}

theorem strict_prefix (W : List J) (a : C) (z : List C →₀ K)
    (hz : z∈strictWordPiece (K := K) e W) :
    prepend a z∈strictWordPiece (K := K) e ((e a).val++W) := by
  rw [strictWordPiece,Finsupp.supported_eq_span_single] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [prefix_single]
    apply Finsupp.single_mem_supported K 1
    constructor
    · exact hL.1.append_left (e a).val
    · change badPairs R ((e a).val++flattenBarWord e L)<badPairs R ((e a).val++W)
      have hc := badPairs_context_balance R (e a).val [] (flattenBarWord e L) W hL.1
      simp only [List.append_nil] at hc
      have hlt : badPairs R (flattenBarWord e L)<badPairs R W := hL.2
      omega
  | zero => simpa only [map_zero] using (strictWordPiece (K := K) e ((e a).val++W)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (strictWordPiece (K := K) e ((e a).val++W)).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using (strictWordPiece (K := K) e ((e a).val++W)).smul_mem c ih

theorem same_prefix (W : List J) (a : C) (z : List C →₀ K)
    (hz : z∈sameWordPiece (K := K) e W) :
    prepend a z∈sameWordPiece (K := K) e ((e a).val++W) := by
  rw [sameWordPiece,Finsupp.supported_eq_span_single] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [prefix_single]
    apply Finsupp.single_mem_supported K 1
    change (e a).val++flattenBarWord e L=(e a).val++W
    rw [hL]
  | zero => simpa only [map_zero] using (sameWordPiece (K := K) e ((e a).val++W)).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (sameWordPiece (K := K) e ((e a).val++W)).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using (sameWordPiece (K := K) e ((e a).val++W)).smul_mem c ih

theorem normal_adjacent_same (a b : C) (L : List C) :
    appendTail L (normalProduct (K := K) e a b)∈sameWordPiece e (flattenBarWord e (a::b::L)) := by
  unfold normalProduct
  split_ifs with h
  · rw [appendTail_single]
    apply Finsupp.single_mem_supported K 1
    change (e (concatenateNormal e a b h)).val++flattenBarWord e L=
      (e a).val++((e b).val++flattenBarWord e L)
    rw [concatenateNormal_word,List.append_assoc]
  · rw [map_zero]
    exact Submodule.zero_mem _

theorem normal_differential_same (L : List C) :
    basisDifferential (normalProduct (K := K) e) L∈sameWordPiece e (flattenBarWord e L) := by
  induction L with
  | nil => exact Submodule.zero_mem _
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [basisDifferential,adjacent,map_zero,sub_zero]
      exact Submodule.zero_mem _
    | cons b L =>
      change appendTail L (normalProduct e a b)-
        prepend a (basisDifferential (normalProduct e) (b::L))∈_
      exact Submodule.sub_mem _ (normal_adjacent_same e a b L) (same_prefix e _ a _ ih)

include hnormal hperm in
theorem adjacent_difference_strict (a b : C) (L : List C) :
    appendTail L (productCoefficients B a b)-appendTail L (normalProduct e a b)∈
      strictWordPiece e (flattenBarWord e (a::b::L)) := by
  by_cases h : ((e a).val++(e b).val).IsChain R
  · rw [hnormal a b h,normalProduct,dif_pos h,sub_self]
    exact Submodule.zero_mem _
  · rw [normalProduct,dif_neg h,map_zero,sub_zero,
      appendTail,Finsupp.linearCombination_apply,Finsupp.sum]
    apply Submodule.sum_mem
    intro c hc
    apply Submodule.smul_mem
    apply Finsupp.single_mem_supported K 1
    have hp := hperm a b c (Finsupp.mem_support_iff.mp hc)
    constructor
    · simpa only [flattenBarWord,List.map_cons,List.flatten_cons,List.append_assoc] using
        hp.append_right (flattenBarWord e L)
    · have hbad : ¬((e a).val++(e b).val).Pairwise R :=
        fun hh => h (List.isChain_iff_pairwise.mpr hh)
      have hgood : (e c).val.Pairwise R := List.isChain_iff_pairwise.mp (e c).property.2
      have hb := badPairs_context_decrease R [] (flattenBarWord e L)
        ((e a).val++(e b).val) (e c).val hp.symm hbad hgood
      simpa only [QuadraticWordBar.flattenBarWord,List.map_cons,List.flatten_cons,
        List.nil_append,List.append_assoc] using hb

include hnormal hperm in
theorem differential_difference_strict (L : List C) :
    differentialBasis B L-basisDifferential (normalProduct e) L∈
      strictWordPiece e (flattenBarWord e L) := by
  induction L with
  | nil => simpa only [differentialBasis,basisDifferential,sub_self] using
      (strictWordPiece (K := K) e (flattenBarWord e [])).zero_mem
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [differentialBasis,basisDifferential,adjacent,merge_single,
        mergeBasis,smul_zero,map_zero,sub_zero,sub_self]
      exact Submodule.zero_mem _
    | cons b L =>
      have h₁ := adjacent_difference_strict B e hnormal hperm a b L
      have h₂ := strict_prefix e (flattenBarWord e (b::L)) a _ ih
      have he : differentialBasis B (a::b::L)-basisDifferential (normalProduct e) (a::b::L)=
          (appendTail L (productCoefficients B a b)-appendTail L (normalProduct e a b))-
            prepend a (differentialBasis B (b::L)-basisDifferential (normalProduct e) (b::L)) := by
        simp only [differentialBasis,basisDifferential,adjacent,merge_single,mergeBasis,
          one_smul,map_sub]
        abel
      rw [he]
      exact Submodule.sub_mem _ h₁ h₂

include hperm in
theorem differential_mem_internal {r N : ℕ} (z : List C →₀ K)
    (hz : z∈internalDegreePiece (K := K) e (r+1) N) :
    differential B z∈internalDegreePiece (K := K) e r N := by
  rw [internalPiece_eq] at hz ⊢
  exact WeightedBar.differential_mem_piece B (wordDegree e) (product_degree B e hperm) z hz

def actualDifferential (r N : ℕ) :
    internalDegreePiece (K := K) e (r+1) N →ₗ[K] internalDegreePiece (K := K) e r N where
  toFun z := ⟨-differential B z.val,
    Submodule.neg_mem _ (differential_mem_internal B e hperm z.val z.property)⟩
  map_add' x y := by
    apply Subtype.ext
    change -differential B (x.val+y.val)= -differential B x.val + -differential B y.val
    rw [map_add,neg_add]
  map_smul' c x := by
    apply Subtype.ext
    change -differential B (c • x.val)=c • -differential B x.val
    rw [map_smul,smul_neg]

include hunit hε in
theorem actualDifferential_squared (r N : ℕ) :
    (actualDifferential B e hperm r N).comp (actualDifferential B e hperm (r+1) N)=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change -differential B (-differential B z.val)=0
  rw [map_neg,neg_neg,differential_squared ε B hunit hε]

def wordWeight (r N : ℕ) (L : InternalDegreeIndex e r N) : ℕ :=
  badPairs R (flattenBarWord e L.val)

theorem leading_homogeneous (r N : ℕ) (L : InternalDegreeIndex e (r+1) N) :
    Homogeneous (R := K) (M := ↥(internalDegreePiece (K := K) e r N))
      (tensorBasis e r N) (wordWeight e r N) (wordWeight e (r+1) N L)
      (leadingDegreeDifferential e r N (tensorBasis e (r+1) N L)) := by
  intro T hT
  rw [tensorBasis_repr_apply,leadingDegreeDifferential_tensorBasis_val,
    Finsupp.neg_apply,neg_ne_zero] at hT
  have hs := normal_differential_same (K := K) e L.val (Finsupp.mem_support_iff.mpr hT)
  change badPairs R (flattenBarWord e T.val)=badPairs R (flattenBarWord e L.val)
  rw [hs]

include hnormal hperm in
theorem actual_hasTop (r N : ℕ) (L : InternalDegreeIndex e (r+1) N) :
    HasTop (R := K) (M := ↥(internalDegreePiece (K := K) e r N))
      (tensorBasis e r N) (wordWeight e r N) (wordWeight e (r+1) N L)
      (actualDifferential B e hperm r N (tensorBasis e (r+1) N L))
      (leadingDegreeDifferential e r N (tensorBasis e (r+1) N L)) := by
  apply hasTop_of_strict_difference (K := K)
    (M₀ := ↥(internalDegreePiece (K := K) e r N)) (tensorBasis e r N) (wordWeight e r N)
  · exact leading_homogeneous e r N L
  · intro T hT
    have he : (tensorBasis (K := K) e r N).repr
        (actualDifferential B e hperm r N (tensorBasis e (r+1) N L)-
          leadingDegreeDifferential e r N (tensorBasis e (r+1) N L)) T=
        -(((differentialBasis B L.val-
          basisDifferential (normalProduct (K := K) e) L.val) : List C →₀ K) T.val) := by
      rw [tensorBasis_repr_sub,leadingDegreeDifferential_tensorBasis_val]
      change (-differential B (tensorBasis e (r+1) N L).val) T.val-
        (-basisDifferential (normalProduct e) L.val) T.val=_
      rw [tensorBasis_val,differential_single,one_smul]
      simp only [Finsupp.neg_apply,Finsupp.sub_apply]
      abel
    rw [he,neg_ne_zero] at hT
    exact (differential_difference_strict B e hnormal hperm L.val
      (Finsupp.mem_support_iff.mpr hT)).2

include hunit hε hnormal hperm in
theorem actual_range_eq_ker (r N : ℕ) (hr : r+1≠N) :
    (actualDifferential B e hperm (r+1) N).range=(actualDifferential B e hperm r N).ker := by
  exact range_eq_ker_of_basis (K := K)
    (M₀ := ↥(internalDegreePiece (K := K) e r N))
    (M₁ := ↥(internalDegreePiece (K := K) e (r+1) N))
    (M₂ := ↥(internalDegreePiece (K := K) e (r+2) N))
    (I₀ := InternalDegreeIndex e r N)
    (I₁ := InternalDegreeIndex e (r+1) N)
    (I₂ := InternalDegreeIndex e (r+2) N)
    (tensorBasis (K := K) e r N) (wordWeight e r N)
    (tensorBasis e (r+1) N) (wordWeight e (r+1) N)
    (tensorBasis e (r+2) N) (wordWeight e (r+2) N)
    (actualDifferential B e hperm r N) (actualDifferential B e hperm (r+1) N)
    (leadingDegreeDifferential (K := K) e r N)
    (leadingDegreeDifferential (K := K) e (r+1) N)
    (actualDifferential_squared ε B hunit hε e hperm r N)
    (actual_hasTop B e hnormal hperm r N)
    (actual_hasTop B e hnormal hperm (r+1) N)
    (leadingDegree_range_eq_ker (K := K) e r N hr)

def actualComplex (N : ℕ) : ChainComplex (ModuleCat K) ℕ :=
  ChainComplex.of
    (fun r => ModuleCat.of K (internalDegreePiece (K := K) e r N))
    (fun r => ModuleCat.ofHom (actualDifferential B e hperm r N))
    (fun r => ModuleCat.hom_ext (actualDifferential_squared ε B hunit hε e hperm r N))

@[simp] theorem actualComplex_d (r N : ℕ) :
    (actualComplex ε B hunit hε e hperm N).d (r+1) r=
      ModuleCat.ofHom (actualDifferential B e hperm r N) := by
  simp [actualComplex]

include hunit hε hnormal hperm in
theorem actual_homology_off_diagonal (r N : ℕ) (hr : r≠N) :
    IsZero ((actualComplex ε B hunit hε e hperm N).homology r) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  cases r with
  | zero =>
    apply HomologicalComplex.ExactAt.of_isZero
    change IsZero (ModuleCat.of K (internalDegreePiece (K := K) e 0 N))
    have hzero (z : internalDegreePiece (K := K) e 0 N) : z=0 := by
      apply Subtype.ext
      apply Finsupp.ext
      intro L
      change z.val L=0
      apply (Finsupp.mem_supported' K z.val).mp z.property
      rintro ⟨hL,hW⟩
      have hn : L=[] := List.length_eq_zero_iff.mp hL
      subst L
      exact hr hW
    letI : Subsingleton (internalDegreePiece (K := K) e 0 N) :=
      ⟨fun x y => (hzero x).trans (hzero y).symm⟩
    exact ModuleCat.isZero_of_subsingleton _
  | succ r =>
    rw [HomologicalComplex.exactAt_iff' _ (r+2) (r+1) r (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change (((actualComplex ε B hunit hε e hperm N).d (r+2) (r+1)).hom).range=
      (((actualComplex ε B hunit hε e hperm N).d (r+1) r).hom).ker
    rw [actualComplex_d,actualComplex_d]
    exact actual_range_eq_ker ε B hunit hε e hnormal hperm r N hr

/-- The relation-word complex is the original internally graded bar
complex. Its component maps are the identity on every coefficient word. -/
def actualWeightedIso (N : ℕ) :
    actualComplex ε B hunit hε e hperm N ≅
      WeightedBar.internalComplex ε B hunit hε (wordDegree e)
        (product_degree B e hperm) N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r => (LinearEquiv.ofEq _ _ (internalPiece_eq (K := K) e r N)).toModuleIso) (by
      intro i j hij
      change j+1=i at hij
      subst i
      rw [actualComplex_d,WeightedBar.internalComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      rfl)

include hunit hε hnormal hperm in
/-- Genuine ordinary Tor is concentrated on the original internal-degree
 diagonal. Every structural hypothesis above concerns the actual algebra
basis and actual multiplication and can be checked independently. -/
theorem hasDiagonalTor :
    WeightedBar.HasDiagonalTor ε B hunit hε (wordDegree e) (product_degree B e hperm) := by
  apply (WeightedBar.hasDiagonalTor_iff ε B hunit hε (wordDegree e)
    (product_degree B e hperm)).mpr
  intro r N hr
  exact (actual_homology_off_diagonal ε B hunit hε e hnormal hperm r N hr).of_iso
    (HomologicalComplex.homologyMapIso
      (actualWeightedIso ε B hunit hε e hperm N) r).symm

end PaperVerification.QuadraticWordPBW
