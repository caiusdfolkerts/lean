module

public import Papers.GraphicalZonotopes.GraphicalCone
public import Papers.GraphicalZonotopes.LocalDeltas
public import Mathlib.Data.Finset.Max

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace PositiveDecomposition
open Finset
open scoped BigOperators

section Minima
variable {X : Type*} [Fintype X] [Nonempty X]

def minimizingArgument (f : X → ℝ) : X :=
  Classical.choose (univ.exists_min_image f univ_nonempty)

def minimumValue (f : X → ℝ) : ℝ := f (minimizingArgument f)

theorem minimumValue_le (f : X → ℝ) (x : X) : minimumValue f ≤ f x :=
  (Classical.choose_spec (univ.exists_min_image f univ_nonempty)).2 x (mem_univ x)

theorem exists_minimumValue (f : X → ℝ) : ∃ x, f x = minimumValue f :=
  ⟨minimizingArgument f,rfl⟩

end Minima

variable {V A : Type*} [Fintype V] [LinearOrder V] [Fintype A]

abbrev Context (u v : V) := {S : Finset V // u ∉ S ∧ v ∉ S}

noncomputable instance contextFintype (u v : V) : Fintype (Context u v) := by
  classical
  infer_instance

instance contextNonempty (u v : V) : Nonempty (Context u v) :=
  ⟨⟨∅,by simp⟩⟩

def minimumSlack (z : SetFunction V) (u v : V) : ℝ :=
  minimumValue (fun S : Context u v => delta z u v S.1)

theorem minimumSlack_le (z : SetFunction V) (u v : V) (S : Finset V)
    (hu : u ∉ S) (hv : v ∉ S) : minimumSlack z u v ≤ delta z u v S :=
  minimumValue_le (fun T : Context u v => delta z u v T.1) ⟨S,hu,hv⟩

theorem exists_minimumSlack (z : SetFunction V) (u v : V) :
    ∃ S : Finset V, u ∉ S ∧ v ∉ S ∧ delta z u v S = minimumSlack z u v := by
  obtain ⟨S,hS⟩ := exists_minimumValue (fun S : Context u v => delta z u v S.1)
  exact ⟨S.1,S.2.1,S.2.2,hS⟩

theorem minimumSlack_comm (z : SetFunction V) (u v : V) :
    minimumSlack z u v = minimumSlack z v u := by
  apply le_antisymm
  · obtain ⟨S,hv,hu,hmin⟩ := exists_minimumSlack z v u
    have h := minimumSlack_le z u v S hu hv
    have he : delta z u v S=delta z v u S := by unfold delta; rw [insert_comm]; ring
    rwa [he,hmin] at h
  · obtain ⟨S,hu,hv,hmin⟩ := exists_minimumSlack z u v
    have h := minimumSlack_le z v u S hv hu
    have he : delta z v u S=delta z u v S := by unfold delta; rw [insert_comm]; ring
    rwa [he,hmin] at h

def pairPart (y : SetFunction V) : SetFunction V :=
  fun C => if C.card = 2 then y C else 0

theorem pairPart_zero {y : SetFunction V} {C : Finset V} (hC : C.card ≠ 2) :
    pairPart y C = 0 := by simp [pairPart,hC]

theorem zeta_pairSupported_delta (y : SetFunction V)
    (hy : ∀ C, C.card ≠ 2 → y C = 0) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (zeta y) u v S = y {u,v} := by
  rw [delta_zeta huv hu hv]
  refine Finset.sum_eq_single (s := (insert u (insert v S)).powerset.filter
    (fun C => u ∈ C ∧ v ∈ C)) (f := y) ({u,v} : Finset V) ?_ ?_
  · intro C hC hne
    apply hy C
    intro hcard
    have hmem := (mem_filter.mp hC).2
    have hsub : ({u,v} : Finset V) ⊆ C :=
      insert_subset hmem.1 (singleton_subset_iff.mpr hmem.2)
    have he : ({u,v} : Finset V) = C := eq_of_subset_of_card_le hsub (by
      simpa [huv] using le_of_eq hcard)
    exact hne he.symm
  · intro hnot
    exact False.elim (hnot (by simp))

def allocation (z : SetFunction V) : SetFunction V := fun C =>
  if h : C.card = 2 then
    -minimumSlack z (C.min' (card_pos.mp (by omega))) (C.max' (card_pos.mp (by omega)))
  else 0

theorem allocation_zero (z : SetFunction V) {C : Finset V} (hC : C.card ≠ 2) :
    allocation z C = 0 := by simp [allocation,hC]

theorem allocation_pair (z : SetFunction V) {u v : V} (huv : u ≠ v) :
    allocation z {u,v} = -minimumSlack z u v := by
  simp only [allocation,card_pair huv,↓reduceDIte,min'_pair,max'_pair]
  rcases le_total u v with h | h
  · rw [min_eq_left h,max_eq_right h]
  · rw [min_eq_right h,max_eq_left h,minimumSlack_comm z v u]

theorem allocation_nonnegative (z : SetFunction V)
    (hzero : ∀ u v, u ≠ v → delta z u v ∅ = 0) (C : Finset V) :
    0 ≤ allocation z C := by
  by_cases hC : C.card = 2
  · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
    rw [allocation_pair z huv]
    have hm := minimumSlack_le z u v ∅ (by simp) (by simp)
    rw [hzero u v huv] at hm
    linarith
  · simp [allocation_zero z hC]

def adjusted (z : SetFunction V) : SetFunction V := z+zeta (allocation z)

theorem adjusted_supermodular (z : SetFunction V) : Supermodular (adjusted z) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [adjusted,delta_add,zeta_pairSupported_delta (allocation z)
    (fun C hC => allocation_zero z hC) huv hu hv,allocation_pair z huv]
  have h := minimumSlack_le z u v S hu hv
  linarith

theorem pairSupported_zeta_normalized (y : SetFunction V)
    (hy : ∀ C, C.card ≠ 2 → y C = 0) : TranslationNormalized (zeta y) := by
  apply (zeta_normalized_iff y).mpr
  exact ⟨hy ∅ (by simp),fun v => hy {v} (by simp)⟩

theorem adjusted_normalized {z : SetFunction V} (hz : TranslationNormalized z) :
    TranslationNormalized (adjusted z) := by
  have ha := pairSupported_zeta_normalized (allocation z)
    (fun C hC => allocation_zero z hC)
  exact ⟨by change z ∅+zeta (allocation z) ∅=0; rw [hz.1,ha.1,add_zero],
    fun v => by change z {v}+zeta (allocation z) {v}=0; rw [hz.2 v,ha.2 v,add_zero]⟩

/-- Exact independence of the conditioning variables used by the separate
higher-coefficient blocks. For triangle classes this is proved by partitioning
the common-neighbor variables of each edge. -/
def IndependentSlacks (h : A → SetFunction V) : Prop :=
  ∀ u v, u ≠ v → ∀ S : A → Context u v,
    ∃ T : Context u v, ∀ a, delta (h a) u v T.1 = delta (h a) u v (S a).1

/-- Disjoint conditioning-variable blocks give exact independent
realizability, not just a lower bound on the sum of their minima. -/
theorem independentSlacks_of_disjoint_variables (h : A → SetFunction V)
    (hblocks : ∀ u v, u ≠ v → ∃ I : A → Finset V,
      (∀ a b, a ≠ b → Disjoint (I a) (I b)) ∧
      ∀ a S, u ∉ S → v ∉ S →
        delta (h a) u v S = delta (h a) u v (S ∩ I a)) :
    IndependentSlacks h := by
  classical
  intro u v huv S
  obtain ⟨I,hdisj,hdep⟩ := hblocks u v huv
  let T : Finset V := univ.biUnion (fun a => (S a).1 ∩ I a)
  have huT : u ∉ T := by
    intro hu
    obtain ⟨a,ha,hu⟩ := mem_biUnion.mp hu
    exact (S a).2.1 (mem_inter.mp hu).1
  have hvT : v ∉ T := by
    intro hv
    obtain ⟨a,ha,hv⟩ := mem_biUnion.mp hv
    exact (S a).2.2 (mem_inter.mp hv).1
  refine ⟨⟨T,huT,hvT⟩,?_⟩
  intro a
  have he : T ∩ I a = (S a).1 ∩ I a := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxT,hxa⟩ := mem_inter.mp hx
      obtain ⟨b,hb,hxb⟩ := mem_biUnion.mp hxT
      by_cases hba : b = a
      · subst b
        exact hxb
      · exact False.elim ((Finset.disjoint_left.mp (hdisj b a hba))
          (mem_inter.mp hxb).2 hxa)
    · intro hx
      exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨a,mem_univ a,hx⟩,(mem_inter.mp hx).2⟩
  calc
    delta (h a) u v T = delta (h a) u v (T ∩ I a) := hdep a T huT hvT
    _ = delta (h a) u v ((S a).1 ∩ I a) := by rw [he]
    _ = delta (h a) u v (S a).1 := (hdep a (S a).1 (S a).2.1 (S a).2.2).symm

def residual (y : SetFunction V) (h : A → SetFunction V) : SetFunction V :=
  fun C => if C.card = 2 then y C-∑ a, allocation (h a) C else 0

theorem residual_zero (y : SetFunction V) (h : A → SetFunction V)
    {C : Finset V} (hC : C.card ≠ 2) : residual y h C = 0 := by
  simp [residual,hC]

theorem residual_nonnegative (y z : SetFunction V) (h : A → SetFunction V)
    (hs : Supermodular z) (he : z = zeta (pairPart y)+∑ a, h a)
    (hind : IndependentSlacks h) (C : Finset V) : 0 ≤ residual y h C := by
  classical
  by_cases hC : C.card = 2
  · obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hC
    choose S hu hv hmin using fun a : A => exists_minimumSlack (h a) u v
    let choice : A → Context u v := fun a => ⟨S a,hu a,hv a⟩
    obtain ⟨T,hT⟩ := hind u v huv choice
    have hpositive := hs.elemental u v huv T.1 T.2.1 T.2.2
    rw [he,delta_add,zeta_pairSupported_delta (pairPart y)
      (fun C hC => pairPart_zero hC) huv T.2.1 T.2.2,delta_sum] at hpositive
    have hmins : (∑ a, delta (h a) u v T.1) = ∑ a, minimumSlack (h a) u v := by
      apply sum_congr rfl
      intro a ha
      exact (hT a).trans (hmin a)
    rw [hmins] at hpositive
    simp only [pairPart,card_pair huv,if_pos] at hpositive
    simp only [residual,card_pair huv,if_pos,allocation_pair _ huv,sum_neg_distrib]
    linarith
  · simp [residual_zero y h hC]

theorem residual_supermodular (y z : SetFunction V) (h : A → SetFunction V)
    (hs : Supermodular z) (he : z = zeta (pairPart y)+∑ a, h a)
    (hind : IndependentSlacks h) : Supermodular (zeta (residual y h)) := by
  apply ElementallyNonnegative.supermodular
  intro u v huv S hu hv
  rw [zeta_pairSupported_delta (residual y h)
    (fun C hC => residual_zero y h hC) huv hu hv]
  exact residual_nonnegative y z h hs he hind _

theorem allocation_add_residual (y : SetFunction V) (h : A → SetFunction V) :
    (∑ a, allocation (h a))+residual y h = pairPart y := by
  classical
  funext C
  by_cases hC : C.card = 2
  · simp only [Pi.add_apply,Finset.sum_apply,residual,pairPart,if_pos hC]
    ring
  · simp [hC,residual,pairPart,allocation_zero]

theorem adjusted_sum_reconstruct (y z : SetFunction V) (h : A → SetFunction V)
    (he : z = zeta (pairPart y)+∑ a, h a) :
    (∑ a, adjusted (h a))+zeta (residual y h) = z := by
  classical
  have hadd : (∑ a, zeta (allocation (h a)))+zeta (residual y h) = zeta (pairPart y) := by
    change (∑ a, zetaLinear (allocation (h a)))+zetaLinear (residual y h) = _
    rw [← map_sum,← map_add,allocation_add_residual]
    rfl
  simp only [adjusted,sum_add_distrib]
  rw [add_assoc,hadd,he,add_comm]

/-- The positivity and exact reconstruction part of Lemma4.2. Every block
receives precisely minus its edgewise conditional minimum; the leftover pair
coefficients are nonnegative. The independence hypothesis is an explicit
mathematical obligation for the triangle-class dictionary, not an assumed
property of arbitrary coefficient partitions. -/
theorem positive_block_decomposition (y z : SetFunction V) (h : A → SetFunction V)
    (hs : Supermodular z) (he : z = zeta (pairPart y)+∑ a, h a)
    (hn : ∀ a, TranslationNormalized (h a))
    (hzero : ∀ a u v, u ≠ v → delta (h a) u v ∅ = 0)
    (hind : IndependentSlacks h) :
    (∀ a, TranslationNormalized (adjusted (h a)) ∧ Supermodular (adjusted (h a))) ∧
    (∀ a C, 0 ≤ allocation (h a) C) ∧
    (∀ C, 0 ≤ residual y h C) ∧
    TranslationNormalized (zeta (residual y h)) ∧
    Supermodular (zeta (residual y h)) ∧
    (∑ a, adjusted (h a))+zeta (residual y h) = z := by
  refine ⟨fun a => ⟨adjusted_normalized (hn a),adjusted_supermodular (h a)⟩,
    fun a C => allocation_nonnegative (h a) (hzero a) C,
    residual_nonnegative y z h hs he hind,
    pairSupported_zeta_normalized _ (fun C hC => residual_zero y h hC),
    residual_supermodular y z h hs he hind,adjusted_sum_reconstruct y z h he⟩

end PositiveDecomposition
end GraphicalZonotopes
