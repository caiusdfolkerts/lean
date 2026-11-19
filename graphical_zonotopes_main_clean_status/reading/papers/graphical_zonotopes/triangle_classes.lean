module

public import Papers.GraphicalZonotopes.PositiveDecomposition

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace PositiveDecomposition
open Finset
open scoped BigOperators
variable {V A : Type*} [Fintype V] [LinearOrder V] [Fintype A]

/-- Compatibility of a coefficient partition with the triangles in every
nonzero higher clique. The coarse and refined triangle-class partitions both
have this property; an arbitrary coefficient partition need not. -/
def ClassCompatible (y : SetFunction V) (classOf : Finset V → A) : Prop :=
  ∀ C, 4 ≤ C.card → y C ≠ 0 → ∀ T, T.card = 3 → T ⊆ C → classOf T = classOf C

def classCoefficients (y : SetFunction V) (classOf : Finset V → A)
    (a : A) : SetFunction V := by
  classical
  exact fun C => if 3 ≤ C.card ∧ classOf C = a then y C else 0

def higherClass (y : SetFunction V) (classOf : Finset V → A) (a : A) : SetFunction V :=
  zeta (classCoefficients y classOf a)

theorem classCoefficients_nonzero {y : SetFunction V} {classOf : Finset V → A}
    {a : A} {C : Finset V} (h : classCoefficients y classOf a C ≠ 0) :
    3 ≤ C.card ∧ classOf C = a ∧ y C ≠ 0 := by
  classical
  by_cases hC : 3 ≤ C.card ∧ classOf C = a
  · simp only [classCoefficients,if_pos hC] at h
    exact ⟨hC.1,hC.2,h⟩
  · simp [classCoefficients,hC] at h

theorem higherClass_normalized (y : SetFunction V) (classOf : Finset V → A) (a : A) :
    TranslationNormalized (higherClass y classOf a) := by
  classical
  apply (zeta_normalized_iff _).mpr
  simp [classCoefficients]

theorem higherClass_delta_empty (y : SetFunction V) (classOf : Finset V → A) (a : A)
    (u v : V) (huv : u ≠ v) : delta (higherClass y classOf a) u v ∅ = 0 := by
  classical
  rw [higherClass,delta_zeta_empty _ huv]
  simp [classCoefficients,card_pair huv]

theorem class_coefficients_reconstruct (y : SetFunction V) (classOf : Finset V → A)
    (hy : y ∅ = 0 ∧ ∀ v, y {v} = 0) :
    pairPart y+∑ a, classCoefficients y classOf a = y := by
  classical
  funext C
  by_cases hC : 3 ≤ C.card
  · have hC2 : C.card ≠ 2 := by omega
    simp [pairPart,classCoefficients,hC,hC2]
  · have hsum : (∑ a, classCoefficients y classOf a C) = 0 := by
      simp [classCoefficients,hC]
    simp only [Pi.add_apply,Finset.sum_apply]
    rw [hsum,add_zero]
    by_cases hC2 : C.card = 2
    · simp [pairPart,hC2]
    · have hsmall : C.card = 0 ∨ C.card = 1 := by omega
      rcases hsmall with he | he
      · rw [card_eq_zero.mp he]
        simp [pairPart,hy.1]
      · obtain ⟨v,rfl⟩ := card_eq_one.mp he
        simp [pairPart,hy.2]

theorem higher_classes_reconstruct (y : SetFunction V) (classOf : Finset V → A)
    (hy : y ∅ = 0 ∧ ∀ v, y {v} = 0) :
    zeta y = zeta (pairPart y)+∑ a, higherClass y classOf a := by
  have he := congrArg zetaLinear (class_coefficients_reconstruct y classOf hy)
  rw [map_add,map_sum] at he
  change zeta (pairPart y)+(∑ a,zeta (classCoefficients y classOf a))=zeta y at he
  exact he.symm

def classVariables (classOf : Finset V → A) (u v : V) (a : A) : Finset V := by
  classical
  exact univ.filter (fun w => w ≠ u ∧ w ≠ v ∧ classOf {u,v,w} = a)

theorem classVariables_disjoint (classOf : Finset V → A) (u v : V)
    (a b : A) (hab : a ≠ b) :
    Disjoint (classVariables classOf u v a) (classVariables classOf u v b) := by
  classical
  rw [Finset.disjoint_left]
  intro w hwa hwb
  have ha := (mem_filter.mp hwa).2.2.2
  have hb := (mem_filter.mp hwb).2.2.2
  exact hab (ha.symm.trans hb)

theorem remaining_vertex_in_classVariables {y : SetFunction V}
    {classOf : Finset V → A} (hcomp : ClassCompatible y classOf)
    {a : A} {C : Finset V} (hC : classCoefficients y classOf a C ≠ 0)
    {u v w : V} (huv : u ≠ v) (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C)
    (hwu : w ≠ u) (hwv : w ≠ v) : w ∈ classVariables classOf u v a := by
  classical
  obtain ⟨hcard,hclass,hyC⟩ := classCoefficients_nonzero hC
  have hTcard : ({u,v,w} : Finset V).card = 3 := by
    simp [huv,hwu,hwv,Ne.symm hwu,Ne.symm hwv]
  have hsub : ({u,v,w} : Finset V) ⊆ C := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have hclasses : classOf {u,v,w} = classOf C := by
    by_cases hfour : 4 ≤ C.card
    · exact hcomp C hfour hyC _ hTcard hsub
    · have he : ({u,v,w} : Finset V) = C :=
        eq_of_subset_of_card_le hsub (by omega)
      rw [he]
  exact mem_filter.mpr ⟨mem_univ _,hwu,hwv,hclasses.trans hclass⟩

theorem pair_subset_inter_iff {C S I : Finset V} {u v : V}
    (hrem : ∀ w ∈ C, w ≠ u → w ≠ v → w ∈ I) :
    C ⊆ insert u (insert v S) ↔ C ⊆ insert u (insert v (S ∩ I)) := by
  constructor
  · intro h w hw
    have hm := h hw
    simp only [mem_insert] at hm ⊢
    rcases hm with hwu | hwv | hwS
    · exact Or.inl hwu
    · exact Or.inr (Or.inl hwv)
    · by_cases hwu : w = u
      · exact Or.inl hwu
      · by_cases hwv : w = v
        · exact Or.inr (Or.inl hwv)
        · exact Or.inr (Or.inr (mem_inter.mpr ⟨hwS,hrem w hw hwu hwv⟩))
  · intro h
    exact h.trans (insert_subset_insert _ (insert_subset_insert _ inter_subset_left))

theorem higherClass_uses_classVariables {y : SetFunction V} {classOf : Finset V → A}
    (hcomp : ClassCompatible y classOf) (a : A) {u v : V} (huv : u ≠ v)
    {S : Finset V} (hu : u ∉ S) (hv : v ∉ S) :
    delta (higherClass y classOf a) u v S =
      delta (higherClass y classOf a) u v (S ∩ classVariables classOf u v a) := by
  classical
  have hu' : u ∉ S ∩ classVariables classOf u v a := by simp [hu]
  have hv' : v ∉ S ∩ classVariables classOf u v a := by simp [hv]
  rw [higherClass,zeta_eq_sum_monomials,delta_sum,delta_sum]
  apply sum_congr rfl
  intro C hC
  rw [delta_smul,delta_smul,delta_setMonomial huv hu hv,delta_setMonomial huv hu' hv']
  by_cases hzero : classCoefficients y classOf a C = 0
  · simp [hzero]
  · by_cases huC : u ∈ C
    · by_cases hvC : v ∈ C
      · have hi := pair_subset_inter_iff (S := S)
          (fun w hw hwu hwv => remaining_vertex_in_classVariables hcomp hzero huv huC hvC hw hwu hwv)
        simp only [hi]
      · simp [hvC]
    · simp [huC]

theorem higherClasses_independent {y : SetFunction V} {classOf : Finset V → A}
    (hcomp : ClassCompatible y classOf) : IndependentSlacks (higherClass y classOf) := by
  apply independentSlacks_of_disjoint_variables
  intro u v huv
  refine ⟨classVariables classOf u v,classVariables_disjoint classOf u v,?_⟩
  intro a S hu hv
  exact higherClass_uses_classVariables hcomp a huv hu hv

theorem higherClass_graphical {G : SimpleGraph V} {y : SetFunction V}
    (hy : CliqueSupported G y) (classOf : Finset V → A) (a : A) :
    Graphical G (higherClass y classOf a) := by
  classical
  apply ((cliqueSupported_iff G _).mp ?_).2
  refine ⟨by simp [classCoefficients],fun v => by simp [classCoefficients],?_⟩
  intro C u v hu hv huv hnon
  have hz := hy.2.2 C u v hu hv huv hnon
  simp [classCoefficients,hz]

theorem minimumSlack_eq_zero {z : SetFunction V} {u v : V}
    (hz : ∀ S, u ∉ S → v ∉ S → delta z u v S = 0) : minimumSlack z u v = 0 := by
  obtain ⟨S,hu,hv,he⟩ := exists_minimumSlack z u v
  exact he.symm.trans (hz S hu hv)

theorem adjusted_graphical {G : SimpleGraph V} {z : SetFunction V}
    (hz : Graphical G z) : Graphical G (adjusted z) := by
  intro u v huv hnon S hu hv
  have hm := minimumSlack_eq_zero (hz u v huv hnon)
  rw [adjusted,delta_add,hz u v huv hnon S hu hv,
    zeta_pairSupported_delta _ (fun C hC => allocation_zero z hC) huv hu hv,
    allocation_pair z huv,hm]
  ring

/-- The actual triangle-class positive decomposition of the supermodular
function, before the separate connected-component construction of its class
index. The coefficients and all elemental rows are unchanged. -/
theorem compatible_class_decomposition {G : SimpleGraph V} (y : SetFunction V)
    (hy : CliqueSupported G y) (hs : Supermodular (zeta y))
    (classOf : Finset V → A) (hcomp : ClassCompatible y classOf) :
    (∀ a, TranslationNormalized (adjusted (higherClass y classOf a)) ∧
      Supermodular (adjusted (higherClass y classOf a)) ∧
      Graphical G (adjusted (higherClass y classOf a))) ∧
    (∀ C, 0 ≤ residual y (higherClass y classOf) C) ∧
    TranslationNormalized (zeta (residual y (higherClass y classOf))) ∧
    Supermodular (zeta (residual y (higherClass y classOf))) ∧
    (∑ a, adjusted (higherClass y classOf a))+
      zeta (residual y (higherClass y classOf)) = zeta y := by
  have he := higher_classes_reconstruct y classOf ⟨hy.1,hy.2.1⟩
  obtain ⟨hp,ha,hr,hn,hsr,hre⟩ := positive_block_decomposition y (zeta y)
    (higherClass y classOf) hs he (higherClass_normalized y classOf)
    (higherClass_delta_empty y classOf) (higherClasses_independent hcomp)
  exact ⟨fun a => ⟨(hp a).1,(hp a).2,
    adjusted_graphical (higherClass_graphical hy classOf a)⟩,hr,hn,hsr,hre⟩

end PositiveDecomposition
end GraphicalZonotopes
