module

public import PaperVerification.AlternatingFormsFiniteExteriorKoszul
public import PaperVerification.AlternatingFormsThreeNormalForm
public import PaperVerification.AlternatingFormsFourNormalForm
public import PaperVerification.AlternatingFormsExteriorStraightening
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The actual exterior quotient Koszul direction in small dimensions

The small finite-set checks below establish only which monomials survive
in dimensions at most four. The homological conclusion has unbounded
homological and internal degrees and follows from the proved actual
word-bar resolution and filtered exactness theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.SmallExteriorKoszul

open PaperVerification ExteriorMonomialQuotient ExteriorMonomialKoszul ExteriorKoszul

universe u
variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]

/-- In dimension two the single exterior pair is killed. -/
def forbiddenTwo : Set (Finset (Fin 2)) := {{0,1}}

/-- The canonical independent pair in dimension three. -/
def forbiddenThree : Set (Finset (Fin 3)) := {{0,1},{1,2}}

/-- The two complementary decomposable forms in dimension four. -/
def forbiddenFour : Set (Finset (Fin 4)) := {{0,1},{2,3}}

def relationEmpty (I : Type*) : I→I→Prop := fun _ _ => False

def relationThree (i j : Fin 3) : Prop := i=0 ∧ j=2

def relationFour (i j : Fin 4) : Prop := i.val<2 ∧ 2≤j.val

instance emptyTransitive (I : Type*) : IsTrans I (relationEmpty I) where
  trans _ _ _ h _ := h.elim

instance threeTransitive : IsTrans (Fin 3) relationThree where
  trans a b c hab hbc := by
    have hb : (2 : Fin 3)=0 := hab.2.symm.trans hbc.1
    contradiction

instance fourTransitive : IsTrans (Fin 4) relationFour where
  trans a b c hab hbc := by
    exact False.elim (Nat.not_lt_of_ge hab.2 hbc.1)

theorem empty_increasing (I : Type*) [LinearOrder I] :
    ∀ i j,relationEmpty I i j→i<j := fun _ _ h => h.elim

theorem three_increasing : ∀ i j,relationThree i j→i<j := by
  rintro i j ⟨rfl,rfl⟩
  decide

theorem four_increasing : ∀ i j,relationFour i j→i<j := by
  intro i j h
  change i.val<j.val
  exact Nat.lt_of_lt_of_le h.1 h.2

theorem two_nonempty : ∀ S∈forbiddenTwo,S.Nonempty := by
  simp [forbiddenTwo]

theorem three_nonempty : ∀ S∈forbiddenThree,S.Nonempty := by
  simp [forbiddenThree]

theorem four_nonempty : ∀ S∈forbiddenFour,S.Nonempty := by
  simp [forbiddenFour]

private theorem pairwise_iff_on_sorted {I : Type*} [LinearOrder I]
    (R : I→I→Prop) (l : List I) (hs : l.Pairwise (· < ·)) :
    l.Pairwise R ↔ ∀ i∈l,∀ j∈l,i<j→R i j := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.pairwise_cons] at hs ⊢
    constructor
    · rintro ⟨ha,hl⟩ i hi j hj hij
      rcases List.mem_cons.mp hi with hia | hil
      · subst i
        rcases List.mem_cons.mp hj with hja | hjl
        · subst j
          exact (lt_irrefl _ hij).elim
        · exact ha j hjl
      · rcases List.mem_cons.mp hj with hja | hjl
        · subst j
          exact (lt_asymm (hs.1 i hil) hij).elim
        · exact (ih hs.2).mp hl i hil j hjl hij
    · intro h
      refine ⟨?_,(ih hs.2).mpr ?_⟩
      · intro j hj
        exact h a (by simp) j (List.mem_cons_of_mem _ hj) (hs.1 j hj)
      · intro i hi j hj hij
        exact h i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj) hij

private theorem sort_chain_iff {I : Type*} [LinearOrder I]
    (R : I→I→Prop) [IsTrans I R] (S : Finset I) :
    S.sort.IsChain R ↔ ∀ i∈S,∀ j∈S,i<j→R i j := by
  rw [List.isChain_iff_pairwise,pairwise_iff_on_sorted R _ (Finset.sortedLT_sort S).pairwise]
  simp only [Finset.mem_sort]

theorem zero_words : ∀ S : Finset (Fin 0),
    ¬Bad (∅ : Set (Finset (Fin 0))) S↔S.sort.IsChain (relationEmpty (Fin 0)) := by
  intro S
  rw [sort_chain_iff]
  simp [Bad,Fin.forall_fin_succ]

theorem one_words : ∀ S : Finset (Fin 1),
    ¬Bad (∅ : Set (Finset (Fin 1))) S↔S.sort.IsChain (relationEmpty (Fin 1)) := by
  intro S
  rw [sort_chain_iff]
  simp [Bad,Fin.forall_fin_succ]

theorem two_words : ∀ S : Finset (Fin 2),
    ¬Bad forbiddenTwo S↔S.sort.IsChain (relationEmpty (Fin 2)) := by
  intro S
  rw [sort_chain_iff]
  simp [Bad,forbiddenTwo,relationEmpty,Fin.forall_fin_succ,
    Finset.insert_subset_iff,Finset.singleton_subset_iff] <;> tauto

theorem three_words : ∀ S : Finset (Fin 3),
    ¬Bad forbiddenThree S↔S.sort.IsChain relationThree := by
  intro S
  rw [sort_chain_iff]
  simp [Bad,forbiddenThree,relationThree,Fin.forall_fin_succ,
    Finset.insert_subset_iff,Finset.singleton_subset_iff] <;> tauto

theorem four_words : ∀ S : Finset (Fin 4),
    ¬Bad forbiddenFour S↔S.sort.IsChain relationFour := by
  intro S
  rw [sort_chain_iff]
  simp [Bad,forbiddenFour,relationFour,Fin.forall_fin_succ,
    Finset.insert_subset_iff,Finset.singleton_subset_iff] <;> tauto

theorem empty_monomial_ideal {I : Type*} [LinearOrder I] (b : Module.Basis I K M) :
    monomialIdeal b ∅=exteriorRelationIdeal (0 : ⋀[K]^2 M) 0 := by
  simp [monomialIdeal,exteriorRelationIdeal]

theorem two_monomial_ideal (b : Module.Basis (Fin 2) K M) :
    monomialIdeal b forbiddenTwo=exteriorRelationIdeal (exteriorPair (b 0) (b 1)) 0 := by
  simp only [monomialIdeal,forbiddenTwo,Set.image_singleton,exteriorRelationIdeal,
    exteriorPair_coe,TauCeti.ExteriorAlgebra.basis_pair b (by decide : (0 : Fin 2)<1),
    ZeroMemClass.coe_zero]
  simp

theorem three_monomial_ideal (b : Module.Basis (Fin 3) K M) :
    monomialIdeal b forbiddenThree=
      exteriorRelationIdeal (exteriorPair (b 0) (b 1)) (exteriorPair (b 1) (b 2)) := by
  simp only [monomialIdeal,forbiddenThree,Set.image_insert_eq,Set.image_singleton,
    exteriorRelationIdeal,exteriorPair_coe,
    TauCeti.ExteriorAlgebra.basis_pair b (by decide : (0 : Fin 3)<1),
    TauCeti.ExteriorAlgebra.basis_pair b (by decide : (1 : Fin 3)<2)]

theorem four_monomial_ideal (b : Module.Basis (Fin 4) K M) :
    monomialIdeal b forbiddenFour=
      exteriorRelationIdeal (exteriorPair (b 0) (b 1)) (exteriorPair (b 2) (b 3)) := by
  simp only [monomialIdeal,forbiddenFour,Set.image_insert_eq,Set.image_singleton,
    exteriorRelationIdeal,exteriorPair_coe,
    TauCeti.ExteriorAlgebra.basis_pair b (by decide : (0 : Fin 4)<1),
    TauCeti.ExteriorAlgebra.basis_pair b (by decide : (2 : Fin 4)<3)]

def zero_normal_form (b : Module.Basis (Fin 0) K M) :
    HomogeneousKoszulCertificate (K := K) (0 : ⋀[K]^2 M) 0 :=
  certificateOfFiniteMonomialIdeal b ∅ (by simp) (relationEmpty (Fin 0))
    (empty_increasing (Fin 0)) zero_words 0 0 (empty_monomial_ideal b)

def one_normal_form (b : Module.Basis (Fin 1) K M) :
    HomogeneousKoszulCertificate (K := K) (0 : ⋀[K]^2 M) 0 :=
  certificateOfFiniteMonomialIdeal b ∅ (by simp) (relationEmpty (Fin 1))
    (empty_increasing (Fin 1)) one_words 0 0 (empty_monomial_ideal b)

def two_normal_form (b : Module.Basis (Fin 2) K M) :
    HomogeneousKoszulCertificate (K := K) (exteriorPair (b 0) (b 1)) (0 : ⋀[K]^2 M) :=
  certificateOfFiniteMonomialIdeal b forbiddenTwo two_nonempty (relationEmpty (Fin 2))
    (empty_increasing (Fin 2)) two_words _ _ (two_monomial_ideal b)

def three_normal_form (b : Module.Basis (Fin 3) K M) :
    HomogeneousKoszulCertificate (K := K) (exteriorPair (b 0) (b 1)) (exteriorPair (b 1) (b 2)) :=
  certificateOfFiniteMonomialIdeal b forbiddenThree three_nonempty relationThree
    three_increasing three_words _ _ (three_monomial_ideal b)

def four_normal_form (b : Module.Basis (Fin 4) K M) :
    HomogeneousKoszulCertificate (K := K) (exteriorPair (b 0) (b 1)) (exteriorPair (b 2) (b 3)) :=
  certificateOfFiniteMonomialIdeal b forbiddenFour four_nonempty relationFour
    four_increasing four_words _ _ (four_monomial_ideal b)

variable [FiniteDimensional K M]

/-- All two-forms vanish below dimension two; no genericity restriction is
needed for either of these boundary algebras. -/
theorem dimension_le_one (hdim : Module.finrank K M≤1) (f g : ⋀[K]^2 M) :
    Nonempty (HomogeneousKoszulCertificate f g) := by
  have hz : Module.finrank K (⋀[K]^2 M)=0 := by
    rw [exteriorPower.finrank_eq]
    exact Nat.choose_eq_zero_of_lt (by omega)
  letI : Subsingleton (⋀[K]^2 M) := (Module.finrank_zero_iff).mp hz
  have hf : f=0 := Subsingleton.elim _ _
  have hg : g=0 := Subsingleton.elim _ _
  subst f
  subst g
  rcases Nat.eq_zero_or_pos (Module.finrank K M) with h0 | h1
  · exact ⟨zero_normal_form (Module.finBasisOfFinrankEq K M h0)⟩
  · have h1' : Module.finrank K M=1 := by omega
    exact ⟨one_normal_form (Module.finBasisOfFinrankEq K M h1')⟩

/-- Every pair in dimension two with nonzero first form has the same
actual relation ideal as the single top exterior monomial. -/
theorem dimension_two (hdim : Module.finrank K M=2) (f g : ⋀[K]^2 M) (hf : f≠0) :
    Nonempty (HomogeneousKoszulCertificate f g) := by
  let b := Module.finBasisOfFinrankEq K M hdim
  let q : ⋀[K]^2 M := exteriorPair (b 0) (b 1)
  have hq : q≠0 := by
    apply (exteriorPower.ιMulti_ne_zero_iff ![b 0,b 1]).mpr
    convert b.linearIndependent using 1
    funext i
    fin_cases i <;> rfl
  have hdim2 : Module.finrank K (⋀[K]^2 M)=1 := by
    rw [exteriorPower.finrank_eq,hdim]
    decide
  have hfspan : Submodule.span K ({f} : Set (⋀[K]^2 M))=⊤ :=
    (finrank_eq_one_iff_of_nonzero f hf).mp hdim2
  have hqspan : Submodule.span K ({q} : Set (⋀[K]^2 M))=⊤ :=
    (finrank_eq_one_iff_of_nonzero q hq).mp hdim2
  have hpair (x y : ⋀[K]^2 M) (hx : Submodule.span K ({x} : Set (⋀[K]^2 M))=⊤) :
      Submodule.span K ({x,y} : Set (⋀[K]^2 M))=⊤ := by
    apply top_unique
    rw [←hx]
    exact Submodule.span_mono (by intro a ha; exact Or.inl (Set.mem_singleton_iff.mp ha))
  have hs : Submodule.span K ({f,g} : Set (⋀[K]^2 M))=
      Submodule.span K ({q,0} : Set (⋀[K]^2 M)) :=
    (hpair f g hfspan).trans (hpair q 0 hqspan).symm
  have he : monomialIdeal b forbiddenTwo=exteriorRelationIdeal f g :=
    (two_monomial_ideal b).trans
      (exteriorRelationIdeal_eq_of_quadraticSpan_eq f g q 0 hs).symm
  exact ⟨certificateOfFiniteMonomialIdeal b forbiddenTwo two_nonempty (relationEmpty (Fin 2))
    (empty_increasing (Fin 2)) two_words f g he⟩

/-- The nonzero first coordinate is a genuine nonempty principal open
in the full two-dimensional coefficient space of a pair of two-forms. -/
theorem dimension_two_generic (hdim : Module.finrank K M=2) :
    ∃ b₂ : Module.Basis (Fin 1) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (Fin 1 ⊕ Fin 1) K,Q≠0 ∧
        (∃ y,MvPolynomial.eval y Q≠0) ∧
        ∀ y,MvPolynomial.eval y Q≠0 →
          Nonempty (HomogeneousKoszulCertificate
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) := by
  have hd : Module.finrank K (⋀[K]^2 M)=1 := by
    rw [exteriorPower.finrank_eq,hdim]
    decide
  let b₂ := Module.finBasisOfFinrankEq K (⋀[K]^2 M) hd
  let Q : MvPolynomial (Fin 1 ⊕ Fin 1) K := MvPolynomial.X (.inl 0)
  refine ⟨b₂,Q,MvPolynomial.X_ne_zero _,?_,?_⟩
  · refine ⟨fun _ => 1,?_⟩
    simpa only [Q,MvPolynomial.eval_X] using (one_ne_zero : (1 : K)≠0)
  · intro y hy
    have hy0 : y (.inl 0)≠0 := by simpa only [Q,MvPolynomial.eval_X] using hy
    apply dimension_two hdim
    have hf : (orbitFormsFromCoordinates b₂ y).1=y (.inl 0) • b₂ 0 := by
      simp [orbitFormsFromCoordinates]
    rw [hf]
    exact smul_ne_zero hy0 (b₂.ne_zero 0)

/-- The complete generic positive result in dimension three, on an
explicit nonempty principal open in the full space of pairs. -/
theorem dimension_three (hdim : Module.finrank K M=3) :
    ∃ b₂ : Module.Basis (Fin 3) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (Fin 3 ⊕ Fin 3) K,Q≠0 ∧
        (∃ y,MvPolynomial.eval y Q≠0) ∧
        ∀ y,MvPolynomial.eval y Q≠0 →
          Nonempty (HomogeneousKoszulCertificate
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) := by
  obtain ⟨b₂,Q,hQ,hpoint,h⟩ := ThreeNormalForm.generic_normal_form (K := K) (M := M) hdim
  refine ⟨b₂,Q,hQ,hpoint,?_⟩
  intro y hy
  obtain ⟨b,hb⟩ := h y hy
  have he : monomialIdeal b forbiddenThree=
      exteriorRelationIdeal (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 :=
    (three_monomial_ideal b).trans
      (exteriorRelationIdeal_eq_of_quadraticSpan_eq _ _ _ _ hb).symm
  exact ⟨certificateOfFiniteMonomialIdeal b forbiddenThree three_nonempty relationThree
    three_increasing three_words _ _ he⟩

/-- The complete generic positive result in dimension four. Algebraic
closure is faithful to the paper's coefficient field ℂ. -/
theorem dimension_four [CharZero K] [IsAlgClosed K]
    (hdim : Module.finrank K M=4) :
    ∃ b₂ : Module.Basis (Fin 6) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (Fin 6 ⊕ Fin 6) K,Q≠0 ∧
        (∃ y,MvPolynomial.eval y Q≠0) ∧
        ∀ y,MvPolynomial.eval y Q≠0 →
          Nonempty (HomogeneousKoszulCertificate
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) := by
  obtain ⟨b₂,Q,hQ,hpoint,h⟩ := FourNormalForm.generic_normal_form (K := K) (M := M) hdim
  refine ⟨b₂,Q,hQ,hpoint,?_⟩
  intro y hy
  obtain ⟨b,hb⟩ := h y hy
  have he : monomialIdeal b forbiddenFour=
      exteriorRelationIdeal (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2 :=
    (four_monomial_ideal b).trans
      (exteriorRelationIdeal_eq_of_quadraticSpan_eq _ _ _ _ hb).symm
  exact ⟨certificateOfFiniteMonomialIdeal b forbiddenFour four_nonempty relationFour
    four_increasing four_words _ _ he⟩

/-- The full positive direction of Proposition 5.3: every dimension at
most four, an actual basis of all quadratic forms, a nonempty principal
open in the complete pair space, and genuine ordinary-Tor concentration
in the original exterior grading at every point of that open. -/
theorem paper_proposition_5_3_koszul_small [CharZero K] [IsAlgClosed K]
    (hdim : Module.finrank K M≤4) :
    ∃ m : ℕ,∃ b₂ : Module.Basis (Fin m) K (⋀[K]^2 M),
      ∃ Q : MvPolynomial (Fin m ⊕ Fin m) K,Q≠0 ∧
        (∃ y,MvPolynomial.eval y Q≠0) ∧
        ∀ y,MvPolynomial.eval y Q≠0 →
          Nonempty (HomogeneousKoszulCertificate
            (orbitFormsFromCoordinates b₂ y).1 (orbitFormsFromCoordinates b₂ y).2) := by
  by_cases h1 : Module.finrank K M≤1
  · have hd : Module.finrank K (⋀[K]^2 M)=0 := by
      rw [exteriorPower.finrank_eq]
      exact Nat.choose_eq_zero_of_lt (by omega)
    let b₂ := Module.finBasisOfFinrankEq K (⋀[K]^2 M) hd
    refine ⟨0,b₂,1,one_ne_zero,?_,?_⟩
    · refine ⟨fun _ => 0,?_⟩
      rw [map_one]
      exact one_ne_zero
    · intro y hy
      exact dimension_le_one h1 _ _
  · by_cases h2 : Module.finrank K M=2
    · obtain ⟨b₂,Q,hQ,hpoint,h⟩ := dimension_two_generic (K := K) (M := M) h2
      exact ⟨1,b₂,Q,hQ,hpoint,h⟩
    · by_cases h3 : Module.finrank K M=3
      · obtain ⟨b₂,Q,hQ,hpoint,h⟩ := dimension_three (K := K) (M := M) h3
        exact ⟨3,b₂,Q,hQ,hpoint,h⟩
      · have h4 : Module.finrank K M=4 := by omega
        obtain ⟨b₂,Q,hQ,hpoint,h⟩ := dimension_four (K := K) (M := M) h4
        exact ⟨6,b₂,Q,hQ,hpoint,h⟩

end PaperVerification.AlternatingForms.SmallExteriorKoszul
