import CommAlg.ProjectiveDimension.KoszulBound
import CommAlg.ProjectiveDimension.IdealGeneratorExact
import CommAlg.Polymatroid.RevlexColonCardinality

/-!
# Actual projective dimension: the upper bound from linear quotients

Finite induction follows initial segments of the genuine reverse lexicographic
order. The quotient at each step is the actual quotient by its colon ideal.
-/

noncomputable section

namespace CommAlg.ProjectiveDimension

open Classical Finset CategoryTheory CategoryTheory.Limits CommAlg.Polymatroid

universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem exists_revlex_greatest (C : Family V) (hC : C.Nonempty) :
    ∃ b ∈ C, ∀ a ∈ C, a = b ∨ RevlexBefore a b := by
  induction C using Finset.induction_on with
  | empty => simp at hC
  | @insert b C hb ih =>
    by_cases hne : C.Nonempty
    · obtain ⟨c, hc, hmax⟩ := ih hne
      by_cases hbc : b = c
      · refine ⟨c, mem_insert_of_mem hc, ?_⟩
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact Or.inl hbc
        · exact hmax a ha
      rcases revlexBefore_total hbc with hbc | hcb
      · refine ⟨c, mem_insert_of_mem hc, ?_⟩
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact Or.inr hbc
        · exact hmax a ha
      · refine ⟨b, mem_insert_self _ _, ?_⟩
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact Or.inl rfl
        · rcases hmax a ha with rfl | hac
          · exact Or.inr hcb
          · exact Or.inr (revlexBefore_trans hac hcb)
    · have he := not_nonempty_iff_eq_empty.mp hne
      subst C
      exact ⟨b, by simp, fun a ha => Or.inl (by simpa using ha)⟩

theorem monomialIdeal_insert_generator (C : Family V) (b : Exponent V) :
    monomialIdeal k (insert b C) =
      CommAlg.generatorExtension (monomialIdeal k C) (MvPolynomial.monomial b 1) := by
  simp [monomialIdeal, CommAlg.generatorExtension,
    Ideal.span_insert, sup_comm]

/-- Every initial segment has projective dimension bounded by the final
partition-rank gap. The proof uses actual short exact module sequences. -/
theorem initialSegment_projectiveDimension_le (g : RankFunction V) (C : Family V)
    (hCB : C ⊆ rankBases g)
    (hdown : ∀ a ∈ C, ∀ b ∈ rankBases g, RevlexBefore b a → b ∈ C) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) (monomialIdeal k C)) ≤
      shiftLength g := by
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    by_cases hne : C.Nonempty
    · obtain ⟨b, hb, hmax⟩ := exists_revlex_greatest C hne
      let D := C.erase b
      have hDC : D ⊂ C := erase_ssubset hb
      have hDB : D ⊆ rankBases g := (erase_subset _ _).trans hCB
      have hDdown : ∀ a ∈ D, ∀ c ∈ rankBases g, RevlexBefore c a → c ∈ D := by
        intro a ha c hc hca
        obtain ⟨hab, haC⟩ := mem_erase.mp ha
        apply mem_erase.mpr
        refine ⟨?_, hdown a haC c hc hca⟩
        intro hcb
        subst c
        rcases hmax a haC with he | habefore
        · exact hab he
        · exact revlexBefore_asymm habefore hca
      have hDpd := ih D hDC hDB hDdown
      have hDeq : D = revlexBeforeFamily (rankBases g) b := by
        ext a
        constructor
        · intro ha
          obtain ⟨hab, haC⟩ := mem_erase.mp ha
          refine (mem_revlexBeforeFamily _ _ _).mpr ⟨hCB haC, ?_⟩
          exact (hmax a haC).resolve_left hab
        · intro ha
          obtain ⟨haB, hab⟩ := (mem_revlexBeforeFamily _ _ _).mp ha
          apply mem_erase.mpr
          refine ⟨?_, hdown b hb a haB hab⟩
          intro he
          subst a
          exact revlexBefore_irrefl b hab
      have hcolon : (monomialIdeal k D).colon {MvPolynomial.monomial b 1} =
          variableIdeal (k := k) (revlexColonVariables (rankBases g) b) := by
        rw [hDeq]
        exact rankBases_revlex_colon_eq g (hCB hb)
      have hquot : projectiveDimension
          (ModuleCat.of (MvPolynomial V k)
            (MvPolynomial V k ⧸ (monomialIdeal k D).colon {MvPolynomial.monomial b 1})) ≤
          shiftLength g := by
        rw [hcolon]
        exact (variableIdeal_quotient_le _).trans
          (by exact_mod_cast revlexColonVariables_card_le_shiftLength g (hCB hb))
      have he : monomialIdeal k C =
          CommAlg.generatorExtension (monomialIdeal k D) (MvPolynomial.monomial b 1) := by
        have hIns : insert b D = C := insert_erase hb
        calc
          monomialIdeal k C = monomialIdeal k (insert b D) :=
            congrArg (monomialIdeal k) hIns.symm
          _ = _ := monomialIdeal_insert_generator D b
      rw [he]
      exact (CommAlg.generatorExtension_projectiveDimension_le _ _).trans (sup_le hDpd hquot)
    · have he : C = ∅ := not_nonempty_iff_eq_empty.mp hne
      subst C
      have he0 : monomialIdeal k (∅ : Family V) = ⊥ := by simp [monomialIdeal]
      haveI : Subsingleton (monomialIdeal k (∅ : Family V)) := by
        rw [he0]
        infer_instance
      have hz : IsZero (ModuleCat.of (MvPolynomial V k) (monomialIdeal k (∅ : Family V))) :=
        ModuleCat.isZero_iff_subsingleton.mpr inferInstance
      rw [(projectiveDimension_eq_bot_iff _).mpr hz]
      exact bot_le

/-- The actual Ext-defined projective dimension of every polymatroid rank
ideal is at most the universal partition-rank gap, including loops and rank zero. -/
theorem rankIdeal_projectiveDimension_le (g : RankFunction V) :
    projectiveDimension (ModuleCat.of (MvPolynomial V k) (rankIdeal k g)) ≤
      shiftLength g :=
  initialSegment_projectiveDimension_le g (rankBases g) le_rfl
    (fun _ _ _ hb _ => hb)

end CommAlg.ProjectiveDimension
