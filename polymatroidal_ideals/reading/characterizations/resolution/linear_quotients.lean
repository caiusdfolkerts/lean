import Characterizations.Resolution.Cone
import Characterizations.Resolution.VariableIdeal
import Characterizations.VariableOrders

/-! # Linear quotients construct actual linear free resolutions -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [DecidableEq V] [CommRing k] [Nontrivial k]

/-- The zero module is resolved by the zero complex, for every proposed shift. -/
def zeroLinearResolution (d : ℕ) : LinearResolution (⊥ : Ideal (MvPolynomial V k)) d where
  Index _ := Empty
  finite _ := inferInstance
  differential _ := 0
  augmentation := 0
  augmentation_range := LinearMap.range_zero
  exact_zero := by simp only [LinearMap.range_zero, LinearMap.ker_zero]; exact Subsingleton.elim _ _
  exact_succ _ := by simp only [LinearMap.range_zero, LinearMap.ker_zero]; exact Subsingleton.elim _ _
  linear _ a := Empty.elim a
  augmentation_homogeneous b := Empty.elim b

private theorem exists_greatest (r : GeneratorOrder V)
    (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a)
    (C : Family V) (hC : C.Nonempty) :
    ∃ b ∈ C, ∀ a ∈ C, a = b ∨ r a b := by
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
      rcases htotal b c hbc with hbc | hcb
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
          · exact Or.inr (htrans hac hcb)
    · have he := not_nonempty_iff_eq_empty.mp hne
      subst C
      exact ⟨b, by simp, fun a ha => Or.inl (by simpa using ha)⟩

private theorem initialSegment_linearResolution (B : Family V) (d : ℕ)
    (hB : Equigenerated B d) (r : GeneratorOrder V)
    (hirr : ∀ a, ¬ r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a)
    (hL : HasLinearQuotients k B r) (C : Family V) (hCB : C ⊆ B)
    (hdown : ∀ a ∈ C, ∀ b ∈ B, r b a → b ∈ C) :
    Nonempty (LinearResolution (monomialIdeal k C) d) := by
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    by_cases hne : C.Nonempty
    · obtain ⟨b, hb, hmax⟩ := exists_greatest r htrans htotal C hne
      let D := C.erase b
      have hDB : D ⊆ B := (erase_subset _ _).trans hCB
      have hDdown : ∀ a ∈ D, ∀ c ∈ B, r c a → c ∈ D := by
        intro a ha c hc hca
        obtain ⟨hab, haC⟩ := mem_erase.mp ha
        apply mem_erase.mpr
        refine ⟨?_, hdown a haC c hc hca⟩
        intro hcb
        subst c
        rcases hmax a haC with he | habefore
        · exact hab he
        · exact hirr a (htrans habefore hca)
      obtain ⟨P⟩ := ih D (erase_ssubset hb) hDB hDdown
      have hDeq : D = preceding B r b := by
        ext a
        constructor
        · intro ha
          obtain ⟨hab, haC⟩ := mem_erase.mp ha
          exact (mem_preceding _ _ _ _).mpr ⟨hCB haC, (hmax a haC).resolve_left hab⟩
        · intro ha
          obtain ⟨haB, hab⟩ := (mem_preceding _ _ _ _).mp ha
          exact mem_erase.mpr ⟨fun he => hirr b (he ▸ hab), hdown b hb a haB hab⟩
      obtain ⟨A, hcolon⟩ := hL b (hCB hb)
      have hcol : variableIdeal (k := k) A =
          (monomialIdeal k D).colon {MvPolynomial.monomial b 1} := by
        rw [hDeq]
        exact hcolon.symm
      have hg : (MvPolynomial.monomial b (1 : k)).IsHomogeneous d :=
        MvPolynomial.isHomogeneous_monomial _ (hB b (hCB hb))
      have he : monomialIdeal k C = monomialIdeal k D ⊔ Ideal.span {MvPolynomial.monomial b (1 : k)} := by
        rw [← insert_erase hb]
        simp only [monomialIdeal, Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert]
        exact sup_comm _ _
      rw [he]
      exact ⟨P.adjoin (variableIdealLinearResolution (k := k) A)
        (MvPolynomial.monomial b 1) hg hcol⟩
    · have he : C = ∅ := not_nonempty_iff_eq_empty.mp hne
      subst C
      have he0 : monomialIdeal k (∅ : Family V) = ⊥ := by simp [monomialIdeal]
      rw [he0]
      exact ⟨zeroLinearResolution d⟩

/-- Lemma 2.1 with its conventional conclusion: an actual exact complex of finite
free modules, generated in degrees `d+i`, resolves the given ideal. -/
theorem linearResolution_of_linearQuotients (B : Family V) (d : ℕ)
    (hB : Equigenerated B d) (r : GeneratorOrder V)
    (hirr : ∀ a, ¬ r a a) (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (htotal : ∀ a b, a ≠ b → r a b ∨ r b a)
    (hL : HasLinearQuotients k B r) :
    Nonempty (LinearResolution (monomialIdeal k B) d) :=
  initialSegment_linearResolution B d hB r hirr htrans htotal hL B le_rfl
    (fun _ _ _ hb _ => hb)

theorem linearResolution_of_polymatroidal {B : Family V} (hB : IsPolymatroidal B) :
    HasLinearResolution (monomialIdeal k B) := by
  obtain ⟨d, hd⟩ := hB.1
  let o : VariableOrder V := Fintype.equivFin V
  refine ⟨d, linearResolution_of_linearQuotients B d hd (variableRevlex o)
    (variableRevlex_irrefl o) (fun h₁ h₂ => variableRevlex_trans o h₁ h₂)
    (variableRevlex_total o) ?_⟩
  exact polymatroidal_variable_linearQuotients hB.2 o

end Characterizations
