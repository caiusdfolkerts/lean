import Characterizations.Resolution.Descent
import Characterizations.Resolution.LocalizationDescent
import Characterizations.TriangleCore
import Characterizations.Isolators.Coverage
import Characterizations.SmallCases

/-! # The full degree cost of a maximal obstruction (Lemma 4.4)

Linearity is the existence of an actual exact finite-free linear resolution.
Polynomial-extension descent is established by coefficient specialization.
-/
noncomputable section
namespace Characterizations
open Classical Finset CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem nonlinear_localization_rank_pos {B : Family V} (hB : B.Nonempty)
    (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) :
    1 ≤ lowerRank B U := by
  by_contra hn
  have he := localize_equigenerated_of_rank_zero hB U (by omega)
  have hf := localFamily_equigenerated_iff.mpr he
  apply hbad
  rw [monomialLocalization_eq]
  exact linearResolution_of_polymatroidal
    (equigenerated_polymatroidal_of_degree_le_one hf (by omega))

theorem nonlinear_equigenerated_localization_rank_ge_two {B : Family V} (hB : B.Nonempty)
    (U : Finset V) (he : ∃ e, Equigenerated (localize B U) e)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) :
    2 ≤ lowerRank B U := by
  by_contra hn
  obtain ⟨e,he⟩ := he
  obtain ⟨a,ha⟩ := localize_nonempty hB U
  have hr : e = lowerRank B U :=
    (he a ha).symm.trans (equigenerated_localize_degree hB he ha)
  have hf := localFamily_equigenerated_iff.mpr he
  apply hbad
  rw [monomialLocalization_eq]
  exact linearResolution_of_polymatroidal
    (equigenerated_polymatroidal_of_degree_le_one hf (by omega))

/-- Lemma 4.4 for an inclusion-maximal localization lacking a genuine linear
free resolution. No prior equigeneration of all localizations is assumed. -/
theorem maximal_nonlinear_rank_cost {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hmax : ∀ W, U ⊂ W →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) W)) :
    2 ≤ U.card ∧ 1 ≤ lowerRank B U ∧
      lowerRank B U + (Fintype.card V-U.card) ≤ d := by
  have hcard : 2 ≤ U.card := by
    by_contra h
    exact hbad (Isolators.local_linearResolution_of_card_le_one hB U (by omega))
  have hequi : ∀ W, U ⊂ W → ∃ e, Equigenerated (localize B W) e := by
    intro W hW
    have hL := hmax W hW
    rw [monomialLocalization_eq] at hL
    obtain ⟨e,⟨P⟩⟩ := hL
    exact ⟨e,localFamily_equigenerated_iff.mp
      (P.equigenerated_of_monomial (localFamily B W) (localFamily_antichain B W))⟩
  have hinc : ∀ i ∉ U, lowerRank B U+1 ≤ lowerRank B (insert i U) := by
    intro i hi
    have hsub : U ⊂ insert i U := Finset.ssubset_insert hi
    have hm := lowerRank_mono hB (Finset.subset_insert i U)
    by_contra hn
    have hr : lowerRank B U = lowerRank B (insert i U) := by omega
    have hf := localize_eq_of_rank_eq hB (Finset.subset_insert i U) (hequi _ hsub) hr
    exact hbad (local_linearResolution_of_insert_family_eq B U i hi hf (hmax _ hsub))
  have hbound := supermodular_rank_codimension_bound
    (lowerRank_supermodular_above hB U hequi) hinc
  rw [lowerRank_univ_of_equigenerated hB hd] at hbound
  exact ⟨hcard,nonlinear_localization_rank_pos hB U hbad,hbound⟩

/-- Both alternatives in the literal statement of Lemma 4.4. -/
theorem maximal_obstruction_degree_cost {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (U : Finset V)
    (hmax :
      ((¬ ∃ e, Equigenerated (localize B U) e) ∧
        ∀ W, U ⊂ W → ∃ e, Equigenerated (localize B W) e) ∨
      ((¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) ∧
        ∀ W, U ⊂ W → HasLinearResolution (monomialLocalization k (monomialIdeal k B) W))) :
    2 ≤ U.card ∧ 1 ≤ lowerRank B U ∧
      lowerRank B U + (Fintype.card V-U.card) ≤ d := by
  rcases hmax with ⟨hbad,hm⟩ | ⟨hbad,hm⟩
  · exact maximal_nonequigenerated_rank_cost hB hd U hbad hm
  · exact maximal_nonlinear_rank_cost hB hd U hbad hm

/-- The final assertion of Lemma 4.4 under prior local equigeneration. -/
theorem maximal_pure_nonlinear_rank_cost {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hl : LocallyEquigenerated B) (U : Finset V)
    (hbad : ¬ HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (hmax : ∀ W, U ⊂ W → HasLinearResolution (monomialLocalization k (monomialIdeal k B) W)) :
    2 ≤ U.card ∧ 2 ≤ lowerRank B U ∧
      lowerRank B U + (Fintype.card V-U.card) ≤ d := by
  obtain ⟨hc,_,hdim⟩ := maximal_nonlinear_rank_cost hB hd U hbad hmax
  exact ⟨hc,nonlinear_equigenerated_localization_rank_ge_two hB U (hl U) hbad,hdim⟩

end Characterizations
