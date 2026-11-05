import Characterizations.GenerationCoverage
import Characterizations.Resolution.Betti
import Characterizations.Resolution.Localizations
import Characterizations.Strands.Restriction

/-! # Rank-maximal nonlinear localizations and the triangular range

Every Betti number used here is a component of the genuine derived Tor module.
Supported ambient degrees are identified with degrees over the polynomial ring
on the retained variables by the checked Koszul chain isomorphism.
-/

noncomputable section
set_option maxHeartbeats 900000
namespace Characterizations
open Classical CommAlg.Polymatroid CommAlg.Koszul Finset
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [Field k]

theorem localFamily_equigenerated_iff {B : Family V} {U : Finset V} {e : ℕ} :
    Equigenerated (localFamily B U) e ↔ Equigenerated (localize B U) e := by
  rw [localize_eq_extend_localFamily]
  constructor
  · intro h a ha
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    simpa only [extendExponent_degree] using h b hb
  · intro h a ha
    have hh := h (extendExponent U a) (mem_image.mpr ⟨a,ha,rfl⟩)
    simpa only [extendExponent_degree] using hh

theorem betti_localize_supported (B : Family V) (U : Finset V)
    (a : Exponent V) (ha : a.support ⊆ U) (i : ℕ) :
    bettiNumber (k := k) (localize B U) a i =
      bettiNumber (k := k) (localFamily B U) (restrictExponent U a) i := by
  have he : extendExponent U (restrictExponent U a) = a := by
    rw [extend_restrict]
    ext j
    by_cases hj : j ∈ U
    · simp [hj]
    · have hz : a j = 0 := Finsupp.notMem_support_iff.mp (fun h => hj (ha h))
      simp [hj,hz]
  rw [← he,localize_eq_extend_localFamily,Strands.betti_extension,restrict_extend]

theorem restrictExponent_degree_supported (U : Finset V) (a : Exponent V)
    (ha : a.support ⊆ U) : (restrictExponent U a).degree = a.degree := by
  rw [restrictExponent_degree,← degree_project]
  congr 1
  ext j
  by_cases hj : j ∈ U
  · simp [hj]
  · have hz : a j = 0 := Finsupp.notMem_support_iff.mp (fun h => hj (ha h))
    simp [hj,hz]

/-- Linearity through a homological position, expressed using actual Tor
components in the naturally identified supported ambient multidegrees. -/
def LocalLinearThrough (B : Family V) (U : Finset V) (e t : ℕ) : Prop :=
  ∀ a : Exponent V, a.support ⊆ U → ∀ i : ℕ, i ≤ t →
    a.degree ≠ e+i → bettiNumber (k := k) (localize B U) a i = 0

def TriangularTests (B : Family V) (d : ℕ) : Prop :=
  ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
    ∃ e, Equigenerated (localize B U) e ∧
      (0 < e → LocalLinearThrough (k := k) B U e
        (min (e-1) (min (d-1-(Fintype.card V-U.card)) (U.card-1))))

theorem localLinearThrough_of_linearResolution {B : Family V} (hB : B.Nonempty)
    (U : Finset V) {e : ℕ} (he : Equigenerated (localize B U) e)
    (hL : HasLinearResolution (monomialLocalization k (monomialIdeal k B) U))
    (t : ℕ) : LocalLinearThrough (k := k) B U e t := by
  rw [monomialLocalization_eq] at hL
  obtain ⟨f,⟨P⟩⟩ := hL
  have hf := P.equigenerated_of_monomial (localFamily B U) (localFamily_antichain B U)
  have he' := localFamily_equigenerated_iff.mpr he
  obtain ⟨b,hb⟩ := localFamily_nonempty hB U
  have hef : e = f := (he' b hb).symm.trans (hf b hb)
  subst f
  intro a ha i hi hoff
  rw [betti_localize_supported B U a ha i]
  exact P.bettiNumber_eq_zero_off_linear (localFamily B U) (localFamily_antichain B U)
    (restrictExponent U a) i (by rwa [restrictExponent_degree_supported U a ha])

theorem triangularTests_of_polymatroidal {B : Family V} (hB : IsPolymatroidal B)
    (d : ℕ) : TriangularTests (k := k) B d := by
  intro U _ _
  have hp := localize_polymatroidal hB U
  obtain ⟨e,⟨P⟩⟩ := linearResolution_of_polymatroidal (k := k) hp
  have he := P.equigenerated_of_monomial (localize B U) (localize_antichain B U)
  refine ⟨e,he,?_⟩
  intro _ a _ i _ hoff
  exact P.bettiNumber_eq_zero_off_linear (localize B U) (localize_antichain B U) a i hoff

theorem locallyEquigenerated_of_triangularTests {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (ht : TriangularTests (k := k) B d) :
    LocallyEquigenerated B :=
  locallyEquigenerated_of_band_tests hB hd (fun U hc hk =>
    let ⟨e,he,_⟩ := ht U hc hk
    ⟨e,he⟩)

/-- Enlarge a nonlinear localization without changing its generators or its
Tor component until every restored variable costs one unit of generator degree. -/
theorem maximize_low_nonlinear_localization {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hl : LocallyEquigenerated B)
    (U : Finset V) (e i : ℕ) (a : Exponent V)
    (he : Equigenerated (localize B U) e) (hr : lowerRank B U = e)
    (hc : 2 ≤ U.card) (hi : 1 ≤ i) (hie : i ≤ e-1) (hic : i ≤ U.card-1)
    (ha : a.support ⊆ U) (hdeg : e+i < a.degree)
    (hbetti : bettiNumber (k := k) (localize B U) a i ≠ 0) :
    ∃ W : Finset V, U ⊆ W ∧ lowerRank B W = e ∧
      Equigenerated (localize B W) e ∧ 2 ≤ W.card ∧ 2 ≤ e ∧
      e+(Fintype.card V-W.card) ≤ d ∧
      i ≤ min (e-1) (min (d-1-(Fintype.card V-W.card)) (W.card-1)) ∧
      a.support ⊆ W ∧ bettiNumber (k := k) (localize B W) a i ≠ 0 := by
  let candidates : Finset (Finset V) := univ.filter (fun W => U ⊆ W ∧ lowerRank B W = e)
  have hne : candidates.Nonempty := ⟨U,mem_filter.mpr ⟨mem_univ _,le_rfl,hr⟩⟩
  obtain ⟨W,hW,hmax⟩ := candidates.exists_maximal hne
  obtain ⟨hUW,hrW⟩ := (mem_filter.mp hW).2
  have hsame : localize B W = localize B U :=
    localize_eq_of_rank_eq hB hUW (hl W) (hr.trans hrW.symm)
  have hinc : ∀ j ∉ W, lowerRank B W+1 ≤ lowerRank B (insert j W) := by
    intro j hj
    have hmono := lowerRank_mono hB (subset_insert j W)
    by_contra hn
    have hreq : lowerRank B (insert j W) = e := by omega
    have hmem : insert j W ∈ candidates :=
      mem_filter.mpr ⟨mem_univ _,hUW.trans (subset_insert j W),hreq⟩
    have hsub := hmax hmem (subset_insert j W)
    exact hj (hsub (mem_insert_self j W))
  have hsm : SupermodularAbove (lowerRank B) W :=
    fun A C _ _ => lowerRank_supermodular hB hl A C
  have hcost := supermodular_rank_codimension_bound hsm hinc
  rw [hrW,lowerRank_univ_of_equigenerated hB hd] at hcost
  have hcards := card_le_card hUW
  refine ⟨W,hUW,hrW,hsame ▸ he,by omega,by omega,hcost,?_,ha.trans hUW,?_⟩
  · exact le_min hie (le_min (by omega) (by omega))
  · rwa [hsame]

theorem triangularTests_exclude_low_nonlinear {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (ht : TriangularTests (k := k) B d)
    (U : Finset V) (e i : ℕ) (a : Exponent V)
    (he : Equigenerated (localize B U) e) (hr : lowerRank B U = e)
    (hc : 2 ≤ U.card) (hi : 1 ≤ i) (hie : i ≤ e-1) (hic : i ≤ U.card-1)
    (ha : a.support ⊆ U) (hdeg : e+i < a.degree)
    (hbetti : bettiNumber (k := k) (localize B U) a i ≠ 0) : False := by
  have hl := locallyEquigenerated_of_triangularTests hB hd ht
  obtain ⟨W,hUW,hrW,heW,hcW,he2,hcost,hiW,haW,hbettiW⟩ :=
    maximize_low_nonlinear_localization hB hd hl U e i a he hr hc hi hie hic ha hdeg hbetti
  obtain ⟨f,hf,hlinear⟩ := ht W hcW (by omega)
  obtain ⟨b,hb⟩ := localize_nonempty hB W
  have hef : e = f := (heW b hb).symm.trans (hf b hb)
  subst f
  exact hbettiW (hlinear (by omega) a haW i hiW (by omega))

theorem linearBand_excludes_low_nonlinear {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d) (hl : LocallyEquigenerated B)
    (ht : ∀ W : Finset V, 2 ≤ W.card → Fintype.card V-W.card ≤ d-2 →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) W))
    (U : Finset V) (e i : ℕ) (a : Exponent V)
    (he : Equigenerated (localize B U) e) (hr : lowerRank B U = e)
    (hc : 2 ≤ U.card) (hi : 1 ≤ i) (hie : i ≤ e-1) (hic : i ≤ U.card-1)
    (ha : a.support ⊆ U) (hdeg : e+i < a.degree)
    (hbetti : bettiNumber (k := k) (localize B U) a i ≠ 0) : False := by
  obtain ⟨W,hUW,hrW,heW,hcW,he2,hcost,hiW,haW,hbettiW⟩ :=
    maximize_low_nonlinear_localization hB hd hl U e i a he hr hc hi hie hic ha hdeg hbetti
  have hL := ht W hcW (by omega)
  exact hbettiW (localLinearThrough_of_linearResolution hB W heW hL i a haW i le_rfl (by omega))

theorem locallyEquigenerated_of_linearBand {B : Family V} (hB : B.Nonempty)
    {d : ℕ} (hd : Equigenerated B d)
    (ht : ∀ U : Finset V, 2 ≤ U.card → Fintype.card V-U.card ≤ d-1 →
      HasLinearResolution (monomialLocalization k (monomialIdeal k B) U)) :
    LocallyEquigenerated B := by
  apply locallyEquigenerated_of_band_tests hB hd
  intro U hc hk
  have hL := ht U hc hk
  rw [monomialLocalization_eq] at hL
  obtain ⟨e,⟨P⟩⟩ := hL
  exact ⟨e,localFamily_equigenerated_iff.mp
    (P.equigenerated_of_monomial (localFamily B U) (localFamily_antichain B U))⟩

end Characterizations
