module

public import Papers.GraphicalZonotopes.ThreeTreeLatticeDilation

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace GraphicalZonotopes
open Finset
open RefinedTriangleComponents
open scoped BigOperators Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Lattice polytopes are allowed arbitrary real translations. -/
def TranslatedLatticePolytope (Q : Set (V → ℝ)) : Prop :=
  ∃ (P : Set (V → ℝ)) (t : V → ℝ), LatticePolytope P ∧ Q=t+ᵥP

theorem lowerSupport_vadd {Q : Set (V → ℝ)} (hQ : IsCompact Q)
    (hne : Q.Nonempty) (t : V → ℝ) :
    lowerSupport (t+ᵥQ)=modular t+lowerSupport Q := by
  rw [← singleton_add_eq_vadd,lowerSupport_add isCompact_singleton hQ (Set.singleton_nonempty _) hne]
  congr 1
  funext S
  simp [lowerSupport,modular]

theorem TranslatedLatticePolytope.compact {Q : Set (V → ℝ)}
    (hQ : TranslatedLatticePolytope Q) : IsCompact Q := by
  obtain ⟨P,t,hP,rfl⟩ := hQ
  rw [← singleton_add_eq_vadd]
  exact isCompact_singleton.add hP.compact

theorem TranslatedLatticePolytope.convex {Q : Set (V → ℝ)}
    (hQ : TranslatedLatticePolytope Q) : Convex ℝ Q := by
  obtain ⟨P,t,hP,rfl⟩ := hQ
  exact hP.convex.vadd t

theorem TranslatedLatticePolytope.integer_normalize_lowerSupport {Q : Set (V → ℝ)}
    (hQ : TranslatedLatticePolytope Q) (hne : Q.Nonempty) :
    IntegerValued (normalize (lowerSupport Q)) := by
  obtain ⟨P,t,hP,rfl⟩ := hQ
  have hnP : P.Nonempty := by
    obtain ⟨x,y,hy,hxy⟩ := hne
    exact ⟨y,hy⟩
  rw [lowerSupport_vadd hP.compact hnP,normalize_add,normalize_modular,zero_add]
  exact (hP.lowerSupport_integerValued hnP).normalize

theorem threeTree_integral_normalized_four_coefficients {n : ℕ} (hn : 4≤n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : IsCompact Q) (hcQ : Convex ℝ Q)
    (hint : IntegerValued (normalize (lowerSupport Q)))
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0<a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    ∀ C∈tetrahedra G,∃ k : ℤ,k≠0 ∧ mobius (lowerSupport Q) C=k := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ hcQ hi.1 hR hcR hnR ha.le he
  let f:=lowerSupport Q
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope (normalize f)))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : normalize f≠0 := by
    intro he
    rw [he,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan, _root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular (normalize f) := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  have hnormgraph : Graphical G (normalize f) := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hall := (threeTree_all_tetrahedra_nonzero hn hG hext hnormgraph hdim).2
  have hint := hint.mobius
  intro C hC
  obtain ⟨k,hk⟩ := hint C
  have hc : C.card=4 := (mem_filter.mp hC).2.1
  rw [mobius_four_normalize hc] at hk
  refine ⟨k,?_,hk⟩
  intro hzero
  have hc : C.card=4 := (mem_filter.mp hC).2.1
  have hnonzero := hall C hC
  rw [mobius_four_normalize hc] at hnonzero
  exact hnonzero (by simpa [hzero] using hk)

theorem threeTree_integral_normalized_lower_bound {n : ℕ} (hn : 6≤n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : IsCompact Q) (hcQ : Convex ℝ Q)
    (hint : IntegerValued (normalize (lowerSupport Q)))
    (hi : MinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0<a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    2≤a ∧ (∀ C∈tetrahedra G,∃ k : ℤ,k≠0 ∧ mobius (lowerSupport Q) C=k) ∧
      ∀ e∈edgeFamily G,
        (Int.ceil ((1/2 : ℝ)*
          ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius (lowerSupport Q) C|) : ℝ)≤a := by
  classical
  have hcoeff := threeTree_integral_normalized_four_coefficients (by omega : 4≤n) hG hQ hcQ hint hi hd ha hsum
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ hcQ hi.1 hR hcR hnR ha.le he
  let f:=lowerSupport Q
  let z:=normalize f
  have hzn : TranslationNormalized z := normalize_translationNormalized hfn
  have hzs : Supermodular z := hfs.normalize
  have hzi : IntegerValued z := hint
  have hzg : Graphical G z := by
    intro u v huv hnon S hu hv
    rw [delta_normalize f huv hu hv]
    exact hgraph u v huv hnon S hu hv
  have hzy : CliqueSupported G (mobius z) := (mobius_cliqueSupported_iff G z).mpr ⟨hzn,hzg⟩
  have hzb : ∀ u v,u≠v → G.Adj u v → ∀ S,u∉S → v∉S → delta z u v S≤a := by
    intro u v huv hadj S hu hv
    rw [delta_normalize f huv hu hv]
    exact hbound u v huv hadj S hu hv
  have hedge : ∀ e∈edgeFamily G,
      (Int.ceil ((1/2 : ℝ)*
        ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C|) : ℝ)≤a := by
    intro e he
    obtain ⟨hc,hcl⟩ := (mem_edgeFamily G e).mp he
    obtain ⟨u,v,huv,rfl⟩ := card_eq_two.mp hc
    have hadj := (pair_mem_edgeFamily G huv).mp he
    have hb := threeTree_integral_slack_bound hG hzs hzi hzy hzb hadj
    have hs : (∑ C∈(tetrahedra G).filter (fun C => ({u,v} : Finset (Fin n))⊆C),
        |mobius z C|)=
        ∑ C∈(tetrahedra G).filter (fun C => ({u,v} : Finset (Fin n))⊆C),|mobius f C| := by
      apply sum_congr rfl
      intro C hC
      have hc : C.card=4 := (mem_filter.mp (mem_filter.mp hC).1).2.1
      rw [mobius_four_normalize hc]
    rwa [hs] at hb
  have hdim : Module.finrank ℝ (vectorSpan ℝ (basePolytope z))=n-1 := by
    rw [vectorSpan_basePolytope_normalize,← hbody]
    simpa only [FullDimension,Fintype.card_fin] using hd
  have hne : z≠0 := by
    intro hz
    rw [hz,basePolytope_zero] at hdim
    have hspan : vectorSpan ℝ ({0} : Set (Fin n → ℝ)) =
        (⊥ : Submodule ℝ (Fin n → ℝ)) :=
      _root_.vectorSpan_singleton ℝ (0 : Fin n → ℝ)
    rw [hspan, _root_.finrank_bot] at hdim
    omega
  have hext : ExtremeSupermodular z := by
    apply MinkowskiIndecomposable.extremeSupermodular_normalize hfn hfs hne
    rwa [← hbody]
  obtain ⟨hF,hall⟩ := threeTree_all_tetrahedra_nonzero (by omega : 4≤n) hG hext hzg hdim
  have hconn := (full_refined_support (by omega : 4≤n) hG.cliqueFree_five hext hzg hdim).2.1
  rw [hF] at hconn
  have hnum : 3≤(tetrahedra G).card := by
    have hc:=hG.tetrahedra_card
    simp only [card_univ,Fintype.card_fin] at hc
    omega
  obtain ⟨e,hecard,hemany⟩ := connected_tetrahedra_pair_multiplicity (tetrahedra G)
    (fun C hC => (mem_filter.mp hC).2.1) hconn hnum
  have heG : e∈edgeFamily G := by
    obtain ⟨C,hC⟩ := card_pos.mp (show 0<((tetrahedra G).filter (fun C => e⊆C)).card by omega)
    obtain ⟨hC,heC⟩ := mem_filter.mp hC
    have hc := (mem_filter.mp hC).2.2
    exact (mem_edgeFamily G e).mpr ⟨hecard,fun u hu v hv huv => hc (heC hu) (heC hv) huv⟩
  have hsum : (3 : ℝ)≤
      ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C| := by
    calc
      (3 : ℝ)≤(((tetrahedra G).filter (fun C => e⊆C)).card : ℝ) := by exact_mod_cast hemany
      _ = ∑ C∈(tetrahedra G).filter (fun C => e⊆C),(1 : ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro C hC
        obtain ⟨k,hk,hvalue⟩ := hcoeff C (mem_filter.mp hC).1
        rw [hvalue]
        have hpos : (0 : ℤ) < abs k := abs_pos.mpr hk
        have hone : (1 : ℤ) ≤ abs k := by omega
        exact_mod_cast hone
  have hceil : (2 : ℤ)≤Int.ceil ((1/2 : ℝ)*
      ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C|) := by
    have hh : (1 : ℤ)<Int.ceil ((1/2 : ℝ)*
        ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C|) :=
      Int.lt_ceil.mpr (by norm_num; linarith)
    omega
  have hcast : (2 : ℝ)≤(Int.ceil ((1/2 : ℝ)*
      ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius f C|) : ℝ) := by exact_mod_cast hceil
  exact ⟨hcast.trans (hedge e heG),hcoeff,hedge⟩

/-- Theorem 9.1 in the full translation-invariant range explicitly stated in
its introduction: every real translate of a lattice polytope is permitted.
All tetrahedral coefficients and every edgewise ceiling retain their literal
values on the original translated body. -/
theorem threeTree_translated_lattice_lower_bound {n : ℕ} (hn : 6≤n)
    {G : SimpleGraph (Fin n)} (hG : IsThreeTree G)
    {Q : Set (Fin n → ℝ)} (hQ : TranslatedLatticePolytope Q)
    (hi : PolytopalMinkowskiIndecomposable Q) (hd : FullDimension Q)
    {a : ℝ} (ha : 0<a) (hsum : IsMinkowskiSummand Q (a • graphicalZonotope G)) :
    2≤a ∧ (∀ C∈tetrahedra G,∃ k : ℤ,k≠0 ∧ mobius (lowerSupport Q) C=k) ∧
      ∀ e∈edgeFamily G,
        (Int.ceil ((1/2 : ℝ)*
          ∑ C∈(tetrahedra G).filter (fun C => e⊆C),|mobius (lowerSupport Q) C|) : ℝ)≤a := by
  obtain ⟨R,hR,hcR,hnR,he⟩ := hsum
  obtain ⟨hfn,hfs,hbody,hgraph,hbound⟩ := actual_summand_lowerSupport
    hQ.compact hQ.convex hi.1 hR hcR hnR ha.le he
  have hgp : IsGeneralizedPermutahedron Q := ⟨lowerSupport Q,hfn,hfs,hbody⟩
  exact threeTree_integral_normalized_lower_bound hn hG hQ.compact hQ.convex
    (hQ.integer_normalize_lowerSupport hi.1)
    ((minkowskiIndecomposable_iff_polytopal hgp).mpr hi) hd ha ⟨R,hR,hcR,hnR,he⟩

end GraphicalZonotopes
