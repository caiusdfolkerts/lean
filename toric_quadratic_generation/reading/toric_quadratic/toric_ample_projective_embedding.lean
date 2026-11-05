module

public import PaperVerification.ToricSectionChartGenerators
public import PaperVerification.ToricBaseSectionNaturality

@[expose] public section

/-!
# A finite projective embedding obtained from intrinsic ampleness

Choose finite generators in each genuine affine nonvanishing chart.
The denominator lemma extends every generator after multiplication by a
common positive power of the chart section. Those finitely many actual
global sections give all coordinate-ring quotients needed by the closed
immersion theorem.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped Classical BaseSections

attribute [local instance] MvPolynomial.gradedAlgebra

namespace BaseSections

theorem polynomial_generators_transport (k : Type u) [CommRing k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    {U V : X.Opens} (h : U=V) {ι : Type u} (g : ι→Γ(X,V))
    (hg : Function.Surjective (MvPolynomial.eval₂Hom (scalarMap k X V) g)) :
    Function.Surjective (MvPolynomial.eval₂Hom (scalarMap k X U)
      (fun j=>X.presheaf.map (eqToHom h).op (g j))) := by
  subst V
  have hid : (fun j => X.presheaf.map (eqToHom (rfl : U = U)).op (g j)) = g := by
    funext j
    change X.presheaf.map (𝟙 (op U)) (g j) = g j
    exact congrArg (fun f : Γ(X,U) ⟶ Γ(X,U) => f (g j))
      (X.presheaf.map_id (op U))
  rw [hid]
  exact hg

end BaseSections

namespace RationalCartierCocycle

variable (k : Type u) [CommRing k] {X : Scheme.{u}} [IsIntegral X]
    [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (C : RationalCartierCocycle X)

/-- The finite ratio-generation construction, before using properness.
The output sections belong to an actual positive tensor power. -/
theorem exists_power_chart_generators [CompactSpace X]
    {ι : Type u} [Fintype ι] (s : ι→Γ(C.sheaf,⊤))
    (hnonempty : ∀ i,Nonempty (C.nonvanishingOpen (s i)))
    (ha : ∀ i,IsAffineOpen (C.nonvanishingOpen (s i)))
    (hcover : (⨆ i,C.nonvanishingOpen (s i))=⊤) :
    ∃ N : ℕ,0<N ∧ ∃ (J : Type u) (_ : Fintype J)
      (t : J→Γ((C.pow N).sheaf,⊤)) (chooseChart : ι→J),
      (∀ i,t (chooseChart i)=C.sectionPow N (s i)) ∧
      (⨆ j,(C.pow N).nonvanishingOpen (t j))=⊤ ∧
      (⨆ i,(C.pow N).nonvanishingOpen (t (chooseChart i)))=⊤ ∧
      (∀ i,IsAffineOpen ((C.pow N).nonvanishingOpen (t (chooseChart i)))) ∧
      (∀ i,Function.Surjective
        ((C.pow N).sectionProjectiveChartCoordinates k t (chooseChart i))) := by
  choose G hG g hg using fun i=>BaseSections.exists_finite_polynomial_generators
    k (C.nonvanishingOpen (s i)) (ha i)
  letI (i : ι) : Fintype (G i) := hG i
  letI (i : ι) : Nonempty (C.nonvanishingOpen (s i)) := hnonempty i
  let P := (i : ι) × G i
  let r (p : P) : X.functionField :=
    X.germToFunctionField (C.nonvanishingOpen (s p.1)) (g p.1 p.2)
  have hext (p : P) : ∃ B : ℕ,0<B ∧ ∀ N : ℕ,B≤N→
      ∃ u : Γ((C.pow N).sheaf,⊤),
        (C.pow N).toCartierData.sectionValue ⊤ u=
          r p*(C.toCartierData.sectionValue ⊤ (s p.1))^N :=
    C.eventually_section_extension (s p.1) (r p)
      (regular_germ_mem_regularAt X _ (g p.1 p.2))
  choose B hB hext using hext
  let N := (∑ p : P,B p)+1
  have hN : 0<N := Nat.succ_pos _
  have hBN (p : P) : B p≤N :=
    (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ p)).trans
      (Nat.le_add_right _ 1)
  choose u hu using fun p : P=>hext p N (hBN p)
  let J := ι⊕P
  let t : J→Γ((C.pow N).sheaf,⊤) :=
    Sum.elim (fun i=>C.sectionPow N (s i)) u
  have hopen (i : ι) : (C.pow N).nonvanishingOpen (t (Sum.inl i))=
      C.nonvanishingOpen (s i) := C.nonvanishingOpen_sectionPow N hN (s i)
  have hc : (⨆ i,(C.pow N).nonvanishingOpen (t (Sum.inl i)))=⊤ := by
    simpa only [hopen] using hcover
  refine ⟨N,hN,J,inferInstance,t,Sum.inl,(fun _=>rfl),?_,hc,?_,?_⟩
  · apply top_unique
    rw [← hc]
    exact iSup_le fun i=>le_iSup_of_le (Sum.inl i) le_rfl
  · intro i
    rw [hopen]
    exact ha i
  · intro i
    let U := (C.pow N).nonvanishingOpen (t (Sum.inl i))
    letI : Nonempty U := by
      obtain ⟨x⟩ := hnonempty i
      refine ⟨⟨x.val, ?_⟩⟩
      change x.val ∈ (C.pow N).nonvanishingOpen (t (Sum.inl i))
      rw [hopen i]
      exact x.property
    let g' (j : G i) : Γ(X,U) :=
      X.presheaf.map (eqToHom (hopen i)).op (g i j)
    have hpoly : Function.Surjective
        (MvPolynomial.eval₂Hom (BaseSections.scalarMap k X U) g') :=
      BaseSections.polynomial_generators_transport k (hopen i) (g i) (hg i)
    apply (C.pow N).sectionProjectiveChartCoordinates_surjective_of_polynomial_generators
      k t (Sum.inl i) (fun j=>Sum.inr ⟨i,j⟩) g' hpoly
    intro j
    apply X.germToFunctionField_injective U
    rw [(C.pow N).ratioSection_value]
    change (C.pow N).toCartierData.sectionValue ⊤ (u ⟨i,j⟩)/
      (C.pow N).toCartierData.sectionValue ⊤ (C.sectionPow N (s i)) = _
    rw [hu,C.sectionPow_value]
    have hs : C.toCartierData.sectionValue ⊤ (s i)≠0 :=
      C.sectionValue_ne_zero_of_nonvanishing (s i)
    rw [mul_div_cancel_right₀ _ (pow_ne_zero N hs)]
    change X.germToFunctionField _ (g i j)=
      X.germToFunctionField U (X.presheaf.map (eqToHom (hopen i)).op (g i j))
    exact (germToFunctionField_restrict X (eqToHom (hopen i)) (g i j)).symm

/-- Intrinsic ampleness on a proper finite-type integral scheme yields
a genuine finite projective closed immersion. The sections are actual
sections of two positive, explicitly nested tensor powers of C. -/
theorem IsAmple.exists_finite_projective_embedding
    [IsProper (X ↘ Spec (CommRingCat.of k))] (hC : C.IsAmple) :
    ∃ a : ℕ,0<a ∧ ∃ b : ℕ,0<b ∧
      ∃ (J : Type u) (_ : Fintype J)
        (t : J→Γ(((C.pow a).pow b).sheaf,⊤)),
        ∃ hcover : (⨆ j,((C.pow a).pow b).nonvanishingOpen (t j))=⊤,
          IsClosedImmersion (((C.pow a).pow b).sectionProjectiveMap k t hcover) := by
  letI : CompactSpace X := hC.1
  obtain ⟨a,ha,ι,hι,s,hnonempty,haff,hcover⟩ :=
    hC.exists_common_power_nonempty_affine_cover
  letI : Fintype ι := hι
  obtain ⟨b,hb,J,hJ,t,chooseChart,ht,hall,hchosen,haff',hgen⟩ :=
    (C.pow a).exists_power_chart_generators k s hnonempty haff hcover
  letI : Fintype J := hJ
  exact ⟨a,ha,b,hb,J,hJ,t,hall,
    ((C.pow a).pow b).sectionProjectiveMap_isClosedImmersion_of_chartGenerators
      k t hall chooseChart hchosen haff' hgen⟩

end RationalCartierCocycle
end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.RationalCartierCocycle.IsAmple.exists_finite_projective_embedding
