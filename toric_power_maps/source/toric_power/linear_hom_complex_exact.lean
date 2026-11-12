module

public import ToricPower.LinearHomComplexFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Exactness of the actual Hom complex from termwise projectives

Each signed Hom degree is the full product of its actual component Hom
modules. Projective lifting is performed independently at every component;
no finite-dimensionality, boundedness, or finite-support replacement is used.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex

namespace ToricPower

universe u v r
variable (R : Type r) [CommRing R]
  {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]
  (K : CochainComplex A ℤ)

instance linearHomComplexFunctor_additive : (linearHomComplexFunctor R K).Additive where
  map_add := by
    intros X Y f g
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    rw [HomologicalComplex.add_f_apply,ModuleCat.hom_add]
    change homCochainPostcomp R K (f+g) n =
      homCochainPostcomp R K f n + homCochainPostcomp R K g n
    apply LinearMap.ext
    intro z
    change z.comp (Cochain.ofHom (f+g)) (add_zero n) =
      z.comp (Cochain.ofHom f) (add_zero n) + z.comp (Cochain.ofHom g) (add_zero n)
    rw [Cochain.ofHom_add,Cochain.comp_add]

variable [∀ i, Projective (K.X i)]

/-- A literal short exact sequence of complete coefficient complexes
remains short exact after the signed Hom-complex construction. -/
theorem linearHomComplex_map_shortExact
    (S : ShortComplex (CochainComplex A ℤ)) (hS : S.ShortExact) :
    (S.map (linearHomComplexFunctor R K)).ShortExact := by
  have hs (q : ℤ) :
      (S.map (HomologicalComplex.eval A (.up ℤ) q)).ShortExact :=
    hS.map_of_exact _
  haveI (q : ℤ) : Mono (S.f.f q) := (hs q).mono_f
  haveI (q : ℤ) : Epi (S.g.f q) := (hs q).epi_g
  haveI (q : ℤ) : Mono (S.map (HomologicalComplex.eval A (.up ℤ) q)).f := (hs q).mono_f
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine {
    exact := ?_
    mono_f := ?_
    epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro z hz
    change homCochainPostcomp R K S.g n z = 0 at hz
    have closed (p q : ℤ) (hpq : p+n=q) : z.v p q hpq ≫ S.g.f q = 0 := by
      simpa only [homCochainPostcomp_v,Cochain.zero_v] using Cochain.congr_v hz p q hpq
    refine ⟨Cochain.mk (fun p q hpq =>
      (hs q).exact.lift (z.v p q hpq) (closed p q hpq)),?_⟩
    change homCochainPostcomp R K S.f n (Cochain.mk (fun p q hpq =>
      (hs q).exact.lift (z.v p q hpq) (closed p q hpq))) = z
    apply Cochain.ext
    intro p q hpq
    rw [homCochainPostcomp_v,Cochain.mk_v]
    exact (hs q).exact.lift_f _ _
  · rw [ModuleCat.mono_iff_injective]
    intro a b h
    change homCochainPostcomp R K S.f n a = homCochainPostcomp R K S.f n b at h
    apply Cochain.ext
    intro p q hpq
    apply (cancel_mono (S.f.f q)).mp
    simpa only [homCochainPostcomp_v] using Cochain.congr_v h p q hpq
  · rw [ModuleCat.epi_iff_surjective]
    intro z
    refine ⟨Cochain.mk (fun p q hpq => Projective.factorThru (z.v p q hpq) (S.g.f q)),?_⟩
    change homCochainPostcomp R K S.g n
      (Cochain.mk (fun p q hpq => Projective.factorThru (z.v p q hpq) (S.g.f q))) = z
    apply Cochain.ext
    intro p q hpq
    rw [homCochainPostcomp_v,Cochain.mk_v]
    exact Projective.factorThru_comp _ _

end ToricPower

end
