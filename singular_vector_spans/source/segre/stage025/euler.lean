module
import all Mathlib.AlgebraicGeometry.Modules.Sheaf
import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.Algebra.MonoidAlgebra.Defs
public import SegreVerified.Stage001
public import SegreVerified.Stage002
public import SegreVerified.Stage003
public import SegreVerified.Stage004
public import SegreVerified.Stage005
public import SegreVerified.Stage006
public import SegreVerified.Stage007
public import SegreVerified.Stage008
public import SegreVerified.Stage009
public import SegreVerified.Stage010
public import SegreVerified.Stage011
public import SegreVerified.Stage012
public import SegreVerified.Stage013
public import SegreVerified.Stage014
public import SegreVerified.Stage015
public import SegreVerified.Stage016
public import SegreVerified.Stage017
public import SegreVerified.Stage018
public import SegreVerified.Stage019
public import SegreVerified.Stage020
public import SegreVerified.Stage021
public import SegreVerified.Stage022
public import SegreVerified.Stage023
public import SegreVerified.Stage024

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Tactic.Push
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Sym.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.Data.Sym.NatCard
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Fin.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Order.Sym2
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Nat.Find
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.TwoSquare
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Order.Fin.Tuple
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.KrullDimension
public import Mathlib.Order.KrullDimension
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Algebra.Ring.Subgroup
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Regular.LinearMap
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Artinian.Algebra
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.Function.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.Logic.Equiv.Option
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Tactic.Abel
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Data.Finset.Interval
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Lean.Util.CollectAxioms
import all Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import Lean.Util.Sorry
public import Lean.Elab.Command
public import Lean.PrettyPrinter

public import SegreVerified.Stage025.ProjectiveCech
public import SegreVerified.Stage025.ProjectiveSections

set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section ProbeLayer391



/-!
# Singular-vector geometry and all-format spanning theorems

The named sections preserve the original proof stages and local scopes.
-/

@[expose] public section

-- Emit compilation progress immediately while checking this large unit.
set_option stderrAsMessages false
-- Style linting is separate from elaboration, kernel checking, and the axiom audit.
set_option linter.all false
noncomputable section
set_option autoImplicit false


section SegreProjectiveCohomology

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE SegreProjectiveCohomology"
  out.flush

/-!
# Projective exterior cohomology and the full Koszul gap

The named sections preserve the original proof stages and local scopes.
-/


section SegreEulerSheaf

/-!
# The global coordinate Euler sequence of actual twisting sheaves

Multiplication by the coordinate sections gives the actual sheaf morphism
`O(t-1)^(n+1) → O(t)`. On every coordinate chart its right inverse is
multiplication by the literal reciprocal coordinate in the corresponding
summand. The sheaf morphism is therefore an epimorphism, and its actual
kernel gives a short exact sequence. This construction retains the section
maps, so the later exterior identifications can be checked against the
local Koszul construction rather than stipulated as an abstract sequence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false



attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.EulerSheaf

open CoordinateLocalization CechMonomials TwistingSections ProjectiveCech
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open scoped BigOperators

universe u

variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "P" => MvPolynomial I K
local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj 𝒜

/-- The actual degree-one coordinate section on every open. -/
def coordinateSection (i : I) (U : (X).Opens) : Γ(Proj.twistingSheaf 𝒜 1,U) :=
  Proj.toTwistingSheaf 𝒜 rfl U ⟨MvPolynomial.X i,MvPolynomial.isHomogeneous_X (R := K) i⟩

@[simp] theorem coordinateSection_apply (i : I) (U : (X).Opens) (x : U) :
    (coordinateSection (K := K) i U).val x=
      algebraMap P (ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val) (MvPolynomial.X i) := by
  exact Localization.mk_one_eq_algebraMap _

/-- Literal coordinate multiplication on whole section modules. -/
def coordinateMulSections (i : I) (t : ℤ) (U : (X).Opens) :
    Γ(Proj.twistingSheaf 𝒜 (t-1),U) →ₗ[Γ(X,U)] Γ(Proj.twistingSheaf 𝒜 t,U) where
  toFun s := ⟨(coordinateSection i U).val*s.val,by
    apply (ProjectiveSpectrum.TwistingSheaf.mem_sectionsAddSubgroup_iff _).mpr
    simpa only [show (1 : ℤ)+(t-1)=t by omega] using
      ProjectiveSpectrum.TwistingSheaf.isLocallyFraction_mul (coordinateSection i U).property s.property⟩
  map_add' s r := by
    apply Proj.twistingSheaf.ext
    intro x
    simp only [Proj.twistingSheaf.add_apply, Pi.mul_apply]
    change (coordinateSection i U).val x * (s.val x + r.val x) =
      (coordinateSection i U).val x * s.val x + (coordinateSection i U).val x * r.val x
    exact mul_add _ _ _
  map_smul' c s := by
    apply Proj.twistingSheaf.ext
    intro x
    change (coordinateSection i U).val x * ((c.val x).val * s.val x) =
      (c.val x).val * ((coordinateSection i U).val x * s.val x)
    exact mul_left_comm _ _ _

@[simp] theorem coordinateMulSections_apply (i : I) (t : ℤ) (U : (X).Opens)
    (s : Γ(Proj.twistingSheaf 𝒜 (t-1),U)) (x : U) :
    (coordinateMulSections i t U s).val x=(coordinateSection i U).val x*s.val x := rfl

/-- Coordinate multiplication is a morphism of the actual sheaves of modules. -/
def coordinateMul (i : I) (t : ℤ) :
    Proj.twistingSheaf 𝒜 (t-1) ⟶ Proj.twistingSheaf 𝒜 t where
  val :=
    { app U := ⟨coordinateMulSections i t U.unop⟩
      naturality f := by
        ext s
        apply Proj.twistingSheaf.ext
        intro x
        rfl }

/-- Sections of the chosen sheaf product are precisely the product of all section modules. -/
def productSectionsEquiv {J : Type u} (M : J → (X).Modules) (U : (X).Opens) :
    Γ((∏ᶜ M),U) ≃ₗ[Γ(X,U)] ((j : J) → Γ(M j,U)) :=
  ((PreservesProduct.iso (SheafOfModules.evaluation (X).ringCatSheaf (op U)) M) ≪≫
    ModuleCat.piIsoPi (fun j => (SheafOfModules.evaluation (X).ringCatSheaf (op U)).obj (M j))).toLinearEquiv

@[simp] theorem productSectionsEquiv_apply {J : Type u} (M : J → (X).Modules) (U : (X).Opens)
    (s : Γ((∏ᶜ M),U)) (j : J) :
    productSectionsEquiv M U s j=(Pi.π M j).app U s := by
  have he : ((PreservesProduct.iso (SheafOfModules.evaluation (X).ringCatSheaf (op U)) M) ≪≫
        ModuleCat.piIsoPi (fun j => (SheafOfModules.evaluation (X).ringCatSheaf (op U)).obj (M j))).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) =
        (SheafOfModules.evaluation (X).ringCatSheaf (op U)).map (Pi.π M j) := by
    simp only [Iso.trans_hom,Category.assoc,ModuleCat.piIsoPi_hom_ker_subtype]
    exact piComparison_comp_π (SheafOfModules.evaluation (X).ringCatSheaf (op U)) M j
  exact ConcreteCategory.congr_hom he s

/-- The full product-section coordinates commute with actual sheaf restrictions. -/
theorem productSectionsEquiv_res {J : Type u} (M : J → (X).Modules) {U V : (X).Opens}
    (i : V ⟶ U) (s : Γ((∏ᶜ M),U)) (j : J) :
    productSectionsEquiv M V ((∏ᶜ M).presheaf.map i.op s) j=
      (M j).presheaf.map i.op (productSectionsEquiv M U s j) := by
  rw [productSectionsEquiv_apply,productSectionsEquiv_apply]
  exact PresheafOfModules.naturality_apply (Pi.π M j).val i.op s

/-- The literal coordinate map in the Euler sequence. -/
def eulerMap (t : ℤ) :
    (∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 (t-1)) ⟶ Proj.twistingSheaf 𝒜 t :=
  ∑ i, Pi.π _ i ≫ coordinateMul i t

/-- The entire section map is the expected coordinate sum. -/
theorem eulerMap_app (t : ℤ) (U : (X).Opens)
    (s : Γ((∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 (t-1)),U)) :
    (eulerMap (I := I) (K := K) t).app U s =
      ∑ i, coordinateMulSections i t U
        (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (t-1)) U s i) := by
  letI : (Scheme.Modules.sectionsFunctor U).Additive := by
    refine ⟨?_⟩
    intro M N f g
    rfl
  change ((Scheme.Modules.sectionsFunctor U).map (∑ i, Pi.π (fun _ : I => Proj.twistingSheaf 𝒜 (t-1)) i ≫
    coordinateMul i t)).hom s=_
  rw [Functor.map_sum,ModuleCat.hom_sum,LinearMap.sum_apply]
  simp only [Functor.map_comp,ModuleCat.hom_comp,LinearMap.comp_apply,productSectionsEquiv_apply]
  rfl

/-- The reciprocal coordinate is an actual section of `O(-1)` on every smaller chart open. -/
def reciprocalSection (j : I) (U : (X).Opens) (hU : U≤coordinateOpen (K := K) j) :
    Γ(Proj.twistingSheaf 𝒜 (-1),U) :=
  Proj.twistingSheaf.const («𝒜» := 𝒜) (i := 1) (j := 0) (by omega) 1 (MvPolynomial.X j)
    SetLike.GradedOne.one_mem (MvPolynomial.isHomogeneous_X (R := K) j) U hU

theorem coordinateSection_mul_reciprocal (j : I) (U : (X).Opens)
    (hU : U≤coordinateOpen (K := K) j) (x : U) :
    (coordinateSection j U).val x*(reciprocalSection j U hU).val x=1 := by
  let d : x.val.asHomogeneousIdeal.toIdeal.primeCompl :=
    ⟨MvPolynomial.X j, hU x.property⟩
  rw [coordinateSection_apply]
  change algebraMap P (ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val)
    (MvPolynomial.X j) * Localization.mk 1 d = 1
  rw [Localization.mk_eq_mk'_apply]
  simpa only [map_one] using
    IsLocalization.mk'_spec' (ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val) (1 : P) d

/-- The explicit local right inverse in the `j`th summand. -/
def reciprocalMulSections (j : I) (t : ℤ) (U : (X).Opens)
    (hU : U≤coordinateOpen (K := K) j) :
    Γ(Proj.twistingSheaf 𝒜 t,U) →ₗ[Γ(X,U)] Γ(Proj.twistingSheaf 𝒜 (t-1),U) where
  toFun s := ⟨(reciprocalSection j U hU).val*s.val,by
    apply (ProjectiveSpectrum.TwistingSheaf.mem_sectionsAddSubgroup_iff _).mpr
    simpa only [show (-1 : ℤ)+t=t-1 by omega] using
      ProjectiveSpectrum.TwistingSheaf.isLocallyFraction_mul
        (reciprocalSection j U hU).property s.property⟩
  map_add' s r := by
    apply Proj.twistingSheaf.ext
    intro x
    simp only [Proj.twistingSheaf.add_apply, Pi.mul_apply]
    change (reciprocalSection j U hU).val x * (s.val x + r.val x) =
      (reciprocalSection j U hU).val x * s.val x +
        (reciprocalSection j U hU).val x * r.val x
    exact mul_add _ _ _
  map_smul' c s := by
    apply Proj.twistingSheaf.ext
    intro x
    change (reciprocalSection j U hU).val x * ((c.val x).val * s.val x) =
      (c.val x).val * ((reciprocalSection j U hU).val x * s.val x)
    exact mul_left_comm _ _ _

theorem coordinateMul_reciprocalMul (j : I) (t : ℤ) (U : (X).Opens)
    (hU : U≤coordinateOpen (K := K) j) (s : Γ(Proj.twistingSheaf 𝒜 t,U)) :
    coordinateMulSections j t U (reciprocalMulSections j t U hU s)=s := by
  apply Proj.twistingSheaf.ext
  intro x
  change (coordinateSection j U).val x*((reciprocalSection j U hU).val x*s.val x)=s.val x
  rw [← mul_assoc,coordinateSection_mul_reciprocal,one_mul]

/-- The actual Euler map is surjective on the whole section module of every chart subopen. -/
theorem eulerMap_surjective_on_chart (j : I) (t : ℤ) (U : (X).Opens)
    (hU : U≤coordinateOpen (K := K) j) :
    Function.Surjective ((eulerMap (I := I) (K := K) t).app U) := by
  intro s
  let w : I → Γ(Proj.twistingSheaf 𝒜 (t-1),U) := Pi.single j (reciprocalMulSections j t U hU s)
  refine ⟨(productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (t-1)) U).symm w,?_⟩
  rw [eulerMap_app,LinearEquiv.apply_symm_apply]
  rw [Finset.sum_eq_single j]
  · simpa only [w,Pi.single_eq_same] using coordinateMul_reciprocalMul j t U hU s
  · intro i _ hij
    simp [w,hij,Ne.symm hij]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Surjectivity is proved locally from the explicit reciprocal-coordinate splitting. -/
instance eulerMap_epi (t : ℤ) : Epi (eulerMap (I := I) (K := K) t) := by
  let F := TauCeti.AlgebraicGeometry.Scheme.Modules.toSheaf X
  have hlocal : Sheaf.IsLocallySurjective (F.map (eulerMap (I := I) (K := K) t)) := by
    constructor
    intro U s x hx
    have hx' : x ∈ (⨆ i, coordinateOpen (I := I) (K := K) i) := by rw [coordinate_cover]; trivial
    obtain ⟨j,hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    let V := U ⊓ coordinateOpen (K := K) j
    have hVU : V≤U := inf_le_left
    have hVj : V≤coordinateOpen (K := K) j := inf_le_right
    refine ⟨V,homOfLE hVU,?_,⟨hx,hj⟩⟩
    exact eulerMap_surjective_on_chart j t V hVj
      ((Proj.twistingSheaf 𝒜 t).presheaf.map (homOfLE hVU).op s)
  letI := hlocal
  exact F.epi_of_epi_map (Sheaf.epi_of_isLocallySurjective _)

/-- The actual global Euler kernel, not a property stipulated of an abstract module. -/
def eulerKernel (t : ℤ) : (X).Modules := kernel (eulerMap (I := I) (K := K) t)

def eulerShortComplex (t : ℤ) : ShortComplex (X).Modules :=
  ShortComplex.mk (kernel.ι (eulerMap t)) (eulerMap t) (kernel.condition (eulerMap t))

/-- The full actual global coordinate Euler sequence is short exact. -/
theorem euler_shortExact (t : ℤ) : (eulerShortComplex (I := I) (K := K) t).ShortExact where
  exact := ShortComplex.exact_kernel (eulerMap t)
  mono_f := by
    change Mono (kernel.ι (eulerMap (I := I) (K := K) t))
    infer_instance
  epi_g := by
    change Epi (eulerMap (I := I) (K := K) t)
    infer_instance

end PaperVerification.Segre.EulerSheaf

end SegreEulerSheaf

section SegreEulerSections

/-!
# The exterior Euler comparison over the actual chart structure rings

The kernel of the actual global Euler sheaf has the expected full section
module on every open. On every coordinate chart the Euler functional is split
over Γ(O_X,U) itself. Applying the split exterior-kernel comparison therefore
identifies all exterior powers of that section kernel with the actual Koszul
cycles. In particular this is a calculation over the degree-zero structure
ring, without treating the full Laurent localization as the chart ring.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false



attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.EulerSections

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open EulerSheaf ProjectiveCech TauCeti

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj 𝒜

/-- The Euler source is the actual product of the negative twisting sheaf. -/
def eulerSource : (X).Modules := ∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 (-1)

/-- The coordinate Euler map, read as a functional over the actual chart ring. -/
def eulerFunctional (U : (X).Opens) :
    Module.Dual Γ(X,U) Γ(eulerSource (I := I) (K := K),U) :=
  (Proj.sectionsLinearEquivTwistingSheafZero 𝒜 U).symm.toLinearMap.comp
    ((eulerMap (I := I) (K := K) 0).val.app (op U)).hom

/-- The actual section functor is additive and preserves the finite limits used below. -/
local instance sectionsFunctor_additive (U : (X).Opens) :
    (Scheme.Modules.sectionsFunctor U).Additive := by
  refine ⟨?_⟩
  intro M N f g
  rfl

local instance sectionsFunctor_preservesFiniteLimits (U : (X).Opens) :
    PreservesFiniteLimits (Scheme.Modules.sectionsFunctor U) := by
  change PreservesFiniteLimits (SheafOfModules.evaluation (X).ringCatSheaf (op U))
  infer_instance

/-- The section kernel of the sheaf map is exactly its categorical kernel evaluated on the open. -/
def kernelSectionsEquiv (t : ℤ) (U : (X).Opens) :
    Γ(eulerKernel (I := I) (K := K) t,U) ≃ₗ[Γ(X,U)]
      LinearMap.ker ((eulerMap (I := I) (K := K) t).val.app (op U)).hom :=
  ((PreservesKernel.iso (Scheme.Modules.sectionsFunctor U) (eulerMap t)) ≪≫
    ModuleCat.kernelIsoKer ((Scheme.Modules.sectionsFunctor U).map
      (eulerMap t))).toLinearEquiv

@[simp] theorem kernelSectionsEquiv_val (t : ℤ) (U : (X).Opens)
    (s : Γ(eulerKernel (I := I) (K := K) t,U)) :
    (kernelSectionsEquiv t U s).val=(kernel.ι (eulerMap t)).app U s := by
  let F := Scheme.Modules.sectionsFunctor U
  have h : ((PreservesKernel.iso F (eulerMap t)) ≪≫
      ModuleCat.kernelIsoKer (F.map (eulerMap t))).hom ≫
        ModuleCat.ofHom (LinearMap.ker (F.map (eulerMap t)).hom).subtype =
      F.map (kernel.ι (eulerMap t)) := by
    simp only [Iso.trans_hom,Category.assoc,ModuleCat.kernelIsoKer_hom_ker_subtype,
      PreservesKernel.iso_hom,kernelComparison_comp_ι]
  exact ConcreteCategory.congr_hom h s

/-- Changing the codomain from O(0) to the structure sheaf does not change the actual kernel. -/
def functionalKernelEquiv (U : (X).Opens) :
    LinearMap.ker ((eulerMap (I := I) (K := K) 0).val.app (op U)).hom ≃ₗ[Γ(X,U)]
      LinearMap.ker (eulerFunctional U) :=
  LinearEquiv.ofEq _ _ (by
    ext s
    change (eulerMap (I := I) (K := K) 0).app U s=0 ↔
      (Proj.sectionsLinearEquivTwistingSheafZero 𝒜 U).symm
        ((eulerMap (I := I) (K := K) 0).app U s)=0
    exact ((Proj.sectionsLinearEquivTwistingSheafZero 𝒜 U).symm.map_eq_zero_iff).symm)

/-- Actual sections of the global Euler kernel, identified with the actual functional kernel. -/
def actualKernelSectionsEquiv (U : (X).Opens) :
    Γ(eulerKernel (I := I) (K := K) 0,U) ≃ₗ[Γ(X,U)] LinearMap.ker (eulerFunctional U) :=
  (kernelSectionsEquiv (I := I) (K := K) 0 U).trans (functionalKernelEquiv U)

/-- A literal reciprocal-coordinate splitting in the selected summand. -/
def eulerSplitting (j : I) (U : (X).Opens) (hU : U≤coordinateOpen (K := K) j) :
    Γ(eulerSource (I := I) (K := K),U) :=
  (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (-1)) U).symm
    (Pi.single j (reciprocalMulSections j 0 U hU
      (Proj.sectionsLinearEquivTwistingSheafZero 𝒜 U 1)))

/-- The Euler functional evaluates the explicit chart splitting to one. -/
theorem eulerFunctional_splitting (j : I) (U : (X).Opens)
    (hU : U≤coordinateOpen (K := K) j) : eulerFunctional U (eulerSplitting j U hU)=1 := by
  change (Proj.sectionsLinearEquivTwistingSheafZero 𝒜 U).symm
    ((eulerMap (I := I) (K := K) 0).app U (eulerSplitting j U hU))=1
  apply (Proj.sectionsLinearEquivTwistingSheafZero 𝒜 U).injective
  rw [LinearEquiv.apply_symm_apply,eulerMap_app]
  -- Fix the whole dependent expression at the definitionally equal integer
  -- twist before canceling the chosen product-section equivalence.
  change (∑ i : I, coordinateMulSections i 0 U
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (-1)) U
        (eulerSplitting j U hU) i)) =
    Proj.sectionsLinearEquivTwistingSheafZero 𝒜 U 1
  simp only [eulerSplitting,LinearEquiv.apply_symm_apply]
  rw [Finset.sum_eq_single j]
  · simpa only [Pi.single_eq_same] using coordinateMul_reciprocalMul j 0 U hU
      (Proj.sectionsLinearEquivTwistingSheafZero 𝒜 U 1)
  · intro i _ hij
    simp [hij,Ne.symm hij]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Every exterior power of the actual sheaf-kernel section module is exactly the contraction
kernel over the actual ring of functions on the chart. -/
def actualExteriorKernelEquiv (j : I) (U : (X).Opens)
    (hU : U≤coordinateOpen (K := K) j) (p : ℕ) :
    (⋀[Γ(X,U)]^(p+1) Γ(eulerKernel (I := I) (K := K) 0,U)) ≃ₗ[Γ(X,U)]
      LinearMap.ker (koszulDifferential (eulerFunctional U) p) :=
  (LinearEquiv.ofBijective (exteriorPower.map (p+1) (actualKernelSectionsEquiv U).toLinearMap)
    (exteriorPower.map_bijective (actualKernelSectionsEquiv U).bijective)).trans
    (SplitKoszul.exteriorKernelEquiv (eulerFunctional U) (eulerSplitting j U hU)
      (eulerFunctional_splitting j U hU) p)

/-- The entire coordinate Koszul complex is locally exact over the actual structure rings. -/
theorem actual_koszul_exact_on_chart (j : I) (U : (X).Opens)
    (hU : U≤coordinateOpen (K := K) j) (p : ℕ) :
    Function.Exact (koszulDifferential (eulerFunctional U) (p+1))
      (koszulDifferential (eulerFunctional U) p) :=
  SplitKoszul.exact_koszul_of_unit_value (eulerFunctional U) (eulerSplitting j U hU)
    (eulerFunctional_splitting j U hU) p

end PaperVerification.Segre.EulerSections

end SegreEulerSections

section SegreEulerCohomology

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE SegreEulerCohomology"
  out.flush

/-!
# Cohomology of the actual first Euler kernel

The actual global sections of the coordinate map are polynomial multiplication.
The positive homogeneous-degree map is onto, using the homogeneous decomposition
of the irrelevant ideal. The exact sheaf sequence therefore gives the full
positive-twist higher-cohomology vanishing of its kernel. Negative and zero twists
have no global kernel sections. All statements refer to derived sheaf cohomology.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false



attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.EulerCohomology

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open EulerSheaf EulerSections ProjectiveCech ProjectiveGlobalSections
open TauCeti.AlgebraicGeometry.Scheme.Modules
open scoped BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj 𝒜

/-- Finite products of actual sheaves retain vanishing cohomology. -/
theorem cohomology_product_subsingleton {J : Type*} [Fintype J] (M : J → (X).Modules) (q : ℕ)
    (h : ∀ i, Subsingleton (Cohomology (M i) q)) :
    Subsingleton (Cohomology (∏ᶜ M) q) := by
  let F := cohomologyFunctor X q
  have hz : IsZero (∏ᶜ fun i => F.obj (M i)) := by
    apply (limit.isLimit (Discrete.functor (fun i => F.obj (M i)))).isZero_pt
    apply Functor.isZero
    intro i
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr (h i.as)
  exact AddCommGrpCat.subsingleton_of_isZero (hz.of_iso (PreservesProduct.iso F M))

/-- Every positive homogeneous polynomial is an actual sum of variables times forms of one
smaller degree. The proof takes the full homogeneous component of an ideal expression. -/
theorem homogeneous_exists_sum_X_mul (n : ℕ) (p : 𝒜 (n+1)) :
    ∃ q : I → 𝒜 n, ∑ i, MvPolynomial.X i*(q i).val=p.val := by
  have hp : p.val ∈ Ideal.span (Set.range (MvPolynomial.X : I → MvPolynomial I K)) := by
    rw [← Set.image_univ]
    apply MvPolynomial.mem_ideal_span_X_image.mpr
    intro a ha
    by_contra! hn
    have ha0 : a=0 := by
      ext i
      exact hn i (Set.mem_univ i)
    have hd := p.property (MvPolynomial.mem_support_iff.mp ha)
    rw [ha0,map_zero] at hd
    omega
  obtain ⟨q,hq⟩ := Ideal.mem_span_range_iff_exists_fun.mp hp
  refine ⟨fun i => DirectSum.decompose 𝒜 (q i) n,?_⟩
  have hh := congrArg (fun z : MvPolynomial I K =>
    (DirectSum.decompose 𝒜 z (n+1) : MvPolynomial I K)) hq
  rw [DirectSum.decompose_of_mem_same 𝒜 p.property] at hh
  simp only [DirectSum.decompose_sum, DirectSum.sum_apply, Submodule.coe_sum] at hh
  have hm (i : I) : (DirectSum.decompose 𝒜 (q i*MvPolynomial.X i) (n+1) : MvPolynomial I K)=
      (DirectSum.decompose 𝒜 (q i) n : MvPolynomial I K)*MvPolynomial.X i := by
    exact DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (i := n) (j := 1)
      (MvPolynomial.isHomogeneous_X (R := K) i)
  simpa only [hm,mul_comm] using hh

/-- On global sections, the actual positive-twist Euler map is onto. -/
theorem eulerMap_global_surjective (n : ℕ) [Nontrivial I] :
    Function.Surjective ((eulerMap (I := I) (K := K) (n+1)).app ⊤) := by
  intro s
  obtain ⟨p,rfl⟩ := (homogeneousGlobalSectionsEquiv (I := I) (K := K) (n+1)).surjective s
  obtain ⟨q,hq⟩ := homogeneous_exists_sum_X_mul n p
  let w : I → Γ(Proj.twistingSheaf 𝒜 ((n+1 : ℤ)-1),⊤) :=
    fun i => Proj.toTwistingSheaf 𝒜 (show (n : ℤ)=(n+1 : ℤ)-1 by omega) ⊤ (q i)
  refine ⟨(productSectionsEquiv _ ⊤).symm w,?_⟩
  rw [eulerMap_app,LinearEquiv.apply_symm_apply]
  apply Proj.twistingSheaf.ext
  intro x
  let ev : Γ(Proj.twistingSheaf 𝒜 (n+1),⊤) →+
      ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val :=
    { toFun s := s.val x
      map_zero' := rfl
      map_add' _ _ := rfl }
  change ev (∑ i, coordinateMulSections i (n+1) ⊤ (w i)) =
    (homogeneousGlobalSectionsEquiv (n+1) p).val x
  rw [map_sum]
  change (∑ i, (coordinateSection i ⊤).val x *
      (w i).val x)=(homogeneousGlobalSectionsEquiv (n+1) p).val x
  simp only [w,coordinateSection_apply,homogeneousGlobalSectionsEquiv_apply,
    Proj.toTwistingSheaf_apply_apply,Localization.mk_one_eq_algebraMap]
  simpa only [map_sum,map_mul] using congrArg
    (algebraMap (MvPolynomial I K) (ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val)) hq

/-- The actual Euler kernel has no global sections at nonpositive twist. -/
theorem eulerKernel_global_eq_zero (hI : 1<Fintype.card I) (t : ℤ) (ht : t≤0)
    (s : Γ(eulerKernel (I := I) (K := K) t,⊤)) : s=0 := by
  let e := kernelSectionsEquiv (I := I) (K := K) t ⊤
  let P := productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 (t-1)) ⊤
  apply e.injective
  apply Subtype.ext
  apply P.injective
  funext i
  exact (global_section_eq_zero_of_negative hI (t-1) (by omega)
    (P (e s).val i)).trans
      (global_section_eq_zero_of_negative hI (t-1) (by omega)
        (P (e 0).val i)).symm

/-- Degree-zero actual sheaf cohomology of the Euler kernel vanishes at nonpositive twist. -/
theorem eulerKernel_cohomology_zero (hI : 1<Fintype.card I) (t : ℤ) (ht : t≤0) :
    Subsingleton (Cohomology (eulerKernel (I := I) (K := K) t) 0) := by
  let e : Cohomology (eulerKernel (I := I) (K := K) t) 0 ≃+
      Γ(eulerKernel (I := I) (K := K) t,⊤) :=
    cohomologyZeroEquiv (eulerKernel (I := I) (K := K) t)
  refine ⟨fun x y => e.injective ?_⟩
  exact (eulerKernel_global_eq_zero hI t ht (e x)).trans
    (eulerKernel_global_eq_zero hI t ht (e y)).symm

/-- The first Euler kernel has no cohomology in degrees two through N−1 for any twist. -/
theorem eulerKernel_cohomology_intermediate (t : ℤ) (q : ℕ)
    (hq : q+3<Fintype.card I) :
    Subsingleton (Cohomology (eulerKernel (I := I) (K := K) t) (q+2)) := by
  apply subsingleton_cohomology_X₁ (euler_shortExact t) (q+1) (q+2) rfl
  · exact twisting_cohomology_vanishes_below_dimension t q (by omega)
  · exact cohomology_product_subsingleton _ (q+2) (fun _ =>
      twisting_cohomology_vanishes_below_dimension (t-1) (q+1) hq)

/-- Every positive-twist Euler kernel has zero cohomology in degrees at least two. -/
theorem eulerKernel_cohomology_high_positive [Nonempty I] (n q : ℕ) :
    Subsingleton (Cohomology (eulerKernel (I := I) (K := K) (n+1)) (q+2)) := by
  have hI := Fintype.card_pos (α := I)
  apply subsingleton_cohomology_X₁ (euler_shortExact (n+1)) (q+1) (q+2) rfl
  · exact twisting_cohomology_vanishes_of_twist (n+1) (by omega) q
  · exact cohomology_product_subsingleton _ (q+2) (fun _ =>
      twisting_cohomology_vanishes_of_twist ((n+1 : ℤ)-1) (by omega) (q+1))

/-- The actual H¹ of the positive-twist Euler kernel vanishes as well, by the proven global
polynomial multiplication surjectivity and the long exact cohomology sequence. -/
theorem eulerKernel_cohomology_one_positive [Nontrivial I] (n : ℕ) :
    Subsingleton (Cohomology (eulerKernel (I := I) (K := K) (n+1)) 1) := by
  have hI := Fintype.card_pos (α := I)
  let S := eulerShortComplex (I := I) (K := K) (n+1)
  have hS : S.ShortExact := euler_shortExact (n+1)
  have hm : Subsingleton (Cohomology S.X₂ 1) :=
    cohomology_product_subsingleton _ 1 (fun _ =>
      twisting_cohomology_vanishes_of_twist ((n+1 : ℤ)-1) (by omega) 0)
  have hδ := cohomologyδ_surjective hS 0 1 rfl hm
  have hg : Function.Surjective (cohomologyMap S.g 0) := by
    intro x
    obtain ⟨s,hs⟩ := eulerMap_global_surjective n (cohomologyZeroEquiv S.X₃ x)
    refine ⟨(cohomologyZeroEquiv S.X₂).symm s,?_⟩
    apply (cohomologyZeroEquiv S.X₃).injective
    rw [cohomologyZeroEquiv_cohomologyMap, AddEquiv.apply_symm_apply]
    exact hs
  have hz (x : Cohomology S.X₁ 1) : x=0 := by
    obtain ⟨y,rfl⟩ := hδ x
    obtain ⟨z,rfl⟩ := hg y
    exact (exact_cohomologyMap_cohomologyδ hS 0 1 rfl).apply_apply_eq_zero z
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

end PaperVerification.Segre.EulerCohomology

end SegreEulerCohomology

section SegreQuadraticEuler

/-!
# Actual quadratic Euler syzygies in every characteristic

The degree-one coefficients of the coordinate Euler map form an arbitrary
matrix. Its quadratic polynomial is zero exactly when the diagonal vanishes
and opposite entries sum to zero. Diagonal vanishing is retained explicitly in
characteristic two. The full kernel is therefore the alternating-matrix space,
and its dimension is the expected binomial coefficient.
-/

set_option autoImplicit false



namespace PaperVerification.Segre.QuadraticEuler

open scoped BigOperators
open MvPolynomial

variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K

/-- The full degree-one homogeneous component in literal coefficient coordinates. -/
def linearForm : (I → K) →ₗ[K] 𝒜 1 where
  toFun c := ⟨∑ i, c i • MvPolynomial.X i,
    (𝒜 1).sum_mem (fun i _ => (𝒜 1).smul_mem (c i) (isHomogeneous_X (R := K) i))⟩
  map_add' c d := Subtype.ext (by simp only [Pi.add_apply,Submodule.coe_add,add_smul,Finset.sum_add_distrib])
  map_smul' c d := Subtype.ext (by simp only [Pi.smul_apply,Submodule.coe_smul,RingHom.id_apply,smul_eq_mul,smul_smul,Finset.smul_sum])

@[simp] theorem linearForm_coeff (c : I → K) (i : I) :
    (linearForm c).val.coeff (Finsupp.single i 1)=c i := by
  simp [linearForm,coeff_smul,coeff_X,Finsupp.single_left_inj one_ne_zero]

/-- All linear forms, with no restriction on their coefficient vectors. -/
def linearFormsEquiv : (I → K) ≃ₗ[K] 𝒜 1 where
  toLinearMap := linearForm
  invFun p i := p.val.coeff (Finsupp.single i 1)
  left_inv c := funext (linearForm_coeff c)
  right_inv p := Subtype.ext (by
    change (∑ i, p.val.coeff (Finsupp.single i 1) • MvPolynomial.X i)=p.val
    rw [← homogeneousComponent_one_eq_sum,homogeneousComponent_eq_self p.property])

/-- The actual homogeneous coordinate Euler multiplication map in polynomial coordinates. -/
def polynomialEuler : (I → 𝒜 1) →ₗ[K] 𝒜 2 where
  toFun p := ⟨∑ i, MvPolynomial.X i*(p i).val,
    (𝒜 2).sum_mem (fun i _ =>
      (isHomogeneous_X (R := K) i).mul (p i).property)⟩
  map_add' p q := Subtype.ext (by simp only [Pi.add_apply,Submodule.coe_add,mul_add,
    Finset.sum_add_distrib])
  map_smul' c p := Subtype.ext (by simp only [Pi.smul_apply,Submodule.coe_smul,RingHom.id_apply,mul_smul_comm,
    Finset.smul_sum])

/-- Rows of arbitrary coefficient matrices are exactly arbitrary tuples of linear forms. -/
def matrixRowsEquiv : Matrix I I K ≃ₗ[K] (I → 𝒜 1) :=
  LinearEquiv.piCongrRight (fun _ => linearFormsEquiv)

/-- The literal degree-two polynomial represented by an arbitrary matrix. -/
def quadratic (A : Matrix I I K) : MvPolynomial I K :=
  (polynomialEuler (matrixRowsEquiv A)).val

theorem quadratic_eval (A : Matrix I I K) (x : I → K) :
    MvPolynomial.aeval x (quadratic A)=∑ i, ∑ j, A i j*x i*x j := by
  change MvPolynomial.aeval x
    (∑ i, MvPolynomial.X i * (∑ j, A i j • MvPolynomial.X j)) = _
  simp only [map_sum,map_mul,map_smul,aeval_X,Finset.mul_sum,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Evaluation on one basis vector extracts the diagonal entry, in every characteristic. -/
theorem quadratic_eval_single (A : Matrix I I K) (i : I) :
    MvPolynomial.aeval (Pi.single i 1) (quadratic A)=A i i := by
  rw [quadratic_eval]
  simp [Pi.single_apply]

/-- Evaluation on the sum of two distinct basis vectors extracts the two diagonal entries
and the two opposite off-diagonal entries; no division by two is used. -/
theorem quadratic_eval_two (A : Matrix I I K) (i j : I) (hij : i≠j) :
    MvPolynomial.aeval (Pi.single i 1+Pi.single j 1) (quadratic A)=
      A i i+A i j+A j i+A j j := by
  rw [quadratic_eval]
  simp only [Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]
  simp [Pi.single_apply,hij,Ne.symm hij,add_assoc,add_left_comm,add_comm]

/-- The full alternating-matrix space, including zero diagonal in characteristic two. -/
def alternatingMatrices : Submodule K (Matrix I I K) where
  carrier := {A | (∀ i, A i i=0) ∧ (∀ i j, A i j+A j i=0)}
  zero_mem' := by simp
  add_mem' := by
    rintro A B ⟨hAd,hAs⟩ ⟨hBd,hBs⟩
    constructor
    · intro i; simp [hAd,hBd]
    · intro i j
      change (A i j+B i j)+(A j i+B j i)=0
      rw [add_add_add_comm,hAs,hBs,zero_add]
  smul_mem' := by
    rintro c A ⟨hAd,hAs⟩
    constructor
    · intro i; simp [hAd]
    · intro i j
      change c*A i j+c*A j i=0
      rw [← mul_add,hAs,mul_zero]

/-- Polynomial equality forces all alternating relations, even over the field of two elements. -/
theorem alternating_of_quadratic_eq_zero (A : Matrix I I K) (hA : quadratic A=0) :
    A ∈ alternatingMatrices := by
  have hd (i : I) : A i i=0 := by
    have h := congrArg (MvPolynomial.aeval (Pi.single i (1 : K))) hA
    simpa only [quadratic_eval_single,map_zero] using h
  refine ⟨hd,fun i j => ?_⟩
  by_cases hij : i=j
  · subst j; simp [hd]
  · have h := congrArg (MvPolynomial.aeval
      (Pi.single i (1 : K) + Pi.single j (1 : K) : I → K)) hA
    simpa only [quadratic_eval_two A i j hij,map_zero,hd,zero_add,add_zero] using h

/-- Every alternating matrix gives zero in the literal quadratic polynomial ring. -/
theorem quadratic_eq_zero_of_alternating (A : alternatingMatrices (I := I) (K := K)) :
    quadratic A.val=0 := by
  change (∑ i, MvPolynomial.X i*(∑ j, A.val i j • MvPolynomial.X j))=0
  simp only [Finset.mul_sum,mul_smul_comm]
  rw [← Finset.sum_product',Finset.univ_product_univ]
  apply Finset.sum_involution (fun p _ => (p.2,p.1))
  · rintro ⟨i,j⟩ _
    change A.val i j • (MvPolynomial.X i*MvPolynomial.X j)+
      A.val j i • (MvPolynomial.X j*MvPolynomial.X i)=0
    rw [mul_comm (MvPolynomial.X j),← add_smul,A.property.2 i j,zero_smul]
  · rintro ⟨i,j⟩ _ hn he
    have hij : i=j := (congrArg Prod.fst he).symm
    subst j
    exact hn (by simp [A.property.1])
  · intro p _; exact Finset.mem_univ _
  · intro p _; cases p; rfl

/-- The exact coefficient criterion for the quadratic Euler kernel. -/
theorem quadratic_eq_zero_iff (A : Matrix I I K) :
    quadratic A=0 ↔ A ∈ alternatingMatrices :=
  ⟨alternating_of_quadratic_eq_zero A,fun h => quadratic_eq_zero_of_alternating ⟨A,h⟩⟩

/-- The alternating-matrix inclusion into the entire polynomial Euler kernel. -/
def alternatingToKernel : alternatingMatrices (I := I) (K := K) →ₗ[K]
    LinearMap.ker (polynomialEuler (I := I) (K := K)) :=
  ((matrixRowsEquiv (I := I) (K := K)).toLinearMap.comp alternatingMatrices.subtype).codRestrict _
    (fun A => Subtype.ext (quadratic_eq_zero_of_alternating A))

/-- Every quadratic Euler relation is exactly an alternating coefficient matrix. -/
def alternatingKernelEquiv : alternatingMatrices (I := I) (K := K) ≃ₗ[K]
    LinearMap.ker (polynomialEuler (I := I) (K := K)) :=
  LinearEquiv.ofBijective alternatingToKernel (by
    constructor
    · intro A B h
      apply Subtype.ext
      apply matrixRowsEquiv.injective
      exact congrArg Subtype.val h
    · intro z
      let A := matrixRowsEquiv.symm z.val
      have hA : A ∈ alternatingMatrices := by
        apply alternating_of_quadratic_eq_zero
        change (polynomialEuler (matrixRowsEquiv A)).val=0
        rw [LinearEquiv.apply_symm_apply]
        exact congrArg Subtype.val z.property
      refine ⟨⟨A,hA⟩,?_⟩
      apply Subtype.ext
      exact matrixRowsEquiv.apply_symm_apply z.val)

/-- Strict upper entries parametrize all alternating matrices, in every characteristic. -/
def alternatingCoordinates [LinearOrder I] :
    alternatingMatrices (I := I) (K := K) ≃ₗ[K] ({q : I × I // q.1<q.2} → K) where
  toFun A q := A.val q.val.1 q.val.2
  invFun c := ⟨Matrix.ofStrictUpper c,by
    refine ⟨Matrix.ofStrictUpper_apply_diag c,fun i j => ?_⟩
    have h := congrFun (congrFun (Matrix.transpose_ofStrictUpper c) i) j
    change Matrix.ofStrictUpper c i j+Matrix.ofStrictUpper c j i=0
    change Matrix.ofStrictUpper c j i= -Matrix.ofStrictUpper c i j at h
    rw [h,add_neg_cancel]⟩
  left_inv A := by
    apply Subtype.ext
    change Matrix.ofStrictUpper
      (fun q : {q : I × I // q.1 < q.2} => A.val q.val.1 q.val.2) = A.val
    apply Matrix.ext_of_lt_of_transpose_eq_neg (Matrix.transpose_ofStrictUpper _)
    · ext i j
      exact eq_neg_of_add_eq_zero_left (A.property.2 j i)
    · exact Matrix.ofStrictUpper_apply_diag _
    · exact A.property.1
    · intro i j hij
      exact Matrix.ofStrictUpper_apply_of_lt _ ⟨(i,j),hij⟩
  right_inv c := funext (Matrix.ofStrictUpper_apply_of_lt c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The exact full Euler-kernel dimension, including characteristic two. -/
theorem finrank_polynomialEuler_kernel :
    Module.finrank K (LinearMap.ker (polynomialEuler (I := I) (K := K)))=
      (Fintype.card I).choose 2 := by
  classical
  let : LinearOrder I := LinearOrder.lift' (Fintype.equivFin I) (Fintype.equivFin I).injective
  rw [← alternatingKernelEquiv.finrank_eq,alternatingCoordinates.finrank_eq,
    Module.finrank_pi,Fintype.card_subtype,Fintype.card_product_filter_lt]

end PaperVerification.Segre.QuadraticEuler

end SegreQuadraticEuler

section SegreActualQuadraticEuler

/-!
# The full global Euler-kernel space is the alternating tensor space

This file transports the literal quadratic-polynomial calculation to actual
global sections of the actual Euler sheaf kernel. The source and target changes
of coordinates are complete linear equivalences over the canonical coefficient
field, and the entire multiplication map commutes with those equivalences.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false



attribute [local instance] MvPolynomial.gradedAlgebra
open Opposite

namespace PaperVerification.Segre.ActualQuadraticEuler

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open EulerSheaf EulerSections ProjectiveGlobalSections QuadraticEuler
open scoped BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K] [Nonempty I]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj 𝒜

local instance globalFunctionsAlgebra : Algebra K Γ(X,⊤) :=
  (Scheme.Modules.baseRingToGlobalSections K X).toAlgebra

local instance globalSectionsTower (M : (X).Modules) : IsScalarTower K Γ(X,⊤) Γ(M,⊤) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The entire source section space is exactly the tuple of all linear homogeneous polynomials. -/
def sourceGlobalEquiv :
    Γ((∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 1),⊤) ≃ₗ[K] (I → 𝒜 1) :=
  ((productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 1) ⊤).restrictScalars K).trans
    (LinearEquiv.piCongrRight (fun _ => (homogeneousGlobalSectionsLinearEquiv 1).symm))

@[simp] theorem sourceGlobalEquiv_component
    (s : Γ((∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 1),⊤)) (i : I) :
    homogeneousGlobalSectionsLinearEquiv 1 (sourceGlobalEquiv s i)=
      productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 1) ⊤ s i := by
  exact LinearEquiv.apply_symm_apply _ _

/-- The literal actual section map of the Euler sequence, over its canonical base field. -/
def eulerGlobalMap :
    Γ((∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 1),⊤) →ₗ[K]
      Γ(Proj.twistingSheaf 𝒜 2,⊤) := by
  -- Fix the section types before restricting scalars: the categorical source
  -- is written with twist `2 - 1`, while its canonical base action is on `O(1)`.
  let f : Γ((∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 1),⊤) →ₗ[Γ(X,⊤)]
      Γ(Proj.twistingSheaf 𝒜 2,⊤) :=
    ((eulerMap (I := I) (K := K) 2).val.app (op ⊤)).hom
  exact f.restrictScalars K

/-- The complete actual global Euler multiplication map becomes literal polynomial
multiplication under the proven source and target equivalences. -/
theorem eulerGlobalMap_compat
    (s : Γ((∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 1),⊤)) :
    homogeneousGlobalSectionsLinearEquiv 2 (polynomialEuler (sourceGlobalEquiv s))=
      eulerGlobalMap s := by
  change homogeneousGlobalSectionsLinearEquiv 2 (polynomialEuler (sourceGlobalEquiv s))=
    (eulerMap (I := I) (K := K) 2).app ⊤ s
  rw [eulerMap_app]
  apply Proj.twistingSheaf.ext
  intro x
  have hp (i : I) := congrArg (fun z : Γ(Proj.twistingSheaf 𝒜 1,⊤) => z.val x)
    (sourceGlobalEquiv_component s i)
  simp only [homogeneousGlobalSectionsLinearEquiv_apply,Proj.toTwistingSheaf_apply_apply,
    Localization.mk_one_eq_algebraMap] at hp
  let ev : Γ(Proj.twistingSheaf 𝒜 2,⊤) →+
      ProjectiveSpectrum.TwistingSheaf.Localizations 𝒜 x.val :=
    { toFun a := a.val x
      map_zero' := rfl
      map_add' _ _ := rfl }
  change ev (homogeneousGlobalSectionsLinearEquiv 2 (polynomialEuler (sourceGlobalEquiv s))) =
    ev (∑ i, coordinateMulSections i 2 ⊤
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 1) ⊤ s i))
  rw [map_sum]
  change Localization.mk (∑ i, MvPolynomial.X i*(sourceGlobalEquiv s i).val) 1=
    ∑ i, (coordinateSection i ⊤).val x *
      (productSectionsEquiv (fun _ : I => Proj.twistingSheaf 𝒜 1) ⊤ s i).val x
  rw [Localization.mk_one_eq_algebraMap,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul,hp i,coordinateSection_apply]

/-- Every actual Euler-kernel section, and every such section, corresponds to a polynomial
Euler relation. This is an isomorphism of the complete kernels. -/
def actualPolynomialKernelEquiv : LinearMap.ker (eulerGlobalMap (I := I) (K := K)) ≃ₗ[K]
    LinearMap.ker (polynomialEuler (I := I) (K := K)) where
  toFun s := ⟨sourceGlobalEquiv s.val,by
    apply (homogeneousGlobalSectionsLinearEquiv 2).injective
    rw [eulerGlobalMap_compat,s.property,map_zero]⟩
  invFun p := ⟨sourceGlobalEquiv.symm p.val,by
    have h := eulerGlobalMap_compat (sourceGlobalEquiv.symm p.val)
    rw [LinearEquiv.apply_symm_apply,p.property,map_zero] at h
    exact h.symm⟩
  left_inv s := Subtype.ext (sourceGlobalEquiv.symm_apply_apply s.val)
  right_inv p := Subtype.ext (sourceGlobalEquiv.apply_symm_apply p.val)
  map_add' s t := Subtype.ext (map_add sourceGlobalEquiv s.val t.val)
  map_smul' c s := Subtype.ext (map_smul sourceGlobalEquiv c s.val)

/-- Sections of the actual sheaf kernel, over the canonical coefficient field. -/
def kernelGlobalEquiv : Γ(eulerKernel (I := I) (K := K) 2,⊤) ≃ₗ[K]
    LinearMap.ker (eulerGlobalMap (I := I) (K := K)) := by
  let f : Γ((∏ᶜ fun _ : I => Proj.twistingSheaf 𝒜 1),⊤) →ₗ[Γ(X,⊤)]
      Γ(Proj.twistingSheaf 𝒜 2,⊤) :=
    ((eulerMap (I := I) (K := K) 2).val.app (op ⊤)).hom
  let e : Γ(eulerKernel (I := I) (K := K) 2,⊤) ≃ₗ[Γ(X,⊤)] LinearMap.ker f :=
    kernelSectionsEquiv (I := I) (K := K) 2 ⊤
  exact e.restrictScalars K

/-- The entire actual global Euler-kernel space is the alternating-matrix space. -/
def alternatingGlobalKernelEquiv : alternatingMatrices (I := I) (K := K) ≃ₗ[K]
    Γ(eulerKernel (I := I) (K := K) 2,⊤) :=
  alternatingKernelEquiv.trans (actualPolynomialKernelEquiv.symm.trans kernelGlobalEquiv.symm)

/-- The actual global Euler-kernel dimension is binomial(card I,2), over every field. -/
theorem finrank_actualGlobalEulerKernel :
    Module.finrank K Γ(eulerKernel (I := I) (K := K) 2,⊤)=(Fintype.card I).choose 2 := by
  rw [kernelGlobalEquiv.finrank_eq,actualPolynomialKernelEquiv.finrank_eq,
    finrank_polynomialEuler_kernel]

end PaperVerification.Segre.ActualQuadraticEuler

end SegreActualQuadraticEuler

end SegreProjectiveCohomology

end
end
end ProbeLayer391

/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
