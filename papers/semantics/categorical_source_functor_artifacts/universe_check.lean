import IndexedSourceSemantics
open IndexedSource IndexedWitness CategoryTheory
#check Object
#check WholeInterface
#check Term
#check Hom
#check semantics
example : Category.{1} Object := inferInstance
example : Category.{1} WholeInterface := inferInstance
noncomputable example : Functor Object WholeInterface := semantics
