module Examples.Category

import Category

public export
TYPE : Category
TYPE = Cat Type TypeMorphism morphismEquality identity compose leftIdentity rightIdentity associativity
  where
    TypeMorphism : Type -> Type -> Type
    TypeMorphism x y = x -> y

    morphismEquality : {a, b : Type} -> TypeMorphism a b -> TypeMorphism a b -> TypeMorphism a b = TypeMorphism a b
    morphismEquality f g = Refl

    identity : {a : Type} -> TypeMorphism a a
    identity = (\x => x)

    compose : {a, b, c : Type} -> (g : TypeMorphism b c) -> (f : TypeMorphism a b) -> TypeMorphism a c
    compose g f = g . f

    leftIdentity : {a, b : Type} -> (f : TypeMorphism a b) -> (identity {a = b}) . f = f
    leftIdentity f = Refl

    rightIdentity : {a, b : Type} -> (f : TypeMorphism a b) -> f . (identity {a = a}) = f
    rightIdentity f = Refl

    associativity :
         {a, b, c, d : Type}
      -> (f : TypeMorphism c d)
      -> (g : TypeMorphism b c)
      -> (h : TypeMorphism a b)
      -> (f . g) . h = f . (g . h)
    associativity f g h = Refl

