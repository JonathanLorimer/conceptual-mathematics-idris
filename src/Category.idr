module Category

public export
record Category where
  constructor Cat
  Obj           : Type
  morph         : Obj -> Obj -> Type
  morphEq       : { a, b : Obj }
               -> morph a b
               -> morph a b
               -> morph a b = morph a b
  id            : { a : Obj } -> morph a a
  compose       : { a, b, c : Obj }
               -> (g : morph b c)
               -> (f : morph a b)
               -> morph a c
  leftIdentity  : { a, b : Obj }
               -> (f : morph a b)
               -> compose id f = f
  rightIdentity : { a, b : Obj }
               -> (f : morph a b)
               -> compose f id = f
  associativity : { a, b, c, d : Obj }
               -> (f : morph c d)
               -> (g : morph b c)
               -> (h : morph a b)
               -> compose f (compose g h) = compose (compose f g) h
