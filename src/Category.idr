module Category


infix 6 ~>
infix 6 <<<

public export
record Category where
  constructor MkCategory
  Obj           : Type
  morph         : Obj -> Obj -> Type
  id            : {a : Obj} -> morph a a
  compose       : { a, b, c : Obj }
               -> (f : morph b c)
               -> (g : morph a b)
               -> morph a c
  leftIdentity  : { a, b : Obj }
               -> (f : morph a b)
               -> compose id f = f
  rightIdentity : { a, b : Obj }
               -> (f : morph a b)
               -> compose f id = f
  associativity : {a, b, c, d : Obj}
               -> (f : morph c d)
               -> (g : morph b c)
               -> (h : morph a b)
               -> compose f (compose g h) = compose (compose f g) h
