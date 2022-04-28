module Isomorphism

import Category

{-----------------------------------------------------------------------------------------------------------------------
A determination problem is one in which we have the first morphism of a composition fixed,
and therefore the second morphism is determined by the target object of the first morphism
and the target object of the overall composition.

A choice problem is the opposite, in this case we have the second morphism in a composition fixed,
and therefore we get to choose a morphism that connects the source object of the overall composition
and the source object of the second morphism.

Here is an example to illustrate the point.

For objects x, y, and z we will define morphisms f, g, and h such that:
 - f : x -> y (this is the first morphism in the composition)
 - g : y -> z (this is the second morphism in the composition)
 - h : x -> z (this is the morphism resulting from the composition of f and g such that h = g . f)

                                                   ┌─┐
                                        f─────────►│y├─────────g
                                        │          └─┘         │
                                        │                      │
                                        │                      │
                                        │                      ▼
                                       ┌┴┐                    ┌─┐
                                       │x├──────────h────────►│z│
                                       └─┘                    └─┘

 A determination problem is where we get to select some r (named r because of the relationship between determination
and retractions) such that for f and h we can reconstruct the diagram above by substituting r in for g. Put another way,
r . f = h, and you can see that the Determination record below carries this proof of commutativity.

Choice, again, mirrors determination; we get to select some s (named because of the relationship between choice and
sections) such that for g and h we can reconstruct the diagram above by substituting s for f. We can express the
commutativity law for choice as g . s = h.

Therefore, determination and choice give us the vocabulary to talk about the two constituent parts of the simplest
composition.
-----------------------------------------------------------------------------------------------------------------------}

public export
record Determination
  -- the category that we are operating in
  (cat : Category)
  -- the objects that our morphisms map between
  (x, y, z : cat.Obj)
  -- h : x -> z, this is the "composition" morphism
  (h : cat.morph x z)
  -- f : x -> y, this is the fixed first morphism
  (f : cat.morph x y)
  where
  constructor Determine
  -- r : y -> z, this is the second morphism in the composition that is determined by f.
  -- it is called r because it is a retraction when h = id, in the diagram above g = r.
  r : cat.morph y z

  -- proof of commutativity
  commutativity : cat.compose {a = x, b = y, c = z} r f = h

public export
record Choice
  -- the category that we are operating in
  (cat : Category)
  -- the objects that our morphisms map between
  (x, y, z : cat.Obj)
  -- h : x -> z, this is the "composition" morphism
  (h : cat.morph x z)
  -- g : y -> z, this is the fixed second morphism
  (g : cat.morph y z)
  where
  constructor Choose
  -- s : x -> y, this is the first morphism in the composition that is chosen to fit with g.
  -- it is called s because it is a section when h = id, in the diagram above f = s.
  s : cat.morph x y

  -- proof of commutativity
  commutativity : cat.compose {a = x, b = y, c = z} g s = h


{-----------------------------------------------------------------------------------------------------------------------
Retractions and sections are special cases of determination and choice problems, where we define h as id. The diagram
below illustrates how we can simplify things by eliminating h (which becomes an implicit identity morphism), and
unifying x and z into a (I chose to rename the variables for clarity).

                                                  ┌─────────┐
                                 ┌─┐              │x = z = a│        ┌─┐
                      f─────────►│y├─────────g    │y = b    │      ┌►│b├─┐
                      │          └─┘         │    │h = id   │      │ └─┘ │
                      │                      │    └─────────┘      │     │
                      │                      │                     f     g
                      │                      ▼     --------->      │     │
                     ┌┴┐                    ┌─┐                    │ ┌─┐ │
                     │x├────────h = id─────►│z│                    └─┤a│◄┘
                     └─┘                    └─┘                      └─┘

The resulting diagram looks like a canonical isomorphism so long as `g . f = id = 1a` and `f . g = id = 1b`. The
commutativity law from determination allows us to prove `g . f = id = 1a` and the commutativity law from choice
allows us to prove `f . g = id = 1b` if we make a couple assumptions:
 - h = id (we already mentioned this one)
 - g = r for the Determination
 - f = s for the Choice

This relationship with isomorphisms is interesting, but it is also possible to talk about retractions and sections that
don't form an isomorphism. This is when we have one without the other. Therefore you can think of sections and
retractions as two halves of an isomorphism; a weaker structure. We can also have sections and retractions as sub-graphs
of categorical diagrams.

                      retraction example                        section example

                             ┌─┐                                      ┌─┐
                  f─────────►│y├─────────g                 f─────────►│y├─────────g
                  │          └┬┘         │                 │          └─┘         │
                  │           │          │                 │           ▲          │
                  │           │          │                 │           │          │
                  │           │          ▼                 │           │          ▼
              ┌─►┌┴┐          │         ┌─┐               ┌┴┐          │         ┌─┐◄─┐
              │  │x│◄─────────r         │z│               │x│          s─────────┤z│  │
             1x──┴┬┘                    └─┘               └┬┘                    └─┴──1z
                  │                      ▲                 │                      ▲
                  └───────────h──────────┘                 └───────────h──────────┘

The retraction example shows an "embedded" retraction in the larger structure. The retraction is made up of f,
r, and 1x (or id on x). The section example also shows how we might embedd a section into the same structure, and it
is made up of g, s, and 1z (or id on z).

Notice how the target object for r has the identity morphism on it, while the source object for s has the identity? This
is the fundamental difference between a section and a retraction. That is how you can distinguish which part of the
isomorphism the section / retraction represents.

The diagram below tries to provide a concrete example of a section and retraction using the example of two objects, one
representing the set of constituents of a district (y) and one representing a set of districts (z / x). I chose the names z
and x as analogies to the diagrams above, but in this case 1x = h = 1z (or put another way x = z).

       ┌───y────┐        ┌───────────────────────section example──────────────────────────┐        ┌───y────┐
       │Samantha├──┐     │Legend:                                                         │        │Samantha├──┐
       │        │  │     │- y are the constituents of a district                          │        │        │  │
       │Dennis  ├──┤  <- │- z is the district (only 1 for simplicity)                     │        │Dennis  ├──┤
       │        │  │     │- g maps constituents to their district                         │        │        │  │
    ┌─►│Robert  ├──┤     │- s maps districts to the representative (perhaps a mp)         │     ┌─►│Robert  ├──┤
    │  └────────┘  │     └────────────────────────────────────────────────────────────────┘     │  └────────┘  │
    │              │     ┌───────────────────────retraction example───────────────────────┐     │              │
    s              g     │Legend:                                                         │     f              r
    │              │     │- y are the constituents of a district                          │     │              │
    │  ┌───z───┐   │     │- x are the representatives of districts (only 1 for simplicity)│ ->  │  ┌───x───┐   │
    └──┤Toronto│◄──┘     │- f maps districts to their representative                      │     └──┤Toronto│◄──┘
       └───────┤         │- r maps constituents to their district                         │        └───────┤
       ▲       │         └────────────────────────────────────────────────────────────────┘        ▲       │
       └────── 1Toronto                                                                            └────── 1Toronto

Therefore, we can think of a section as "taking a section" of a morphism's (in this case g's) source object. We can
think of a retraction as "retracting" or "condensing" the target object back into the source with respect to some
morphism (in this case f). The direction of this is all determined by the order of composition which preserves
commutativity (i.e. whether left or right composition is equivalent to the id). A section s is right composed
(runs first) `g . s = id`, while a retraction r is left composed (runs last) `r . f = id`.
-----------------------------------------------------------------------------------------------------------------------}

public export
HasRetraction : {cat : Category} -> {a, b : cat.Obj} -> (f : cat.morph a b) -> Type
HasRetraction = Determination cat a b a cat.id

public export
HasSection : {cat : Category} -> {a, b : cat.Obj} -> (g : cat.morph b a) -> Type
HasSection = Choice cat a b a cat.id

{-----------------------------------------------------------------------------------------------------------------------
-----------------------------------------------------------------------------------------------------------------------}
public export
record Isomorphism
  (cat : Category)
  (a, b : cat.Obj)
  where
  constructor Iso
  forward : cat.morph a b
  backward : cat.morph b a
  fInverse : cat.compose {a = b, b = a, c = b} forward backward = cat.id {a = b}
  bInverse : cat.compose {a = a, b = b, c = a} backward forward = cat.id {a = a}

public export
Automorphism : {cat : Category} -> (a : cat.Obj) -> Type
Automorphism a = Isomorphism cat a a

-- The below examples are intended to elucidate the missing piece of a retraction / section that is needed to complete
-- the isomorphism

public export
isoFromRetraction :
  {cat : Category} ->
  {x, y : cat.Obj} ->
  (f : cat.morph x y) ->
  (retract : HasRetraction {cat, a = x, b = y} f) ->
  (cat.compose {a = y, b = x, c = y} f retract.r = cat.id {a = y}) ->
  Isomorphism cat x y
isoFromRetraction {cat} f (Determine r detComm) comm = Iso f r comm detComm

public export
isoFromSection :
  {cat : Category} ->
  {x, y : cat.Obj} ->
  (f : cat.morph x y) ->
  (section : HasSection {cat, a = y, b = x} f) ->
  (cat.compose {a = x, b = y, c = x} section.s f = cat.id {a = x}) ->
  Isomorphism cat x y
isoFromSection {cat} f (Choose s choiceComm) comm = Iso f s choiceComm comm
