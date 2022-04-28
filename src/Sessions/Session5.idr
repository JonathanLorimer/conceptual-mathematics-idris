module Sessions.Session5

import Isomorphism
import Category
import Examples.Category

{-----------------------------------------------------------------------------------------------------------------------
The below examples are intended to illustrate the relationship between choice <-> sections and
determination <-> retractions further. This example is drawn from page 72 of Conceptual Mathematics. The idea is roughly
as follows, say we a determination problem (missing some g) or a section problem (missing some f) but we do have a
retraction on f or a section on g, then we can use composition to recover the missing function:

                      determination problem                    choice problem with
                        with retraction                              section

                             ┌─┐                                      ┌─┐
                  f─────────►│y│                                      │y├─────────g
                  │          └┬┘                                      └─┘         │
                  │           │      g?                       f?       ▲          │
                  │           │                                        │          │
                  │           │                                        │          ▼
              ┌─►┌┴┐          │         ┌─┐               ┌─┐          │         ┌─┐◄─┐
              │  │x│◄─────────r         │z│               │x│          s─────────┤z│  │
             1x──┴┬┘                    └─┘               └┬┘                    └─┴──1z
                  │                      ▲                 │                      ▲
                  └───────────h──────────┘                 └───────────h──────────┘



                      retraction example                        section example

                             ┌─┐         g                 f          ┌─┐
                  f─────────►│y├──────(h . r)           (s . h)──────►│y├─────────g
                  │          └┬┘         │                 │          └─┘         │
                  │           │          │                 │           ▲          │
                  │           │          │                 │           │          │
                  │           │          ▼                 │           │          ▼
              ┌─►┌┴┐          │         ┌─┐               ┌┴┐          │         ┌─┐◄─┐
              │  │x│◄─────────r         │z│               │x│          s─────────┤z│  │
             1x──┴┬┘                    └─┘               └┬┘                    └─┴──1z
                  │                      ▲                 │                      ▲
                  └───────────h──────────┘                 └───────────h──────────┘


The crux of this move is being able to prove that we can derive commutivity of the entire determination / choice from the
commutivity of the retraction / section. It turns out we can.

    Retraction:
   ┌─────────────────────┐
   │r . f = id           │ From the commutivity of a retraction
   │g = h . r            │ From the composition of h . r to form g
   ├─────────────────────┤
   │h . (r . f) = h . id │ From pre-composing both sides with h (often called cong)
   │(h . r) . f = h . id │ From the associativity of composition
   │g . f = h . id       │ From the composition of h . r to form g
   │g . f = h            │ From the right identity of composition
   ├─────────────────────┤
   │g . f = h            │ q.e.d
   └─────────────────────┘

    Section:
   ┌─────────────────────┐
   │g . s = id           │ From the commutivity of a retraction
   │f = s . h            │ From the composition of s . h to form f
   ├─────────────────────┤
   │(g . s) . h = id . h │ From post-composing both sides with h (often called cong)
   │g . (s . h) = id . h │ From the associativity of composition
   │g . f = id . h       │ From the composition of s . h to form f
   │g . f = h            │ From the left identity of composition
   ├─────────────────────┤
   │g . f = h            │ q.e.d
   └─────────────────────┘

-----------------------------------------------------------------------------------------------------------------------}

choiceFromSection : {cat : Category} -> {a, b, c : cat.Obj}
                 -> (g : cat.morph b c) -> (h : cat.morph a c)
                 -> HasSection {cat, b, a = c} g
                 -> Choice cat a b c h g
choiceFromSection g h (Choose s choiceComm) = Choose (cat.compose s h) commutativity
  where
    commutativity : cat.compose {a, b, c} g (cat.compose {a, b = c, c = b} s h) = h
    commutativity =
      let asoc : cat.compose { a, b, c } g (cat.compose {a, b = c, c = b} s h) ~=~
                 cat.compose { a, b = c, c } (cat.compose {a = c, b, c} g s) h
          asoc = cat.associativity g s h

          congChoiceComm : cat.compose { a, b = c, c } (cat.compose {a = c, b, c} g s) h ~=~
                           cat.compose { a, b = c, c } (cat.id {a = c}) h
          congChoiceComm = cong (flip cat.compose h) $ choiceComm
      in rewrite asoc in
         rewrite congChoiceComm in
         rewrite cat.leftIdentity {a, b = c} h in Refl

determinationFromRetraction : {cat : Category} -> {a, b, c : cat.Obj}
                           -> (f : cat.morph a b) -> (h : cat.morph a c)
                           -> HasRetraction {cat, a = a, b = b} f
                           -> Determination cat a b c h f
determinationFromRetraction f h (Determine r detComm) = Determine (cat.compose h r) commutativity
  where
    commutativity : cat.compose {a, b, c} (cat.compose {a = b, b = a, c} h r) f = h
    commutativity =
      let asoc : cat.compose {a, b, c} (cat.compose {a = b, b = a, c} h r) f ~=~
                 cat.compose {a, b = a , c} h (cat.compose {a, b, c = a} r f)
          asoc = sym $ cat.associativity h r f

          congDetComm : cat.compose {a, b = a, c} h (cat.compose {a, b, c = a} r f) ~=~
                        cat.compose {a, b = a, c} h (cat.id {a})
          congDetComm = cong (cat.compose h) $ detComm
      in rewrite asoc in
         rewrite congDetComm in
         rewrite cat.rightIdentity {a, b = c} h in Refl
