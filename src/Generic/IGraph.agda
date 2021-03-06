open import Generic.Graph

module Generic.IGraph
  {A B : Set}
  {âª_â«á´µ : A â B}
  (ð® : Graph âª_â«á´µ)
  where

open Graph ð® renaming
  ( â_â to â_âá´µ
  ; â_â to â_âá´µ)

-- Is this ever used?
open import Relation.Binary.PropositionalEquality
open import Data.Product

record IGraph {F : A â Set} {G : B â Set}
       (âª_â« : â {a} â F a â G âª a â«á´µ) : Setâ where
  field R : â {a b} â Graph.P ð® a b â F a â G b â Set
        â_â : â {a} â (x : F a) â R â a âá´µ x âª x â«
        â_â : â {a} {p : P a âª a â«á´µ} {x : F a} {y : G âª a â«á´µ} â R p x y â y â¡ âª x â«
--        â_âá´µ : â {a b} {x : F a} {y : G b} â R x y â Graph.P ð® a b

--  open Graph ð® renaming public
