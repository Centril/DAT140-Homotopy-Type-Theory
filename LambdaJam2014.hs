{-# LANGUAGE GADTs #-}

-- for blanket instance Functor f => Transport0 f :
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}

import Prelude hiding (id, (.))

import Data.Void
import Control.Category

{-

# Lambda Jam 2014

## Things

"Same & Different"

What makes a Shape a Shape?
+ Anything it can be continously deformed into.
  All ways to map shape onto all surfaces, the shape is all such maps.
  i.e: "everything we can __do__ with it"

### The power of representation

+ A "description" of a shape is a datastructure
+ With a repr we can enumerate shapes
+ We can count, combine, transform them
+ Shapes fly first class

## All equivalent functions:

id
\x -> x
(\y x -> y) ()
(\y z x -> x) () ()
flip (\x y -> x) ()

### What makes a function a function?

+ Ignoring syntax, the essence of a function is all functions
  it can be "continously" transformed into.
  i.e: they Act/Do the same

### The power of representation

+ A "description" of a function is a datastructure
+ With a repr we can enumerate functions
+ We can classify, count, combine, transform them
+ Functions fly first class

## Here are some Data Structures
-}

data Pair1 a = Pair1 a a
data Pair2 a = Pair2 (a, ()) a -- If we forget laziness, same as above.
data Pair3 a = Either Void (a, a) -- Acts the same?

{-
### The power of representation

+ A "description" of a data structure is itself a datastructure"
+ With a repr we can enumerate functions
+ We can classify, count, combine, transform them
+ Data structures fly first class

### What makes a structure a structure?

+ Ignoring syntax, the essence of a structure is all structures that it can be
  "continously" transformed into.
  How structures act on inputs (church encoding), then a structure is a function
  that universally captures the actions of the stucture (a fold).

(,)     Either  ()  Void    Maybe

## Usually: Types are Sets

A bag of stuff

## In Homotopy type theory: Types are Spaces

They have structure, form, loops, connections.

## Type Families are Fibrations

Pi = Forall, Sigma = Exists,
U = type in the "universe", I = Interval type

P : Pi (x : Circle). U
P = \x -> (x, I)

Sigma (x : Circle) (P(x))

## Curry-Howard correspondence:

Types are precicely propositions.
Types are precicely spaces. (Homotopy).

## Equalities are Paths

x == y

*----*

## Paths have Higher Paths

(x == y) == (a == b)

      *------*
      |      |
      |      |
      *------*

Points = 0-dim spaces

## Univalence:

True False
 .     .
  \   /
   \ /
    \
   / \
  /   \
 .     .

Univalence axiom: Equivalence is equivalent to equality.
You can only change "True" to "False" if you do it consistently.

Equalities can carry nontrivial computational content
(i.e. they "remember" the path they trace).

## Traditional Type Equality

In old style type theory there's only one way for things to be equal,
you give it back (refl).
-}

{-
class Category where
    id  :: cat a a
    (.) :: cat b c -> cat a b -> cat a c
-}

class Category c => Groupoid c where
    inv :: c a b -> c b a

data Id a b where
    Refl :: Id a a

instance Category Id where
    id          = Refl
    Refl . Refl = Refl

instance Groupoid Id where
    inv Refl    = Refl

applyId :: Id a b -> a -> b
applyId Refl = id

transport :: Id a b -> f a -> f b
transport Refl = id

{-
## Equivalences
-}

data Equiv a b = Equiv (a -> b) (b -> a)

instance Category Equiv where
    id                      = Equiv id id
    Equiv f g . Equiv f' g' = Equiv (f . f') (g' . g)

instance Groupoid Equiv where
    inv (Equiv f g) = Equiv g f

applyE :: Equiv a b -> a -> b
applyE (Equiv f g) = f

{-
Homotopy Type Equality
-}

data IdH a b where
    ReflH :: IdH a a
    UA    :: Equiv a b -> IdH a b -- UA = UnivalenceAxiom

instance Category IdH where
    id           = ReflH

    ReflH . x    = x
    x . ReflH    = x
    UA x . UA y  = UA (x . y)

instance Groupoid IdH where
    inv ReflH  = ReflH
    inv (UA x) = UA (inv x)

applyIdH :: IdH a b -> a -> b
applyIdH ReflH            = id
applyIdH (UA (Equiv f g)) = f

{-
## Univalence, sorta:
-}

equivToId :: Equiv a b -> IdH a b
equivToId = UA

idToEquiv :: IdH a b -> Equiv a b
idToEquiv ReflH  = Equiv id id
idToEquiv (UA x) = x

univalenceAxiom :: Equiv (Equiv a b) (IdH a b)
univalenceAxiom = Equiv equivToId idToEquiv

{-
## Univalence, really:
-}

class Transport0 f where
    transport0 :: IdH a b -> f a -> f b

transportF :: Functor f => IdH a b -> f a -> f b
transportF = fmap . applyIdH

instance Transport0 ((,) a) where
    transport0 = transportF

instance Transport0 (Either e) where
    transport0 = transportF

instance Functor f => Transport0 f where
    transport0 = transportF

class Transport1 f where
    transport1 :: IdH a b -> f a c -> f b c

class Transport2 f where
    transport2 :: IdH a b -> f a c d -> f b c d

{-
Univalence is the claim that all types in haskell are instances of
Transport0 .. TransportN
-}

{-
## What's Next:

### Applications

+ Patch Theory (Lincata et al.)
+ Combinatorial Species (Yorgey et al.)
+ Quotient Types in General
    - Equations under renaming
    - Algebraic Equivalences
    - Time Intervals
    - ... etc.

-}