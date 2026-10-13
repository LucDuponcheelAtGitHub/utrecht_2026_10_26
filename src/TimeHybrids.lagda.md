# Formalizing Fred Van Oystaeyen's "Time Hybrids" book

This talk presents a pointfree formalization of a mathematical abstraction of the basics of Fred Van
Oystaeyen's book

- "Time Hybrids: A New Generic Theory of Reality".

The mathematical abstraction is written in another book by Fred Van Oystaeyen

- "Virtual topology and Functor geometry".

Frankly, the mathematical abstraction that I formalize is not fully in sync with Fred's mathematical
abstraction. I know Fred personally and we have many discussions both books. 

I dedicate my work to him. He is an outstanding mathematician who is far too modest to extensively
promote his work. He compares his "Time Hybrids" book with this poem that a Chinese poet carved on a
small stone and throwed into the sea, hoping that, someday, someone would find it, read it, and
appreciate it. 

### Being versus Existing versus Observing

Fred distinguishes *entities* that "are" (pre-things, pre-places) from entities that "exist"
(things, places).

Notice that I used the word "entity" in order to distinguish it from pre-thing and thing.

I will continue doing so.

Moreover, Fred distinguishes entities that we "observe" form entities that "are" or "exist".

... anyway ...

This talk is mainly dealing with entities that "are". In fact, Fred argues that entities that "are",
are more about what reality is all about than entities that "exist", let alone than entities that we
"observe".

## Dynamic Reality

The main aspect of reality is that its universe is dynamic.

One can think about universe change in terms of *cause*, change of universe *time*, or in terms of 
*effect*, change of universe *state* in general and change of universe entities contributing to that
state in particular.

When you ask physicists 
"what is (change of) time" 
they often respond 
"(change of) time is what clocks measure".

But, think about it for a minute, "clocks measure (change of) entities".

More precisely, clocks measure entities that are periodically changing.

Can you think of some examples?

But we just stated that change of entities is caused by change of time. 

Taken together we have 

"Change of time is what clocks measure, change of entities, caused by change of time".

This sounds like circular reasoning 🤔.

This also indicates that, when adopting Fred's Algebraic Generic Theory of Reality, we'd better be
careful when fitting time into Analytic Specializations of it, like Relativity Theory and Quantum
Theory.

According to Fred, Relativity Theory and Quantum Theory are perfect pragmatic approximations of what
reality is all about, but do they really describe reality?

Conclusion about universe time and universe state: it is better to consider (change of) universe
state and (change of) universe time as being the same concept.

## The `Reality` specification

### `import`s

We need primitive `Agda` artifacts and foundational `Cubical` artifacts.

```agda
{-# OPTIONS --cubical --guardedness #-}

module TimeHybrids where

open import Agda.Primitive

open import Cubical.Foundations.Prelude
```

We need the basics of `Categories`, `Functors` and `Profunctors`.

```agda
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Profunctor.Base
```
Think of a category as entities with homomorphisms, between them. Endomorphisms, in this talk called
*transitions*, are homomorphisms between one and the same entity.

Think of a homomorphism as generalizing a function. Homomorphism composition has an identity, is
associative but, typically, is non-commutative.

Think of a transition as a *change* of an entity.

Think of a functor as mapping a change of an entity of one category to a correponding change of an
entity of another category. In other words, if one entity changes, then another entity changes
accordingly.

Think of a heteromorphism (of a profunctor) as a *connection* between entities of one category with
entities of another category. A change of entities of the former category *acts contravariantly*,
upon such a connection from the left resulting in a change of the connection. A change of entities
of the latter category *acts covariantly*, upon such a connection from the right resulting in a
change of the connection.

The words contravariantly resp. covariantly are related to swapping resp. not-swapping the order of
the transitions involved when composing actions
(recall that transitions are, typically, non-commutative).

### Basics

Recall that universe time and universe state are essentially one and the same concept.

In what follows I am using `U` as an identifier instead of `T` or `S`.

The dynamic universe is modeled as a category, `Categoryᵈ`, whose time/state, `U`, object
transitions define change. 

The virtual universe is modeled as a category, `Categoryᵥ`, whose pre-place, `PrePlace`, objects
define a *(virtual) topology*. 

The material universe is modeled as a category, `Categoryₘ`, whose pre-thing, `PreThing`, objects
define *matter*. 

The material collection functor, `Collectionfunctorₘ`, is used to define *pre-thing collections*.

The virtual collection functor, `Collectionfunctorᵥ`, is used to define *pre-place collections*.

Pre-place collections do not play a role in this talk, therefore I do not formalize them
(they do, however, play a role in other parts the book and my formalization of them). 

The *material-to-virtual connection* is modeled as a profunctor, `Profunctorₘᵥ`, whose pre-thing
collection to pre-place, `preThingCollectionPrePlace`, heteromorphisms define
*virtual pre-places of material pre-thing collections*. 

Virtual pre-place change in terms of universe time/state change is modeled as a functor,
`prePlaceFunctor`, mapping time/state transitions to pre-place transitions.

Material pre-thing collection change in terms of time/state universe change is modeled as a functor,
`preThingCollectionFunctor`, mapping time/state transitions to pre-thing collection transitions.

Notice that material universe related concepts were defined at pre-thing *collection* level, not at
pre-thing level. Pre-thing collection changes are not necessarily defined in terms of pre-thing
changes.

... let us move along ...

First we define `ObjectConstrainedFunctor`, constraining which specific type of objects a functor
maps a specific type of objects to.

```agda
record ObjectConstrainedFunctor {o h : Level}
    (Category₁ : Category o h)
    (Obj₁ : Category.ob Category₁)
    (Category₂ : Category o h)
    (Obj₂ : Category.ob Category₂) : Type (o ⊔ h) where
  field
    functor : Functor Category₁ Category₂
    objectTypeConstraint : functor ⟅ Obj₁ ⟆ ≡ Obj₂

open ObjectConstrainedFunctor public
```

We are ready to start with `Reality`.

```
record Reality {o h : Level}

    (Categoryᵈ : Category o h)

    (Categoryᵥ : Category o h)

    (Categoryₘ : Category o h)

    (Collectionfunctorₘ : Functor Categoryₘ Categoryₘ)

    (Profunctorₘᵥ : Profunctor⊶ o h Categoryₘ Categoryᵥ) :

  Type (lsuc (o ⊔ h)) where

  open Category Categoryᵈ renaming (ob to obᵈ)
  open Category Categoryᵥ renaming (ob to obᵥ)
  open Category Categoryₘ renaming (ob to obₘ)

  Homᵈ[_,_] : obᵈ → obᵈ → Type h
  Homᵈ[_,_] = Categoryᵈ [_,_]

  Homᵥ[_,_] : obᵥ → obᵥ → Type h
  Homᵥ[_,_] = Categoryᵥ [_,_]

  Homₘ[_,_] : obₘ → obₘ → Type h
  Homₘ[_,_] = Categoryₘ [_,_]

  Transᵈ[_] : obᵈ → Type h
  Transᵈ[ Z ] = Homᵈ[ Z , Z ]

  Transᵥ[_] : obᵥ → Type h
  Transᵥ[ Z ] = Homᵥ[ Z , Z ]

  Transₘ[_] : obₘ → Type h
  Transₘ[ Z ] = Homₘ[ Z , Z ]

  open Profunctor⊶ Profunctorₘᵥ

  Hetₘᵥ[_,_] : obₘ → obᵥ → Type h
  Hetₘᵥ[_,_] = Het[_,_]

  field

    U : obᵈ

    PrePlace : obᵥ

    PreThing : obₘ

  PreThingCollection : obₘ
  PreThingCollection = Collectionfunctorₘ ⟅ PreThing ⟆

  field

    preThingCollectionPrePlace : Hetₘᵥ[ PreThingCollection , PrePlace ]

  PrePlaceFunctor = 
    ObjectConstrainedFunctor Categoryᵈ U Categoryᵥ PrePlace

  PreThingCollectionFunctor =
    ObjectConstrainedFunctor Categoryᵈ U Categoryₘ PreThingCollection

  field

    prePlaceFunctor : PrePlaceFunctor

    preThingCollectionFunctor : PreThingCollectionFunctor
```

### Movement

How can we define *movement* in a dynamic universe where both pre-places and pre-thing collections
change corresponding to universe time/state changes?

Given a `UniverseTransition`, say `universeTransition`, movement is a `PrePlaceFunctor`, say
`aPrePlaceFunctor`, that satisfies the pointfree equality 

- `aPrePlaceFunctor isMovementAt universeTransition`

defined below.

```agda
  Propertyₕ = Type h
  
  UniverseTransition = Transᵈ[ U ]

  _isMovementAt_ : PrePlaceFunctor → UniverseTransition → Propertyₕ
  aPrePlaceFunctor isMovementAt universeTransition =
    let 
      prePlaceTransition : Transᵥ[ PrePlace ]
      prePlaceTransition =
        transport
          (λ i →  Transᵥ[ (objectTypeConstraint prePlaceFunctor) i ])
            (functor prePlaceFunctor ⟪ universeTransition ⟫)

      preThingCollectionTransition : Transₘ[ PreThingCollection ]
      preThingCollectionTransition =
        transport
          (λ i →  Transₘ[ (objectTypeConstraint preThingCollectionFunctor) i ])
            (functor preThingCollectionFunctor ⟪ universeTransition ⟫)

      movement : Transᵥ[ PrePlace ]
      movement =
        transport
          (λ i → Transᵥ[ (objectTypeConstraint aPrePlaceFunctor) i ])
            (functor aPrePlaceFunctor ⟪ universeTransition ⟫)
    in 
        (preThingCollectionTransition ⋆L preThingCollectionPrePlace)
      ≡ (preThingCollectionPrePlace ⋆R prePlaceTransition) ⋆R movement
```

`preThingCollectionTransition` acts on the left upon `preThingCollectionPrePlace`,
`prePlaceTransition` acts on the right upon `preThingCollectionPrePlace`, and, 
`movement` acts on the right upon the result of the latter action in order to equal it with the
result of the former action.

Notice, on the one hand, how HoTT naturally `transport`s transitions along paths. Both transitions
and paths are *interval*-like, so, HoTT naturally `transport`s intervals along intervals
(a remarkable similarity).

But, on the one hand, HoTT models structural induction, *traditionally discrete*, using 
*continuous* functions on intervals, while, on the other hand, Fred models existing things as
manifestations of pre-things at time intervals, *traditionally continuous*, using transitions
that he treats as *discrete* entities, hence the usage of "at" as opposed to "during",
(a remarkable dissimilarity).

Thanks for listening!
